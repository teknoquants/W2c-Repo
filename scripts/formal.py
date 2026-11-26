# SPDX-License-Identifier: MIT
# MIT License
#
# Copyright (c) 2026 Roger Cooperman; A.E. Petrunina V.V.
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

"""Freeze, assemble and audit statement and proof packets. Run Lean separately."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys
from tempfile import NamedTemporaryFile

ROOT=Path(__file__).resolve().parents[1]
PACK=ROOT/'packets'
REC=ROOT/'records/w2c-r'
UNITS='ABCDEFS'
NS='W2.W2cR.'
ALLOW={'propext','Quot.sound','Classical.choice'}
PRIOR={'gaussian_chaos_gap':'B.3','gaussian_chaos_gap_pos':'B.3','hessian_floor':'D.3',
       'hessian_floor_matrix':'D.3','BakryEmery':'D.1','HessianLowerBoundHyp':'D.1',
       'fibre_poincare_of_hessian':'E.2','eliminated_gap_small_field':'E.3','freeModel_curv':'E.2',
       'freeModelHyp':'E.2','freeModel_bakryEmery':'E.2','curvature_excludes_collapse':'E.4',
       'separation_explicit':'E.6'}

def sha(x):
    return hashlib.sha256(x.encode() if isinstance(x,str) else x).hexdigest()

def write_record(path, value):
    """Leave a matching frozen file untouched and replace a changed file atomically."""
    data=value.encode('utf-8')
    if path.exists() and path.read_bytes()==data:
        return
    work=ROOT/'.lake'
    work.mkdir(exist_ok=True)
    with NamedTemporaryFile(dir=work,delete=False) as tmp:
        tmp.write(data)
        name=Path(tmp.name)
    try:
        name.replace(path)
    finally:
        name.unlink(missing_ok=True)

def check(test,message):
    if not test: raise ValueError(message)

def source(unit):
    return (ROOT/f'W2/W2cR/Rebuilt/{unit}.lean').read_text()

def entries(unit):
    text=source(unit).split('namespace W2.W2cR\n',1)[1].rsplit('end W2.W2cR',1)[0].strip()
    parts=re.split(r'^-- @result (\S+) (\S+)\n',text,flags=re.M)
    check(not parts[0].strip(),'Unregistered declaration')
    for target,level,body in zip(parts[1::3],parts[2::3],parts[3::3],strict=True):
        body=body.rstrip()
        m=re.match(r'(?:noncomputable )?(theorem|def|structure) (\w+)',body)
        check(m,'Unknown declaration '+body[:70])
        signature=body.split(':= by\n')[0]+':= by' if m[1]=='theorem' else body
        yield dict(unit=unit,target=target,level=level,name=NS+m[2],kind=m[1],
                   signature=signature,body=body)

def locks():
    return 'unit\ttarget\tlevel\tdeclaration\tsha256\n'+''.join(
        f"{r['unit']}\t{r['target']}\t{r['level']}\t{r['name']}\t{sha(r['signature'])}\n"
        for u in UNITS for r in entries(u))

def inherited():
    base=(ROOT/'baseline/packets/W2_final.lean').read_text()
    annex=(ROOT/'sources/prior-annex.lean').read_text()
    head=base[base.index('module\npublic import Mathlib'):base.index('#eval Lean.versionString')].rstrip()
    tail=annex[annex.index('-- Source W2/W2cR/FreeGap.lean'):annex.index('#eval Lean.versionString')].rstrip()
    return head+'\n\n'+tail

def packet(units,statement=False):
    chunks=[inherited()]
    names=list(NS+n for n in PRIOR) if len(units)>1 else []
    for u in units:
        blocks=[]
        for r in entries(u):
            blocks.append(r['signature']+'\n  sorry' if statement and r['kind']=='theorem' else r['body'])
            names.append(r['name'])
        chunks.append('namespace W2.W2cR\n\n'+'\n\n'.join(blocks)+'\n\nend W2.W2cR')
    src='\n\n'.join(chunks)+'\n\n#eval Lean.versionString\n'
    if not statement:
        check(not re.search(r'\b(sorry|sorryAx|admit|axiom|run_tac|native_decide)\b',src),'Forbidden final construct')
        src+=''.join('#print axioms '+n+'\n' for n in names)
    stamp='W2c-R-rebuilt '+sha(src)
    return src+'#eval "'+stamp+'"\n',names,stamp

def prepare(mode):
    lock=ROOT/'locks/w2c-r.tsv'
    if mode=='freeze' and not lock.exists():write_record(lock,locks())
    check(lock.read_text()==locks(),'Frozen declaration changed')
    if mode=='freeze':
        for u in UNITS:
            src,_,_=packet(u,True)
            path=REC/'statement-round'/f'{u}.lean'
            if path.exists():check(path.read_text()==src,'Retained packet changed')
            else:write_record(path,src)
    else:
        folder=REC/'fill';folder.mkdir(exist_ok=True)
        for u in UNITS:write_record(folder/f'{u}.lean',packet(u)[0])
        src=packet(UNITS)[0]
        write_record(PACK/'W2cR_final.lean',src)
        write_record(PACK/'W2cR_final.txt','Check this immutable file in Lean 4.36.0 with Mathlib v4.36.0. Return the complete raw compiler output.\n\n```lean\n'+src+'```\n')
        write_record(REC/'final.lean',src)

def audit_one(path,units,statement=False):
    src,names,stamp=packet(units,statement)
    check(path.with_suffix('.lean').read_text()==src,'Packet mismatch '+str(path))
    out=path.read_text().splitlines()
    check(out[-1:]==['"'+stamp+'"'],'Fingerprint mismatch '+str(path))
    if statement:
        holes=sum(r['kind']=='theorem' for u in units for r in entries(u))
        check(out[-2]=='"4.36.0"' and len(out)==holes+2 and all(re.fullmatch(r'<stdin>:\d+:\d+: warning: declaration uses `sorry`',l) for l in out[:-2]),'Statement diagnostics changed')
        return {}
    check(out[0]=='"4.36.0"','Wrong version')
    rows={}
    for l,name in zip(out[1:-1],names,strict=True):
        m=re.fullmatch(r"'([\w.]+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)",l)
        check(m and m[1]==name,'Missing axiom row '+name)
        ax=(m[2] or '').split(', ') if m[2] else []
        check(set(ax)<=ALLOW,'Unapproved axiom for '+name)
        rows[name]=ax
    return rows

def audit(write=False):
    check(locks()==(ROOT/'locks/w2c-r.tsv').read_text(),'Locked type changed')
    for u in UNITS:
        audit_one(REC/'statement-round'/f'{u}.out',u,True)
        audit_one(REC/'fill'/f'{u}.out',u)
    src,_,_=packet(UNITS)
    check(src==(PACK/'W2cR_final.lean').read_text() and src==(REC/'final.lean').read_text(),'Final source mismatch')
    local=REC/'final.local.out'
    # The canonical final filename differs from its transcript suffix.
    alias=REC/'final.out'
    def read_final(p):
        lines=p.read_text().splitlines()
        _,names,stamp=packet(UNITS)
        check(lines[0]=='"4.36.0"' and lines[-1]=='"'+stamp+'"','Final fingerprint')
        rows={}
        for name,line in zip(names,lines[1:-1],strict=True):
            m=re.fullmatch(r"'([\w.]+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)",line)
            check(m and m[1]==name,'Final declaration '+name)
            axioms=(m[2] or '').split(', ') if m[2] else []
            check(set(axioms)<=ALLOW,'Final axioms '+name);rows[name]=axioms
        return rows
    rows=read_final(local)
    if alias.exists():check(read_final(alias)==rows,'Hosted and local records differ')
    evidence={'version':'4.36.0','source_sha256':sha(src),'transcript_sha256':sha(local.read_bytes()),'declarations':rows}
    target=REC/'audit.json'
    if write:write_record(target,json.dumps(evidence,indent=2)+'\n')
    else:check(json.loads(target.read_text())==evidence,'Published audit mismatch')
    print(f'PASS | seven statement and seven fill packets | {len(rows)} final declarations')
    return rows

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('action',choices=['freeze','prepare','record','audit'])
    action=p.parse_args().action
    if action in ('freeze','prepare'):prepare(action)
    else:audit(action=='record')
