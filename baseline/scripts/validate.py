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

"""Validate the complete exercise, frozen declarations, modules and numerical evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory
from packet import ROOT, UNITS, ensure, equivalent_output, frozen, metadata, module_decls, sources, verify, audit, run_lean
from prompt_reader import read_targets

def coverage():
    frozen()
    data=json.loads((ROOT/'study/claims.json').read_text())
    master=ROOT/'W2-Upgraded-Prompt.docx'
    ensure(data['specification_sha256']==hashlib.sha256(master.read_bytes()).hexdigest(),'Unexpected integrated specification.')
    targets=read_targets(master);claims=data['claims']
    ensure([r['id'] for r in claims]==list(targets),'Target list differs from the specification.')
    inventory={n:private for path in sources() for n,private in module_decls(path)}
    public={n for n,private in inventory.items() if not private}
    rows=[s.split('\t') for s in (ROOT/'scripts/released.tsv').read_text().splitlines() if not s.startswith('#')]
    ensure({r[0] for r in rows}==public and len(rows)==len(public),'Incomplete released-proof inventory.')
    from packet import DEFS
    import re
    inputs=set()
    for path in sources():
        s=(ROOT/path).read_text()
        ns=re.search(r'^namespace (W2[.\w]*)',s,re.M)[1]
        inputs.update(ns+'.'+n for n in DEFS.findall(s))
    for c in claims:
        ensure(c['lean'] or c['inputs'],'Missing proof or research obligation: '+c['id'])
        ensure(set(c['lean'])<=public and set(c['inputs'])<=inputs,'Unrecognized proof or predicate: '+c['id'])
        ensure(len(c['proof'])>=120 and c['kind']==targets[c['id']]['kind'] and c['statement_sha256']==targets[c['id']]['signature'],'Missing derivation or changed type.')
    lic=(ROOT/'LICENSE').read_text().strip()
    for f in [*(ROOT/'W2').rglob('*.lean'),ROOT/'W2.lean',*(ROOT/'scripts').glob('*.py'),*(ROOT/'w2_validation').rglob('*.py')]:
        text=f.read_text()
        plain='\n'.join(line.removeprefix('# ').removeprefix('#') if f.suffix=='.py' else line for line in text.splitlines())
        ensure(lic in plain, 'Incomplete MIT notice: '+str(f))
    record_names={f.name for f in (ROOT/'records').glob('*-v1') if f.is_dir()}
    ensure(record_names=={unit.lower()+'-v1' for unit in UNITS}|{'common-prelude-v1'},'Incomplete set of unit records.')
    ensure(all(r[2] in ('L1','L2') and r[1] and r[3] for r in rows),'Public release classification missing.')
    for folder in sorted((ROOT/'records').glob('*-v1')):
        src=(folder/'final.lean').read_text();verify(src,src);audit((folder/'final.local.out').read_bytes(),src)
    print(f'{len(claims)} numbered targets | {len(public)} public Lean proofs | {len(inventory)-len(public)} private helpers | reference records parsed',flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--python-only',action='store_true');p.add_argument('--modules',action='store_true',help='also run every individual fill-return comparison');a=p.parse_args()
    coverage()
    env={**os.environ,'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1','LEAN_NUM_THREADS':os.environ.get('LEAN_NUM_THREADS','3')}
    subprocess.run([sys.executable,str(ROOT/'w2_validation/run_all.py')],env=env,cwd=ROOT,check=True)
    if not a.python_only:
        subprocess.run(['lake','build'],env=env,cwd=ROOT,check=True)
        for folder in sorted((ROOT/'records').glob('*-v1')):
            path=folder/'final.lean';raw=run_lean(path)
            ensure(raw==(folder/'final.local.out').read_bytes(),'Recorded local stdout differs from fresh replay at '+folder.name)
            audit(raw,path.read_text())
            print('REPLAY PASSED |',folder.name,flush=True)
            hosted=folder/'final.out'
            if hosted.exists():ensure(equivalent_output(hosted.read_bytes(),raw,path.read_text()),'Hosted return differs from local check.')
        if a.modules:subprocess.run([sys.executable,str(ROOT/'scripts/replay.py'),'--modules'],env=env,cwd=ROOT,check=True)
    print('VALIDATION PASSED',flush=True)
