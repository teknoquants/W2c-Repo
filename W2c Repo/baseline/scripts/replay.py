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

"""Fresh unit and module replays against the frozen release; preserve local raw stdout."""
import argparse
import os
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from packet import ROOT, UNITS, audit, bodies, ensure, make, run_lean, sha, sources, verify

def record(unit, prelude=False):
    key='common-prelude' if prelude else unit.lower()
    name='prelude' if prelude else unit+'_final'
    folder=ROOT/'records'/(key+'-v1')
    folder.mkdir(parents=True,exist_ok=True)
    file=folder/'final.lean'
    src=make(unit,prelude=prelude)
    file.write_text(src)
    raw=run_lean(file)
    verify(src,src);proofs=audit(raw,src)
    (folder/'final.local.out').write_bytes(raw)
    (folder/'lean_report.md').write_text('# '+key+' local kernel audit\n\nLocal Lean 4.36.0 replay.\n\nPacket SHA-256 `'+sha(src.encode())+'`.\n\n| Declaration | Transitive axioms |\n|---|---|\n'+''.join('| `'+n+'` | '+(', '.join(v) or 'none')+' |\n' for n,v in proofs.items()))
    if not prelude:
        subprocess.run([sys.executable,str(ROOT/'scripts/make_packet.py'),'--final',unit],cwd=ROOT,check=True,stdout=subprocess.DEVNULL)
    return f'PASS {name} | {len(proofs)} '+('prelude declarations' if prelude else 'proofs, including dependencies')

def module_check(path):
    unit=Path(path).parts[1]
    if unit=='Research':unit='W2'
    if unit=='Framework':unit='W2e'
    with tempfile.TemporaryDirectory() as work:
        work=Path(work)
        template, proof, out=(work/p for p in ('retained.lean','candidate.lean','local.out'))
        template.write_text(make(unit,path));proof.write_text(make(unit,path,solved=True))
        out.write_bytes(run_lean(proof))
        result=subprocess.run([sys.executable,str(ROOT/'scripts/check_return.py'),str(template),str(proof),str(out)],cwd=ROOT,capture_output=True,text=True)
        ensure(result.returncode==0,result.stdout+result.stderr)
        ensure((ROOT/'extracted'/path).read_bytes()==(ROOT/path).read_bytes(),'Extracted module differs from local source.')
        record_path=ROOT/'records/modules'/Path(path).with_suffix('')
        record_path.mkdir(parents=True,exist_ok=True)
        (record_path/'local.out').write_bytes(out.read_bytes())
        (record_path/'sha256.txt').write_text('retained '+sha(template.read_bytes())+'\nreturned '+sha(proof.read_bytes())+'\nstdout '+sha(out.read_bytes())+'\n')
        return result.stdout.strip()

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--modules',action='store_true');p.add_argument('--jobs',type=int,default=2)
    a=p.parse_args()
    with ThreadPoolExecutor(max_workers=a.jobs) as pool:
        if a.modules:
            tasks=[(module_check,path) for path in sources() if bodies((ROOT/path).read_text())]
        else:
            tasks=[(record,unit) for unit in UNITS]+[(lambda _:record('Common',True),None)]
        futures=[pool.submit(func,arg) for func,arg in tasks]
        results=[]
        for future in futures:
            line=future.result();results.append(line);print(line,flush=True)
    dest=ROOT/'records'/('module-replay.txt' if a.modules else 'unit-replay.txt')
    dest.write_text('\n'.join(results)+'\n')
