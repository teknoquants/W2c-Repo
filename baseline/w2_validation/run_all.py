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

"""Recompute the original baseline, the clock quadrature and every W2 numerical unit."""
import csv
import math
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
import w2b,w2c,w2d,w2e,w2f

ROOT=Path(__file__).resolve().parents[1]

def compare_tables(folder, reference):
    produced=sorted(p.name for p in folder.glob('*.csv'))
    expected=sorted(p.name for p in reference.glob('*.csv'))
    if produced!=expected:raise ValueError(f'Table list changed: {produced}, {expected}')
    for name in expected:
        with (folder/name).open() as a,(reference/name).open() as b:
            ar,br=csv.DictReader(a),csv.DictReader(b)
            if ar.fieldnames!=br.fieldnames:raise ValueError('Column mismatch '+name)
            for i,(l,r) in enumerate(zip(ar,br,strict=True),start=2):
                for key in r:
                    if l[key]==r[key]:continue
                    try:match=math.isclose(float(l[key]),float(r[key]),rel_tol=4e-8,abs_tol=3e-10)
                    except ValueError:match=False
                    if not match:raise ValueError(f'{name}:{i} {key} {l[key]} differs from {r[key]}')
    return len(expected)

def main():
    if not __debug__:raise SystemExit('Run Python without -O so assertions are active.')
    env={**os.environ,'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1'}
    legacy=ROOT/'w2_validation/baseline/run_all.py'
    r=subprocess.run([sys.executable,str(legacy)],capture_output=True,text=True,cwd=legacy.parent,env=env)
    print(r.stdout,flush=True)
    if r.returncode or r.stdout.count('[PASS]')!=46:raise ValueError('The 46-check baseline failed. '+r.stderr)
    with tempfile.TemporaryDirectory() as tmp:
        tmp=Path(tmp);(tmp/'scripts').mkdir()
        copied=tmp/'scripts/w2ar_numerical.py'
        shutil.copyfile(ROOT/'w2_validation/w2ar_numerical.py',copied)
        s=subprocess.run([sys.executable,str(copied)],cwd=tmp,capture_output=True,text=True,env=env,check=True)
        checks=46+int(re.search(r'W2a-R numerical assertions: (\d+)',s.stdout)[1])
        tables=compare_tables(tmp/'numerical',ROOT/'study/w2ar_reference')
        print(f'W2a-R | recomputed {tables} reference tables, including the two recorded Wilson residuals')
        target=tmp/'benchmark';target.mkdir();checks+=w2b.run(target)
        print(f'W2b | recomputed {compare_tables(target,ROOT/"study/benchmark")} tables')
    for unit in (w2c,w2d,w2e,w2f):checks+=unit.run()
    print('Executed numerical assertions (baseline and six units):',checks)
    print('PYTHON VALIDATION PASSED')
if __name__=='__main__':main()
