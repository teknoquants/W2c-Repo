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

"""Run eight independent Python parts in sequence without starting a Lean process."""
import argparse
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import json
from collections import Counter

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out',type=Path,help='keep fresh numerical records in this external directory')
    args=parser.parse_args()
    here=Path(__file__).resolve().parent
    with tempfile.TemporaryDirectory(prefix='w2cr-run-') as name:
        dest=(args.out if args.out else Path(name)).resolve()
        if dest.is_relative_to(here.parent):parser.error('choose an output directory outside this immutable release')
        dest.mkdir(parents=True,exist_ok=True)
        env=dict(os.environ,OPENBLAS_NUM_THREADS='1',MKL_NUM_THREADS='1',OMP_NUM_THREADS='1',PYTHONHASHSEED='0')
        counts=Counter()
        for part in range(1,9):
            subprocess.run([sys.executable,str(here/f'part{part}.py'),str(dest)],env=env,check=True)
            for row in json.loads((dest/f'checks-{part}.json').read_text()):counts[row['target']]+=1
        print('Rebuilt suite:',sum(counts.values()),'assertions')
        for u,n in zip('ABCDEF',(8,8,8,8,7,7)):
            print(' | '.join(f'{u}.{i} {counts[f"{u}.{i}"]}' for i in range(1,n+1)))
        if args.out:print('Computed data:',dest)
if __name__=='__main__':main()
