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

"""Canonical listings, exact signatures and data controls printed in the exercise."""
from pathlib import Path
import csv
import json
import re
from collections import Counter
import formal

ROOT = Path(__file__).resolve().parents[1]
BOOK = ROOT / 'W2c-R-Rebuilt-Exercise.docx'
DATA = ROOT / 'data/w2cr'
NS = {'w':'http://schemas.openxmlformats.org/wordprocessingml/2006/main'}
FIGURES = [('geometry','Fine paths, the retained product and the midpoint.'),
           ('swaps','Four adjacent transpositions on a maximal path in dimension three.'),
           ('spectra','Periodic and open scalar gaps. The two panels have independent vertical scales.'),
           ('chain','Conditional implications and the boundary premise required for the Wilson law.'),
           ('kernel','Absolute shell envelope of the projected precision, with a cubic reference slope.'),
           ('strip','Finite-slab coupled SU(2) trials. Error bars are chain-level 95% intervals.')]

def sources():
    found = {ROOT/'W2.lean', ROOT/'W2cR.lean', ROOT/'packets/W2cR_final.lean'}
    for folder,pattern in [('W2','**/*.lean'),('scripts','*.py'),('w2cr_validation','*.py'),
                           ('baseline/scripts','*.py'),('baseline/w2_validation','**/*.py'),
                           ('baseline-paper/w2_validation','*.py')]:
        found.update((ROOT/folder).glob(pattern))
    return sorted(p.relative_to(ROOT).as_posix() for p in found)

def signatures():
    rows = []
    for path in sorted((ROOT/'W2/W2cR').glob('*.lean')):
        txt = path.read_text().split('namespace W2.W2cR')[-1].split('end W2.W2cR')[0]
        for m in re.finditer(r'^(theorem|structure|def) (\w+)\b',txt,flags=re.M):
            kind,name=m.group(1,2)
            if name not in formal.PRIOR: continue
            body=txt[m.start():].split('/--',1)[0].rstrip()
            if kind=='theorem':body=body.split(':= by')[0]+':= by'
            target=formal.PRIOR[name]
            level='Def' if kind in ('def','structure') else ('L2' if name in ('fibre_poincare_of_hessian','eliminated_gap_small_field') else 'L1')
            rows.append(dict(name=formal.NS+name,kind=kind,target=target,level=level,signature=body,path=path.relative_to(ROOT).as_posix()))
    for u in formal.UNITS:
        for row in formal.entries(u):
            rows.append(dict(row,path=f'W2/W2cR/Rebuilt/{u}.lean'))
    return rows

def counts(out=DATA):
    c=Counter()
    for part in range(1,8):
        for r in json.loads((out/f'checks-{part}.json').read_text()):c[r['target']]+=1
    c.update({'F.5':4,'F.6':4,'F.7':3})
    return c

def source_bytes(name):
    return (ROOT/name).read_bytes()

def lines_with_format(data):
    text=data.decode('utf-8')
    eol='\r\n' if '\r\n' in text else '\n'
    normalized=text.replace(eol,'\n')
    assert '\r' not in normalized
    terminal=normalized.endswith('\n')
    lines=normalized[:-1].split('\n') if terminal else normalized.split('\n')
    return lines, ('CRLF' if eol=='\r\n' else 'LF'), terminal
