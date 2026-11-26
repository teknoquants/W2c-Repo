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

"""Replay local records and compare the editable document to the canonical evidence."""
import json
import sys
from pathlib import Path
import math
from common import ROOT, OUT, Checks, output
sys.path.insert(0,str(ROOT/'scripts'))
from catalogue import BOOK, FIGURES, counts, signatures, sources
from extract_sources import read_book
import formal
import release
from tables import numerical

def equivalent(a,b):
    if a==b:return True
    if isinstance(a,list) and isinstance(b,list):
        return len(a)==len(b) and all(equivalent(x,y) for x,y in zip(a,b))
    try:
        # Rounded table cells include eigensolver residuals; both must obey the
        # independent per-part residual criterion before reaching this point.
        x,y=float(a),float(b)
        return math.isclose(x,y,rel_tol=3e-6,abs_tol=1e-8)
    except (ValueError,TypeError):
        return False

def run(out):
    c=Checks()
    controls,media=read_book(BOOK)
    raw=formal.audit()
    rows=signatures();expected={r['name'] for r in rows}
    c.test('F.5',set(raw)==expected,'combined kernel transcript covers every registered declaration')
    c.test('F.5',set(k[4:] for k in controls if k.startswith('sig:'))==expected and
           all(controls['sig:'+r['name']]==r['signature'] for r in rows),'all printed declaration statements match the canonical bytes')
    c.test('F.5',all(controls['src:'+s]==(ROOT/s).read_bytes() for s in sources()) and
           {s for s in controls if s.startswith('src:')}=={'src:'+s for s in sources()},'entire printed Lean and Python library round trips byte for byte')
    c.test('F.5',(ROOT/'records/w2c-r/upstream.local.out').read_bytes()==(ROOT/'baseline/records/w2-v1/final.local.out').read_bytes(),
           'fresh upstream kernel record agrees with the released upstream record')
    published=numerical(OUT);new=numerical(out)
    c.test('F.6',all(controls['tbl:'+k]==v[1] for k,v in published.items()),'every published numerical table matches its saved data')
    c.test('F.6',all(equivalent(v[1],new[k][1]) for k,v in published.items()),'new calculations reproduce the displayed values at the printed precision or numerical tolerance')
    targets=json.loads((ROOT/'docs/targets.json').read_text());count=counts(out)
    c.test('F.6',len(targets)==46 and all(controls['prompt:'+r['id']]=='Prompt status   '+r['expected'] for r in targets) and all(controls['target:'+r['id']]==r['actual']+' | '+str(count[r['id']])+' tagged checks' for r in targets),
           'all 46 target outcomes and check counts agree with the exercise')
    c.test('F.6',all((ROOT/f'figures/{k}.png').read_bytes() in media for k,_ in FIGURES),'all six reproduced figures are present as exact Word image objects')
    c.test('F.7',release.verify()>0,'manifest protects every distributed file')
    c.test('F.7', all('MIT License' in (ROOT/s).read_text() for s in sources() if s.startswith(('W2/W2cR/Rebuilt/','scripts/','w2cr_validation/'))),
           'every newly developed script and Lean module contains the MIT grant')
    c.test('F.7',set(r['id'] for r in targets)=={f'{u}.{i}' for u,n in zip('ABCDEF',[8,8,8,8,7,7]) for i in range(1,n+1)}
           and (ROOT/'W2c-R-Rebuilt-Exercise.pdf').stat().st_size>10000,'complete target inventory, PDF and editable document')
    c.finish(8,out)
if __name__=='__main__':run(output())
