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

"""Compare retained statements, replay a returned source, and check its actual axiom inventory."""
import argparse
from pathlib import Path
from packet import ROOT, audit, ensure, equivalent_output, run_lean, subst, verify

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ('retained','candidate','transcript'):
        parser.add_argument(name,type=Path)
    a=parser.parse_args()
    src=a.candidate.read_bytes().decode();meta, proofs=verify(a.retained.read_bytes().decode(),src)
    raw=run_lean(a.candidate)
    ensure(equivalent_output(a.transcript.read_bytes(),raw,src),'Submitted output differs from fresh Lean stdout.')
    results=audit(raw,src)
    if meta['module']:
        path=ROOT/'extracted'/meta['module'];path.parent.mkdir(parents=True,exist_ok=True)
        path.write_text(subst((ROOT/meta['module']).read_text(),{k:proofs[k] for k in meta['editable']}))
    print('CHECK PASSED |',meta['module'] or meta['unit'],'|',len(results),'axiom records')
