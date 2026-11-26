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

"""Recompile an immutable check-only packet and compare the submitted transcript."""
import argparse
from pathlib import Path
from packet import audit, ensure, equivalent_output, run_lean, verify

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('output',type=Path);p.add_argument('--file',required=True,type=Path)
    p.add_argument('--report',type=Path)
    a=p.parse_args();src=a.file.read_bytes().decode()
    meta,_=verify(src,src);ensure(not meta['module'],'Expected a check-only packet.')
    raw=run_lean(a.file);ensure(equivalent_output(a.output.read_bytes(),raw,src),'Supplied transcript differs from replay.')
    rows=audit(raw,src)
    if a.report:
        a.report.parent.mkdir(parents=True,exist_ok=True)
        a.report.write_text('# Kernel axiom audit\n\n| Declaration | Transitive axioms |\n|---|---|\n'+''.join('| `'+n+'` | '+(', '.join(v) or 'none')+' |\n' for n,v in rows.items()))
    print('AUDIT PASSED |',meta['unit'],'|',len(rows),'axiom records')
