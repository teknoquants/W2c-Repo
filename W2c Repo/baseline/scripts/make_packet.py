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

"""Build the versioned master, unit, prelude or module return packet."""
import argparse
from pathlib import Path
from packet import ROOT, UNITS, make

if __name__ == '__main__':
    p=argparse.ArgumentParser(description=__doc__)
    modes=p.add_mutually_exclusive_group(required=True)
    modes.add_argument('module',nargs='?')
    modes.add_argument('--final',choices=UNITS)
    modes.add_argument('--prelude',nargs='?',const='Common',choices=UNITS)
    p.add_argument('--unit',choices=UNITS,default='W2')
    p.add_argument('--emit-return',action='store_true')
    a=p.parse_args()
    unit=a.final or a.prelude or a.unit
    name=Path(a.module).stem if a.module else ('prelude' if a.prelude else unit+'_final')
    source=make(unit,a.module,bool(a.prelude))
    folder=ROOT/'packets';folder.mkdir(exist_ok=True)
    (folder/(name+'.lean')).write_text(source)
    intro=('Fill only the indented tactic blocks marked for editing. Return the complete file and actual compiler output.'
           if a.module else 'Run the enclosed source without edits. Return the complete actual compiler stdout as plain text, including its final newline. If execution is unavailable, state that explicitly.')
    (folder/(name+'.txt')).write_text(intro+' Use Lean and Mathlib v4.36.0.\n\n```lean\n'+source+'```\n')
    if a.emit_return and a.module:
        (ROOT/'returns').mkdir(exist_ok=True)
        (ROOT/'returns'/(name+'.lean')).write_text(make(unit,a.module,solved=True))
    print(folder/(name+'.lean'))
