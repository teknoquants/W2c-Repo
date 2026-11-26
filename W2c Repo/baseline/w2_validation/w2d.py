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

"""Free retained-defect diagnostic and weak-running geometric bound."""
import csv,math
from pathlib import Path
checks = 0

def require(condition):
    global checks
    checks += 1
    if not condition:
        raise AssertionError('Numerical validation failed')

def run():
    global checks
    checks=0
    root=Path(__file__).resolve().parents[1]
    with (root/'study/benchmark/axial.csv').open() as f:
        for row in csv.DictReader(f):
            estimate=1/float(row['cov_ratio'])-1
            require(abs(float(row['retained_defect_over_m'])-estimate)<2e-14 and estimate<0)
    A=11*2*math.log(2)/(12*math.pi**2);b=A/(4*math.log(2))
    for n in (0,2,8,64):
        require(2.**(-n)<=math.exp(-A*n/(6*b))+1e-15)
        require(sum(4.**(-k) for k in range(n))<=4/3+1e-15)
    print('W2d | 4 axial identities and 4 paired running/geometric checks')
    return checks
if __name__=='__main__':run()
