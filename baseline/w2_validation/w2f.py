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

"""Check the transfer floor and time factor on illustrative, explicitly chosen trajectories."""
import math
checks = 0

def require(condition):
    global checks
    checks += 1
    if not condition:
        raise AssertionError('Numerical validation failed')

def run():
    global checks
    checks=0
    A=11*2*math.log(2)/(12*math.pi**2)
    xs=1/6;r=.5
    for K in (10,100,1000,10000):
        x=[1/(6+A*(K-j)) for j in range(K+1)]
        eta=[t*t+.01*4.**(-j) for j,t in enumerate(reversed(x[:-1]))]
        S=xs**2+xs/A+.01*4/3
        require(max(eta)<r and sum(eta)<=S and sum(math.log1p(-v) for v in eta)>=-S/(1-r))
        for c1 in (-.1,.1):
            c=[1+c1*t for t in x]
            require(abs(math.prod(l/h for l,h in zip(c,c[1:]))-c[0]/c[-1])<3e-12)
    print('W2f | 4 weak-product floors and 8 endpoint comparisons')
    return checks
if __name__=='__main__':run()
