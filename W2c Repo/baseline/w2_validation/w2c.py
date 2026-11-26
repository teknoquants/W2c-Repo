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

"""Finite-volume checks of the count and of the collapsing trial function."""
import math
from scipy.integrate import quad

checks = 0

def require(condition):
    global checks
    checks += 1
    if not condition:
        raise AssertionError('Numerical validation failed')

def run():
    global checks
    checks=0
    for n in (1,2,4,8):
        vertices=lambda j:(j+1)**3
        links=lambda j:3*j*(j+1)**2
        require(links(2*n)-links(n)-vertices(2*n)+vertices(n)==14*n**3+9*n**2)
    for s in (0,2,8,16):
        # Normalize both integrals by e^s.
        numerator=32*quad(lambda x:math.exp(s*(x*x-1)),0,.25)[0]
        denominator=2*quad(lambda x:min(1,4*x)**2*math.exp(s*(x*x-1)),0,1,points=[.25])[0]
        require(numerator/denominator<=8*math.exp(-3*s/16)+1e-13)
    print('W2c | 4 open-box counts and 4 Rayleigh bounds')
    return checks
if __name__=='__main__':run()
