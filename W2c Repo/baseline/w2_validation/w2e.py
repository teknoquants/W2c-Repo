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

"""Direct diagonal resolvent and clock scaling with positive denominators."""
import numpy as np
checks = 0

def require(condition):
    global checks
    checks += 1
    if not condition:
        raise AssertionError('Numerical validation failed')

def run():
    global checks
    checks=0
    for L in (4,8,16,32):
        z=2*np.pi/L;s,h=np.sin(z/2),np.cos(z/2);m=np.sin(z)
        E=2*np.array([s,h,np.sqrt(1+s*s),np.sqrt(1+h*h)])
        w=(1/E)/sum(1/E);A=w@E
        for xi in (.9,1,1.1):
            margin=1/sum(w/(xi*E-xi*m))
            raw_ratio=(xi*A-xi*m-margin)/(xi*A)
            reference=(A-m-1/sum(w/(E-m)))/A
            require(abs(raw_ratio-reference)<5e-14 and margin>0)
    print('W2e | 12 clock-resolvent comparisons')
    return checks
if __name__=='__main__':run()
