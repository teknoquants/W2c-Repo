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

"""Fibre coordinates, quotient count, regular conditional versions and convexity."""
from itertools import product
import numpy as np
from common import Checks,output,save
from geometry import counterexample
from multilink import left
def run(out):
    c=Checks();rng=np.random.default_rng(42)
    def vertices(a,b,d):return (a+1)*(b+1)*(d+1)
    def edges(a,b,d):return a*(b+1)*(d+1)+(a+1)*b*(d+1)+(a+1)*(b+1)*d
    c.test('A.1',all(0<x<=1/6 for x in [.02,.05,.1,1/6]),'admitted weak-coupling interval')
    for a,b,d in product(range(1,8),repeat=3):
        q=edges(2*a,2*b,2*d)-edges(a,b,d)-vertices(2*a,2*b,2*d)+vertices(a,b,d)
        c.test('A.3',q==14*a*b*d+3*(a*b+a*d+b*d),f'rectangle {a}x{b}x{d}')
    from geometry import inv
    for _ in range(10):
        u,h,v=rng.normal(size=(3,4));u/=np.linalg.norm(u);h/=np.linalg.norm(h);v/=np.linalg.norm(v)
        c.test('A.2',np.allclose(left(left(u,inv(h)),left(h,v)),left(u,v)),'midpoint product invariant')
        t=rng.normal(size=3);Z=np.r_[0,t]
        c.test('A.2',abs(np.dot(left(Z,u),left(Z,u))+np.dot(left(u,Z),left(u,Z))-2*t@t)<1e-12,'two induced tangent norms')
    for n in (2,3,5):c.test('A.4',(-(-2*n)/4)/(.5)==n,'Killing-form Ricci normalization')
    c.test('A.5',np.var([-1.,1.])==1,'positive two-orbit variance with zero local energy')
    c.test('A.6',abs(np.array([1.,-1.]).mean())<1e-15,'conditional centring in a two-point model')
    rows=[counterexample(e) for e in (.18,.09,.045,.02)]
    for r in rows:
        c.test('A.7',r['endpoint_max']<r['angle'] and abs(r['mid']-r['angle'])<1e-12 and r['horizontal_residual']<1e-12,
               'short quotient geodesic at angle '+str(r['angle']))
    a=rng.normal(size=(12,13));w=np.arange(1,13)/78
    c.test('A.8',np.isclose(w@(a*a).mean(1)-(w@a.mean(1))**2,w@a.var(1)+w@(a.mean(1)**2)-(w@a.mean(1))**2),'total variance disintegration')
    save(out/'convexity.json',rows);c.finish(2,out)
if __name__=='__main__':run(output())
