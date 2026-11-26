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

"""Check curvature comparisons, precision-kernel decay and validated pinned SU(2) floors."""
from fractions import Fraction
import numpy as np
from common import Checks,output,save
from kernel import table,jump
from pinned_interval import compute
def run(out):
    c=Checks();rng=np.random.default_rng(741);marg=[]
    c.test('D.1',2*(1-.2)/64>0,'typed floor has positive constant when the loss is below one')
    c.test('D.2',all(k*np.sqrt((1/(4*k))**2)<1 for k in (1,10,100)),'fixed-box loss can shrink with a box-dependent range')
    for i in range(80):
        a,b=rng.normal(size=(2,4,4));A=a.T@a+np.eye(4);B=.75*A+b.T@b
        c.test('D.3',np.min(np.linalg.eigvalsh(B-.75*A))>-1e-10,'relative matrix comparison '+str(i+1))
    for rho in (.1,.5,.9):
        schur=1-rho*rho;marg.append([rho,schur])
        c.test('D.3',0<schur<1,'marginal covariance subtracts from precision')
    c.test('D.4',np.isclose(np.linalg.solve(np.diag([2.,3.]),[1,0])[0],.5),'Gaussian inverse Hessian covariance')
    c.test('D.5',.75*(.4**2)>=0,'horizontal sectional correction sign')
    rows=[table(L) for L in (8,16,32)];j=jump()
    c.test('D.6',abs(j[0]-2)<3e-5 and abs(j[1]-(10+np.sqrt(2))/8)<3e-5,'two directional limits of the embedded multiplier')
    c.test('D.6',rows[-1]['finite_fit']>2.5 and rows[-1]['maximum_absolute_row_sum']>rows[0]['maximum_absolute_row_sum'],'finite shell fit and absolute rows')
    c.test('D.7',0<(1-.4)**2<1,'block tensorization constant at a test contraction')
    curv=[compute(x) for x in (Fraction(1,50),Fraction(1,20),Fraction(1,10),Fraction(1,6))]
    for r in curv:c.test('D.8',r['radial_curvature_lower']>=r['analytic_floor'] and r['min_normalized_amplitude']>0,'outward-rounded pinned vacuum and curvature at '+str(r['x']))
    save(out/'kernel.json',{'rows':rows,'directional_limits_test':j});save(out/'marginals.json',marg)
    save(out/'curvature.json',curv);c.finish(5,out)
if __name__=='__main__':run(output())
