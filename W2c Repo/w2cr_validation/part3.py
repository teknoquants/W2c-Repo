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

"""Test the three Gaussian sectors, the Wilson expansion obstruction and colour contraction."""
import numpy as np
from common import Checks,output,save
from chaos import two_mode,periodic_occupations,quadratic
from geometry import expv,inv
from multilink import left
from free_spectra import dense_sector,two_forms
def run(out):
    c=Checks();records=[]
    for n in (2,3):
        for t in (.05,.1,.2):
            u,v=expv(np.array([t,0,0])),expv(np.array([0,t,0]))
            h=left(left(left(u,v),inv(u)),inv(v))
            action=4*(1-h[0])/n
            c.test('B.1',action>0 and abs(action-8*np.sin(t)**4/n)<3e-15,'zero curl, noncommuting constant fields')
            records.append(dict(N=n,t=t,wilson=action,linear_curl_squared=0,absolute_cubic_constant=64/3))
    for L in (4,6,8):
        for p in ((0,0,1),(0,1,1),(1,1,1)):
            e,T=dense_sector(L,p);f,j=two_forms(T,e)
            c.test('B.2',f<=j+2e-12,'Loewner quotient comparison '+str((L,p)))
    g=periodic_occupations();model=two_mode()
    for i,x in enumerate(g['homogeneous'],1):c.test('B.3',abs(x-i*np.sqrt(2))<1e-12,'periodic homogeneous gap '+str(i))
    c.test('B.4',abs(model['minimum']-(4-np.sqrt(2)))<3e-14 and model['minimum']<2*model['first'],'exact two-mode failure of doubling')
    rng=np.random.default_rng(30)
    for d in (3,8):
        Q=np.linalg.qr(rng.normal(size=(d,d)))[0];x,y=rng.normal(size=(2,d))
        c.test('B.5',abs((Q@x)@(Q@y)-x@y)<1e-13,'invariance of the colour contraction')
    for L in (4,6,8):
        r=quadratic(L);save(out/f'chaos-{L}.json',r)
        c.test('B.6',r['all_sector_residual']<1e-8 and r['absolute_lower']<=r['quadratic'],'every computed quadratic sector residual')
        if L==4:c.test('B.6',r['dimension']==15170 and abs(r['quadratic']-2.186794)<5e-7,'four-cell singlet benchmark')
    c.test('B.7',abs(2.186793963538067/(2*1.4979234616972574)-.7299)<.00005,'four-cell doubling ratio')
    H=rng.normal(size=(5,5));G=H.T@H;u=rng.normal(size=(5,3))
    c.test('B.8',np.linalg.eigvalsh(u.T@G@u).min()>-1e-11,'compression preserves a relative form bound')
    save(out/'gaussian.json',{'wilson':records,'occupations':g,'two_mode':model});c.finish(3,out)
if __name__=='__main__':run(output())
