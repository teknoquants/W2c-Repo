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

"""Run SU(2), SU(3), finite transfer and finite-volume coupled-link benchmarks."""
import numpy as np
from common import Checks,output,save,csvwrite
from pinned import experiments as su2,transfer,quotient
from su3 import experiments as su3,character_check
from multilink import experiments as strips
def run(out):
    c=Checks();a,b=su2();csvwrite(out/'su2.csv',a);csvwrite(out/'slab.csv',b)
    for r in a:c.test('F.1',r['ritz14']>0 and r['change']<2e-4,'character convergence '+str((r['x'],r['domain'])))
    ref=[.99468,.98664,.97305,.95457]
    for x,y in zip([r['ratio'] for r in a if r['domain']=='full'][:4],ref):
        c.test('F.1',abs(x-y)<.000005,'five-decimal pinned ratio')
    s=su3();csvwrite(out/'su3.csv',s)
    for r in s:c.test('F.2',r['change']<1e-3 and r['matrix_residual']<1e-8,'SU(3) convergence '+str((r['x'],r['domain'])))
    err=character_check();c.test('F.2',err<1e-12,'fundamental character multiplication by Weyl integration')
    for r in b:c.test('F.3',abs(r['zscore'])<3,'sampling against grid '+str((r['x'],r['domain'],r['eps'],r['T'],r['grid'],r['power'])))
    aligned=[]
    for x in (.05,1/6):
        group=[]
        for n in (511,1023):
            t,w=transfer(x,1/64,6,n,True,True)
            row=dict(x=x,N=n,q1=quotient(t,w,1),q2=quotient(t,w,2));group.append(row);aligned.append(row)
        c.test('F.3',max(abs(group[0][k]-group[1][k]) for k in ('q1','q2'))<1e-8,'boundary-aligned quadrature')
    save(out/'aligned-slab.json',aligned);rows=strips();csvwrite(out/'multilink.csv',rows)
    for r in rows:c.test('F.4',r['midpoint_norm_error']<1e-10 and r['ci_low']<r['ratio']<r['ci_high'] and .1<r['hmc_acceptance']<=1,'reversible strip benchmark '+str((r['n'],r['x'],r['eps'])))
    flags=[]
    for x in (.05,1/6):
        seq=sorted([r for r in rows if r['x']==x and r['eps']==.125],key=lambda r:r['n'])
        flags.append(seq[-1]['ci_high']<seq[0]['ci_low'] and all(a['ratio']>b['ratio'] for a,b in zip(seq,seq[1:])))
    save(out/'benchmarks.json',dict(su3_character_error=err,strip_warning=all(flags),criteria_by_coupling=flags))
    c.finish(7,out)
if __name__=='__main__':run(output())
