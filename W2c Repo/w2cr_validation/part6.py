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

"""Check conditional constants, collapse, concentration, resolvents and W2 loss composition."""
import math
from scipy.integrate import quad
from common import Checks,output,save
def run(out):
    c=Checks();rows=[];running=[];collapse=[]
    c.test('E.1',quad(lambda t:2*math.exp(-2*t),0,100)[0]>1-1e-12,'variance integral of the scalar curvature profile')
    for k in (1/27648,1/64,.4):
        for m in (0.,.2,.8):
            for x in (.02,.05,1/6):
                d=m/2;K=2*(1-d)*k/x;v=1/K;a=.25;energy=x/(2*a);C=2*(1-m)*k
                c.test('E.2',C*v<=x+1e-13,'uniform Poincare transfer')
                c.test('E.3',C/2<=(1-d)*k+1e-14 and (1-d)*k<=a*energy/v+1e-13,'direction and energy conversion')
                rows.append(dict(k=k,m=m,x=x,uniform=C/2,pointwise=(1-d)*k))
    for s in (8,16,32,64):
        w=lambda y:math.exp(s*(y*y-1))
        num=32*quad(w,0,.25,epsabs=1e-100)[0]
        var=2*quad(lambda y:min(1,4*y)**2*w(y),0,1,points=[.25],epsabs=1e-80)[0]
        bound=8*math.exp(-3*s/16);q=num/var
        c.test('E.4',0<q<=bound,'collapse quotient s='+str(s));collapse.append([s,q,bound])
    c.test('E.5',math.isclose(math.exp(-.5)*math.exp(.25),math.exp(-.25)),'Herbst exponential completion')
    k=1.3892074859;b=22/(48*math.pi**2)
    for n in (0,1,2,4,8):
        d=4*b*n*math.log(2);x=1/(6+d)
        lo=1-.1*math.exp(-d/(6*b))/k;actual=1-.1*2**(-n)/k
        c.test('E.6',lo<=actual+1e-14,'weak running separation n='+str(n))
        running.append([n,x,lo,actual])
    for k in (1/27648,1/64):
        am=k/4;C=2*(1-.25)*k;res=1/(C/2-am)
        c.test('E.7',res>0 and 1/(C/2-am)==res,'positive resolvent margin in W2 allowance')
    save(out/'consequences.json',dict(constants=rows,collapse=collapse,separation=running,
         illustrative_assembly={'k':1/27648,'delta_max':.25,'am':1/110592,'dimensionless_resolvent':55296}))
    c.finish(6,out)
if __name__=='__main__':run(output())
