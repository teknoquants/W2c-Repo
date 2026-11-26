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

"""Certify both periodic continuum infima by a one-dimensional interval test."""
from fractions import Fraction as F
from mpmath import iv
iv.dps=34

def rat(x):
    return iv.mpf(x.numerator)/iv.mpf(x.denominator)

def scalar(u,lam,alpha,parallel):
    s=u*u/4
    def g(v):
        e=2*iv.sqrt(v);h=1/(e**alpha*(e-lam))
        return h,-h*(alpha/e+1/(e-lam))*2/e
    a,da=g(1-s);b,db=g(1+s);c,dc=g(2-s)
    if parallel:
        d,dd=g(2+s);f,df=g(3-s);w=s/(1-s)
        h=2*b+d+w*(a+2*c+f)
        dh=2*db+dd+(a+2*c+f)/(1-s)**2+w*(-da-2*dc-df)
    else:h=a+b+c;dh=-da+db-dc
    factor=(lam-u)*u**alpha
    slope=-1 if alpha==0 else lam-2*u
    return factor*h,slope*h+factor*dh*u/2

def certify(alpha,low,high,witness):
    lam=rat(low);visited=0;deepest=0
    for parallel in (False,True):
        pending=[(F(0),low,0)]
        while pending:
            a,b,depth=pending.pop();visited+=1;deepest=max(depth,deepest)
            assert depth<50
            m=(a+b)/2
            box=iv.mpf([rat(a).a,rat(b).b])
            h,dh=scalar(box,lam,alpha,parallel)
            if h.b<=1:continue
            center=scalar(rat(m),lam,alpha,parallel)[0]
            if (center+abs(dh)*rat((b-a)/2)).b<=1:continue
            pending.extend([(a,m,depth+1),(m,b,depth+1)])
    point=scalar(rat(witness),rat(high),alpha,False)[0]
    assert point.a>1
    return dict(form='fibre' if alpha==0 else 'joint',lower=str(low),upper=str(high),
                decimals=[float(low),float(high)],upper_witness_u=str(witness),
                certified_boxes=visited,maximum_subdivision_depth=deepest)

def results():
    return [certify(0,F('0.5499937532'),F('0.5499937534'),F(0)),
            certify(1,F('1.3892074858'),F('1.3892074861'),F('0.855583'))]
