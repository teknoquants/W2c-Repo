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

"""Rational Sturm bounds and outward interval evaluation for the pinned SU(2) vacuum."""
from fractions import Fraction as F
import math
from mpmath import iv
from pinned import ground
iv.dps=42

def I(x):
    if isinstance(x,F): return iv.mpf(x.numerator)/iv.mpf(x.denominator)
    return iv.mpf(x)

def sturm(x,E,N,tail):
    # The infinite tail has lower bound x*N*(N+2)/2 from diagonal dominance.
    # Subtract its largest possible Schur correction to certify a lower bound.
    a=1/x**2;h=None;negative=0
    for j in range(N):
        d=x*j*(j+2)/2+2/x-E
        if tail and j==N-1:d-=a/(x*N*(N+2)/2-E)
        h=d if j==0 else d-a/h
        if h<0:negative+=1
    return negative

def bound(x):
    N=64
    e=ground(float(x),N)[0];m=round(e*10**10)
    lo,hi=F(m-3,10**10),F(m+3,10**10)
    assert x*N*(N+2)/2>hi and sturm(x,lo,N,True)==0 and sturm(x,hi,N,False)==1
    return lo,hi

def compute(x):
    lo,hi=bound(x);X=I(x);E=iv.mpf([I(lo).a,I(hi).b]);M=150
    # z=1-cos(theta), Y(0)=1; the recurrence is the regular solution of the radial ODE.
    a=[I(1)];prev=I(0)
    for n in range(M):
        nxt=((n*(n+2)-2*E/X)*a[-1]+4*prev/X**2)/((n+1)*(2*n+3))
        prev=a[-1];a.append(nxt)
    # For n>=M the sum of absolute recurrence multipliers is <=1.
    assert 2*hi/x <= M*(M+2) and 4/x**2 <= (M+1)*(2*M+3)-M*(M+2)
    envelope=max(float(abs(a[-1]).b),float(abs(a[-2]).b))
    envelope=I(str(max(envelope*1.001,1e-70)))+I('1e-60')
    assert abs(a[-1]).b<=envelope.a and abs(a[-2]).b<=envelope.a
    top=F(math.ceil(math.sqrt(float(x))/4*10**12)+1,10**12)
    assert 16*top**2>=x
    Z=I(top)
    def tails(k):
        # Sum_{n>=M+1} n(n-1)...(n-k+1) z^(n-k) by a geometric-majorant ratio.
        start=M+1;coef=math.prod(range(start-k+1,start+1))
        ratio=Z*(start+1)/(start+1-k)
        return envelope*coef*Z**(start-k)/(1-ratio)
    pol=[[a[n]*math.prod(range(n-k+1,n+1)) for n in range(k,M+1)] for k in (0,1,2,3)]
    errors=[tails(k) for k in (0,1,2,3)]
    cells=448 if x==F(1,50) else 144;floor=math.inf;smin=1.;dermax=[0.,0.]
    for j in range(cells):
        z=iv.mpf([I(top*j/cells).a,I(top*(j+1)/cells).b]);c=1-z
        mid=I(top*(2*j+1)/(2*cells));dx=I(top/(2*cells))
        def evaluate(row,where):
            value=I(0)
            for co in reversed(row):value=value*where+co
            return value
        broad=evaluate(pol[3],z)+iv.mpf([-errors[3].b,errors[3].b])
        vals=[]
        for k in (2,1,0):
            err=errors[k]+dx*abs(broad)
            broad=evaluate(pol[k],mid)+iv.mpf([-err.b,err.b])
            vals.insert(0,broad)
        y,dy,ddy=vals
        assert y.a>0
        # The leftmost interval includes theta=0. Use the reciprocal of its maximum sin².
        sin2=z*(2-z)
        curv=2/sin2.b+4*(-c*dy/y-sin2*(ddy/y-(dy/y)**2))
        floor=min(floor,float(curv.a));smin=min(smin,float(y.a))
        dermax=[max(dermax[0],float(abs(dy).b)),max(dermax[1],float(abs(ddy).b))]
    return dict(x=float(x),vacuum_e_lower=str(lo),vacuum_e_upper=str(hi),cells=cells,
                radial_curvature_lower=math.floor(floor*1e6)/1e6,
                min_normalized_amplitude=math.floor(smin*1e8)/1e8,
                upper_abs_derivatives_z=[math.ceil(v*1e5)/1e5 for v in dermax],
                analytic_floor=4*(1-math.sqrt(float(x))/4)/float(x),
                delta_uniform_comparison=1-2*(1-math.sqrt(float(x))/4)/7)
