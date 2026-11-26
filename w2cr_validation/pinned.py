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

"""Pinned SU(2) vacuum, variational character fits and finite Euclidean transfer."""
import numpy as np
from scipy.linalg import eigh_tridiagonal, eigvalsh
from scipy.special import roots_legendre,ive
from scipy.fft import dst
COUPLINGS=(.02,.05,.1,1/6,.2,.5)

def ground(x,count):
    j=np.arange(count);diag=x*j*(j+2)/2+2/x
    en,V=eigh_tridiagonal(diag,np.full(count-1,-1/x),select='i',select_range=(0,0))
    return float(en[0]),V[:,0]

def weighted_gap(theta,w,x,order):
    w=w/w.sum();u=(1-np.cos(theta))/x;du=np.sin(theta)/x
    old=np.zeros_like(u);cur=np.ones_like(u);dold=old.copy();dcur=old.copy()
    beta=0.;der=[]
    for _ in range(order):
        alpha=w@(u*cur*cur)
        v=(u-alpha)*cur-beta*old;dv=du*cur+(u-alpha)*dcur-beta*dold
        norm=np.sqrt(w@(v*v))
        old,cur=cur,v/norm;dold,dcur=dcur,dv/norm;beta=norm;der.append(dcur)
    D=np.array(der)
    return float(eigvalsh((D*w)@D.T/2,subset_by_index=(0,0))[0])

def su2_fit(x,cut,n,q,r):
    E,c=ground(x,n)
    hi=np.arccos(1-np.sqrt(x)/4) if cut else np.pi
    nodes,weights=roots_legendre(q);t=(nodes+1)*hi/2
    psi=(np.sin(t[:,None]*np.arange(1,n+1))@c)/np.sin(t)
    w=weights*np.sin(t)**2*(psi/abs(psi).max())**4
    return E,weighted_gap(t,w,x,r)

def transfer(x,eps,T,grid,cut,align=False):
    theta=np.pi*np.arange(1,grid+1)/(grid+1)
    pot=np.exp(-(eps/x)*(1-np.cos(theta)))
    freqs=np.arange(1,grid+1);beta=1/(eps*x)
    mult=ive(freqs,beta)/ive(1,beta)
    state=np.sin(theta)
    for _ in range(round(T/eps)):
        state=pot*dst(mult*dst(pot*state,type=1,norm='ortho'),type=1,norm='ortho')
        state/=abs(state).max()
    if align:
        nodes,weight=roots_legendre(288)
        hi=np.arccos(1-np.sqrt(x)/4) if cut else np.pi
        theta=(nodes+1)*hi/2
        state=np.sin(theta[:,None]*freqs)@dst(state,type=1,norm='ortho')
    else:weight=1
    psi=state/np.sin(theta);w=weight*np.sin(theta)**2*(psi/np.max(abs(psi)))**4
    if cut:w[4*(1-np.cos(theta))>=np.sqrt(x)]=0
    return theta,w/w.sum()

def quotient(t,w,p):
    u=1-np.cos(t);f=u**p;df=p*u**(p-1)*np.sin(t)
    return float((w@(df**2))/(2*(w@((f-w@f)**2))))

def experiments():
    ritz=[];slab=[];rng=np.random.default_rng(20261125)
    for x in COUPLINGS:
        for cut in (False,True):
            rows=[su2_fit(x,cut,*cfg) for cfg in ((96,384,6),(144,640,10),(192,896,14))]
            lam=rows[-1][1]
            ritz.append(dict(x=x,domain='cut' if cut else 'full',E=rows[-1][0],ritz6=rows[0][1],
                             ritz10=rows[1][1],ritz14=lam,change=abs(lam-rows[-2][1])/lam,
                             z=x*lam/2,ratio=x*lam/(4*np.sqrt(2))))
        if x not in (.05,1/6):continue
        for cut in (False,True):
            for eps,T,N in ((1/16,4,511),(1/32,4,511),(1/64,4,511),(1/64,6,511),(1/64,6,1023)):
                t,w=transfer(x,eps,T,N,cut);samples=t[rng.choice(len(t),size=(64,2048),p=w)]
                for p in (1,2):
                    exact=quotient(t,w,p)
                    batches=np.array([quotient(s,np.ones(2048)/2048,p) for s in samples])
                    est=quotient(samples.ravel(),np.ones(samples.size)/samples.size,p)
                    se=batches.std(ddof=1)/8
                    slab.append(dict(x=x,domain='cut' if cut else 'full',eps=eps,T=T,grid=N,
                                     power=p,draws=samples.size,estimate=est,se=se,quadrature=exact,
                                     zscore=(est-exact)/se))
    return ritz,slab
