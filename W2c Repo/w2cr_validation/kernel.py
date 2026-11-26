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

"""Embedded P E P precision on a periodic factor-two lattice, in a real-space cell basis."""
from itertools import product
import numpy as np
from scipy.optimize import differential_evolution
R=np.array(list(product((0,1),repeat=3)))
def transverse(q):
    g=np.expm1(1j*q);h=np.vdot(g,g).real
    return np.eye(3)-np.outer(g,g.conj())/h if h>1e-22 else np.zeros((3,3),complex)
def matrix(p,cell=True):
    q=p+np.pi*R;Ec=np.repeat(np.linalg.norm(np.expm1(1j*q),axis=1),3)
    Pf=np.zeros((24,24),complex);B=np.zeros((3,24),complex)
    for k,v in enumerate(q):
        sl=slice(3*k,3*k+3);Pf[sl,sl]=transverse(v);B[:,sl]=np.diag(1+np.exp(1j*v))/np.sqrt(8)
    Pc=transverse(2*p)
    P=Pf-(B.conj().T@Pc@B)/2
    K=P@(Ec[:,None]*P)
    if not cell:return K
    H=np.kron(np.exp(1j*R@q.T)/np.sqrt(8),np.eye(3))
    return H@K@H.conj().T

def table(L):
    n=L//2;freq=np.pi*np.fft.fftfreq(n)
    blocks=np.empty((n,n,n,24,24),complex)
    for idx in np.ndindex(n,n,n):blocks[idx]=matrix(freq[np.array(idx)])
    ker=np.fft.ifftn(blocks,axes=(0,1,2))
    norms=np.sqrt((abs(ker)**2).sum(axis=(3,4)))
    ar=np.minimum(np.arange(n),n-np.arange(n));r=np.sqrt(sum(a*a for a in np.meshgrid(ar,ar,ar,indexing='ij')))
    bins=[]
    for j in range(1,n//2+1):
        m=(r>=j-.5)&(r<j+.5);bins.append([j,float(norms[m].mean())])
    selected=[(a,b) for a,b in bins if a>=2 and a<=max(3,n//2-1)]
    exponent=float(-np.polyfit(np.log(np.array(selected)[:,0]),np.log(np.array(selected)[:,1]),1)[0]) if len(selected)>=2 else None
    return dict(L=L,maximum_absolute_row_sum=float(abs(ker).sum(axis=(0,1,2,4)).max()),
                shell_frobenius_means=bins,finite_fit=exponent)
def jump():
    # r=(1,0,0), y component. Approach along y and x respectively.
    k=list(map(tuple,R)).index((1,0,0))*3+1
    return [float(matrix(np.array(v)*1e-5,False)[k,k].real) for v in [(0,1,0),(1,0,0)]]
