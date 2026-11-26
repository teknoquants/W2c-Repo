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

"""SU(3) character Hamiltonian, Weyl integration and singlet Ritz estimates."""
from itertools import permutations
import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import eigsh
from scipy.linalg import eigh
from scipy.special import roots_legendre
from scipy.ndimage import map_coordinates
from pinned import COUPLINGS
PERM=list(permutations(range(3)))
SIG=[(-1)**sum(p[i]>p[j] for i in range(3) for j in range(i+1,3)) for p in PERM]

def character_ground(x,M):
    labels=[(a,b) for a in range(M+1) for b in range(M+1-a)];idx={k:i for i,k in enumerate(labels)}
    row=[];col=[];val=[]
    for i,(p,q) in enumerate(labels):
        C=(p*p+q*q+p*q+3*p+3*q)/3
        row.append(i);col.append(i);val.append(x*C/2+2/x)
        for a,b in ((1,0),(-1,1),(0,-1),(-1,0),(1,-1),(0,1)):
            j=idx.get((p+a,q+b))
            if j is not None:row.append(i);col.append(j);val.append(-1/(3*x))
    H=coo_matrix((val,(row,col)),shape=(len(labels),)*2).tocsr()
    e,v=eigsh(H,k=1,which='SA',v0=np.ones(len(labels)),tol=2e-13)
    return float(e[0]),np.array(labels),v[:,0],float(np.linalg.norm(H@v[:,0]-e[0]*v[:,0]))

def alternant_grid(labels,weights,N,shift):
    freq=np.column_stack([labels[:,0]+labels[:,1]+2,labels[:,1]+1,np.zeros(len(labels),int)])
    out=np.zeros((N,N),complex)
    for perm,sgn in zip(PERM,SIG):
        u,v,w=freq[:,perm].T;u=u-w;v=v-w
        phase=np.exp(2j*np.pi*(shift[0]*u+shift[1]*v)/N)
        np.add.at(out,(u%N,v%N),sgn*weights*phase)
    return np.fft.ifft2(out)*N*N

def ritz(t,s,weight,x,degree):
    a=t.ravel();b=s.ravel();w=weight.ravel();sel=w>w.max()*1e-18
    a,b,w=a[sel],b[sel],w[sel];w=w/w.sum()
    z=np.exp(1j*a);v=np.exp(1j*b);u=np.exp(-1j*(a+b));tr=z+v+u
    X=(3-tr.real)/x;Y=tr.imag/x**1.5
    da=1j*(z-u);db=1j*(v-u)
    xa,xb=-da.real/x,-db.real/x;ya,yb=da.imag/x**1.5,db.imag/x**1.5
    vals=[];Aa=[];Ab=[]
    for i in range(degree+1):
        for j in range(degree+1-i):
            if i+j==0:continue
            f=X**i*Y**j;dX=i*X**max(0,i-1)*Y**j;dY=j*X**i*Y**max(0,j-1)
            scale=np.sqrt(w@((f-w@f)**2))
            vals.append((f-w@f)/scale);Aa.append((dX*xa+dY*ya)/scale);Ab.append((dX*xb+dY*yb)/scale)
    F,A,B=map(np.array,(vals,Aa,Ab))
    mass=(F*w)@F.T
    stiffness=((A*w)@A.T+(B*w)@B.T)/6-((A*w)@B.T+(B*w)@A.T)/12
    return float(eigh(stiffness,mass,eigvals_only=True,subset_by_index=(0,0))[0])

def calc(x,M,N,degree):
    en,labels,coef,res=character_ground(x,M);shift=(.173,.419)
    den=alternant_grid(np.array([[0,0]]),np.ones(1),N,shift)
    num=alternant_grid(labels,coef,N,shift);psi=(num/den).real
    psi/=np.max(abs(psi))
    a,b=np.meshgrid(*(2*np.pi*(np.arange(N)+s)/N for s in shift),indexing='ij')
    full=ritz(a,b,abs(den)**2*psi**4,x,degree)
    # A boundary-fitted polar rule on the identity component of the torus.
    # The small-field threshold is ||1-U||_HS^2 < sqrt(x).
    angles=2*np.pi*(np.arange(N)+.31)/N;ca=np.cos(angles);cb=np.sin(angles)
    lo=np.zeros(N);hi=np.full(N,2.)
    for _ in range(49):
        mid=(lo+hi)/2
        q=2*(3-np.cos(mid*ca)-np.cos(mid*cb)-np.cos(mid*(ca+cb)))
        lo,hi=np.where(q<np.sqrt(x),mid,lo),np.where(q<np.sqrt(x),hi,mid)
    nodes,weights=roots_legendre(max(32,N//4));radius=(lo+hi)/2
    rr=radius[None,:]*(1+nodes[:,None])/2;u=rr*ca;v=rr*cb
    interp=map_coordinates(psi,[N*u/(2*np.pi)-shift[0],N*v/(2*np.pi)-shift[1]],order=5,mode='grid-wrap')
    haar=(8*np.sin((u-v)/2)*np.sin((2*u+v)/2)*np.sin((u+2*v)/2))**2
    weight=haar*interp**4*rr*radius*weights[:,None]
    cut=ritz(u,v,weight,x,degree)
    return en,full,cut,res

def experiments():
    rows=[]
    for x in COUPLINGS:
        records=[calc(x,*cfg) for cfg in ((44,192,4),(64,256,5),(82,320,6))]
        for i,domain in ((1,'full'),(2,'cut')):
            lam=records[-1][i];z=x*lam/2
            rows.append(dict(x=x,domain=domain,vacuum=records[-1][0],ritz4=records[0][i],ritz5=records[1][i],
                 ritz6=lam,change=abs(lam-records[-2][i])/lam,z=z,free_z=2/np.sqrt(3),
                 ratio=z/(2/np.sqrt(3)),matrix_residual=records[-1][3]))
    return rows

def character_check():
    N=64;shift=(.173,.419)
    den=alternant_grid(np.array([[0,0]]),np.ones(1),N,shift)
    def chi(p,q):return alternant_grid(np.array([[p,q]]),np.ones(1),N,shift)/den
    errors=[]
    for p,q in ((0,0),(1,0),(1,1),(2,1)):
        f=chi(1,0)*chi(p,q);expected={(p+1,q),(p-1,q+1),(p,q-1)}
        for a in range(4):
            for b in range(4-a):
                coeff=np.mean(abs(den)**2*f*chi(a,b).conj())/6
                errors.append(abs(coeff-((a,b) in expected)))
    return float(max(errors))
