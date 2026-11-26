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

"""Scalar Gaussian gaps on periodic tori and reflection sectors of open cubes."""
from functools import lru_cache
from itertools import product, permutations, combinations_with_replacement
import math
import numpy as np
from scipy.linalg import null_space, eigh, cho_factor, cho_solve
from scipy.sparse.linalg import LinearOperator, eigsh, lobpcg
from threadpoolctl import threadpool_limits

def aliases(p):
    def frame(q):
        g=np.expm1(1j*q)
        return null_space(g.conj()[None,:]),np.linalg.norm(g)
    Q,_=frame(2*p)
    T=[];E=[]
    for r in product((0,1), repeat=3):
        q=p+np.pi*np.array(r);U,omega=frame(q)
        T.append(Q.conj().T@((1+np.exp(1j*q))[:,None]*U)/np.sqrt(8))
        E.extend([omega]*U.shape[1])
    return np.concatenate(T,axis=1),np.array(E)

def two_forms(T,E):
    vals=[]
    for a in (T,T/np.sqrt(E)):
        V=null_space(a)
        vals.append(float(np.linalg.eigvalsh(V.conj().T@(E[:,None]*V))[0]))
    return vals

def orbit(k,n):
    return {tuple((s*a)%n for s,a in zip(sign,p)) for p in set(permutations(k))
            for sign in product((-1,1),repeat=3)}

def periodic(L):
    n=L//2;rows=[]
    for k in combinations_with_replacement(range(n//2+1),3):
        if k==(0,0,0):continue
        f,j=two_forms(*aliases(np.pi*np.array(k)/n));rows.append((k,f,j))
    result={'L':L,'coarse_nonzero':n**3-1}
    for i,name in ((1,'fibre'),(2,'joint')):
        low=min(r[i] for r in rows)
        winners=[r[0] for r in rows if abs(r[i]-low)<8e-10]
        ties=sorted(set.union(*(orbit(k,n) for k in winners)))
        result[name]={'gap':low,'representatives':winners,'ties':ties}
    return result

@lru_cache(maxsize=16)
def path_matrices(L):
    x=np.arange(L+1);k=np.arange(L+1)
    vertex=np.cos(np.pi*(x[:,None]+.5)*k/(L+1))*np.sqrt(2/(L+1))
    vertex[:,0]/=np.sqrt(2)
    edge=np.zeros((L,L+1))
    edge[:,1:]=np.sin(np.pi*(np.arange(L)[:,None]+1)*np.arange(1,L+1)/(L+1))*np.sqrt(2/(L+1))
    return vertex,edge

@lru_cache(maxsize=48)
def modes(L,parity):
    keys=[];pol=[];energy=[]
    s=2*np.sin(np.pi*np.arange(L+1)/(2*(L+1)))
    for k in product(*(range(v,L+1,2) for v in parity)):
        active=np.flatnonzero(k)
        if len(active)<2:continue
        sig=s[np.array(k)];idx=active
        u=np.zeros(3);u[idx[0]]=sig[idx[1]];u[idx[1]]=-sig[idx[0]];u/=np.linalg.norm(u)
        vectors=[u]
        if len(active)==3:vectors.append(np.cross(sig,u)/np.linalg.norm(sig))
        for v in vectors:keys.append(k);pol.append(v);energy.append(np.linalg.norm(sig))
    return np.array(keys,dtype=int).reshape(-1,3),np.array(pol).reshape(-1,3),np.array(energy)

@lru_cache(maxsize=16)
def restriction(L):
    V,S=path_matrices(L);v,s=path_matrices(L//2)
    return v.T@V[::2],s.T@(S[::2]+S[1::2])

def dense_sector(L,parity):
    k,U,e=modes(L,parity);h,Q,_=modes(L//2,parity)
    v,s=restriction(L)
    T=np.zeros((len(h),len(k)))
    for j in range(3):
        a=Q[:,j,None]*U[None,:,j]
        for i in range(3):
            a*=(s if i==j else v)[h[:,i,None],k[None,:,i]]
        T+=a
    return e,T

def ground_diag(e,T,kind):
    W=T if kind=='fibre' else T/np.sqrt(e)
    # Orthogonal range of W*. A positive penalty moves the complementary spectrum away.
    Q=np.linalg.qr(W.T,mode='reduced')[0]
    def P(v):return v-Q@(Q.T@v)
    def mv(v):
        z=P(v)
        return P(e*z)+8*(v-z)
    if len(e)<100:
        M=np.eye(len(e))-Q@Q.T
        lam,z=eigh(M@(e[:,None]*M)+8*(np.eye(len(e))-M),subset_by_index=(0,0))
        val,vec=lam[0],z[:,0]
    else:
        op=LinearOperator((len(e),)*2,matvec=mv,dtype=float)
        lam,z=eigsh(op,k=1,which='SA',v0=np.random.default_rng(614).normal(size=len(e)),tol=5e-13)
        val,vec=lam[0],z[:,0]
    return float(val),P(vec),float(np.linalg.norm(mv(vec)-val*vec))

def boundary(L,parity,coeff):
    k,U,e=modes(L,parity);V,S=path_matrices(L)
    total=edge_count=face_count=0;norm=0.
    for j in range(3):
        spec=np.zeros((L+1,)*3)
        np.add.at(spec,tuple(k.T),U[:,j]*coeff)
        mats=[S if i==j else V for i in range(3)]
        space=np.einsum('ai,bj,ck,ijk->abc',*mats,spec,optimize=True)
        mask=np.zeros(space.shape,bool)
        for i in range(3):
            if i==j:continue
            for loc in (0,-1):
                sl=[slice(None)]*3;sl[i]=loc;mask[tuple(sl)]=True
        total+=(space[mask]**2).sum();norm+=(space**2).sum()
        edge_count+=mask.size;face_count+=mask.sum()
    return float(total/norm),face_count/edge_count

class OpenSector:
    """Apply B and B* by tensor products, avoiding a big dense L=32 constraint."""
    def __init__(self,L,p):
        self.L=L;self.p=p
        self.k,self.u,self.e=modes(L,p);self.h,self.q,_=modes(L//2,p)
        v,s=restriction(L);self.mats=[]
        self.fids=tuple(np.arange(a,L+1,2) for a in p)
        self.cids=tuple(np.arange(a,L//2+1,2) for a in p)
        self.i=tuple((self.k[:,i]-p[i])//2 for i in range(3))
        self.j=tuple((self.h[:,i]-p[i])//2 for i in range(3))
        for axis in range(3):
            self.mats.append([(s if n==axis else v)[np.ix_(self.cids[n],self.fids[n])] for n in range(3)])
    @staticmethod
    def transform(A,mats):
        for i,M in enumerate(mats):
            A=np.moveaxis(np.tensordot(M,A,axes=(1,i)),0,i)
        return A
    def apply(self,X,reverse=False):
        if X.ndim==1:return self.apply(X[:,None],reverse)[:,0]
        if reverse:
            U,Q,ii,jj,ids=self.q,self.u,self.j,self.i,self.cids
        else:U,Q,ii,jj,ids=self.u,self.q,self.i,self.j,self.fids
        out=np.zeros((len(Q),X.shape[1]))
        for axis in range(3):
            cube=np.zeros(tuple(map(len,ids))+(X.shape[1],))
            # At most two transverse polarizations share a frequency.
            np.add.at(cube,ii,U[:,axis,None]*X)
            mats=self.mats[axis]
            if reverse:mats=[M.T for M in mats]
            out+=Q[:,axis,None]*self.transform(cube,mats)[jj]
        return out
    def P(self,x):return x-self.apply(self.apply(x),True)/2
    def minimum(self,kind):
        e=self.e
        if kind=='joint':
            # Work in white coordinates. A single coarse Cholesky solve
            # realizes the exact projector in each Lanczos multiplication.
            r=len(self.h)
            schur=np.empty((r,r))
            for start in range(0,r,24):
                cols=np.arange(start,min(start+24,r))
                eye=np.zeros((r,len(cols)));eye[cols,np.arange(len(cols))]=1
                schur[:,cols]=self.apply(self.apply(eye,True)/e[:,None])
            chol=cho_factor((schur+schur.T)/2,check_finite=False)
            root=np.sqrt(e)
            def white(z):
                coarse=self.apply(z/root)
                return z-self.apply(cho_solve(chol,coarse,check_finite=False),True)/root
            def H(z):
                y=white(z)
                return white(e*y)+8*(z-y)
            op=LinearOperator((len(e),)*2,matvec=H,dtype=float)
            val,Z=eigsh(op,k=1,which='SA',v0=np.random.default_rng(551).normal(size=len(e)),
                        ncv=42,tol=4e-12,maxiter=3000)
            z=Z[:,0]
            return float(val[0]),white(z)/root,float(np.linalg.norm(H(z)-val[0]*z))
        def radial(x,k):return e[:,None]**k*x if x.ndim==2 else e**k*x
        def A(x):
            y=self.P(x);return self.P(radial(y,1 if kind=='fibre' else 2))+8*(x-y)
        def B(x):
            y=self.P(x);return self.P(radial(y,1))+(x-y)
        def M(x):
            y=self.P(x);return self.P(radial(y,-1 if kind=='fibre' else -2))+(x-y)/8
        wrap=lambda fun:LinearOperator((len(e),len(e)),matvec=fun,matmat=fun,dtype=float)
        X=self.P(np.random.default_rng(551).normal(size=(len(e),2)))
        v,z=lobpcg(wrap(A),X,B=wrap(B) if kind=='joint' else None,M=wrap(M),largest=False,tol=2e-10,maxiter=410)
        x=z[:,0];D=B(x) if kind=='joint' else x
        res=np.linalg.norm(A(x)-v[0]*D)/np.linalg.norm(D)
        return float(v[0]),self.P(x),float(res)

def open_box(L):
    best={k:(float('inf'),None,None,None) for k in ('fibre','joint')}
    # Permuting the three coordinate axes gives unitarily equivalent sectors.
    for p in combinations_with_replacement((0,1),3):
        if L<=16:e,T=dense_sector(L,p)
        else:op=OpenSector(L,p);e=op.e
        for kind in best:
            if L<=16:
                v,x,res=ground_diag(e,T,kind)
                if kind=='joint':x=x/np.sqrt(e)
            else:v,x,res=op.minimum(kind)
            if v<best[kind][0]:best[kind]=(v,p,x,res)
    out={}
    for kind,(v,p,x,res) in best.items():
        mass,share=boundary(L,p,x)
        out[kind]=dict(gap=v,parity=p,residual=res,boundary_mass=mass,edge_share=share)
    return dict(L=L,**out)
