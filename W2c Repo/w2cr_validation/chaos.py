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

"""Second quantization with actual retained--eliminated mixing in the joint form."""
from itertools import product, permutations, combinations_with_replacement
from functools import lru_cache
import numpy as np
from scipy.sparse.linalg import LinearOperator,eigsh
from scipy.linalg import null_space
from free_spectra import dense_sector, aliases

def quadratic(L):
    sectors={}
    for p in product((0,1),repeat=3):
        e,T=dense_sector(L,p)
        Q=np.linalg.qr((T/np.sqrt(e)).T,mode='reduced')[0]
        sectors[p]=e,Q
    candidates={}
    for a,b in combinations_with_replacement(sectors,2):
        key=min(tuple(sorted((tuple(a[i] for i in perm),tuple(b[i] for i in perm)))) for perm in permutations(range(3)))
        if key==(a,b):candidates[key]=min(sectors[a][0])+min(sectors[b][0])
    best=np.inf;records=[];winner=None
    for (a,b),lower in sorted(candidates.items(),key=lambda z:z[1]):
        if lower>=best-1e-10:
            records.append(dict(a=a,b=b,lower=float(lower),method='energy lower bound'));continue
        ea,A=sectors[a];eb,B=sectors[b];w=ea[:,None]+eb[None,:]
        same=a==b;ix=np.triu_indices(len(ea)) if same else None
        weights=np.where(ix[0]==ix[1],1,np.sqrt(2.)) if same else None
        def unpack(x):
            if not same:return x.reshape(w.shape)
            M=np.zeros(w.shape);M[ix]=x/weights;M[ix[::-1]]=M[ix];return M
        def pack(M):return M[ix]*weights if same else M.ravel()
        def retained(M):return A@((A.T@M@B)@B.T)
        def mv(x):
            M=unpack(x);R=retained(M);H=w*(M-R)
            return pack(H-retained(H)+16*R)
        n=len(ix[0]) if same else w.size
        op=LinearOperator((n,n),matvec=mv,dtype=float)
        lam,z=eigsh(op,k=1,which='SA',v0=np.random.default_rng(411).normal(size=n),tol=5e-12)
        val=float(lam[0]);res=float(np.linalg.norm(mv(z[:,0])-val*z[:,0]))
        records.append(dict(a=a,b=b,lower=float(lower),ritz=val,residual=res))
        if val<best:best=val;winner=records[-1]
    n=sum(len(v[0]) for v in sectors.values());r=sum(v[1].shape[1] for v in sectors.values())
    emin=min(float(min(v[0])) for v in sectors.values())
    return dict(L=L,modes=n,retained=r,dimension=(n*(n+1)-r*(r+1))//2,
                quadratic=best,residual=winner['residual'],all_sector_residual=max(x.get('residual',0) for x in records),
                higher_floor=3*emin,absolute_lower=2*emin,blocks=records)

def periodic_occupations():
    # For L=4, every fine frequency in the seven nonzero coarse blocks is >= sqrt(2).
    # Construct a tangent AND dynamically invariant eigenvector at the floor.
    # Its nth Wick power reaches the n-particle lower bound in either model.
    found=[]
    for k in product((0,1),repeat=3):
        if not any(k):continue
        T,e=aliases(np.pi*np.array(k)/2);floor=e.min()
        space=np.flatnonzero(abs(e-floor)<1e-12)
        V=null_space(T[:,space])
        if V.shape[1]:found.append((float(floor),float(np.linalg.norm(T[:,space]@V))))
    best=min(a for a,r in found)
    return dict(particle_floor=best,witness_residual=max(r for a,r in found),
                homogeneous=[n*best for n in (1,2,3)],method='exact floor plus an annihilated eigenmode')

def two_mode():
    q=np.array([[1.,1.],[1.,-1.]])/np.sqrt(2)
    H=q.T@np.diag([1.,3.])@q
    trip=np.kron(H,np.eye(2))+np.kron(np.eye(2),H)
    B=np.array([[0,1/np.sqrt(2),1/np.sqrt(2),0],[0,0,0,1]]).T
    block=B.T@trip@B
    return dict(first=float(H[1,1]),quadratic=block.tolist(),minimum=float(np.linalg.eigvalsh(block)[0]))
