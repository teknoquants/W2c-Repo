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

"""Finite Euclidean SU(2) strips with four time arms meeting the conditioned midpoint."""
import numpy as np
from scipy.linalg import eigvalsh
from scipy.stats import t as student

def left(a,b):
    s=a[...,:1]*b[...,:1]-(a[...,1:]*b[...,1:]).sum(-1,keepdims=True)
    v=a[...,:1]*b[...,1:]+b[...,:1]*a[...,1:]+np.cross(a[...,1:],b[...,1:])
    return np.concatenate([s,v],axis=-1)

class Strip:
    def __init__(self,n,x,eps,T,seed,chains):
        self.n=n;self.x=x;self.eps=eps;self.T=T;self.m=int(round(T/eps));m=self.m
        self.rng=np.random.default_rng(seed);self.chains=chains
        self.q=np.zeros((chains,1+4*m,n,4));self.q[...,0]=1
        self.w=np.full(1+4*m,eps/x);self.w[0]*=2;self.w[m::m]*=.5
        depth=np.r_[0,np.tile(np.arange(1,m+1),4)]
        self.parity=(depth[:,None]+np.arange(n))%2
        # The rightmost dynamic row has one more incident pinned plaquette.
        self.pins=np.ones(n);self.pins[-1]+=1
        K=np.eye(n);K[-1,-1]+=1
        for j in range(n-1):
            K[j,j]+=1;K[j+1,j+1]+=1;K[j,j+1]-=1;K[j+1,j]-=1
        ev,U=np.linalg.eigh(K);self.mode=U[:,0];self.free_z=2*np.sqrt(ev[0])
    def spatial_field(self,q):
        h=np.zeros_like(q);h[...,0]=self.pins
        h[:,:,:-1]+=q[:,:,1:];h[:,:,1:]+=q[:,:,:-1]
        return h*self.w[None,:,None,None]
    def spatial_action(self,q):
        pin=(q[...,0]*self.pins).sum(2)
        pair=(q[:,:,:-1]*q[:,:,1:]).sum((2,3))
        return -((pin+pair)*self.w).sum(1)
    def heatbath(self,parity):
        q=self.q;m=self.m;h=self.spatial_field(q);arms=q[:,1:].reshape(self.chains,4,m,self.n,4)
        tor=h[:,1:].reshape(arms.shape);beta=1/(self.eps*self.x)
        h[:,0]+=beta*arms[:,:,0].sum(1)
        tor[:,:,0]+=beta*q[:,0,None];tor[:,:,1:]+=beta*arms[:,:,:-1];tor[:,:,:-1]+=beta*arms[:,:,1:]
        mask=self.parity==parity;h=h[:,mask];kap=np.linalg.norm(h,axis=-1)
        # Exact S^3 heat bath in the local field. For zero field draw Haar.
        direction=h/np.maximum(kap[...,None],1e-300)
        small=kap<1e-6;direction[small]=[1,0,0,0]
        if small.any():raise ArithmeticError('Degenerate field: select a direct Haar-envelope sampler')
        d=self.rng.gamma(1.5,1.,size=kap.shape)
        while True:
            reject=self.rng.random(kap.shape)**2>np.maximum(0,1-d/(2*kap))
            if not reject.any():break
            # Preserve accepted values while resampling the remaining entries.
            while reject.any():
                z=self.rng.gamma(1.5,1.,size=reject.sum());k=kap[reject]
                accept=self.rng.random(z.shape)**2<=np.maximum(0,1-z/(2*k))
                idx=np.flatnonzero(reject);d.flat[idx[accept]]=z[accept];reject.flat[idx[accept]]=False
            break
        c=1-d/kap;v=self.rng.normal(size=h.shape);v-=direction*(v*direction).sum(-1,keepdims=True)
        v/=np.linalg.norm(v,axis=-1,keepdims=True)
        q[:,mask]=c[...,None]*direction+np.sqrt(np.maximum(0,1-c*c))[...,None]*v
    def force(self,q):
        H=self.spatial_field(q)
        return (-H[...,:1]*q[...,1:]+q[...,:1]*H[...,1:]+np.cross(q[...,1:],H[...,1:])).sum(1)
    def hmc(self):
        old=self.q;new=old.copy();p=self.rng.normal(size=(self.chains,self.n,3))
        initial=self.spatial_action(old)+(p*p).sum((1,2))/2
        step=.43*np.sqrt(self.x/(4*self.T));steps=int(self.rng.integers(3,7))
        p+=step*self.force(new)/2
        for j in range(steps):
            speed=np.linalg.norm(p,axis=-1,keepdims=True)
            g=np.concatenate([np.cos(step*speed),step*np.sinc(step*speed/np.pi)*p],axis=-1)
            new=left(g[:,None],new)
            p+=step*self.force(new)*(0.5 if j==steps-1 else 1.)
        final=self.spatial_action(new)+(p*p).sum((1,2))/2
        ok=np.log(self.rng.random(self.chains))<initial-final
        self.q=np.where(ok[:,None,None,None],new,old)
        return ok
    def sample(self):
        q=self.q[:,0];v=self.mode;b=(v[None,:,None]*q[...,1:]).sum(1)
        f=np.stack([(1-q[...,0]).sum(1),(b*b).sum(1)],axis=1)
        d=np.zeros((self.chains,2,self.n,4));d[:,0,:,0]=-1
        d[:,1,:,1:]=2*v[None,:,None]*b[:,None,:]
        d-=q[:,None]*(d*q[:,None]).sum(-1,keepdims=True)
        return f,np.einsum('cfni,cgni->cfg',d,d)/2

def estimate(F,G):
    a=F.reshape(-1,2);z=a-a.mean(0)
    return float(eigvalsh(G.reshape(-1,2,2).mean(0),z.T@z/len(z))[0])

def one(n,x,eps,T,seed,chains=8,burn=75,keep=160):
    S=Strip(n,x,eps,T,seed,chains);samples=[];grad=[];accept=[]
    for sweep in range(burn+keep):
        # Palindromic composition of reversible heat baths and a collective
        # HMC kernel. Four time arms yield the fourth power of the slab amplitude.
        order=int(S.rng.integers(2));S.heatbath(order);S.heatbath(1-order)
        a=S.hmc();S.heatbath(1-order);S.heatbath(order)
        if sweep>=burn:
            f,g=S.sample();samples.append(f);grad.append(g);accept.append(a)
    A=np.array(samples).transpose(1,0,2);B=np.array(grad).transpose(1,0,2,3)
    factor=x/(2*S.free_z);ratio=factor*estimate(A,B)
    leave=np.array([factor*estimate(np.delete(A,j,0),np.delete(B,j,0)) for j in range(chains)])
    se=np.sqrt((chains-1)*np.mean((leave-leave.mean())**2))
    t=student.ppf(.975,chains-1);series=A[:,:,0]-A[:,:,0].mean(1,keepdims=True)
    var=(series**2).mean();tau=1.
    for lag in range(1,keep//3):
        ac=(series[:,lag:]*series[:,:-lag]).mean()/var
        if ac<=0:break
        tau+=2*ac
    return dict(n=n,x=x,eps=eps,T=T,chains=chains,burn=burn,sweeps=keep,seed=seed,
           free_z=S.free_z,ratio=ratio,ci_low=ratio-t*se,ci_high=ratio+t*se,
           hmc_acceptance=np.mean(accept),integrated_autocorrelation=tau,
           effective_samples=chains*keep/tau,midpoint_norm_error=float(abs(np.linalg.norm(S.q,axis=-1)-1).max()))

def experiments():
    rows=[]
    for n in (1,2,4,8):
        for j,x in enumerate((.05,1/6)):
            for k,(eps,T) in enumerate(((.25,1.5),(.125,2.0))):
                row=one(n,x,eps,T,27000+101*n+10*j+k);rows.append(row)
    return rows
