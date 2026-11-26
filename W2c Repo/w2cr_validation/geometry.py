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

"""Check a short horizontal quotient geodesic at a single active SU(2) plaquette."""
from itertools import product,combinations
import numpy as np
from scipy.linalg import solve
from multilink import left
I=np.array([1.,0.,0.,0.])
def inv(q):
    r=q.copy();r[...,1:]*=-1;return r
def expv(v):
    a=np.linalg.norm(v,axis=-1,keepdims=True)
    return np.concatenate([np.cos(a),np.sinc(a/np.pi)*v],axis=-1)
def rotation(q):
    basis=np.c_[np.zeros(3),np.eye(3)]
    return left(left(q,basis),inv(q))[:,1:].T
def step(x,j,t=1):
    y=list(x);y[j]+=t;return tuple(y)
def square(x,i,j):
    return [((x,i),1),((step(x,i),j),1),((step(x,j),i),-1),((x,j),-1)]
def angle(U,sq):
    p=I
    for e,sgn in sq:p=left(p,U[e] if sgn==1 else inv(U[e]))
    return float(np.arctan2(np.linalg.norm(p[1:]),p[0]))
def counterexample(epsilon):
    L=4;vertices=list(product(range(L+1),repeat=3))
    edges=[(x,i) for x in vertices for i in range(3) if x[i]<L]
    plaquettes=[square(x,i,j) for x in vertices for i,j in combinations(range(3),2) if max(x[i],x[j])<L]
    face=(1,1,1);active=square(face,0,1);eye=np.eye(3);z=eye[2]
    base={e:I.copy() for e in edges}
    for e,a in active:base[e]=expv(a*epsilon*z/4)
    roots=[x for x in vertices if any(v%2 for v in x)];idx={x:i for i,x in enumerate(roots)}
    # Fibre parameters: each ordered midpoint pair is stored once with metric 2.
    params=[];pairs={}
    for x,i in edges:
        paired=all(x[j]%2==0 for j in range(3) if j!=i)
        if paired and x[i]%2:continue
        params.append((x,i))
        if paired:pairs[(x,i)]=(step(x,i),i)
    pos={e:k for k,e in enumerate(params)}
    D=np.zeros((len(params),3,len(roots),3));metric=np.array([2 if e in pairs else 1 for e in params])
    for n,(x,i) in enumerate(params):
        y=step(x,i)
        if x in idx:D[n,:,idx[x],:]=eye
        if y in idx:D[n,:,idx[y],:]=-rotation(base[x,i])
    # Exterior loops can prescribe the four velocities on the active square
    # independently. Use X,-Y,-X,Y, so their group commutator points toward -Z.
    V=np.zeros((len(params),3))
    for (edge,sgn),v,root in zip(active,[eye[0],-eye[1],-eye[0],eye[1]],
             [step(face,1,-1),step(face,0),step(face,1),step(face,0,-1)]):
        loop=square(root,0,1);a=dict(loop)[edge]
        for other,sign in loop:V[pos[other]]+=sign*a*sgn*v
    A=D.reshape(3*len(params),-1);w=np.repeat(metric,3)
    v=V.ravel();J=A.T*w
    horizontal=(v-A@solve(J@A,J@v,assume_a='pos')).reshape(-1,3)
    residual=float(np.max(abs(J@horizontal.ravel())))
    def move(t):
        q=left(expv(t*horizontal),np.array([base[e] for e in params]));U=dict(zip(params,q))
        for e,f in pairs.items():U[f]=inv(U[e])
        return U
    h=epsilon/5;plus=move(h);minus=move(-h)
    return dict(angle=epsilon,h=h,mid=angle(base,active),plus=angle(plus,active),minus=angle(minus,active),
                endpoint_max=max(angle(Y,sq) for Y in (plus,minus) for sq in plaquettes),
                other_max_at_center=max(angle(base,sq) for sq in plaquettes if sq!=active),
                horizontal_residual=residual,second=(angle(plus,active)+angle(minus,active)-2*epsilon)/h**2)
