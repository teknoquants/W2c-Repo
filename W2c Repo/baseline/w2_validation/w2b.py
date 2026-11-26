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

"""Finite-volume free Maxwell benchmark. Frequencies use fine spacing and coupling equal to one."""
import argparse
import csv
from itertools import product
from pathlib import Path
import math
import numpy as np
from scipy.linalg import null_space

checks = 0

def check(ok, label):
    global checks
    checks += 1
    if not ok:
        raise ArithmeticError(label)

def record(path, rows):
    with path.open('w', newline='', encoding='utf-8') as out:
        writer=csv.DictWriter(out,fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)

def transverse(q):
    gradient=np.expm1(1j*q)
    norm=np.linalg.norm(gradient)
    if norm<1e-12:
        return 0.,np.zeros((3,0),complex)
    return norm,null_space(gradient.conj()[None,:])

def space_kernel(symbol):
    kernel=np.fft.ifftn(symbol,axes=(0,1,2))
    n=kernel.shape[0]
    row_sum=float(abs(kernel).sum(axis=(0,1,2,4)).max())
    coord=np.minimum(np.arange(n),n-np.arange(n))
    radius=np.sqrt(sum(axis**2 for axis in np.meshgrid(coord,coord,coord,indexing='ij')))
    size=np.linalg.norm(kernel,axis=(-2,-1))
    means=[]
    for r in range(2,n//2+1):
        mask=(radius>=r-.5)&(radius<r+.5)
        if mask.any():
            means.append((r,size[mask].mean()))
    exponent=float(-np.polyfit(np.log([r for r,_ in means]),np.log([v for _,v in means]),1)[0]) if len(means)>=3 else ''
    return row_sum,exponent

def fourier_block(p,Q):
    blocks=[]
    energy=[]
    for alias in product((0,1),repeat=3):
        q=p+np.pi*np.asarray(alias)
        omega,U=transverse(q)
        if U.shape[1]:
            B=Q.conj().T@((1+np.exp(1j*q))[:,None]*U)/math.sqrt(8)
            blocks.append(B)
            energy.extend([omega]*U.shape[1])
    if not blocks:
        return np.zeros((0,0)),np.array([])
    return np.concatenate(blocks,axis=1),np.asarray(energy)

def analyze(L):
    n=L//2
    momenta=2*np.pi*np.fft.fftfreq(n)
    M=np.zeros((n,n,n,3,3),complex)
    minimum_D=math.inf
    minimum_A=math.inf
    max_score=0.
    max_mixed=0.
    axial=None
    full=[]
    m=math.sin(2*np.pi/L)
    for ind in np.ndindex(n,n,n):
        Pc=np.array([momenta[j] for j in ind])
        _,Q=transverse(Pc)
        T,E=fourier_block(Pc/2,Q)
        if not Q.shape[1]:
            minimum_D=min(minimum_D,min(E))
            continue
        check(np.allclose(T@T.conj().T,2*np.eye(2),atol=2e-12), 'horizontal lift normalization')
        G=T/np.sqrt(2*E)
        cov=G@G.conj().T
        ev,V=np.linalg.eigh(cov)
        inverse_root=(V/np.sqrt(ev))@V.conj().T
        retained=G.conj().T@inverse_root
        elim=null_space(retained.conj().T)
        A=retained.conj().T@(E[:,None]*retained)
        D=elim.conj().T@(E[:,None]*elim)
        B=elim.conj().T@(E[:,None]*retained)
        d,U=np.linalg.eigh(D)
        ae,AU=np.linalg.eigh(A)
        minimum_D=min(minimum_D,d[0])
        minimum_A=min(minimum_A,ae[0])
        mixed=np.linalg.svd((U.conj().T@B@AU)/(np.sqrt(d)[:,None]*np.sqrt(ae)),compute_uv=False)[0]
        max_mixed=max(max_mixed,mixed)
        score=(T*(2*E))@T.conj().T/4-np.linalg.inv(cov)
        check(np.linalg.eigvalsh(score)[0]>-1e-10,'Gaussian conditional score covariance')
        max_score=max(max_score,np.linalg.eigvalsh(score)[-1])
        M[ind]=Q@score@Q.conj().T
        coarse_ref=1/(2*np.linalg.norm(np.expm1(1j*Pc)))
        full.append(dict(L=L,kx=ind[0],ky=ind[1],kz=ind[2],
                         ratio_min=ev[0]/coarse_ref,ratio_max=ev[-1]/coarse_ref,
                         variance_min=ev[0],variance_max=ev[-1],retained_min=ae[0],
                         eliminated_min=d[0],mixed_norm=mixed,score_max=np.linalg.eigvalsh(score)[-1]))
        if ind==(1,0,0):
            z=2*np.pi/L
            s,h=np.sin(z/2),np.cos(z/2)
            frequencies=2*np.array([s,h,np.sqrt(1+s*s),np.sqrt(1+h*h)])
            weights=(1/frequencies)/sum(1/frequencies)
            aa=float(np.dot(weights,frequencies))
            eff=m+1/sum(weights/(frequencies-m))
            corr=aa-eff
            direct=B.conj().T@np.linalg.solve(D-m*np.eye(len(D)),B)
            check(np.allclose(direct, np.eye(2)*corr,atol=1e-10),'matrix Schur versus spectral resolvent')
            check(np.allclose(A,np.eye(2)*aa,atol=1e-10),'retained compressed energy')
            formula=np.sin(z)/2*(1/s+1/h+1/np.sqrt(1+s*s)+1/np.sqrt(1+h*h))
            check(np.allclose(ev/coarse_ref,formula,atol=1e-11),'static four-alias formula')
            c=s/(z/2)
            check(0<=c-1+(z/2)**2/6<=(z/2)**4/120+1e-15, 'signed sinc error')
            axial=dict(L=L,z=z,cov_ratio=formula,static_slope=(formula-1)/z,clock=c,
                signed_sinc_remainder=c-1+(z/2)**2/6,sinc_upper=(z/2)**4/120,
                gamma_fine=frequencies[0],gamma_coarse=m,gap_ratio=frequencies[0]/m,
                A_retained=aa,raw_schur=corr,schur_over_A=corr/aa,
                schur_margin=eff-m,retained_defect_over_m=aa/(4*m)-1,first_chaos_gap_sufficient=eff>=m,weights_sum=sum(weights))
    fine_q=2*np.pi*np.fft.fftfreq(L)
    coords=np.stack(np.meshgrid(fine_q,fine_q,fine_q,indexing='ij'),axis=-1)
    g=np.expm1(1j*coords)
    freq=np.linalg.norm(g,axis=-1)
    safe=np.where(freq>1e-12,freq,1.)
    precision=2*freq[...,None,None]*(np.eye(3)-g[...,None]*g[...,None,:].conj()/safe[...,None,None]**2)
    ps,pexp=space_kernel(precision)
    ss,sexp=space_kernel(M)
    metrics=dict(L=L,alpha_first_chaos=max(0.,1-minimum_A/m),lambda_eliminated_first_chaos=minimum_D,
        mixed_energy_norm=max_mixed,g_squared_J_gaussian=max_score,zeta_first_chaos=max_score/(minimum_D-m),
        precision_row_sum=ps,score_row_sum=ss,precision_shell_exponent=pexp,score_shell_exponent=sexp)
    return axial,metrics,full

def open_gaps(L):
    # Tensor products of the free path graph cochain Laplacians. Transverse modes require two active axes.
    def first(side):
        inc=np.eye(side,side+1,k=1)-np.eye(side,side+1)
        eig=np.linalg.eigvalsh(inc@inc.T)
        return math.sqrt(2*eig[0])
    f,c=first(L),first(L//2)/2
    check(abs(f-2*math.sqrt(2)*math.sin(math.pi/(2*(L+1))))<1e-12,'open cochain spectrum')
    return dict(L=L,open_fine_gap=f,open_coarse_gap=c,open_ratio=f/c)

def pole_rows(L):
    rows=[]
    for direction in ((1,0,0),(1,1,0)):
        p=2*np.pi*np.array(direction)/L
        component=1 if direction==(1,0,0) else 2
        energies=[];residues=[]
        for r in product((0,1), repeat=3):
            q=p+np.pi*np.asarray(r)
            E,U=transverse(q)
            proj=float(np.real((U@U.conj().T)[component,component]))
            w=abs(1+np.exp(1j*q[component]))**2 * proj/(16*E)
            rows.append(dict(L=L,direction=''.join(map(str,direction)),component=component+1,alias=''.join(map(str,r)),energy=E,residue=w,phase_speed=E/np.linalg.norm(p)))
            energies.append(E);residues.append(w)
        visible=np.asarray(residues)>1e-12
        low=min(np.array(energies)[visible])
        check(abs(low-energies[0])<1e-12 and residues[0]>0,'positive lowest pole')
        check(1-max(abs(p/2))**2/6-1e-12<=low/np.linalg.norm(p)<=1+1e-12,'directional phase bound')
    return rows

def direct_periodic(L):
    # Diagonalize path differences with the periodic wrap, independently of the alias compression.
    inc=np.eye(L)-np.roll(np.eye(L),1,axis=1)
    val=np.linalg.eigvalsh(inc.T@inc)
    check(abs(math.sqrt(val[1])-2*math.sin(math.pi/L))<2e-13,'periodic gap from Laplacian')
    # Fourier transform a unit link impulse and its translated neighbour. Retained volume factor = 1/8.
    impulse=np.zeros((L,L,L));impulse[0,0,0]=1;impulse[0,1,0]=1
    F=np.fft.fftn(impulse)
    z=2*math.pi/L
    cov=0.
    for r in product((0,1),repeat=3):
        index=((1+r[0]*L//2)%L,r[1]*L//2,r[2]*L//2)
        q=2*np.pi*np.array(index)/L
        E,U=transverse(q)
        cov+=abs(F[index])**2*float(np.real((U@U.conj().T)[1,1]))/(16*E)
    return cov*4*math.sin(z)

def angular_rows():
    rows=[]
    for direction in ((1,0,0),(1,1,0),(1,1,1),(1,2,3),(-1,2,-3)):
        u=np.asarray(direction,dtype=float);u/=np.linalg.norm(u)
        for z in (.1,.01,.001):
            ec,Q=transverse(2*z*u);T,E=fourier_block(z*u,Q)
            ratio=np.linalg.eigvalsh((T/(2*E))@T.conj().T)*(2*ec)
            slopes=(ratio-1)/z
            target=1+1/(2*math.sqrt(2))
            check(max(abs(slopes-target))<.25*z,'directional linear covariance slope')
            rows.append(dict(direction=' '.join(map(str,direction)),z=z,smaller_ratio=ratio[0],
                larger_ratio=ratio[1],smaller_slope=slopes[0],larger_slope=slopes[1],limiting_slope=target))
    return rows

def run(out):
    global checks
    checks = 0
    rows=[]; metrics=[]; full=[]; openrows=[]; poles=[]
    for L in (4,8,16,32):
        a,b,grid=analyze(L)
        rows.append(a);metrics.append(b);full.extend(grid);openrows.append(open_gaps(L));poles.extend(pole_rows(L))
        check(abs(direct_periodic(L)-a["cov_ratio"])<2e-12,"real-space link sum versus axial covariance")
    check(all(r['schur_over_A']>.45 for r in rows[-2:]),'raw Schur counterexample')
    check(all(r['first_chaos_gap_sufficient'] for r in rows),'combined Schur margin')
    check(all(r['g_squared_J_gaussian']>0 for r in metrics),'nonzero Gaussian score')
    for n,r in [('axial.csv',rows),('gaussian.csv',metrics),('all-momenta.csv',full),('open-gaps.csv',openrows),('poles.csv',poles),('angular.csv',angular_rows())]:
        record(out/n,r)
    print(f'{len(full)} nonzero coarse momentum blocks in four boxes; independent spectral and matrix Schur tests passed.')
    return checks

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output',type=Path)
    folder=parser.parse_args().output
    folder.mkdir(parents=True,exist_ok=True)
    run(folder)
