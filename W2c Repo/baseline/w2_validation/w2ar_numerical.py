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

#!/usr/bin/env python3
"""Reproduce the W2a-R free-mode, one-loop matching and clock-product tables."""
from pathlib import Path
import csv, math
import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.integrate import quad
from scipy.special import i0e

checks = 0

def require(condition):
    global checks
    checks += 1
    if not condition:
        raise AssertionError('Numerical validation failed')

OUT = Path(__file__).resolve().parents[1] / 'numerical'

def table(name, rows):
    with (OUT/name).open('w',newline='') as f:
        writer=csv.DictWriter(f, fieldnames=rows[0]); writer.writeheader(); writer.writerows(rows)

def hamiltonian(order):
    # Partition the positive octant by its largest coordinate, then make the
    # Duffy substitution (t,t*u,t*v). Symmetrize the directional moments.
    raw,weights=leggauss(order); u=(raw+1)/2; w=weights/2
    U,V=np.meshgrid(u,u,indexing='ij'); W=np.outer(w,w)
    moments=np.zeros(4)
    for t,wt in zip(u,w):
        x,y,z=(math.pi/2*t, math.pi/2*t*U, math.pi/2*t*V)
        X,Y,Z=np.sin(x)**2,np.sin(y)**2,np.sin(z)**2
        b=np.sqrt(X+Y+Z)
        kernels=(b,1/b,(X*Y+Y*Z+Z*X)/(3*b**3),
                 (np.sin(2*x)**2+np.sin(2*y)**2+np.sin(2*z)**2)/(3*b**3))
        moments+=3*wt*t*t*np.array([np.sum(W*f) for f in kernels])
    i1,i2,i3,i4=moments
    alpha=-4*(i1/24-7*i2/288+i3/48+i4/128); beta=i1/6
    return moments,alpha,beta

def bessel_moments():
    # Laplace transform for b²; the three directions now factorize.
    def f(s):
        return i0e(s*s/2)**3
    def numerator(s):
        if s < 1e-4:
            return 1.5 - (21/16)*s*s
        return -math.expm1(3*math.log(i0e(s*s/2)))/(s*s)
    i1 = quad(numerator, 0, np.inf, epsabs=2e-12, epsrel=2e-12)[0]/math.sqrt(math.pi)
    i2 = 2*quad(f, 0, np.inf, epsabs=2e-12, epsrel=2e-12)[0]/math.sqrt(math.pi)
    return i1,i2

def finite_anisotropy(chi, order=32):
    # Evaluate Karsch (A.2)-(A.9) BEFORE taking the Hamiltonian limit.
    nodes,weights=leggauss(order); nodes=(nodes+1)/2; weights=weights/2
    U,V=np.meshgrid(nodes,nodes,indexing='ij')
    W=np.outer(weights,weights)
    values=np.zeros(8)
    for t,wt in zip(nodes,weights):
        x,y,z=math.pi*t/2,math.pi*t*U/2,math.pi*t*V/2
        X,Y,Z=np.sin(x)**2,np.sin(y)**2,np.sin(z)**2
        b=np.sqrt(X+Y+Z); v=b/chi; R=np.sqrt(1+v*v)
        correction=(1+2*v*v)/(R**3)
        pair=(X*Y+Y*Z+Z*X)/3
        double=(np.sin(2*x)**2+np.sin(2*y)**2+np.sin(2*z)**2)/3
        kernels=(b/R,correction/b,1/(b*R*(v+R)**2),pair*correction/b**3,
                 double*correction/b**3,1/(R*(v+R)),(1-b*b/3)/(b*R**3),1/(b*R**3))
        values+=3*wt*t*t*np.array([np.sum(W*k) for k in kernels])
    i1,i2a,i2b,i3,i4,i5,i6,i7=values
    differences=[]
    for N in (2,3):
        group=1-1/N**2
        hB=group*i1/24-5*i2a/288+i3/48+i4/128
        hE=group*(i1/(3*chi**2)+i5/chi)/16+i2b/64-5*i2a/576
        hE+=(i4/256-i6/48-i7/192)/chi**2
        differences.append(-4*N*(hB-hE))
    return differences

def blocked_free_modes():
    import itertools
    rows=[]
    for L in (8,16,32,64):
        p=2*math.pi/L
        for direction in ((1,0,0),(1,1,0)):
            mom=p*np.array(direction); poles=[]
            for r in itertools.product((0,1),repeat=3):
                q=mom+math.pi*np.array(r)
                link=1+np.exp(1j*q[2])
                khat=2*np.sin(q/2); energy=np.linalg.norm(khat)
                # The z-polarized coarse link is transverse on the low branch.
                weight=abs(link)**2*(1-khat[2]**2/energy**2)/(2*energy)
                if weight>1e-12:
                    poles.append((energy,r,weight))
            poles.sort()
            require(poles[0][1]==(0,0,0))
            phase=poles[0][0]/np.linalg.norm(mom)
            require(abs(phase-math.sin(p/2)/(p/2))<1e-14)
            rows.append(dict(L=L,direction=''.join(map(str,direction)),coarse_phase_speed=phase,
                             low_pole=poles[0][0],next_visible_pole=poles[1][0],low_weight=poles[0][2]))
    table('blocked_free_modes.csv',rows)
    return rows

def main():
    OUT.mkdir(exist_ok=True)
    quads=[]; checks=[]
    for n in (8,12,20,32,48):
        I,alpha,beta=hamiltonian(n)
        quads.append(dict(order=n,I1=I[0],I2=I[1],I3=I[2],I4=I[3],alpha=alpha,beta=beta,
                          c1_SU2=2*alpha+beta/2,c1_SU3=3*alpha+beta/3))
    table('hamiltonian_quadrature.csv',quads)
    require(max(abs(quads[-1][k]-quads[-2][k]) for k in ('I1','I2','I3','I4','c1_SU2','c1_SU3'))<1e-12)
    i1b,i2b=bessel_moments()
    independent_alpha=-(5*i1b+4*i2b)/72
    independent_beta=i1b/6
    require(abs(independent_alpha-alpha)<2e-12 and abs(independent_beta-beta)<2e-12)
    require(abs(I[3]-(4*I[1]-8*I[0]/3))<2e-12 and abs(I[2]-(I[1]/3-I[0]/6))<2e-12)
    coeff=[]
    for N,cs,ct in ((2,.09958,-.06798),(3,.18018,-.15405)):
        a=11*N*math.log(2)/(12*math.pi**2);c1=alpha*N+beta/N
        independent=independent_alpha*N+independent_beta/N
        require(abs(c1-independent)<2e-12)
        diff=abs(c1-(ct-cs))
        rounding_ok=diff<=1.00001e-5
        print(f'SU({N}) printed-pair rounding check: {rounding_ok}, discrepancy {diff:.9g}, maximum rounding 0.000010')
        xs=1/6
        Q=1/(1-a*xs)
        Mc=c1*c1/(1-abs(c1)*xs)
        d0=1-abs(c1)*xs-Mc*xs*xs
        coeff.append(dict(N=N,A=a,c1=c1,karsch_csigma=cs,karsch_ctau=ct,karsch_B2=ct-cs,
                     bessel_c1=independent,abs_difference=diff,within_published_pair_rounding=rounding_ok,
                     rel_difference=diff/abs(ct-cs),Cxi_schemeB=6*a*abs(c1),model_xs=xs,
                     model_B=0,model_Mc=Mc,model_d0=d0,model_Q=Q,
                     model_Cxi_schemeA=(abs(c1)*a*Q+Mc*(1+Q*Q))/d0,
                     model_schemeB_Mmatch_bound=Mc*(1+Q*Q)/d0))
    table('coefficients.csv',coeff)
    anis=[]
    for chi in (1,4,32,1000,1e6,1e9):
        su2,su3=finite_anisotropy(chi)
        anis.append(dict(chi=chi,contrast_SU2=su2,contrast_SU3=su3))
    require(max(abs(anis[0][k]) for k in ('contrast_SU2','contrast_SU3'))<1e-12)
    require(max(abs(anis[-1][k]-quads[-1][g]) for k,g in
               [('contrast_SU2','c1_SU2'),('contrast_SU3','c1_SU3')])<1e-8)
    table('anisotropic_limit.csv',anis)
    print('Finite-anisotropy contrasts:',anis)
    print('Blocked free poles:',len(blocked_free_modes()),'momentum/box pairs passed')
    boxes=[]
    for L in (4,8,16,32):
        # Periodic nearest-neighbour Laplacian evaluated on its first Fourier mode.
        theta=2*np.pi*np.arange(L)/L; v=np.exp(1j*theta); Av=2*v-np.roll(v,1)-np.roll(v,-1)
        lam=(np.vdot(v,Av)/np.vdot(v,v)).real; t=math.pi/L; value=math.sqrt(lam)/(2*t)
        ref=math.sin(t)/t; err=value-(1-t*t/6)
        require(abs(value-ref)<1e-14 and -2e-15<=err<=t**4/120+2e-15)
        boxes.append(dict(L=L,mode_clock=value,sinc=ref,abs_difference=abs(value-ref),remainder=err,upper=t**4/120))
    table('free_clock.csv',boxes)
    products=[]
    for row in coeff:
        for K in (10,100,1000,10000):
            x=1/(6+row['A']*np.arange(K,-1,-1,dtype=float))
            for c1 in (-.20,-.10,-.05,.05,.10,.20):
                c=1+c1*x
                direct=math.prod(float(t) for t in (c[:-1]/c[1:]))
                endpoint=c[0]/c[-1]; uv=1/c[-1]; delta=abs(direct-endpoint)
                require(delta<3e-12)
                products.append(dict(N=row['N'],K=K,trial_c1=c1,product=direct,endpoint=endpoint,
                                     uv_limit=uv,abs_difference=delta,finite_cutoff_error=abs(endpoint-uv)))
    table('clock_products.csv',products)
    print('Hamiltonian quadrature',quads[-1]);print('Coefficients',coeff)
    print('Free clocks',[r['mode_clock'] for r in boxes]);print('48 endpoint checks, maximum difference',max(r['abs_difference'] for r in products))

if __name__=='__main__':
    main()
    print('W2a-R numerical assertions:',checks)
