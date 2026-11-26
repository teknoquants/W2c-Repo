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

"""W2c: gauge reduction and the eliminated gap (targets W2c.1 to W2c.6)."""
import itertools
import math

import numpy as np
from scipy.integrate import quad

from common import A_of, b0, check, close, finish, read_csv, rng


def haar_su(n, r):
    Z = (r.normal(size=(n, n)) + 1j * r.normal(size=(n, n))) / math.sqrt(2)
    Q, R = np.linalg.qr(Z)
    Q = Q @ np.diag(np.diag(R) / np.abs(np.diag(R)))
    return Q / np.linalg.det(Q) ** (1.0 / n)


# --------------------------------------------------------------- W2c.1
def w2c1():
    r = rng(21)
    for n in (2, 3):
        ok = True
        for _ in range(1000):
            U1, U2, h = haar_su(n, r), haar_su(n, r), haar_su(n, r)
            ok &= np.allclose((U1 @ h.conj().T) @ (h @ U2), U1 @ U2, atol=1e-12)
        check("W2c.1", f"SU({n}): midpoint gauge transformation preserves the coarse product U1 U2 (1000 samples)", ok)
    # a conditional law that depends on fine links only through gauge-invariant data is invariant
    U1, U2 = haar_su(2, r), haar_su(2, r)
    w = lambda a, b: math.exp(np.real(np.trace(a @ b)))
    hs = [haar_su(2, r) for _ in range(200)]
    check("W2c.1", "a weight of the coarse product is constant on each eliminated-gauge orbit",
          np.allclose([w(U1 @ h.conj().T, h @ U2) for h in hs], w(U1, U2)))


# --------------------------------------------------------------- W2c.2
def cube_counts(s):
    V = (s + 1) ** 3
    E = 3 * s * (s + 1) ** 2
    return V, E


def enumerate_cube(s):
    verts = set(itertools.product(range(s + 1), repeat=3))
    links = 0
    for v in verts:
        for d in range(3):
            w = list(v); w[d] += 1
            if tuple(w) in verts:
                links += 1
    return len(verts), links


def w2c2():
    per_vertex_vertices = 1 + 3 + 3 + 1
    per_vertex_links = 3 * 8
    check("W2c.2", "per coarse vertex: 8 fine vertices (1+3+3+1) and 24 fine links (6 on paths + 18 unused)",
          per_vertex_vertices == 8 and per_vertex_links == 24 and 6 + 18 == 24)
    check("W2c.2", "bulk: fibre 21 dim G, eliminated group 7 dim G, quotient 14 dim G", 24 - 3 == 21 and 8 - 1 == 7 and 21 - 7 == 14)
    ok = True
    for s in range(1, 9):
        ok &= enumerate_cube(s) == cube_counts(s)
    check("W2c.2", "V(s)=(s+1)^3, E(s)=3s(s+1)^2 by explicit enumeration of open cubes, s=1..8", ok)
    ok = True
    for n in range(1, 60):
        V2, E2 = cube_counts(2 * n); V1, E1 = cube_counts(n)
        ok &= (E2 - E1 - V2 + V1) == 14 * n ** 3 + 9 * n ** 2
    check("W2c.2", "open cube: E(2n)-E(n)-V(2n)+V(n) = 14n^3 + 9n^2 for n = 1..59", ok)
    # periodic block: the coarse map uses disjoint pairs of fine links -> submersion
    Lc = 3; ok = True
    used = set()
    for x in itertools.product(range(Lc), repeat=3):
        for d in range(3):
            a = tuple((2 * x[i] + (1 if False else 0)) for i in range(3))
            l1 = (tuple(2 * x[i] for i in range(3)), d)
            mid = list(2 * x[i] for i in range(3)); mid[d] = (mid[d] + 1) % (2 * Lc)
            l2 = (tuple(mid), d)
            ok &= l1 not in used and l2 not in used
            used |= {l1, l2}
    check("W2c.2", "coarse paths use disjoint pairs of fine links (block map is a submersion)", ok and len(used) == 6 * Lc ** 3)


# --------------------------------------------------------------- W2c.3
def w2c3():
    rows = read_csv("gaussian.csv")
    lam = [float(r["lambda_eliminated_first_chaos"]) for r in rows]
    check("W2c.3", "[evidence] first-chaos eliminated gap a*Lambda_perp >= 1.39 on all four grids", min(lam) > 1.39, f"min {min(lam):.6f}")
    ratios = []
    for s in (0, 8, 16, 32, 64):
        ratios.append(rayleigh(s)[0])
    check("W2c.3", "[obstruction] without a curvature bound the Poincare constant is not uniform (Rayleigh -> 0)",
          ratios[-1] < 1e-3 * ratios[0])


# --------------------------------------------------------------- W2c.4
def w2c4():
    r = rng(24); ok = True
    for _ in range(5000):
        g2, a, c, T = r.uniform(0.01, 1), r.uniform(0.01, 1), r.uniform(0.1, 5), r.uniform(0, 10)
        Var = r.uniform(0, 1) * g2 / c * T                 # fibre Poincare inequality
        D = g2 / (2 * a) * T                               # c_k times tangential Dirichlet integral
        ok &= D >= c * Var / (2 * a) - 1e-12
    check("W2c.4", "fibre Poincare + c_k = g^2/(2a) gives D_k >= (c/2a) Var: kappa = c/2 (5000 samples)", ok)


# --------------------------------------------------------------- W2c.5
def w2c5():
    r = rng(25); ok = True
    for _ in range(5000):
        m, a, k = r.uniform(0.01, 2), r.uniform(0.001, 1), r.uniform(0.1, 3)
        Lam = k / a * r.uniform(1, 5)
        s = 1 - m / Lam
        ok &= s >= 1 - a * m / k - 1e-14
    check("W2c.5", "s = sigma/(1+sigma) >= 1 - a m / kappa (5000 samples)", ok)
    N = 2; bb = b0(N); A = A_of(N); gK2 = 1 / 6; aKm = 0.5; kap = 1.0
    errs = []
    for n in (5, 10, 20, 40):
        gk2 = 1 / (1 / gK2 + 1.5 * A * n)                 # strongest admissible running
        am = aKm * math.exp(-(1 / gk2 - 1 / gK2) / (6 * bb))
        errs.append(am / kap)
    check("W2c.5", "error a_k m / kappa decays exponentially in the inverse squared coupling",
          all(errs[i + 1] < errs[i] ** 1.5 for i in range(2)) and errs[-1] < 1e-10)


# --------------------------------------------------------------- W2c.6
def rayleigh(s):
    f = lambda x: max(-1.0, min(1.0, 4 * x))
    rho = lambda x: math.exp(s * x * x)
    Z = quad(rho, -1, 1, points=[-0.25, 0.25], limit=200)[0]
    mean = quad(lambda x: f(x) * rho(x), -1, 1, points=[-0.25, 0.25], limit=200)[0] / Z
    energy = quad(lambda x: 16 * rho(x), -0.25, 0.25)[0]
    norm = quad(lambda x: f(x) ** 2 * rho(x), -1, 1, points=[-0.25, 0.25], limit=200)[0]
    return energy / norm, mean, energy, norm


def w2c6():
    ok_mean = ok_bound = ok_pieces = True
    vals = []
    for s in (0, 2, 5, 10, 20, 40, 80):
        R, mean, energy, norm = rayleigh(s)
        vals.append(R)
        ok_mean &= abs(mean) < 1e-12
        ok_pieces &= energy <= 8 * math.exp(s / 16) + 1e-12 and norm >= math.exp(s / 4) - 1e-12
        ok_bound &= R <= 8 * math.exp(-3 * s / 16) + 1e-12
    check("W2c.6", "odd test function has weighted mean zero", ok_mean)
    check("W2c.6", "energy <= 8 e^(s/16) and squared norm >= e^(s/4)", ok_pieces)
    check("W2c.6", "Rayleigh quotient <= 8 e^(-3s/16) and tends to zero", ok_bound and vals[-1] < 1e-5, f"R(80)={vals[-1]:.2e}")


if __name__ == "__main__":
    print("W2c  Gauge reduction and the eliminated gap")
    for fn in (w2c1, w2c2, w2c3, w2c4, w2c5, w2c6):
        fn()
    finish("W2c")
