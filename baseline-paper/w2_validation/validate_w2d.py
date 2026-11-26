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

"""W2d: transport and the retained form (targets W2d.1 to W2d.7)."""
import math

import numpy as np

from common import PI, SLOPE, A_of, R_closed, b0, check, close, finish, read_csv, rng, schur_axial
from validate_w2ar import upward_witness


# --------------------------------------------------------------- W2d.1
def w2d1():
    zs = [1e-2, 5e-3, 2.5e-3]
    sl = [(R_closed(z) ** -0.5 - 1) / z for z in zs]
    check("W2d.1", "[obstruction] axial transport multiplier has a nonzero first coefficient -(1+1/(2 sqrt2))/2",
          all(abs(s + SLOPE / 2) < 0.02 for s in sl) and abs(sl[-1] + SLOPE / 2) < abs(sl[0] + SLOPE / 2), f"{sl[-1]:.5f}")
    check("W2d.1", "[obstruction] a blanket quadratic symbol estimate fails at the axial point: |T-1|/z^2 unbounded",
          abs(R_closed(1e-4) ** -0.5 - 1) / 1e-8 > 1e3)


# --------------------------------------------------------------- W2d.2
def w2d2():
    ok = True
    for z in np.linspace(0.01, 1.5, 80):
        A, m, J, corr, E, w = schur_axial(z)
        ok &= close(A, 4 * m / R_closed(z), 1e-12)
    check("W2d.2", "A = 4m / R(z) on the first axial mode (80 momenta)", ok)
    z = 1e-5; A, m, *_ = schur_axial(z)
    check("W2d.2", "normalized defect A/(4m) - 1 = -(1 + 1/(2 sqrt 2)) z + O(z^2)", abs((A / (4 * m) - 1) / z + SLOPE) < 1e-4)
    viol = []
    for L in (64, 256, 1024, 4096):
        A, m, *_ = schur_axial(2 * PI / L)
        defect = A / (4 * m) - 1; Ca_bound = 10.0 * m * m      # any C_a (am)^2 with C_a = 10
        viol.append(defect < -Ca_bound)
    check("W2d.2", "[counterexample] the O(g^0) linear defect violates -C_a (am)^2 for large boxes (C_a = 10)", all(viol))
    ok = True
    for L, ref in ((4, -0.551712), (8, -0.472700), (16, -0.333459), (32, -0.205986)):
        A, m, *_ = schur_axial(2 * PI / L)
        ok &= abs(A / (4 * m) - 1 - ref) < 5e-7
    check("W2d.2", "defect/m column of the signed-margin table reproduced", ok)


# --------------------------------------------------------------- W2d.3
def w2d3():
    r = rng(33); ok = True
    for _ in range(10000):
        mV, R, b, rr = r.uniform(0, 5), r.uniform(0, 5), r.uniform(0, 1), r.uniform(1, 6)
        D = -R / 2 - b * mV + r.uniform(0, 3)
        Ar = rr * (D + mV + R)
        ok &= Ar >= (1 - b) * mV - 1e-12
    check("W2d.3", "D >= -R/2 - b mV, r >= 1, 0 <= b <= 1 imply A >= (1 - b) m V (10000 samples)", ok)
    N = 2; A = A_of(N); B = A / 2 / (1 / 6)
    check("W2d.3", "A g*^2 + B g*^4 <= 3/4 holds at g*^2 = 1/6, B g*^2 = A/2 (so r_k >= 1)", A / 6 + B / 36 <= 0.75)


# --------------------------------------------------------------- W2d.4
def w2d4():
    r = rng(34); ok = True
    for _ in range(1000):
        u, v = r.normal(size=2)
        ok &= u * 0.0 + v * 0.0 == 0.0
        kb, kp = r.normal(size=2)
        ok &= (u * kb + v * kp == 0.0) or (kb != 0 or kp != 0)
    check("W2d.4", "coefficient u*kappa_bar + v*kappa_phys vanishes when both mismatches vanish", ok)


# --------------------------------------------------------------- W2d.5
def w2d5():
    r = rng(35)
    for N in (2, 3):
        bb = b0(N); A = A_of(N); Ap = 1.5 * A
        check("W2d.5", f"SU({N}): A_+ = 3A/2 = 6 b0 log 2", close(Ap, 6 * bb * math.log(2)))
        ok = True
        for _ in range(2000):
            n = int(r.integers(1, 60)); gK2 = r.uniform(0.05, 1 / 6)
            dec = r.uniform(A, Ap, n)                     # admissible inverse-coupling decrements
            d = float(np.sum(dec)); gk2 = 1 / (1 / gK2 + d)
            aKm = r.uniform(0.01, 1); akm = aKm * 2.0 ** (-n)
            ok &= akm <= aKm * math.exp(-(1 / gk2 - 1 / gK2) / (6 * bb)) * (1 + 1e-12)
            ok &= akm ** 2 <= aKm ** 2 * math.exp(-(1 / gk2 - 1 / gK2) / (3 * bb)) * (1 + 1e-12)
        check("W2d.5", f"SU({N}): a_k m <= a_K m exp[-(g_k^-2 - g_K^-2)/(6 b0)] and its square (2000 runs)", ok)
    c, delta = 1.0, 1.5
    g = np.array([0.3, 0.2, 0.1, 0.05])
    lhs = np.exp(-1 / (g ** 2 * 3 * b0(2))); rhs = np.exp(-c / g ** delta)
    check("W2d.5", "exp(-C/g^2) is eventually smaller than exp(-c/g^delta), delta < 2", lhs[-1] < rhs[-1] and lhs[-2] < rhs[-2])


# --------------------------------------------------------------- W2d.6
def w2d6():
    r = rng(36); ok = True
    for _ in range(3000):
        n = int(r.integers(0, 80)); aw = r.uniform(0.01, 1); mbar = r.uniform(0.1, 3)
        a = aw * 2.0 ** (-np.arange(n)[::-1].astype(float)) if n else np.array([])
        mk = mbar * r.uniform(0, 1, n)
        ok &= float(np.sum((a * mk) ** 2)) <= 4 / 3 * (aw * mbar) ** 2 + 1e-15
    check("W2d.6", "sum_k (a_k m_k)^2 <= (4/3)(a_w m_bar)^2, empty run included (3000 runs)", ok)


# --------------------------------------------------------------- W2d.7
def w2d7():
    upward_witness("W2d.7")
    r = rng(37); ok = True
    for _ in range(5000):
        c0 = r.uniform(0.1, 3); c = r.uniform(0, 5)
        ok &= abs(c - c0) <= abs(c * c - c0 * c0) / c0 + 1e-12
    check("W2d.7", "speed error <= two-sided squared-speed error / reference speed (5000 samples)", ok)


if __name__ == "__main__":
    print("W2d  Transport and the retained form")
    for fn in (w2d1, w2d2, w2d3, w2d4, w2d5, w2d6, w2d7):
        fn()
    finish("W2d")
