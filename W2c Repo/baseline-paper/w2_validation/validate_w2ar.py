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

"""W2a-R: the physical clock and Wilson calibration (targets W2a-R.1 to W2a-R.10)."""
import math

import mpmath as mp
import numpy as np
from scipy.integrate import quad
from scipy.special import i0e

from common import A_of, check, close, finish, read_csv, rng

C1 = {2: -0.167509851556, 3: -0.334167632989}      # W2a-R.8 targets
XS = 1.0 / 6.0                                      # x* = g*^2


# --------------------------------------------------------------- W2a-R.1
def w2ar1():
    r = rng(1)
    coeff = {row["N"]: row for row in read_csv("coefficients.csv")}
    for N in (2, 3):
        A = A_of(N); c1 = C1[N]; Ap = A; Q = 1 / (1 - Ap * XS)
        # model clock c_ref = 1 + c1 x; reciprocal remainder constant on (0, x*]
        Mc = c1 * c1 / (1 - abs(c1) * XS)
        d0 = 1 - abs(c1) * XS - Mc * XS ** 2
        CxiA = (abs(c1) * Ap * Q + Mc * (1 + Q * Q)) / d0
        row = coeff[str(N)]
        check("W2a-R.1", f"SU({N}) Scheme A constants d0, Q, C_xi^A reproduce reference table",
              close(d0, float(row["model_d0"]), 1e-9) and close(Q, float(row["model_Q"]), 1e-9)
              and close(CxiA, float(row["model_Cxi_schemeA"]), 1e-9), f"C_xi^A={CxiA:.6f}")
        u = lambda x: 1 / (1 + c1 * x)
        worst = 0.0
        for _ in range(20000):
            x = r.uniform(1e-6, XS)
            ymax = min(x + Ap * Q * x * x, Q * x)
            y = r.uniform(x, ymax)
            worst = max(worst, abs(u(y) - u(x)) / u(x) / (x * x) / CxiA)
        check("W2a-R.1", f"SU({N}) one-step clock change <= C_xi^A x^2 on 20000 samples", worst <= 1.0,
              f"max ratio {worst:.4f}")
        # Scheme B: linear calibration xi_B = 1 - c1 x
        dB = 1 - abs(c1) * XS
        CxiB = abs(c1) * Ap * Q / dB
        bound6 = 6 * A * abs(c1)
        check("W2a-R.1", f"SU({N}) Scheme B: C_xi^B <= 6A|c1| under the smallness hypotheses",
              CxiB <= bound6 and Ap * XS <= 0.5 and abs(c1) * XS <= 0.5 and close(bound6, float(row["Cxi_schemeB"]), 1e-9),
              f"{CxiB:.5f} <= {bound6:.5f}")
        MmB = Mc * (1 + Q * Q) / d0
        worst = 0.0
        for _ in range(20000):
            x = r.uniform(1e-6, XS); y = r.uniform(x, min(x + Ap * Q * x * x, Q * x))
            e = lambda t: u(t) - (1 - c1 * t)
            worst = max(worst, abs(e(y) - e(x)) / u(x) / (x * x) / MmB)
        check("W2a-R.1", f"SU({N}) Scheme B mismatch <= M_c(1+Q^2)/d0 x^2", worst <= 1.0, f"max ratio {worst:.4f}")
    # product of two factors: (1+a)(1+b)-1 <= a+b+ab
    ok = True
    for _ in range(5000):
        Cx, Mm, x = r.uniform(0, 1, 3); x *= XS
        a, b = Cx * x * x, Mm * x * x
        ok &= (1 + a) * (1 + b) - 1 <= (Cx + Mm + Cx * Mm * XS ** 2) * x * x + 1e-15
    check("W2a-R.1", "per-step error <= [C_xi + M_match + C_xi M_match x*^2] g^4", ok)


# --------------------------------------------------------------- W2a-R.2
def w2ar2():
    A = A_of(2); c1 = C1[2]; rho = 0.3
    c = lambda x: 1 + c1 * x + rho * x * x
    xJ = XS
    for J in (10, 1000, 100000):
        xs = 1.0 / (1.0 / xJ + A * np.arange(J, -1, -1))      # x_0 (finest) ... x_J
        F = c(xs[:-1]) / c(xs[1:])
        prod = float(np.prod(F))
        check("W2a-R.2", f"J={J}: product of step factors telescopes to c(x0)/c(xJ)",
              close(prod, c(xs[0]) / c(xJ), 1e-11))
    check("W2a-R.2", "cutoff removed at fixed g_J: product -> 1/c_ref(g_J)",
          abs(prod - 1 / c(xJ)) < 2e-5, f"|diff|={abs(prod - 1 / c(xJ)):.2e}")
    xs = 1.0 / (1.0 / xJ + A * np.arange(200000, -1, -1))
    F = c(xs[:-1]) / c(xs[1:])
    idx = np.array([0, 10, 100, 1000, 10000, 100000])
    ratio = (F[idx] - 1) / (-c1 * A * xs[idx] ** 2)
    rel = np.abs(ratio - 1) / xs[idx]
    check("W2a-R.2", "first correction F_k - 1 = -c1 A g_k^4 + O(g_k^6): |ratio-1| <= 10 g_k^2",
          np.all(rel <= 10.0), f"max |ratio-1|/g^2={np.max(rel):.2f}")
    check("W2a-R.2", "empty product (J=0) equals 1", float(np.prod(np.array([]))) == 1.0)


# --------------------------------------------------------------- W2a-R.3
def w2ar3():
    mp.mp.dps = 40
    A = mp.mpf(A_of(2)); b = mp.mpf(6)
    for kappa in (mp.mpf("0.05"), mp.mpf("-0.04"), mp.mpf("0.12")):
        for K in (10, 500):
            prod = mp.fprod([1 + kappa / (b + A * j) for j in range(K)])
            gam = (mp.gamma((b + kappa) / A + K) * mp.gamma(b / A)) / (mp.gamma(b / A + K) * mp.gamma((b + kappa) / A))
            check("W2a-R.3", f"kappa={float(kappa)}, K={K}: product equals the gamma ratio", abs(prod - gam) < mp.mpf(10) ** -30)
        K = 10 ** 6
        lim = mp.gamma(b / A) / mp.gamma((b + kappa) / A)
        gam = (mp.gamma((b + kappa) / A + K) * mp.gamma(b / A)) / (mp.gamma(b / A + K) * mp.gamma((b + kappa) / A))
        check("W2a-R.3", f"kappa={float(kappa)}: product ~ const * K^(kappa/A)", abs(gam / mp.mpf(K) ** (kappa / A) / lim - 1) < 1e-4)
    prod0 = mp.fprod([1 + 0 / (b + A * j) for j in range(1000)])
    check("W2a-R.3", "kappa = 0 gives no drift (product identically 1)", prod0 == 1)
    rho = 1.0
    check("W2a-R.3", "time covariance (1-rho)s = kappa with rho = 1 forces kappa = 0",
          all((1 - rho) * s == 0.0 for s in (-0.3, 0.2, 1.7)))


# --------------------------------------------------------------- W2a-R.4
def w2ar4():
    r = rng(4); ok = True
    for _ in range(500):
        E0, E1p, E1r = sorted(r.uniform(0, 5, 3))[0], r.uniform(2, 6), r.uniform(1, 2)
        p1 = r.uniform(0.1, 1)
        shift = r.uniform(-50, 50)
        c2 = ((E1p - E0) ** 2 - (E1r - E0) ** 2) / p1 ** 2
        c2s = (((E1p + shift) - (E0 + shift)) ** 2 - ((E1r + shift) - (E0 + shift)) ** 2) / p1 ** 2
        ok &= close(c2, c2s, 1e-9, 1e-9)
    check("W2a-R.4", "c_L^2 is invariant under a common energy shift (500 samples)", ok)


# --------------------------------------------------------------- W2a-R.5 (shared with W2b.10)
def sinc_checks(target):
    ok = True
    mp.mp.dps = 50
    for L in range(2, 4001):
        t = mp.pi / L; cL = mp.sin(t) / t
        rem = cL - 1 + t * t / 6
        ok &= (0 <= rem <= t ** 4 / 120)
    check(target, "signed bound 0 <= c_L - 1 + t^2/6 <= t^4/120 for L = 2..4000", ok)
    r = rng(5); ok = True
    for _ in range(300):
        L = int(r.integers(2, 200)); mu = r.uniform(0, 3); t = math.pi / L
        E = lambda k: math.sqrt(mu * mu + 4 * math.sin(k / 2) ** 2)
        k1 = 2 * math.pi / L
        cL = math.sqrt((E(k1) ** 2 - E(0) ** 2) / k1 ** 2)
        ok &= close(cL, math.sin(t) / t, 1e-12)
    check(target, "free branch: c_L = sin(pi/L)/(pi/L) for every rest mass mu >= 0", ok)


def w2ar5():
    sinc_checks("W2a-R.5")
    free = read_csv("free_clock.csv")
    ok = all(close(float(rw[k]), math.sin(math.pi / float(rw["L"])) / (math.pi / float(rw["L"])), 1e-9)
             for rw in free for k in rw if k.lower() in ("c_l", "cl", "c_l_free", "free_clock"))
    check("W2a-R.5", "reference free-clock table agrees with sin t / t", ok)


# --------------------------------------------------------------- W2a-R.6 (shared with W2b.9)
def pole_checks(target):
    from common import ALIASES, PI, omega
    r = rng(6); sep_ok = True; pole_ok = True; speed_ok = True
    for _ in range(200):
        p = r.uniform(-1, 1, 3); p *= r.uniform(0.01, 1.4) / np.linalg.norm(p)
        p = np.clip(p, -PI / 2 + 1e-3, PI / 2 - 1e-3)
        w0 = omega(p)
        others = [omega(p + PI * np.array(a)) for a in ALIASES[1:]]
        sep_ok &= min(others) > w0
        speed_ok &= abs(w0 / np.linalg.norm(p) - 1) <= np.linalg.norm(p) ** 2 / 12 + 1e-15
    check(target, "every switched alias has strictly larger energy for |a p_j / 2| < pi/4", sep_ok)
    for z in (0.05, 0.2, 0.6):
        p = np.array([z, 0.0, 0.0]); i = 1
        ws, Es = [], []
        for a in ALIASES:
            q = p + PI * np.array(a); sh = 2 * np.sin(q / 2); w = math.sqrt(sh @ sh)
            ws.append(abs(1 + np.exp(1j * q[i])) ** 2 * (1 - sh[i] ** 2 / (w * w)) / (2 * w)); Es.append(w)
        ws, Es = np.array(ws), np.array(Es)
        C = lambda tau: float(np.sum(ws * np.exp(-Es * tau)))
        tau = 400.0
        eff = math.log(C(tau) / C(tau + 1.0))
        pole_ok &= abs(eff - omega(p)) < 1e-8 and ws[0] > 0
    check(target, "long-time effective energy recovers omega(p) with positive residue", pole_ok)
    check(target, "phase speed |omega/|p| - 1| <= |p|^2/12 (200 random momenta)", speed_ok)


def w2ar6():
    pole_checks("W2a-R.6")


# --------------------------------------------------------------- W2a-R.7 (and W2d.7 witness)
def upward_witness(target):
    r = rng(7); ok = True
    for _ in range(200):
        H0 = np.sort(r.uniform(0, 5, 6)); x = r.uniform(0, 0.5)
        Hx = (1 + x) * H0
        gaps0, gapsx = H0[1:] - H0[0], Hx[1:] - Hx[0]
        ok &= np.allclose(gapsx, (1 + x) * gaps0)
        c2_0 = gaps0[1] ** 2 - gaps0[0] ** 2; c2_x = gapsx[1] ** 2 - gapsx[0] ** 2
        ok &= close(c2_x / c2_0 - 1, 2 * x + x * x, 1e-9, 1e-12)
        ok &= np.all(Hx >= H0)                    # lower form bound still holds
    check(target, "H_x=(1+x)H_0: same vacuum, gaps scale by 1+x, squared speed changes by 2x+x^2", ok)


def w2ar7():
    upward_witness("W2a-R.7")


# --------------------------------------------------------------- W2a-R.8
def bessel_I():
    f = lambda s: i0e(s * s / 2) ** 3

    def num(s):
        if s < 1e-4:
            return 1.5 - (21 / 16) * s * s
        return -math.expm1(3 * math.log(i0e(s * s / 2))) / (s * s)
    I1 = quad(num, 0, np.inf, epsabs=2e-12, epsrel=2e-12, limit=400)[0] / math.sqrt(math.pi)
    I2 = 2 * quad(f, 0, np.inf, epsabs=2e-12, epsrel=2e-12, limit=400)[0] / math.sqrt(math.pi)
    return I1, I2


def duffy_I(order=40):
    raw, wts = np.polynomial.legendre.leggauss(order); u = (raw + 1) / 2; w = wts / 2
    U, V = np.meshgrid(u, u, indexing="ij"); W = np.outer(w, w)
    mom = np.zeros(4)
    for t, wt in zip(u, w):
        x, y, z = math.pi / 2 * t, math.pi / 2 * t * U, math.pi / 2 * t * V
        X, Y, Z = math.sin(x) ** 2, np.sin(y) ** 2, np.sin(z) ** 2
        b = np.sqrt(X + Y + Z)
        ks = (b, 1 / b, (X * Y + Y * Z + Z * X) / (3 * b ** 3),
              (math.sin(2 * x) ** 2 + np.sin(2 * y) ** 2 + np.sin(2 * z) ** 2) / (3 * b ** 3))
        mom += 3 * wt * t * t * np.array([np.sum(W * k) for k in ks])
    return mom


def w2ar8():
    I1, I2 = bessel_I()
    alpha, beta = -(5 * I1 + 4 * I2) / 72, I1 / 6
    for N in (2, 3):
        c1 = alpha * N + beta / N
        check("W2a-R.8", f"SU({N}): c1 = -(5I1+4I2)N/72 + I1/(6N) = {C1[N]}", abs(c1 - C1[N]) < 5e-12, f"{c1:.12f}")
    m = duffy_I()
    check("W2a-R.8", "independent Duffy cube quadrature reproduces I1, I2", abs(m[0] - I1) < 1e-9 and abs(m[1] - I2) < 1e-9)
    alpha_full = -4 * (m[0] / 24 - 7 * m[1] / 288 + m[2] / 48 + m[3] / 128)
    check("W2a-R.8", "four-moment kernel reduces to alpha = -(5I1+4I2)/72", abs(alpha_full - alpha) < 1e-9)
    import sympy as sp
    Nn, a1, a2 = sp.symbols("N I1 I2", positive=True)
    lhs = -(5 * a1 + 4 * a2) * Nn / 72 + a1 / (6 * Nn)
    rhs = (-(5 * a1 + 4 * a2) * Nn ** 2 + 12 * a1) / (72 * Nn)
    check("W2a-R.8", "colour factors over a common denominator (symbolic)", sp.simplify(lhs - rhs) == 0)
    for N, printed, disc in ((2, -0.16756, 5.0148e-5), (3, -0.33423, 6.2367e-5)):
        d = abs(C1[N] - printed)
        check("W2a-R.8", f"SU({N}) residual against printed Hamiltonian-limit pair = {disc:.4e}",
              abs(d - disc) < 1e-8 and d > 5e-6, f"{d:.6e}")


# --------------------------------------------------------------- W2a-R.9
def w2ar9():
    r = rng(9); ok = True
    for _ in range(200):
        kE, kB = r.uniform(-2, 2, 2); h = 1e-6
        f = lambda x: math.sqrt((1 + kE * x) / (1 + kB * x))
        der = (f(h) - f(-h)) / (2 * h)
        ok &= abs(der - (kE - kB) / 2) < 1e-8
    check("W2a-R.9", "d/dx sqrt((1+k_E x)/(1+k_B x)) at 0 equals (k_E - k_B)/2", ok)
    ok = True
    for _ in range(200):
        dc, sl = r.uniform(-1, 1, 2); h = 1e-6
        phys = lambda x: 1 + 0.0 * x + 0.7 * x * x       # value one, zero first derivative
        trunc = lambda x: 1 - dc * x
        prod = lambda x: trunc(x) * phys(x)
        ok &= abs((prod(h) - prod(-h)) / (2 * h) + dc) < 1e-8
    check("W2a-R.9", "normalized product has slope -Delta c_irr when the physical multiplier is 1 + O(x^2)", ok)


# --------------------------------------------------------------- W2a-R.10
def w2ar10():
    r = rng(10); ok = True; worst = 0
    for _ in range(3000):
        c1 = r.uniform(-1, 1); M = r.uniform(0, 2)
        x = r.uniform(0, XS)
        e = M * x * x * r.uniform(-1, 1)
        c = 1 + c1 * x + e
        d = 1 - abs(c1) * XS - M * XS * XS
        if d <= 0:
            continue
        bound = (c1 * c1 + (1 + abs(c1) * XS) * M) / d * x * x
        val = abs(1 / c - (1 - c1 * x))
        worst = max(worst, val / bound if bound > 0 else 0)
        ok &= val <= bound + 1e-15
    check("W2a-R.10", "inverse-clock remainder <= (c1^2+(1+|c1|x*)M)/d x^2 (3000 samples)", ok, f"max ratio {worst:.3f}")
    c1 = 0.4; x = 0.1; e = 0.01
    lhs = 1 - (1 + c1 * x + e) * (1 - c1 * x)
    check("W2a-R.10", "identity 1 - c(1 - c1 x) = c1^2 x^2 - e(1 - c1 x)", close(lhs, c1 * c1 * x * x - e * (1 - c1 * x), 1e-12))


if __name__ == "__main__":
    print("W2a-R  The physical clock and Wilson calibration")
    for fn in (w2ar1, w2ar2, w2ar3, w2ar4, w2ar5, w2ar6, w2ar7, w2ar8, w2ar9, w2ar10):
        fn()
    finish("W2a-R")
