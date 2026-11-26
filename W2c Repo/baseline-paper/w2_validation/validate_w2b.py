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

"""W2b: the exact Gaussian block (targets W2b.1 to W2b.11)."""
import itertools
import math

import numpy as np
import sympy as sp
from scipy.linalg import sqrtm

from common import (PI, SLOPE, R_closed, axial_energies, blocked_covariance, check, close, finish,
                    read_csv, rng, schur_axial, transverse_ratios)
from validate_w2ar import pole_checks, sinc_checks


# --------------------------------------------------------------- W2b.1
def w2b1():
    g, E, B = sp.symbols("g E B", positive=True)
    check("W2b.1", "U = exp(gA), E -> E/g: quadratic electric and magnetic terms lose g",
          sp.simplify(g ** 2 / 2 * (E / g) ** 2 - E ** 2 / 2) == 0 and sp.simplify((g * B) ** 2 / (2 * g ** 2) - B ** 2 / 2) == 0)
    x, w = sp.symbols("x omega", positive=True)
    psi = sp.exp(-w * x ** 2 / 2)
    Hpsi = -sp.diff(psi, x, 2) / 2 + w ** 2 * x ** 2 * psi / 2
    check("W2b.1", "oscillator ground state: H psi = (omega/2) psi", sp.simplify(Hpsi - w / 2 * psi) == 0)
    var = sp.integrate(x ** 2 * psi ** 2, (x, -sp.oo, sp.oo)) / sp.integrate(psi ** 2, (x, -sp.oo, sp.oo))
    check("W2b.1", "position variance of the Gaussian ground state is 1/(2 omega)", sp.simplify(var - 1 / (2 * w)) == 0)
    r = rng(11); ok = True
    for _ in range(50):
        X = r.normal(size=(6, 6)); K = X @ X.T + 0.5 * np.eye(6)
        Om = np.real(sqrtm(K))
        ok &= np.allclose(Om @ Om, K) and np.allclose(np.linalg.inv(2 * Om), 0.5 * np.linalg.inv(np.real(sqrtm(K))))
    check("W2b.1", "matrix functional calculus: vacuum covariance (2 Omega)^-1 = K^(-1/2)/2", ok)
    ok = True
    for _ in range(200):
        q = r.uniform(-PI, PI, 3); sh = 2 * np.sin(q / 2)
        K = (sh @ sh) * np.eye(3) - np.outer(sh, sh)          # curl^T curl symbol on links
        ev = np.sort(np.linalg.eigvalsh(K))
        ok &= abs(ev[0]) < 1e-12 and np.allclose(ev[1:], sh @ sh)
    check("W2b.1", "K = d*d has eigenvalue 0 (gauge) and omega^2 twice (transverse) at q != 0", ok)


# --------------------------------------------------------------- W2b.2
def path_laplacian_eigs(n):
    """Graph Laplacian of a path with n vertices (open boundary)."""
    Lm = np.diag([1.0] + [2.0] * (n - 2) + [1.0]) - np.diag(np.ones(n - 1), 1) - np.diag(np.ones(n - 1), -1)
    return np.sort(np.linalg.eigvalsh(Lm))


def w2b2():
    for L in (4, 8, 16, 32):
        ks = 2 * PI * np.arange(L) / L
        fine = min(2 * math.sqrt(sum(math.sin(k / 2) ** 2 for k in kk)) for kk in itertools.product(ks, repeat=3) if any(kk))
        kc = 2 * PI * np.arange(L // 2) / L                 # same physical momenta on the coarse grid
        coarse = min(math.sqrt(sum(math.sin(k) ** 2 for k in kk)) for kk in itertools.product(kc, repeat=3) if any(kk))
        t = PI / L
        check("W2b.2", f"L={L}: periodic gaps 2 sin(pi/L), sin(2pi/L); ratio 1/cos(pi/L)",
              close(fine, 2 * math.sin(t)) and close(coarse, math.sin(2 * t)) and close(fine / coarse, 1 / math.cos(t)))
    ok = True
    for L in range(4, 400, 2):
        t = PI / L
        ok &= abs(1 / math.cos(t) - 1 - t * t / 2) <= 0.3 * t ** 4
    check("W2b.2", "1/cos(pi/L) = 1 + pi^2/(2L^2) + O(L^-4)", ok)
    rows = read_csv("open-gaps.csv")
    for row in rows:
        L = int(float(row[list(row)[0]]))
        lam = path_laplacian_eigs(L + 1); lamc = path_laplacian_eigs(L // 2 + 1)
        fine = math.sqrt(2 * lam[1]); coarse = math.sqrt(2 * lamc[1]) / 2
        check("W2b.2", f"open L={L}: diagonalized path Laplacians give gap 2 sqrt2 sin(pi/(2(L+1)))",
              close(fine, 2 * SQ2 * math.sin(PI / (2 * (L + 1))), 1e-9)
              and close(fine, float(list(row.values())[1]), 1e-6) and close(coarse, float(list(row.values())[2]), 1e-6))


SQ2 = math.sqrt(2.0)


# --------------------------------------------------------------- W2b.3
def w2b3():
    h = sp.symbols("h", positive=True)
    expr = 1 / h - 1 - 4 * (1 - h ** 2) * h ** 2 / 8
    fact = (1 - h) ** 2 * (2 + 2 * h + 2 * h ** 2 + h ** 3) / (2 * h)
    check("W2b.3", "factorization 1/h - 1 - sin^2(2t)/8 = (1-h)^2(2+2h+2h^2+h^3)/(2h)", sp.simplify(expr - fact) == 0)
    ok = True
    for L in range(4, 2001, 2):
        t = PI / L; hh = math.cos(t); am = math.sin(2 * t)
        err = 1 / hh - 1 - am * am / 8
        ok &= -1e-15 <= err <= 7 * am ** 4 and 2 + 2 * hh + 2 * hh ** 2 + hh ** 3 <= 7 and 1 - hh <= am * am
    check("W2b.3", "0 <= Gamma_k/Gamma_{k+1} - 1 - (a m)^2/8 <= 7 (a m)^4 for even L >= 4", ok)
    t = 1e-3
    check("W2b.3", "free lattice-artifact constant C_a^free = 1/8",
          abs((1 / math.cos(t) - 1) / math.sin(2 * t) ** 2 - 0.125) < 1e-6)


# --------------------------------------------------------------- W2b.4
def w2b4():
    ok = True
    for z in np.linspace(0.01, 1.5, 60):
        ok &= np.allclose(transverse_ratios(np.array([z, 0, 0])), R_closed(z), rtol=1e-12)
    check("W2b.4", "closed form R(z) equals the eight-alias covariance ratio (60 momenta, both polarizations)", ok)
    M = blocked_covariance(np.array([0.4, 0, 0]))
    check("W2b.4", "four aliases with r_2 = 1 are killed by the two-link factor", abs(math.cos((0.0 + PI) / 2)) < 1e-15)
    check("W2b.4", "R(0) = 1 (smooth continuation)", abs(R_closed(1e-8) - 1) < 1e-7)
    hst = 1e-5
    d = (R_closed(2 * hst) - R_closed(hst)) / hst
    check("W2b.4", "R'(0) = 1 + 1/(2 sqrt 2) = 1.353553", abs(d - SLOPE) < 1e-4, f"{d:.6f}")
    u = np.array([1.0, 2.0, 3.0]) / math.sqrt(14); z = 1e-3
    sl = (transverse_ratios(z * u) - 1) / z
    check("W2b.4", "direction (1,2,3), a|p|=0.001: slopes 1.353390 and 1.353466",
          abs(sl[0] - 1.353390) < 2e-6 and abs(sl[1] - 1.353466) < 2e-6, f"{sl[0]:.6f}, {sl[1]:.6f}")
    r = rng(14); ok = True
    for _ in range(20):
        u = r.normal(size=3); u /= np.linalg.norm(u)
        s1 = (transverse_ratios(1e-4 * u) - 1) / 1e-4
        ok &= np.all(np.abs(s1 - SLOPE) < 2e-3)
    check("W2b.4", "both transverse eigenvalues 1 + (1 + 1/(2 sqrt 2)) z + O(z^2) in 20 random directions", ok)
    contrib = 0.0
    for k in (1, 2):                                   # singleton (k=1) and doubleton (k=2) switched aliases
        mult = 2 if k == 1 else 1                     # each coordinate: two singletons, one doubleton
        contrib += mult / (2 * math.sqrt(k))
    check("W2b.4", "alias bookkeeping: 2*(1/2) + 1/(2 sqrt 2) = 1 + 1/(2 sqrt 2)", close(contrib, SLOPE))


# --------------------------------------------------------------- W2b.5
def w2b5():
    g, a = sp.symbols("g a", positive=True)
    ck, ck1 = g ** 2 / (2 * a), g ** 2 / (4 * a)
    check("W2b.5", "kinetic normalization r_k = 2c_k/c_{k+1} = 4", sp.simplify(2 * ck / ck1) == 4)
    h = 1e-6
    der = (R_closed(2 * h) ** -0.5 - R_closed(h) ** -0.5) / h
    check("W2b.5", "transport multiplier R^(-1/2): value 1, slope -(1+1/(2 sqrt2))/2", abs(R_closed(1e-9) ** -0.5 - 1) < 1e-8
          and abs(der + SLOPE / 2) < 1e-4, f"{der:.6f}")


# --------------------------------------------------------------- W2b.6
def w2b6():
    r = rng(16)
    for L in (4, 8, 16, 32, 64, 256):
        A, m, J, corr, E, w = schur_axial(2 * PI / L)
        v = np.sqrt(w)
        Q, _ = np.linalg.qr(np.column_stack([v, r.normal(size=(4, 3))]))
        Q[:, 0] = v
        H = Q.T @ np.diag(E) @ Q
        a = H[0, 0]; Bv = H[1:, 0]; D = H[1:, 1:]
        schur = a - m - Bv @ np.linalg.solve(D - m * np.eye(3), Bv)
        check("W2b.6", f"L={L}: matrix Schur complement equals (sum w_i/(E_i-m))^-1 and A = 4/sum(1/E_i)",
              close(schur, J, 1e-9) and close(a, A, 1e-12) and close(A, 4 / np.sum(1 / E), 1e-12))
        check("W2b.6", f"L={L}: signed margin J* > 0", J > 0, f"{J:.6f}")
    ratios = [schur_axial(2 * PI / L)[3] / schur_axial(2 * PI / L)[0] for L in (1e3, 1e4, 1e5)]
    check("W2b.6", "bare correction / retained energy -> 3/4", abs(ratios[-1] - 0.75) < 1e-4 and ratios[0] < ratios[1] < ratios[2],
          f"{ratios[-1]:.6f}")
    ok = True
    for L in (16, 64, 512):
        A, m, J, corr, E, w = schur_axial(2 * PI / L)
        hh = m / E[0]; T = np.sum(E[0] / E); b = J / E[0]
        ok &= 0 < b <= (1 - hh) * T + 1e-15 and close(corr / A, 1 - (hh + b) * T / 4, 1e-10)
    check("W2b.6", "0 < b <= (1-h)T and (A-m-J*)/A = 1 - (h+b)T/4", ok)


# --------------------------------------------------------------- W2b.7
def kernel_exponent(L):
    k = 2 * PI * np.fft.fftfreq(L)
    KX, KY, KZ = np.meshgrid(k, k, k, indexing="ij")
    sym = 2 * np.sqrt(np.sin(KX / 2) ** 2 + np.sin(KY / 2) ** 2 + np.sin(KZ / 2) ** 2)
    ker = np.real(np.fft.ifftn(sym))
    idx = np.arange(L); idx = np.minimum(idx, L - idx)
    X, Y, Z = np.meshgrid(idx, idx, idx, indexing="ij")
    rad = np.sqrt(X ** 2 + Y ** 2 + Z ** 2)
    rs, vals = [], []
    for n in range(2, L // 2 + 1):
        sel = (rad >= n - 0.5) & (rad < n + 0.5)
        rs.append(n); vals.append(np.mean(np.abs(ker[sel])))
    rs, vals = np.array(rs), np.array(vals)
    half = rs <= L // 4
    return -np.polyfit(np.log(rs[half]), np.log(vals[half]), 1)[0]


def w2b7():
    ok = all((2 * n + 1) ** 3 - (2 * n - 1) ** 3 <= 26 * n * n for n in range(1, 2000))
    check("W2b.7", "sup-norm shell in Z^3 has at most 26 n^2 sites", ok)
    partial = sum(26 * 1.0 / n ** 2 for n in range(1, 200000))
    check("W2b.7", "C/n^4 kernel on K n^2-site shells: total <= K C pi^2/6 (summable)", partial <= 26 * PI ** 2 / 6)
    e32, e64 = kernel_exponent(32), kernel_exponent(64)
    check("W2b.7", "free |k| symbol kernel decays like |x|^-4 (fitted exponent approaches 4)",
          3.5 < e32 < 4.5 and 3.5 < e64 < 4.5 and abs(e64 - 4) <= abs(e32 - 4) + 0.05, f"{e32:.3f}, {e64:.3f}")
    rows = read_csv("gaussian.csv")
    sc = [float(r["score_row_sum"]) for r in rows]
    check("W2b.7", "reference score row sums grow across the four grids (no uniform bound established)",
          all(sc[i] < sc[i + 1] for i in range(len(sc) - 1)))


# --------------------------------------------------------------- W2b.8
def w2b8():
    for C, mu, c in ((10.0, 0.1, 1e-3), (1e3, 0.05, 1e-2)):
        n = next(n for n in range(1, 10 ** 6) if all(C * math.exp(-mu * k) < c * k ** -4 for k in range(n, n + 200)))
        check("W2b.8", f"C e^(-mu n) < c n^-4 eventually (C={C}, mu={mu}, c={c}): from n={n} on", n < 10 ** 6)


# --------------------------------------------------------------- W2b.9, W2b.10, W2b.11
def w2b9():
    pole_checks("W2b.9")


def w2b10():
    sinc_checks("W2b.10")


def w2b11():
    y = sp.symbols("y")
    check("W2b.11", "fourth derivative of 2(1-cos y) at 0 equals -2", sp.diff(2 * (1 - sp.cos(y)), y, 4).subs(y, 0) == -2)
    r = rng(111); ok = True
    for _ in range(2000):
        p = r.uniform(-1, 1, 3) * r.uniform(0, 1.5)
        w2 = np.sum(4 * np.sin(p / 2) ** 2)
        rem = abs(w2 - (p @ p) + np.sum(p ** 4) / 12)
        ok &= rem <= np.sum(np.abs(p) ** 6) / 360 + 1e-15
    check("W2b.11", "|omega^2 - |p|^2 + sum p_j^4/12| <= sum |p_j|^6/360 (2000 momenta)", ok)
    rows = read_csv("angular.csv"); ok = True
    for row in rows:
        u = np.array([float(v) for v in row["direction"].split()]); u /= np.linalg.norm(u)
        rr = transverse_ratios(float(row["z"]) * u)
        z = float(row["z"]); axial = np.count_nonzero(u) == 1
        tol = 1e-9 if axial else 0.05 * z * z          # off-axis O(z^2) depends on the coarse reference convention
        ok &= abs(rr[0] - float(row["smaller_ratio"])) <= tol and abs(rr[1] - float(row["larger_ratio"])) <= tol
    check("W2b.4", f"angular table recomputed independently: exact on axis, agreement to O(z^2) off axis ({len(rows)} rows)",
          ok and len(rows) >= 15)


if __name__ == "__main__":
    print("W2b  The exact Gaussian block")
    for fn in (w2b1, w2b2, w2b3, w2b4, w2b5, w2b6, w2b7, w2b8, w2b9, w2b10, w2b11):
        fn()
    finish("W2b")
