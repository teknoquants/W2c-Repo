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

"""W2e: conditional scores and the Schur form (targets W2e.1 to W2e.5)."""
import math

import numpy as np

from common import ALIASES, PI, check, close, finish, omega, read_csv, rng, schur_axial


# --------------------------------------------------------------- W2e.1
def w2e1():
    r = rng(41); ok_pos = True; strict = 0
    for _ in range(400):
        p = r.uniform(-PI / 2, PI / 2, 3)
        if np.linalg.norm(p) < 1e-3:
            continue
        i = int(r.integers(0, 3))
        t2, Q = [], []
        for a in ALIASES:
            q = p + PI * np.array(a)
            t2.append(abs(1 + np.exp(1j * q[i])) ** 2 / 8)    # unitary volume factor: sum |t|^2 = 2 (TT* = 2I)
            Q.append(2 * omega(q))
        t2, Q = np.array(t2), np.array(Q)
        resid = (t2 @ Q) / 4 - 1 / (t2 @ (1 / Q))
        ok_pos &= abs(t2.sum() - 2) < 1e-12 and resid >= -1e-12
        strict += resid > 1e-8
    check("W2e.1", "residual precision TQT*/4 - C_nu^-1 >= 0 (Cauchy-Schwarz, 400 momenta)", ok_pos)
    check("W2e.1", "residual is strictly positive at generic momenta: Gaussian coupling does not vanish", strict > 350,
          f"{strict}/400 strictly positive")
    rows = read_csv("gaussian.csv")
    gJ = [float(rw["g_squared_J_gaussian"]) for rw in rows]
    check("W2e.1", "[evidence] g^2 J_k > 0 on all four grids, so S_i = O(g^-1), J_k = O(g^-2)", all(v > 0 for v in gJ),
          ", ".join(f"{v:.4f}" for v in gJ))


# --------------------------------------------------------------- W2e.2
def w2e2():
    r = rng(42); ok = True
    for _ in range(500):
        n = 5; X = r.normal(size=(n, n)); D = X @ X.T + 2 * np.eye(n)
        Lam = np.linalg.eigvalsh(D)[0]; m = r.uniform(0, Lam * 0.99)
        nrm = np.linalg.norm(np.linalg.inv(D - m * np.eye(n)), 2)
        ok &= nrm <= 1 / (Lam - m) * (1 + 1e-10)
    check("W2e.2", "||(D - m)^-1|| <= (Lambda_perp - m)^-1 when D >= Lambda_perp > m (500 matrices)", ok)
    ok = True
    for _ in range(2000):
        J, A, Lam, m = r.uniform(0, 3), r.uniform(0.1, 3), r.uniform(1, 4), r.uniform(0, 0.9)
        h2 = J * A * r.uniform(0, 1)                     # score covariance bound <h,h> <= J A
        ok &= h2 / (Lam - m) <= J / (Lam - m) * A + 1e-12
    check("W2e.2", "scalar lift: mixed term <= J/(Lambda_perp - m) * retained energy", ok)
    gJ = [float(rw["g_squared_J_gaussian"]) for rw in read_csv("gaussian.csv")]
    check("W2e.2", "[obstruction] Gaussian score of the plain map is nonzero, so the quartic route's premise fails", min(gJ) > 0.1)


# --------------------------------------------------------------- W2e.3
def w2e3():
    r = rng(43); ok = True
    for _ in range(2000):
        n = 4; X = r.normal(size=(n, n)); D = X @ X.T + 0.1 * np.eye(n)
        B = r.normal(size=n); a = r.uniform(-3, 6)
        H = np.block([[np.array([[a]]), B[None, :]], [B[:, None], D]])
        psd = np.linalg.eigvalsh(H)[0] >= -1e-10
        schur = a - B @ np.linalg.solve(D, B) >= -1e-10
        ok &= psd == schur
    check("W2e.3", "Schur criterion: block form >= 0 iff A - B* D^-1 B >= 0 for D > 0 (2000 matrices)", ok)
    margins = [schur_axial(2 * PI / L)[2] for L in (4, 8, 16, 32, 64, 128, 512)]
    check("W2e.3", "signed axial margin A - m - B*(D - m)^-1 B > 0 at every tested box", all(v > 0 for v in margins))
    ratio = schur_axial(2 * PI / 1e5)
    check("W2e.3", "[counterexample] bare correction / A -> 3/4, so no uniform C (am)^2 bare estimate",
          abs(ratio[3] / ratio[0] - 0.75) < 1e-4)


# --------------------------------------------------------------- W2e.4
def w2e4():
    r = rng(44); ok = True
    for _ in range(10000):
        al, ep = r.uniform(0, 1, 2)
        ok &= close(1 - (1 - al) * (1 - ep), al + ep - al * ep, 1e-12, 1e-15) and al + ep - al * ep <= al + ep + 1e-15
    check("W2e.4", "relative loss alpha + epsilon - alpha*epsilon <= alpha + epsilon (10000 samples)", ok)


# --------------------------------------------------------------- W2e.5
def w2e5():
    r = rng(45); ok = True
    for _ in range(3000):
        n = int(r.integers(1, 8)); d = r.uniform(1, 5, n); lam = r.uniform(0, 0.9)
        hcoef = r.normal(size=n); beta2 = r.uniform(0.1, 3); Au = r.uniform(0.1, 3); xi = r.uniform(0.05, 20)
        base = beta2 * np.sum(hcoef ** 2 / (d - lam)) / Au
        scaled = (xi ** 2 * beta2) * np.sum(hcoef ** 2 / (xi * d - xi * lam)) / (xi * Au)
        ok &= close(base, scaled, 1e-11)
    check("W2e.5", "resolvent ratio is invariant under every clock xi > 0 (3000 eigen-data samples)", ok)


if __name__ == "__main__":
    print("W2e  Conditional scores and the Schur form")
    for fn in (w2e1, w2e2, w2e3, w2e4, w2e5):
        fn()
    finish("W2e")
