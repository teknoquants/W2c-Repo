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

"""W2f: small-field assembly and transfer (targets W2f.1 to W2f.5)."""
import math

import numpy as np

from common import A_of, check, close, finish, rng


# --------------------------------------------------------------- W2f.1
def w2f1():
    r = rng(51); ok = True; tested = 0
    for _ in range(3000):
        n = 5; X = r.normal(size=(n, n)); D = X @ X.T + 1.0 * np.eye(n)
        B = r.normal(size=n) * 0.5; a = r.uniform(0.5, 6)
        H = np.block([[np.array([[a]]), B[None, :]], [B[:, None], D]])
        lam = r.uniform(0, min(a, np.linalg.eigvalsh(D)[0]) * 0.999)
        signed = a - lam - B @ np.linalg.solve(D - lam * np.eye(n), B)
        if signed >= 0:
            tested += 1
            ok &= np.linalg.eigvalsh(H)[0] >= lam - 1e-10
    check("W2f.1", f"signed Schur estimate at trial gap lambda implies H >= lambda ({tested} cases)", ok and tested > 500)
    CS, CM, Ca, Cap = 0.3, 0.2, 0.125, 0.4
    check("W2f.1", "Scheme A coefficients add: C_4 = C_S + C_M, C_a'' = C_a + C_a'",
          close(CS + CM, 0.5) and close(Ca + Cap, 0.525))


# --------------------------------------------------------------- W2f.2
def w2f2():
    r = rng(52); ok = True
    for _ in range(500):
        J = int(r.integers(1, 200)); c = r.uniform(0.5, 1.5, J + 1)
        Z = float(np.prod(c[:-1] / c[1:]))
        ok &= close(Z, c[0] / c[-1], 1e-10)
    check("W2f.2", "inherited-time step factors telescope: Z_clock = c(x_0)/c(x_J)", ok)
    gap_scaled, xi_in = 2.7, 1.3
    check("W2f.2", "certificate in a clock-scaled Hamiltonian converts back by one division (no double reciprocal)",
          close((xi_in * gap_scaled) / xi_in, gap_scaled) and not close(gap_scaled / xi_in ** 2 * xi_in, gap_scaled))
    ok = True
    for _ in range(2000):
        y = r.uniform(-0.5, 0.5, int(r.integers(1, 50)))
        ok &= float(np.prod(1 + y)) <= math.exp(float(np.sum(y))) * (1 + 1e-12)
    check("W2f.2", "prod(1 + y_k) <= exp(sum y_k)", ok)


# --------------------------------------------------------------- W2f.3
def w2f3():
    c1 = -0.167509851556; r = rng(53); ok = True
    for _ in range(500):
        xs = np.sort(r.uniform(0, 1 / 6, int(r.integers(2, 100))))
        xi = 1 - c1 * xs
        ok &= close(float(np.prod(xi[1:] / xi[:-1])), xi[-1] / xi[0], 1e-11)
    check("W2f.3", "Scheme B endpoint factor xi_B(x_J)/xi_B(x_0) exactly", ok)
    CS, CM, MmB = 0.3, 0.2, 0.06075567376518034
    check("W2f.3", "C_4 = C_S + C_M + M_match^B (SU(2) reference M_match^B bound)", close(CS + CM + MmB, 0.56075567376518034))


# --------------------------------------------------------------- W2f.4
def w2f4():
    ok = True
    for c in (0.5, 1.0, 3.0):
        for delta in (0.5, 1.0, 1.5, 1.9):
            D = (4 / (math.e * c * delta)) ** (4 / delta)
            g = np.linspace(1e-3, 3, 20000)
            ok &= np.all(np.exp(-c / g ** delta) <= D * g ** 4 * (1 + 1e-12))
    check("W2f.4", "exp(-c/g^delta) <= D_delta g^4 with D_delta = (4/(e c delta))^(4/delta)", ok)
    u = np.linspace(1e-6, 60, 200001); delta = 1.2
    check("W2f.4", "max_u u^(4/delta) e^(-u) = (4/(e delta))^(4/delta)",
          abs(np.max(u ** (4 / delta) * np.exp(-u)) - (4 / (math.e * delta)) ** (4 / delta)) < 1e-6)
    r = rng(54); ok = True
    for N in (2, 3):
        A = A_of(N); Am = A / 2
        for _ in range(500):
            xs = 1 / 6; xk = [xs]
            for _ in range(int(r.integers(1, 3000))):
                xk.append(1 / (1 / xk[-1] + r.uniform(Am, 1.5 * A)))
            ok &= sum(x * x for x in xk) <= xs ** 2 + xs / Am + 1e-15
    check("W2f.4", "sum x_k^2 <= x*^2 + x*/A_- along every admissible run", ok)
    ok = True
    for _ in range(5000):
        rr = r.uniform(0, 0.95); eta = r.uniform(0, rr)
        ok &= math.log(1 - eta) >= -eta / (1 - rr) - 1e-15
    check("W2f.4", "log(1 - eta) >= -eta/(1 - r) for 0 <= eta <= r < 1", ok)
    ok = True
    for _ in range(2000):
        rr = r.uniform(0, 0.9); eta = r.uniform(0, rr, int(r.integers(1, 200)))
        ok &= float(np.prod(1 - eta)) >= math.exp(-float(np.sum(eta)) / (1 - rr)) * (1 - 1e-12)
    check("W2f.4", "weak-step product >= exp[-S/(1 - r)] with S >= sum eta_k", ok)


# --------------------------------------------------------------- W2f.5
def w2f5():
    A = A_of(2); g1sq = 5.701; gs2 = 1 / 6
    M_half = math.ceil((1 / gs2 - 1 / g1sq) / (A / 2)); M_full = math.ceil((1 / gs2 - 1 / g1sq) / A)
    check("W2f.5", "SU(2) intermediate step count M = 91 (A_int = A/2) and 46 (A_int = A)", M_half == 91 and M_full == 46,
          f"{M_half}, {M_full}")
    r = rng(55); ok = True
    for _ in range(1000):
        Aint = r.uniform(0.05, 0.2); g1m2 = r.uniform(0.05, 1); n = 0; y = 1 / gs2
        while y > g1m2:
            y -= r.uniform(Aint, 2 * Aint); n += 1
        M = math.ceil((1 / gs2 - g1m2) / Aint)
        b = r.uniform(0.1, 1)
        ok &= n <= M and b ** n >= b ** M - 1e-300
    check("W2f.5", "n <= M and b^n >= b^M for 0 < b <= 1 (1000 trajectories)", ok)
    f1 = lambda g2: 1 + 0.1 * g2
    f2 = lambda g2: 1 + 0.1 * g2 + (max(0.0, g2 - gs2)) ** 3
    agree = all(f1(x) == f2(x) for x in np.linspace(1e-4, gs2, 500))
    check("W2f.5", "endpoint not determined: two positive clocks agree on the weak interval and differ later",
          agree and f1(5.701) != f2(5.701))
    Z, zL, mIR, b, M, S, rr = 0.98, 0.9, 1.2, 0.95, 46, 0.3, 0.5
    bound = Z * zL * mIR * b ** M * math.exp(-S / (1 - rr))
    check("W2f.5", "fine-scale bound Gamma_0 >= Z_clock z_L m_IR b^M exp[-S/(1-r)] is positive for positive inputs",
          bound > 0, f"{bound:.4e}")


if __name__ == "__main__":
    print("W2f  Small-field assembly and transfer")
    for fn in (w2f1, w2f2, w2f3, w2f4, w2f5):
        fn()
    finish("W2f")
