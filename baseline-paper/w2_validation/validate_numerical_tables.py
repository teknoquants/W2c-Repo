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

"""Numerical inputs: recompute every reference table quoted in the paper (Section 9)."""
import itertools
import math

import numpy as np
from scipy.linalg import null_space

from common import PI, R_closed, axial_energies, check, close, finish, omega, read_csv, schur_axial


def transverse(q):
    grad = np.expm1(1j * q)
    nrm = np.linalg.norm(grad)
    if nrm < 1e-12:
        return 0.0, np.zeros((3, 0), complex)
    return nrm, null_space(grad.conj()[None, :])


def fourier_block(p, Q):
    """Horizontal lift T (coarse transverse <- fine transverse aliases) and fine energies."""
    blocks, energy = [], []
    for alias in itertools.product((0, 1), repeat=3):
        q = p + PI * np.asarray(alias)
        w, U = transverse(q)
        if U.shape[1]:
            blocks.append(Q.conj().T @ ((1 + np.exp(1j * q))[:, None] * U) / math.sqrt(8))
            energy.extend([w] * U.shape[1])
    return np.concatenate(blocks, axis=1), np.asarray(energy)


def analyze_momentum(Pc):
    _, Q = transverse(Pc)
    T, E = fourier_block(Pc / 2, Q)
    if not Q.shape[1]:
        return None, E
    G = T / np.sqrt(2 * E)
    cov = G @ G.conj().T
    ev, V = np.linalg.eigh(cov)
    retained = G.conj().T @ ((V / np.sqrt(ev)) @ V.conj().T)
    elim = null_space(retained.conj().T)
    A = retained.conj().T @ (E[:, None] * retained)
    D = elim.conj().T @ (E[:, None] * elim)
    B = elim.conj().T @ (E[:, None] * retained)
    d, U = np.linalg.eigh(D); ae, AU = np.linalg.eigh(A)
    mixed = np.linalg.svd((U.conj().T @ B @ AU) / (np.sqrt(d)[:, None] * np.sqrt(ae)), compute_uv=False)[0]
    score = (T * (2 * E)) @ T.conj().T / 4 - np.linalg.inv(cov)
    ref = 1 / (2 * np.linalg.norm(np.expm1(1j * Pc)))
    return dict(T=T, ratio_min=ev[0] / ref, ratio_max=ev[-1] / ref, variance_min=ev[0], variance_max=ev[-1],
                retained_min=ae[0], eliminated_min=d[0], mixed_norm=mixed,
                score_max=np.linalg.eigvalsh(score)[-1], score_min=np.linalg.eigvalsh(score)[0]), E


def tables_axial():
    rows = read_csv("axial.csv")
    for row in rows:
        L = int(row["L"]); z = 2 * PI / L; t = PI / L
        A, m, J, corr, E, w = schur_axial(z)
        vals = dict(z=z, cov_ratio=R_closed(z), static_slope=(R_closed(z) - 1) / z, clock=math.sin(t) / t,
                    signed_sinc_remainder=math.sin(t) / t - 1 + t * t / 6, sinc_upper=t ** 4 / 120,
                    gamma_fine=2 * math.sin(t), gamma_coarse=math.sin(2 * t), gap_ratio=1 / math.cos(t),
                    A_retained=A, raw_schur=corr, schur_over_A=corr / A, schur_margin=J,
                    retained_defect_over_m=A / (4 * m) - 1, weights_sum=float(w.sum()))
        ok = all(close(v, float(row[k]), 1e-9, 1e-12) for k, v in vals.items())
        check("Tables", f"axial table L={L}: 15 columns recomputed (gap, clock, R, A, correction, margin, defect)", ok)


def tables_open():
    from validate_w2b import path_laplacian_eigs
    for row in read_csv("open-gaps.csv"):
        L = int(row["L"])
        f = math.sqrt(2 * path_laplacian_eigs(L + 1)[1]); c = math.sqrt(2 * path_laplacian_eigs(L // 2 + 1)[1]) / 2
        check("Tables", f"open-box table L={L}: fine, coarse gaps and ratio",
              close(f, float(row["open_fine_gap"]), 1e-10) and close(c, float(row["open_coarse_gap"]), 1e-10)
              and close(f / c, float(row["open_ratio"]), 1e-10))


def tables_poles():
    ok = True; n = 0
    for row in read_csv("poles.csv"):
        L = int(row["L"]); d = np.array([int(ch) for ch in row["direction"]], float)
        p = 2 * PI / L * d / 2 if False else 2 * PI / L * d          # physical momentum, a = 1
        i = int(row["component"]) - 1
        q = p + PI * np.array([int(ch) for ch in row["alias"]])
        sh = 2 * np.sin(q / 2); w = math.sqrt(sh @ sh)
        res = abs(1 + np.exp(1j * q[i])) ** 2 * (1 - sh[i] ** 2 / (w * w)) / (2 * w) / 8
        ok &= close(w, float(row["energy"]), 1e-10) and abs(res - float(row["residue"])) < 1e-10
        ok &= close(w / np.linalg.norm(p), float(row["phase_speed"]), 1e-10); n += 1
    check("Tables", f"pole table: {n} alias energies, residues and phase speeds (axial and diagonal, four sizes)", ok)


def tables_all_momenta():
    rows = read_csv("all-momenta.csv")
    worst = 0.0; fields = ("ratio_min", "ratio_max", "variance_min", "variance_max", "retained_min",
                           "eliminated_min", "mixed_norm", "score_max")
    agg = {}; lift_ok = True; score_ok = True
    for row in rows:
        L = int(row["L"]); n = L // 2
        mom = 2 * PI * np.fft.fftfreq(n)
        Pc = np.array([mom[int(row["kx"])], mom[int(row["ky"])], mom[int(row["kz"])]])
        res, E = analyze_momentum(Pc)
        lift_ok &= np.allclose(res["T"] @ res["T"].conj().T, 2 * np.eye(2), atol=2e-12)
        score_ok &= res["score_min"] > -1e-10
        for k in fields:
            worst = max(worst, abs(res[k] - float(row[k])) / max(1.0, abs(float(row[k]))))
        a = agg.setdefault(L, dict(lam=math.inf, mixed=0.0, score=0.0))
        a["lam"] = min(a["lam"], res["eliminated_min"]); a["mixed"] = max(a["mixed"], res["mixed_norm"])
        a["score"] = max(a["score"], res["score_max"])
    check("Tables", f"all {len(rows)} nonzero coarse momenta: covariance ratios, energies, mixed norms, scores",
          worst < 1e-9, f"max rel diff {worst:.1e}")
    check("Tables", "horizontal lift normalization T T* = 2I at every momentum", lift_ok)
    check("Tables", "Gaussian conditional score covariance is positive semidefinite at every momentum", score_ok)
    for row in read_csv("gaussian.csv"):
        L = int(row["L"]); a = agg[L]
        _, E0 = analyze_momentum(np.zeros(3))
        lam = min(a["lam"], float(np.min(E0)))
        m = math.sin(2 * PI / L)
        ok = (close(lam, float(row["lambda_eliminated_first_chaos"]), 1e-9) and close(a["mixed"], float(row["mixed_energy_norm"]), 1e-9)
              and close(a["score"], float(row["g_squared_J_gaussian"]), 1e-9)
              and close(a["score"] / (lam - m), float(row["zeta_first_chaos"]), 1e-9) and float(row["alpha_first_chaos"]) == 0.0)
        check("Tables", f"first-chaos table L={L}: alpha, a*Lambda_perp, mixed norm, g^2 J, zeta", ok)


def tables_clock():
    coeff = read_csv("coefficients.csv")
    check("Tables", "Wilson coefficients c1(SU(2)), c1(SU(3)) in the reference table",
          abs(float(coeff[0]["c1"]) + 0.167509851556) < 1e-11 and abs(float(coeff[1]["c1"]) + 0.334167632989) < 1e-11)
    ok = True
    for row in read_csv("clock_products.csv"):
        c1 = float(row["trial_c1"])
        ok &= close(float(row["product"]), float(row["endpoint"]), 1e-12)
        ok &= close(float(row["uv_limit"]), 1 / (1 + c1 / 6), 1e-12)
        ok &= close(abs(float(row["endpoint"]) - float(row["uv_limit"])), float(row["finite_cutoff_error"]), 1e-9, 1e-12)
    check("Tables", "clock-product table: products telescope to the endpoint, UV limit 1/c(x*)", ok)
    ok = True
    for row in read_csv("blocked_free_modes.csv"):
        L = int(row["L"]); d = np.array([int(ch) for ch in row["direction"]], float)
        ok &= close(float(row["low_pole"]), omega(2 * PI / L * d), 1e-10)
    check("Tables", "blocked free modes: lowest visible pole equals the fine energy omega(p)", ok)


if __name__ == "__main__":
    print("Numerical tables")
    tables_axial(); tables_open(); tables_poles(); tables_clock(); tables_all_momenta()
    finish("Numerical tables")
