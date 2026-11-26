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

"""Shared helpers and physical constants for the W2 validation suite.

Paper: "The Small-Field Wilson Estimates for One Blocking Step in SU(N)
Lattice Yang-Mills" (Weak-Coupling Series W2), R. Cooperman and
A.E. Petrunina V.V., XISOSIS, Vienna, 2026.

Every check is tagged with the numbered target of the paper it supports.
Units: fine spacing a = 1, x = g^2, coarse spacing 2.
"""
import itertools
import math
import os
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
DATA = HERE / "data"
LEAN = HERE / "lean"

PI = math.pi
SQ2 = math.sqrt(2.0)
SLOPE = 1.0 + 1.0 / (2.0 * SQ2)          # R'(0) = 1 + 1/(2*sqrt 2)

_results = []


def b0(N):
    return 11.0 * N / (48.0 * PI ** 2)


def A_of(N):
    """One-loop inverse-coupling decrement per factor-two step, A = 4 b0 log 2."""
    return 4.0 * b0(N) * math.log(2.0)


def check(target, label, ok, detail=""):
    """Record one check.  `target` is the paper's numbered target, e.g. 'W2b.4'."""
    ok = bool(ok)
    _results.append((target, label, ok))
    tag = "PASS" if ok else "FAIL"
    extra = f"  ({detail})" if detail != "" else ""
    print(f"  [{tag}] {target}: {label}{extra}", flush=True)
    return ok


def close(x, y, rel=1e-10, abs_=1e-12):
    return math.isclose(float(x), float(y), rel_tol=rel, abs_tol=abs_)


def finish(unit):
    n = len(_results)
    passed = sum(1 for _, _, ok in _results if ok)
    print(f"  -> {unit}: {passed}/{n} checks passed")
    sys.exit(0 if passed == n else 1)


def rng(seed=2026):
    return np.random.default_rng(seed)


def read_csv(name):
    import csv
    with (DATA / name).open() as f:
        return list(csv.DictReader(f))


# ----------------------------------------------------------------- free lattice

def omega(q):
    """Fine free transverse frequency (a = 1): 2 sqrt(sum sin^2(q_j/2))."""
    q = np.asarray(q, dtype=float)
    return 2.0 * math.sqrt(float(np.sum(np.sin(q / 2.0) ** 2)))


ALIASES = list(itertools.product((0, 1), repeat=3))


def axial_energies(z):
    """Four visible axial alias energies (a = 1) for momentum (z,0,0), polarization 2."""
    s, h = math.sin(z / 2), math.cos(z / 2)
    return np.array([2 * s, 2 * h, 2 * math.sqrt(1 + s * s), 2 * math.sqrt(1 + h * h)])


def R_closed(z):
    """Closed form R(z) of W2b.4."""
    s, h = math.sin(z / 2), math.cos(z / 2)
    return (math.sin(z) / 2) * (1 / s + 1 / h + 1 / math.sqrt(1 + s * s) + 1 / math.sqrt(1 + h * h))


def blocked_covariance(p):
    """Equal-time covariance matrix of the two-link blocked field at coarse momentum p.

    Sum over the eight fine aliases q_r = p + pi r with link-midpoint form factors
    2 cos(q_i/2), the fine transverse projector and 1/(2 omega); unitary Fourier
    volume factor 1/8.
    """
    p = np.asarray(p, dtype=float)
    M = np.zeros((3, 3))
    for r in ALIASES:
        q = p + PI * np.array(r)
        sh = 2 * np.sin(q / 2)
        w = math.sqrt(float(sh @ sh))
        P = np.eye(3) - np.outer(sh, sh) / (w * w)
        F = 2 * np.cos(q / 2)
        M += np.outer(F, F) * P / (2 * w)
    return M / 8.0


def coarse_reference(p):
    """Coarse Wilson reference covariance at the same physical momentum (fine units)."""
    sc = np.sin(np.asarray(p, dtype=float))
    wc = math.sqrt(float(sc @ sc))
    Pc = np.eye(3) - np.outer(sc, sc) / (wc * wc)
    return Pc, wc


def transverse_ratios(p):
    """Eigenvalues of the normalized blocked covariance on the coarse transverse plane."""
    Pc, wc = coarse_reference(p)
    M = blocked_covariance(p)
    vals, vecs = np.linalg.eigh(Pc)
    T = vecs[:, vals > 0.5]                      # orthonormal basis of the transverse plane
    return np.sort(np.linalg.eigvalsh(4 * wc * T.T @ M @ T))


def schur_axial(z):
    """Retained energy A, margin J*, bare correction for the first axial mode (W2b.6)."""
    E = axial_energies(z)
    m = math.sin(z)
    inv = 1.0 / E
    w = inv / inv.sum()
    A = float(w @ E)
    Jstar = 1.0 / float(np.sum(w / (E - m)))
    return A, m, Jstar, A - m - Jstar, E, w
