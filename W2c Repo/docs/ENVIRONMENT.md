# Reproduction environment

Local release build on 25 November 2026.

Python 3.12.14
x86_64
Lean 4.36.0 and Mathlib v4.36.0 (see lean-toolchain and lake-manifest.json).

All BLAS/OpenMP thread counts for the published numerical replay were one.
The release embeds the code and data. A fresh Lean installation needs the pinned Lean and Mathlib dependencies.

numpy 2.3.5
scipy 1.17.0
sympy 1.14.0
mpmath 1.3.0
python-docx 1.2.0
threadpoolctl 3.6.0
matplotlib 3.10.8
PyMuPDF 1.26.6

Eigenvalue checks use the target residual for the reported mode. Some LOBPCG runs warn about an additional requested Ritz vector or an internal stopping tolerance. Open-4/8/16/32.json give the recomputed residuals of the actual reported modes.
The packet transcripts themselves have no fill-round placeholder or warning. The Lake project build may emit module-system migration advice for compatible legacy-style imports.
