# w2_validation

Validation suite for the white paper

**The Small-Field Wilson Estimates for One Blocking Step in SU(N) Lattice Yang–Mills**
(Weak-Coupling Series, programme W2)

Roger Cooperman — https://orcid.org/0009-0009-5011-2135
A.E. Petrunina V.V. — https://orcid.org/0009-0002-4595-736X
XISOSIS, Vienna, 23 November 2026

- GitHub: https://github.com/teknoquants/W2-Exercise-and-Lean
- DOI: https://doi.org/10.5281/zenodo.24492913

## Run

```
pip install -r requirements.txt
python run_all.py          # exit code 0 only if every check passes and all 44 targets are covered
```

Run Python without `-O`. Every check is tagged with the numbered target of the paper it supports
(W2a-R.1 … W2f.5); `run_all.py` also verifies that all 44 targets are covered.

## Checks (189)

| Script | Content | Checks |
|---|---|---|
| `validate_w2ar.py` | W2a-R.1–10: clock constants, telescoping, gamma drift, sinc clock, poles, c₁ quadrature | 45 |
| `validate_w2b.py` | W2b.1–11: Gaussian vacuum, gaps, 1/8 artifact, R(z), transport, 3/4 Schur limit, kernels, poles | 54 |
| `validate_w2c.py` | W2c.1–6: gauge reduction, fibre counts, eliminated gap, Rayleigh collapse | 16 |
| `validate_w2d.py` | W2d.1–7: transport obstruction, defect, retained gap, running decay, artifact sum | 17 |
| `validate_w2e.py` | W2e.1–5: Gaussian score, resolvent bounds, Schur criterion, clock invariance | 11 |
| `validate_w2f.py` | W2f.1–5: assembly, endpoint clock, D_δ, product floor, step count | 16 |
| `validate_numerical_tables.py` | every table of Section 9, all 4,676 momentum blocks | 19 |
| `validate_lean_register.py` | Lean source digests, no sorry/axiom, axiom audit, name register | 11 |
| **Total** | | **189** |

`run_log.txt` is the output of the last complete run.

## Lean 4 project (`lean/`)

The formal proofs cited in the paper: 29 modules under `lean/W2/`, the combined file `W2_final.lean`,
Lean 4.36.0 with Mathlib v4.36.0. 74 public theorems (`data/released.tsv`), bound to the 44 targets in
`data/claims.json`. `final.local.out` is the authors' recorded kernel run (91 axiom records, only
`propext`, `Classical.choice`, `Quot.sound`); `module-replay.txt` the per-module replay; `SHA256SUMS` the
digests of the sources. To re-run the kernel check:

```
cd lean
lake exe cache get
lake build
lake env lean W2_final.lean
```

`validate_lean_register.py` does not run Lean; it checks the digests, the absence of `sorry`, `admit` and
user axioms, the recorded audit and the name register.

## Data (`data/`)

Reference tables recomputed by the suite (benchmark and W2a-R reference CSV files), the release register
`released.tsv` and the target register `claims.json`.

## Citation

R. Cooperman and A.E. Petrunina V.V., “The Small-Field Wilson Estimates for One Blocking Step in
SU(N) Lattice Yang–Mills,” XISOSIS, Vienna, 23 November 2026,
DOI:https://doi.org/10.5281/zenodo.24492913.

## Licence

MIT — see `LICENSE`. Every script carries the MIT notice.
