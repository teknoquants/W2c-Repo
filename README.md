# The Eliminated Fibre Gap

**W2c-R rebuilt exercise • 25 November 2026 • six units and 46 target entries.**

Start with **W2c-R-Rebuilt-Exercise.docx** (editable) or **W2c-R-Rebuilt-Exercise.pdf**. Both contain the complete active Lean library, combined packet, numerical and validation scripts, and supporting Python listings. The companion files are executable sources. The older attachment and the complete released W2 snapshot are retained separately. See sources/README.md for the six reconstructed Unit B entries.

## Reproduce the numerical and document checks

Use Python 3.12 and the packages in requirements.txt, from the extracted project root.

```sh
python3 -m venv ../w2cr-env
. ../w2cr-env/bin/activate
python3 -m pip install -r requirements.txt
python3 scripts/release.py verify
python3 w2cr_validation/run_all.py --out ../w2cr-fresh-data
```

The optional output path must be outside the immutable project. Each of the eight parts can also run separately. Part 8 consumes the outputs of Parts 1–7 and can replay the archived data directly with `python3 w2cr_validation/part8.py ../w2cr-fresh-data`. Numerical controls, random seeds, residuals, confidence intervals and interval enclosures are under data/w2cr. Derived numerical evidence has the meaning identified at the relevant target.

## Run the Lean kernel locally

With elan installed, use the toolchain pinned by lean-toolchain and Lake's pinned mathlib manifest. On a first checkout allow access to the official Lean and mathlib package servers.

```sh
lake exe cache get
bash scripts/run_lean.sh
python3 scripts/formal.py audit
```

The final local record is records/w2c-r/final.local.out. Seven exploratory statement packets use proof placeholders; every filled packet and the combined final are checked without them. The 77 rebuilt and inherited declarations in the combined final have only the permitted standard axioms. The released W2 master transcript is separately reproduced. Per-declaration level and source are printed in the book. Python never launches Lean during the eight-part replay.

## Package guide

| Path | Contents |
| --- | --- |
| W2/, W2.lean, W2cR.lean | Canonical Lean sources, including prerequisites |
| w2cr_validation/ | Independent parts, operators, benchmarks and interval computations |
| scripts/ | Packet locks and audit, book, tables, figures, extraction and release tools |
| packets/, locks/, records/ | Frozen statements, filled packets, raw outputs and axiom audit |
| data/w2cr/, figures/ | Full precision values, check logs and six research figures |
| docs/ | Target register, numerical design, release and citation guidance |
| sources/, baseline/, baseline-paper/ | Received exercise, transcribed annex, released W2 inputs |

## Research status

The uncut Gaussian open-box certificate, the periodic scalar infima and the pinned SU(2) estimate have distinct domains. The uniform interacting Wilson curvature and the required cut-domain control remain open. See D–E for the quantified premises. The public record is https://github.com/teknoquants/W2c-Repo and https://doi.org/10.5281/zenodo.24558116. The authors’ hosted Lean transcript is pending. Full MIT license in LICENSE.
