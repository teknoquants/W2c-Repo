# The small-field Wilson estimates for one blocking step

The integrated Word prompt generates the worked W2 exercise. Its 44 numbered targets cover W2a-R and W2b–W2f. The exercise gives the mathematical statement, available derivation or counterexample, names of the exact Lean results, and remaining hypotheses for each target.

| File | Contents |
|---|---|
| W2-Upgraded-Prompt.docx | Full generator specification, with the W2b changes integrated in context |
| W2-Generated-Exercise.docx | Editable mathematical exercise and proof register |
| W2-Generated-Exercise.md | Searchable worked text, native LaTeX formulas and evidence tables |
| W2/ and W2.lean | Source declarations, proofs, open predicates and public imports |
| study/claims.json | Machine-readable target register binding the Word specification to the proof or obligation |
| scripts/released.tsv | All 74 public Lean theorems with target, classification and scope |
| study/frozen.json | Exact source, toolchain and dependency digests |
| packets/W2_final.lean | One compilable proof file containing all theorem bodies |
| packets/W2_final.txt | Complete check-only prompt ready to submit to a compatible Lean execution service |
| records/w2-v1/final.local.out | Complete local master output for Lean 4.36.0 |
| records/module-replay.txt | Per-module results from the frozen return checker |
| records/modules/ | Raw local compiler outputs and retained, returned and transcript digests for module replays |
| study/benchmark/ | Periodic transverse Gaussian data, axial/diagonal pole residues, and open-box calibration |
| study/w2ar_reference/ | Six clock, Wilson and trajectory tables reproduced by the validation suite |
| sources/ | The original W2 Word prompt and W2b amendment document, preserved for comparison |

## Regenerate the Word exercise

Use Python 3.11 or later, the packages in requirements.txt, and Pandoc on your PATH. From this directory run

```sh
python3 -m pip install -r requirements.txt
python3 scripts/generate_exercise.py --output W2-Generated-Exercise.docx
python3 scripts/generate_exercise.py --output W2-Generated-Exercise.md
```

The generator reads all numbered targets in the Word specification, including the formulas in the amended W2b entries. It joins them to the mathematical arguments in the reviewed register. The generator reads the actual Word equations with Pandoc. Re-saving a file with the same mathematical targets preserves their binding to the arguments. If a target changes, review its mathematical argument and proof scope before issuing the next edition; the generator identifies that target. The release validator also checks the exact archived Word-file digest.

## Run the Lean proofs and numerical checks

Install Lean via elan with the project toolchain named in lean-toolchain. From this directory run

```sh
lake exe cache get
lake build
python3 scripts/validate.py
```

Lake resolves the exact Mathlib revision and transitive dependencies in lake-manifest.json. A first installation needs access to those dependencies. The archive has the complete W2 proof sources. Prebuilt Lean executables and dependency caches are supplied by the normal Lean installation. The standard validator checks all 44 target mappings and the MIT notices, reruns the numerical suite, builds the imported sources, and independently recompiles all nine retained packets including the common prelude. It checks the raw outputs against the saved records. For the individual editable module workflow use

```sh
python3 scripts/validate.py --modules
```

The three outcomes in the records are distinct. The 26 common-prelude declarations check the vocabulary. The master has 74 public theorems (61 L1, 13 L2) and 17 private proof lemmas. Local verification of 26 proof-bearing module returns is also included. Unit inventories overlap through dependencies and cannot be summed. The 9,579 executed numerical assertions include the 46 original regression checks; they test finite cases. Predicates in W2/Research/Obligations.lean express the open quantified inputs. The declaration types and hypotheses in the actual Lean source govern the scope of every proof.

## Reproduce one frozen return

```sh
python3 scripts/make_packet.py --prelude
python3 scripts/make_packet.py W2/W2b/Normalization.lean --unit W2b --emit-return
lake env lean --stdin < returns/Normalization.lean > returns/Normalization.out
python3 scripts/check_return.py packets/Normalization.lean returns/Normalization.lean returns/Normalization.out
python3 scripts/make_packet.py --final W2b
python3 scripts/axiom_audit.py records/w2b-v1/final.local.out --file records/w2b-v1/final.lean --report records/w2b-v1/lean_report.md
```

The editable template generates proof holes only in the permitted tactic bodies. The returned source and every check-only release packet have complete proofs. The checker verifies the retained module digests, frozen statements and exact return outside the permitted bodies. It recompiles before comparing the actual transcript and allowed transitive axioms. When Lean chooses a different module prefix for private declarations because of a filename, comparison canonicalizes that prefix only. Saved raw output is preserved.

The official hosted procedure remains available via the appropriate `packets/<unit>_final.txt`. A verbatim response from an actual hosted Lean run belongs in `records/<unit>-v1/final.out`. Each bundled `final.local.out` comes from a local run. A local transcript cannot establish hosted provenance.

## Scientific scope

The free calculation uses one Maxwell component on the positive transverse quotient. The first Wiener chaos comprises linear functions of the Gaussian field. On the first axial mode the normalized static covariance has slope 1 + 1/(2√2), the bare relative Schur correction tends to 3/4, and the combined Schur margin remains positive at finite volume. The interacting spectral bridge, uniform fibre, transport and signed-form estimates, and the W3/W4 physical inputs remain open. The quadrature for the cited Wilson kernel preserves the residual against the printed Hamiltonian-limit pairs.

Copyright and permission terms for the authored project sources appear in LICENSE and in every Lean and Python source. Original source documents and cited works retain their stated provenance. GitHub [GITHUB-URL] · DOI [DOI-PENDING].
