/-
SPDX-License-Identifier: MIT
MIT License

Copyright (c) 2026 Roger Cooperman; A.E. Petrunina V.V.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/
import Mathlib
import W2.W2c.EliminatedGap
import W2.W2d.Artifact
 
namespace W2.W2cR
 
/-- Proposition W2c-R.7: a uniform curvature floor `K > 0` on the Rayleigh quotients is
incompatible with the collapse `R s ≤ C · exp(-3s/16)` of W2c.6. -/
theorem curvature_excludes_collapse (R : ℝ → ℝ) (K C : ℝ) (hK : 0 < K)
    (hR : ∀ s, K ≤ R s) (hcollapse : ∀ s, R s ≤ C * Real.exp (-(3 * s / 16))) : False := by
-- W2 PROOF BEGIN W2.W2cR.curvature_excludes_collapse
  by_cases hC : 0 < C
  · let t := 2 * C / K
    have ht : 0 < t := div_pos (by positivity) hK
    let s := (16 / 3 : ℝ) * Real.log t
    have he : -(3 * s / 16) = -Real.log t := by dsimp [s]; ring
    have h := (hR s).trans (hcollapse s)
    rw [he, Real.exp_neg, Real.exp_log ht, ← div_eq_mul_inv, le_div_iff₀ ht] at h
    dsimp [t] at h
    field_simp [ne_of_gt hK] at h
    nlinarith
  · have h := (hR 0).trans (hcollapse 0)
    simp at h
    linarith
-- W2 PROOF END W2.W2cR.curvature_excludes_collapse
 
/-- Corollary W2c-R.8: explicit separation along a weak trajectory, `aₖ = a_K / 2 ^ n`. -/
theorem separation_explicit (κ aK m Λ d b : ℝ) (n : ℕ) (hk : 0 < κ) (haK : 0 < aK)
    (hm : 0 < m) (hb : 0 < b) (run : d ≤ (n : ℝ) * (6 * b * Real.log 2))
    (hgap : κ ≤ (aK / 2 ^ n) * Λ) :
    1 - aK * m * Real.exp (-d / (6 * b)) / κ ≤ 1 - m / Λ := by
-- W2 PROOF BEGIN W2.W2cR.separation_explicit
  have hsep := W2.W2c.cor_5_separation κ (aK / 2 ^ n) m Λ hk (by positivity) hm hgap
  have hd := W2.W2d.lattice_artifact_decay d b (aK * m) n hb (by positivity) run
  have hmul : aK / 2^n * m = (aK * m) / 2^n := by ring
  rw [hmul] at hsep
  exact (sub_le_sub_left (div_le_div_of_nonneg_right hd hk.le) 1).trans hsep
-- W2 PROOF END W2.W2cR.separation_explicit
 
end W2.W2cR
