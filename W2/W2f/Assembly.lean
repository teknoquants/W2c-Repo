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

module
public import W2.W2e.Loss
public import W2.W2aR.Clock
public import W2.W2aR.Threshold
public import W2.W2d.Artifact
@[expose] public section

namespace W2.W2f
structure W2Constants where
  CS : ℝ
  CM : ℝ
  Ca : ℝ
  Cmix : ℝ
  nonnegative : 0 ≤ CS ∧ 0 ≤ CM ∧ 0 ≤ Ca ∧ 0 ≤ Cmix

theorem small_field_loss (loss α ζ x u : ℝ) (c : W2Constants)
    (combine : loss ≤ α+ζ)
    (retained : α ≤ c.CS*x^2+c.Ca*u^2) (mixed : ζ ≤ c.CM*x^2+c.Cmix*u^2) :
    loss ≤ (c.CS+c.CM)*x^2 + (c.Ca+c.Cmix)*u^2 := by
-- W2 PROOF BEGIN W2.W2f.small_field_loss
  linarith
-- W2 PROOF END W2.W2f.small_field_loss

theorem small_field_loss_schemeB (loss physical mismatch x C M artifact : ℝ)
    (combine : loss ≤ physical+mismatch) (hp : physical ≤ C*x^2+artifact)
    (hm : mismatch ≤ M*x^2) : loss ≤ (C+M)*x^2+artifact := by
-- W2 PROOF BEGIN W2.W2f.small_field_loss_schemeB
  linarith
-- W2 PROOF END W2.W2f.small_field_loss_schemeB

theorem clock_endpoint_factor : W2.W2aR.isotropic_telescopes.statement := by
-- W2 PROOF BEGIN W2.W2f.clock_endpoint_factor
  exact W2.W2aR.isotropic_telescopes
-- W2 PROOF END W2.W2f.clock_endpoint_factor

theorem weak_product_floor : W2.W2aR.transfer_bound.statement := by
-- W2 PROOF BEGIN W2.W2f.weak_product_floor
  exact W2.W2aR.transfer_bound
-- W2 PROOF END W2.W2f.weak_product_floor

theorem fine_scale_gap (gap Z z m b floor : ℝ) (n M : ℕ) (hn : n ≤ M)
    (hb : 0 < b) (hb1 : b ≤ 1) (hZ : 0 ≤ Z) (hz : 0 ≤ z) (hm : 0 ≤ m)
    (hf : 0 ≤ floor) (weak : Z*z*m*b^n*floor ≤ gap) : Z*z*m*b^M*floor ≤ gap := by
-- W2 PROOF BEGIN W2.W2f.fine_scale_gap
  have hpow : b^M ≤ b^n := pow_le_pow_of_le_one hb.le hb1 hn
  exact le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity)) hf) weak
-- W2 PROOF END W2.W2f.fine_scale_gap

/-- Two positive endpoint calibrations can coincide on the weak interval and differ outside. -/
theorem endpoint_not_determined (cut endpoint : ℝ) (h : cut < endpoint) :
    ∃ c d : ℝ → ℝ, (∀ x ≤ cut, c x = d x) ∧ c endpoint ≠ d endpoint := by
-- W2 PROOF BEGIN W2.W2f.endpoint_not_determined
  refine ⟨fun _ => 1, fun x => if x ≤ cut then 1 else 2, ?_, ?_⟩
  · intro x hx; simp [hx]
  · simp [not_le.mpr h]
-- W2 PROOF END W2.W2f.endpoint_not_determined
theorem exp_le_Ddelta {x c δ : ℝ} (hx : 0 < x) (hc : 0 < c) (hδ : 0 < δ) :
    Real.exp (-c/(Real.sqrt x)^δ) ≤ (4/(Real.exp 1*c*δ))^(4/δ) * x^2 := by
-- W2 PROOF BEGIN W2.W2f.exp_le_Ddelta
  let p := 4/δ
  let g := Real.sqrt x
  let b := g^δ
  let u := c/(p*b)
  have hp : 0 < p := by dsimp [p]; positivity
  have hg : 0 < g := Real.sqrt_pos.2 hx
  have hb : 0 < b := Real.rpow_pos_of_pos hg _
  have hu : 0 < u := div_pos hc (mul_pos hp hb)
  have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hu) hp.le
  have lu : Real.log u = Real.log c - Real.log p - δ*Real.log g := by
    rw [show u = c/(p*b) by rfl,Real.log_div hc.ne' (mul_pos hp hb).ne',
      Real.log_mul hp.ne' hb.ne',show b = g^δ by rfl,Real.log_rpow hg]; ring
  have coeff : 4/(Real.exp 1*c*δ) = p/(Real.exp 1*c) := by dsimp [p]; ring
  have lg : 2*Real.log g = Real.log x := by dsimp [g]; rw [Real.log_sqrt hx.le]; ring
  have pd : p*δ = 4 := by dsimp [p]; field_simp
  have pu : p*u = c/b := by dsimp [u]; field_simp
  change Real.exp (-c/b) ≤ (4/(Real.exp 1*c*δ))^p * x^2
  rw [coeff,← Real.log_le_log_iff (Real.exp_pos _) (mul_pos (Real.rpow_pos_of_pos (by positivity) _) (by positivity)),
      Real.log_exp,Real.log_mul (Real.rpow_pos_of_pos (by positivity) _).ne' (pow_ne_zero _ hx.ne'),
      Real.log_rpow (by positivity),Real.log_div hp.ne' (mul_pos (Real.exp_pos _) hc).ne',
      Real.log_mul (Real.exp_pos _).ne' hc.ne',Real.log_exp,Real.log_pow]
  rw [lu] at h
  rw [neg_div,← pu]
  have mult : p*δ*Real.log g = 4*Real.log g := by rw [pd]
  norm_num only [Nat.cast_ofNat] at *
  linarith only [h,mult,lg]
-- W2 PROOF END W2.W2f.exp_le_Ddelta


end W2.W2f
