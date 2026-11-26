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

public import W2.Common.Basic
-- W2 PROOF IMPORTS
public import W2.W2aR.Estimates
-- W2 END IMPORTS

@[expose] public section
namespace W2.W2aR
open W2.Common

/-- W2a Lemma 6, equality of the first-order output and calibration coefficients. -/
def first_order_compat.statement : Prop :=
  ∀ κ ρ s : ℝ, κ + ρ * s = s ↔ (1 - ρ) * s = κ

/-- W2a Cor. 7 for a time-covariant response, whose input slope is one. -/
def no_regular_clock.statement : Prop :=
  ∀ κ : ℝ, κ ≠ 0 → ¬ ∃ s : ℝ, κ + 1 * s = s

/-- W2a-R.1(A). The full clock's exact matching makes the actual block error
identical to the calibration-ratio error. -/
def step_error_schemeA.statement : Prop :=
  ∀ (c : Clock) (a B xs x y c₁ Mc : ℝ), stepData a B xs x y →
    (∀ t, weak xs t → 0 < c t) → hasRemainder (fullClock c) xs (-c₁) Mc →
    0 < clockFloor (-c₁) Mc xs →
    let u := fullClock c
    let C := stepConstant a B xs (-c₁) Mc
    physicalRatio c x y (u x) = u y ∧
    |u y / u x - 1| ≤ C * x ^ 2 ∧
    |physicalRatio c x y (u x) / u x - 1| ≤ blockConstant C 0 xs * x ^ 2

/-- W2a-R.1(B). The truncated calibration has zero Taylor remainder. Its residual
against the physical response is controlled using the full reciprocal remainder.
The denominator of `matchConstant` includes `Mc * xs²`. -/
def step_error_schemeB.statement : Prop :=
  ∀ (c : Clock) (a B xs x y c₁ Mc : ℝ), stepData a B xs x y →
    (∀ t, weak xs t → 0 < c t) → hasRemainder (fullClock c) xs (-c₁) Mc →
    0 < clockFloor (-c₁) Mc xs → B * xs ≤ a / 2 →
    aPlus a B xs * xs ≤ 1 / 2 → |c₁| * xs ≤ 1 / 2 →
    let u := truncClock c₁
    let C := 6 * a * |c₁|
    let R := matchConstant a B xs c₁ Mc
    hasRemainder u xs (-c₁) 0 ∧ |u y / u x - 1| ≤ C * x ^ 2 ∧
    |physicalRatio c x y (u x) / u y - 1| ≤ R * x ^ 2 ∧
    |physicalRatio c x y (u x) / u x - 1| ≤ blockConstant C R xs * x ^ 2

end W2.W2aR

-- W2 IMPLEMENTATION
namespace W2.W2aR
open W2.Common

theorem first_order_compat : first_order_compat.statement := by
-- W2 PROOF BEGIN W2.W2aR.first_order_compat
  intro κ ρ s; constructor <;> intro h <;> linarith
-- W2 PROOF END W2.W2aR.first_order_compat

theorem no_regular_clock : no_regular_clock.statement := by
-- W2 PROOF BEGIN W2.W2aR.no_regular_clock
  rintro κ hk ⟨s,h⟩; apply hk; linarith
-- W2 PROOF END W2.W2aR.no_regular_clock

theorem step_error_schemeA : step_error_schemeA.statement := by
-- W2 PROOF BEGIN W2.W2aR.step_error_schemeA
  intro c a B xs x y c₁ Mc step hc rem floorpos
  dsimp only
  have he : physicalRatio c x y (fullClock c x) = fullClock c y := by
    simp [physicalRatio,fullClock,(hc _ step.1).ne']
  have hb := clockEstimate step rem floorpos
  exact ⟨he,hb,by simpa [he,blockConstant] using hb⟩
-- W2 PROOF END W2.W2aR.step_error_schemeA

private theorem combineFactors (f v w x xs C R : ℝ) (hv : v ≠ 0) (hw : w ≠ 0)
    (hx : 0 ≤ x) (hxs : x ≤ xs) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (cal : |w/v-1| ≤ C*x^2) (res : |f/w-1| ≤ R*x^2) :
    |f/v-1| ≤ blockConstant C R xs*x^2 := by
  let p := w/v-1
  let q := f/w-1
  have he : f/v-1 = p+q+p*q := by dsimp [p,q]; field_simp; ring
  rw [he]
  calc |p+q+p*q| ≤ |p| + |q| + |p| * |q| := by
         rw [← abs_mul]; exact (abs_add_le ..).trans (add_le_add (abs_add_le ..) le_rfl)
       _ ≤ C*x^2 + R*x^2 + (C*x^2)*(R*x^2) := by gcongr
       _ ≤ blockConstant C R xs*x^2 := by
         unfold blockConstant
         have hpow : x^2 ≤ xs^2 := by gcongr
         nlinarith only [mul_le_mul_of_nonneg_right hpow (show 0 ≤ C*R*x^2 by positivity)]

theorem step_error_schemeB : step_error_schemeB.statement := by
-- W2 PROOF BEGIN W2.W2aR.step_error_schemeB
  intro c a B xs x y c₁ Mc step hc rest hfloor hB hsmall hcs
  dsimp only
  let l := 1 - |c₁| * xs
  let d := clockFloor (-c₁) Mc xs
  let Q := stepQ a B xs
  let v := truncClock c₁
  let p := fun t => fullClock c t / v t
  have b := stepBounds step
  have hM := rest.1
  have hq : 0 < Q := b.q_pos
  have hd : 0 < d := hfloor
  have de : d = l - Mc*xs^2 := by simp [d,l,clockFloor]
  have hl : 0 < l := by dsimp [l]; linarith
  have vlo (t : ℝ) (ht : weak xs t) : l ≤ v t := by
    dsimp [v,truncClock,l]
    have he := le_abs_self (c₁*t)
    rw [abs_mul,abs_of_pos ht.1] at he
    linarith [mul_le_mul_of_nonneg_left ht.2 (abs_nonneg c₁)]
  have vp (t : ℝ) (ht : weak xs t) := hl.trans_le (vlo t ht)
  have rr : hasRemainder v xs (-c₁) 0 := by
    refine ⟨le_rfl,fun t _ => ?_⟩; simp [v,truncClock]; ring_nf
  have vf : clockFloor (-c₁) 0 xs = l := by simp [clockFloor,l]
  have hA : 0 < a := by have := step.2.2.2.1; nlinarith [mul_nonneg step.2.2.1 b.xs_pos.le]
  have hQ₂ : Q ≤ 2 := (div_le_iff₀ (by linarith : 0 < 1-aPlus a B xs*xs)).mpr (by linarith)
  have cal : |v y/v x-1| ≤ 6*a*|c₁| * x^2 := by
    apply (clockEstimate step rr (vf ▸ hl)).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    rw [stepConstant,vf,abs_neg,zero_mul,add_zero, div_le_iff₀ hl]
    have hap : aPlus a B xs ≤ 3*a/2 := by dsimp [aPlus]; linarith
    calc |c₁| * aPlus a B xs * Q ≤ |c₁| * (3*a/2)*2 := by gcongr
         _ ≤ 6*a*|c₁| * l := by dsimp [l]; nlinarith [mul_le_mul_of_nonneg_left hcs (show 0 ≤ 6*a*|c₁| by positivity)]
  have pr (t : ℝ) (ht : weak xs t) : |p t-1| ≤ Mc*t^2/l := by
    have vv := vp t ht
    have he : p t-1 = (fullClock c t-v t)/v t := by dsimp [p]; field_simp
    rw [he,abs_div,abs_of_pos vv]
    apply div_le_div₀ (by positivity) _ hl (vlo t ht)
    simpa [v,truncClock,sub_eq_add_neg] using rest.2 t ht
  have plow : d/l ≤ p x := by
    have hr := (abs_le.mp (pr x step.1)).1
    have hpow : x^2 ≤ xs^2 := by gcongr; exact b.x_pos.le; exact step.1.2
    rw [de,sub_div,div_self hl.ne']
    linarith [div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hM) hl.le]
  have ppos := (div_pos hd hl).trans_le plow
  have resid : |physicalRatio c x y (v x)/v y-1| ≤ matchConstant a B xs c₁ Mc*x^2 := by
    have e : physicalRatio c x y (v x)/v y-1 = (p y-p x)/p x := by
      dsimp [p,fullClock,physicalRatio]; field_simp [(hc _ step.1).ne',(hc _ step.2.1).ne',(vp _ step.1).ne',(vp _ step.2.1).ne']
    have hdiff : |p y-p x| ≤ Mc*(1+Q^2)*x^2/l := by
      calc |p y-p x| ≤ |p y-1| + |p x-1| := by simpa [abs_sub_comm (1:ℝ) (p x)] using abs_sub_le (p y) 1 (p x)
           _ ≤ Mc*y^2/l + Mc*x^2/l := add_le_add (pr y step.2.1) (pr x step.1)
           _ ≤ Mc*(Q*x)^2/l + Mc*x^2/l := by gcongr; exact b.y_pos.le; exact b.factor
           _ = _ := by ring
    rw [e,abs_div,abs_of_pos ppos]
    apply (div_le_div₀ (by positivity : 0 ≤ Mc*(1+Q^2)*x^2/l) hdiff (div_pos hd hl) plow).trans_eq
    change _ = (Mc*(1+Q^2)/d)*x^2
    field_simp
  refine ⟨rr,cal,resid,combineFactors _ _ _ _ _ _ _ (vp _ step.1).ne' (vp _ step.2.1).ne' b.x_pos.le step.1.2 (by positivity) ?_ cal resid⟩
  change 0 ≤ Mc * (1+Q^2) / d; positivity
-- W2 PROOF END W2.W2aR.step_error_schemeB

end W2.W2aR
