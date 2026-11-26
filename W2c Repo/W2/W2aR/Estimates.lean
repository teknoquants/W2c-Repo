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
public import W2.Common.Hypotheses
public import Mathlib.Tactic
@[expose] public section
namespace W2.W2aR
open W2.Common

structure StepBounds (a B xs x y : ℝ) : Prop where
  x_pos : 0 < x
  y_pos : 0 < y
  xs_pos : 0 < xs
  ap_pos : 0 < aPlus a B xs
  q_pos : 0 < stepQ a B xs
  inc : x ≤ y
  factor : y ≤ stepQ a B xs * x
  jump : y - x ≤ aPlus a B xs * stepQ a B xs * x ^ 2
  lower : a - B * xs ≤ 1 / x - 1 / y

theorem stepBounds {a B xs x y : ℝ} (h : stepData a B xs x y) : StepBounds a B xs x y := by
-- W2 PROOF BEGIN W2.W2aR.stepBounds
  obtain ⟨⟨hx,hxs⟩,⟨hy,hys⟩,hB,hm,hmax,hd⟩ := h
  let d := 1 / x - 1 / y
  have d0 : 0 < xs := hx.trans_le hxs
  have dmin : a - B*xs ≤ d := by dsimp [d]; linarith [(abs_le.mp hd).2, mul_le_mul_of_nonneg_left hxs hB]
  have dmax : d ≤ aPlus a B xs := by dsimp [d,aPlus]; linarith [(abs_le.mp hd).1, mul_le_mul_of_nonneg_left hxs hB]
  have hdpos := hm.trans_le dmin
  have hap := hdpos.trans_le dmax
  have hid : d * x * y = y - x := by dsimp [d]; field_simp
  have hinc : x ≤ y := by nlinarith [mul_nonneg (mul_nonneg hdpos.le hx.le) hy.le]
  have he : 0 < 1-aPlus a B xs * xs := by linarith
  have hq : 0 < stepQ a B xs := one_div_pos.mpr he
  have hxf : y ≤ stepQ a B xs * x := by
    rw [stepQ, one_div_mul_eq_div, le_div_iff₀ he]
    have hp : d*x ≤ aPlus a B xs * xs := mul_le_mul dmax hxs hx.le hap.le
    nlinarith [mul_le_mul_of_nonneg_right hp hy.le]
  refine ⟨hx,hy,d0,hap,hq,hinc,hxf,?_,dmin⟩
  calc y-x = d*x*y := hid.symm
       _ ≤ aPlus a B xs * x * (stepQ a B xs * x) := by gcongr
       _ = _ := by ring
-- W2 PROOF END W2.W2aR.stepBounds

theorem calibration_floor {u : Clock} {s M xs x : ℝ} (h : hasRemainder u xs s M)
    (hx : weak xs x) : clockFloor s M xs ≤ u x := by
-- W2 PROOF BEGIN W2.W2aR.calibration_floor
  obtain ⟨hM,hr⟩ := h
  have e := (abs_le.mp (hr x hx)).1
  have a : |s*x| ≤ |s| * xs := by rw [abs_mul,abs_of_pos hx.1]; gcongr; exact hx.2
  have b : M*x^2 ≤ M*xs^2 := by gcongr; exact hx.1.le; exact hx.2
  unfold clockFloor
  linarith [neg_abs_le (s*x)]
-- W2 PROOF END W2.W2aR.calibration_floor

theorem clockEstimate {u : Clock} {a B xs x y s M : ℝ} (step : stepData a B xs x y)
    (rest : hasRemainder u xs s M) (floorpos : 0 < clockFloor s M xs) :
    |u y / u x - 1| ≤ stepConstant a B xs s M * x^2 := by
-- W2 PROOF BEGIN W2.W2aR.clockEstimate
  have b := stepBounds step
  have lower := calibration_floor rest step.1
  have hp := floorpos.trans_le lower
  let Q := stepQ a B xs
  let C := |s| * aPlus a B xs * Q + M * (1 + Q^2)
  have hc : 0 ≤ C := by dsimp [C]; have := b.ap_pos; have : 0 < Q := b.q_pos; have := rest.1; positivity
  have d : |u y-u x| ≤ C*x^2 := by
    calc |u y-u x| = |(u y-(1+s*y)) + s*(y-x) - (u x-(1+s*x))| := by ring_nf
         _ ≤ |u y-(1+s*y)| + |s*(y-x)| + |u x-(1+s*x)| :=
           by
           rw [sub_eq_add_neg (_ + _)]
           exact (abs_add_le ..).trans (by rw [abs_neg]; gcongr; exact abs_add_le ..)
         _ ≤ M*(Q*x)^2 + |s| * (aPlus a B xs*Q*x^2) + M*x^2 := by
           rw [abs_mul,abs_of_nonneg (sub_nonneg.mpr b.inc)]
           have hy2 : y^2 ≤ (Q*x)^2 := by gcongr; exact b.y_pos.le; exact b.factor
           exact add_le_add (add_le_add ((rest.2 y step.2.1).trans (mul_le_mul_of_nonneg_left hy2 rest.1)) (mul_le_mul_of_nonneg_left b.jump (abs_nonneg s))) (rest.2 x step.1)
         _ = _ := by dsimp [C]; ring
  rw [show u y / u x - 1 = (u y-u x) / u x by field_simp, abs_div, abs_of_pos hp]
  change |u y-u x| / u x ≤ C / clockFloor s M xs * x^2
  rw [div_mul_eq_mul_div]
  exact div_le_div₀ (mul_nonneg hc (sq_nonneg _)) d floorpos lower
-- W2 PROOF END W2.W2aR.clockEstimate

end W2.W2aR
