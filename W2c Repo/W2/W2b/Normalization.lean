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

public import Mathlib

@[expose] public section

namespace W2.W2b
noncomputable def axialRatio (z : ℝ) : ℝ :=
  Real.cos (z/2) + Real.sin z / 2 *
    (1 / Real.cos (z/2) + 1 / Real.sqrt (1 + Real.sin (z/2)^2) +
      1 / Real.sqrt (1 + Real.cos (z/2)^2))

/-- The complete static covariance ratio for an axial momentum and transverse component. -/
theorem axis_alias_reduction (z : ℝ) (hs : Real.sin (z/2) ≠ 0) :
    Real.sin z/2 * (1/Real.sin (z/2) + 1/Real.cos (z/2) +
      1/Real.sqrt (1 + Real.sin (z/2)^2) + 1/Real.sqrt (1 + Real.cos (z/2)^2)) = axialRatio z := by
-- W2 PROOF BEGIN W2.W2b.axis_alias_reduction
  unfold axialRatio
  have hd : Real.sin z = 2 * Real.sin (z/2) * Real.cos (z/2) := by
    convert Real.sin_two_mul (z/2) using 1
    ring_nf
  rw [hd]
  field_simp [hs]
  ring
-- W2 PROOF END W2.W2b.axis_alias_reduction

@[simp] theorem axialRatio_zero : axialRatio 0 = 1 := by
-- W2 PROOF BEGIN W2.W2b.axialRatio_zero
  simp [axialRatio]
-- W2 PROOF END W2.W2b.axialRatio_zero

/-- At positive axial momentum this derivative is the one-sided physical slope. -/
theorem axis_ratio_slope : HasDerivAt axialRatio (1+1/(2*Real.sqrt 2)) 0 := by
-- W2 PROOF BEGIN W2.W2b.axis_ratio_slope
  let b := fun z : ℝ => 1/Real.cos (z/2) + 1/Real.sqrt (1+Real.sin (z/2)^2) +
    1/Real.sqrt (1+Real.cos (z/2)^2)
  have d : DifferentiableAt ℝ (fun z : ℝ => z/2) 0 := differentiableAt_id.div_const 2
  have ds := d.sin
  have dc := d.cos
  have one : DifferentiableAt ℝ (fun _ : ℝ => (1:ℝ)) 0 := differentiableAt_const _
  have ps := (one.add (ds.pow 2)).sqrt (by norm_num : (1:ℝ) + Real.sin (0/2)^2 ≠ 0)
  have pc := (one.add (dc.pow 2)).sqrt (by norm_num : (1:ℝ) + Real.cos (0/2)^2 ≠ 0)
  have hb : DifferentiableAt ℝ b 0 :=
    ((one.div dc (by norm_num)).add (one.div ps (by norm_num))).add (one.div pc (by norm_num))
  have ht := (hasDerivAt_id (0:ℝ)).div_const 2
  have hc := (Real.hasDerivAt_cos (0/2 : ℝ)).comp 0 ht
  have hp := ((Real.hasDerivAt_sin 0).div_const 2).mul hb.hasDerivAt
  change HasDerivAt (fun z : ℝ => Real.cos (z/2) + Real.sin z / 2 * b z) _ 0
  convert hc.add hp using 1
  · rfl
  · simp [b]
    ring_nf
-- W2 PROOF END W2.W2b.axis_ratio_slope

theorem normalization_scalar (g a : ℝ) (hg : 0 < g) (ha : 0 < a) :
    (2 * (g^2/(2*a))) / (g^2/(2*(2*a))) = 4 := by
-- W2 PROOF BEGIN W2.W2b.normalization_scalar
  field_simp
  ring
-- W2 PROOF END W2.W2b.normalization_scalar

theorem axis_transport_slope :
    HasDerivAt (fun z => (Real.sqrt (axialRatio z))⁻¹) (-(1+1/(2*Real.sqrt 2))/2) 0 := by
-- W2 PROOF BEGIN W2.W2b.axis_transport_slope
  have h := (axis_ratio_slope.sqrt (by simp)).inv (by simp)
  convert h using 1
  simp
  ring
-- W2 PROOF END W2.W2b.axis_transport_slope
/-- The nonzero-alias diagonal background is scalar. Singleton aliases contribute on
both perpendicular axes; each two-axis alias contributes on the missing axis. -/
theorem alias_background_is_scalar (u v : Fin 3 → ℝ) (a b : ℝ) :
    (∑ k : Fin 3, ∑ j : Fin 3, if j = k then 0 else a*u j*v j) +
      (∑ j : Fin 3, b*u j*v j) = (2*a+b)*(∑ j : Fin 3, u j*v j) := by
-- W2 PROOF BEGIN W2.W2b.alias_background_is_scalar
  simp [Fin.sum_univ_succ]
  ring
-- W2 PROOF END W2.W2b.alias_background_is_scalar

end W2.W2b
