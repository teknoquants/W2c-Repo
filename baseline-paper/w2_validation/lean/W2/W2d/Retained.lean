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
namespace W2.W2d
/-- D = retained/r − reference. Positivity of the target controls multiplication by r. -/
theorem retained_of_defect (r retained reference m V b : ℝ) (hr : 1 ≤ r)
    (hm : 0 ≤ m) (hV : 0 ≤ V) (hb : b ≤ 1) (excess : m*V ≤ reference)
    (defect : -(reference-m*V)/2-b*m*V ≤ retained/r-reference) :
    (1-b)*m*V ≤ retained := by
-- W2 PROOF BEGIN W2.W2d.retained_of_defect
  have hr' : 0 < r := by linarith
  have bound : (1-b)*m*V ≤ retained/r := by linarith
  have prod := (le_div_iff₀ hr').mp bound
  exact le_trans (le_mul_of_one_le_right (by positivity : 0 ≤ (1-b)*m*V) hr) prod
-- W2 PROOF END W2.W2d.retained_of_defect

theorem no_quadratic_term (u v k h : ℝ) (hk : k=0) (hh : h=0) : u*k+v*h=0 := by
-- W2 PROOF BEGIN W2.W2d.no_quadratic_term
  simp [hk,hh]
-- W2 PROOF END W2.W2d.no_quadratic_term

/-- A positive first-order change of spectral units is consistent with a one-sided comparison. -/
theorem upward_shift_witness (x : ℝ) (hx : 0 < x) :
    0 < (1+x)^2-1 ∧ (1+x)^2-1 = 2*x+x^2 := by
-- W2 PROOF BEGIN W2.W2d.upward_shift_witness
  constructor <;> nlinarith [sq_nonneg x]
-- W2 PROOF END W2.W2d.upward_shift_witness
/-- A two-sided estimate on squared speeds gives a speed bound when the reference is positive. -/
theorem speed_from_squared_gap (c v e : ℝ) (hc : 0 < c) (hv : 0 ≤ v)
    (bound : |v^2-c^2| ≤ e) : |v-c| ≤ e/c := by
-- W2 PROOF BEGIN W2.W2d.speed_from_squared_gap
  apply (le_div_iff₀ hc).2
  calc
    _ ≤ |v-c| * (v+c) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    _ = |v^2-c^2| := by calc
      _ = |(v-c)*(v+c)| := by rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ v+c)]
      _ = _ := by congr 1; ring
    _ ≤ e := bound
-- W2 PROOF END W2.W2d.speed_from_squared_gap

end W2.W2d
