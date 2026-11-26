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
namespace W2.W2c

theorem eliminated_gap_of_fibre_poincare (g a c V T E : ℝ) (ha : 0 < a) (hc : 0 < c)
    (hV : V ≤ g^2 / c * T) (hE : g^2/(2*a)*T ≤ E) : c/(2*a)*V ≤ E := by
-- W2 PROOF BEGIN W2.W2c.eliminated_gap_of_fibre_poincare
  calc
    _ ≤ c/(2*a)*(g^2/c*T) := mul_le_mul_of_nonneg_left hV (by positivity)
    _ = _ := by field_simp
    _ ≤ E := hE
-- W2 PROOF END W2.W2c.eliminated_gap_of_fibre_poincare

theorem cor_5_separation (κ a m Λ : ℝ) (hk : 0 < κ) (ha : 0 < a) (hm : 0 < m)
    (h : κ ≤ a*Λ) : 1 - a*m/κ ≤ 1 - m/Λ := by
-- W2 PROOF BEGIN W2.W2c.cor_5_separation
  have hΛ : 0 < Λ := pos_of_mul_pos_right (lt_of_lt_of_le hk h) ha.le
  have h' : m/Λ ≤ a*m/κ := (div_le_div_iff₀ hΛ hk).2 (by nlinarith [mul_le_mul_of_nonneg_left h hm.le])
  linarith
-- W2 PROOF END W2.W2c.cor_5_separation

/-- Ratio of an inner-gradient mass bound to an outer variance lower bound. -/
theorem negative_control (s A B E V : ℝ) (hB : 0 < B) (hA : 0 ≤ A)
    (hE : E ≤ A*Real.exp (s/16)) (hV : B*Real.exp (s/4) ≤ V) :
    E/V ≤ A/B * Real.exp (-(3*s/16)) := by
-- W2 PROOF BEGIN W2.W2c.negative_control
  have hv := lt_of_lt_of_le (mul_pos hB (Real.exp_pos _)) hV
  calc
    E/V ≤ (A*Real.exp (s/16))/(B*Real.exp (s/4)) := by
      exact div_le_div₀ (by positivity) hE (by positivity) hV
    _ = A/B*(Real.exp (s/16)/Real.exp (s/4)) := by ring
    _ = _ := by rw [←Real.exp_sub]; congr 2; ring
-- W2 PROOF END W2.W2c.negative_control
end W2.W2c
