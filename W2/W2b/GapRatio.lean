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

/-- Cancellation before diagonalizing the free Hamiltonian, for one field component. -/
theorem quadratic_coupling_cancel (g e b : ℝ) (hg : g ≠ 0) :
    g ^ 2 / 2 * (e / g) ^ 2 + (g * b) ^ 2 / (2 * g ^ 2) = (e ^ 2 + b ^ 2) / 2 := by
-- W2 PROOF BEGIN W2.W2b.quadratic_coupling_cancel
  field_simp
-- W2 PROOF END W2.W2b.quadratic_coupling_cancel

/-- A positive harmonic frequency fixes the variance of its normalized position Gaussian. -/
theorem oscillator_variance (ω v : ℝ) (hω : 0 < ω) :
    2 * ω * v = 1 ↔ v = 1 / (2 * ω) := by
-- W2 PROOF BEGIN W2.W2b.oscillator_variance
  rw [eq_div_iff (by positivity : 2 * ω ≠ 0), mul_comm v]
-- W2 PROOF END W2.W2b.oscillator_variance

theorem angle_bounds (L : ℕ) (hL : 4 ≤ L) :
    0 < Real.pi / L ∧ Real.pi / L ≤ Real.pi / 4 := by
-- W2 PROOF BEGIN W2.W2b.angle_bounds
  have h : (4 : ℝ) ≤ L := by exact_mod_cast hL
  exact ⟨by positivity, div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) h⟩
-- W2 PROOF END W2.W2b.angle_bounds

/-- The nonzero periodic transverse gap ratio in matched physical units. -/
theorem gap_ratio_eq_inv_cos (L : ℕ) (hL : 4 ≤ L) (a : ℝ) (ha : 0 < a) :
    (2 * Real.sin (Real.pi / L) / a) / (Real.sin (2 * (Real.pi / L)) / a) =
      1 / Real.cos (Real.pi / L) := by
-- W2 PROOF BEGIN W2.W2b.gap_ratio_eq_inv_cos
  obtain ⟨ht, ht'⟩ := angle_bounds L hL
  have hs := Real.sin_pos_of_pos_of_lt_pi ht (by linarith [Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo (show Real.pi / (L:ℝ) ∈ Set.Ioo (-(Real.pi/2)) (Real.pi/2) from
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
  rw [Real.sin_two_mul]
  field_simp
-- W2 PROOF END W2.W2b.gap_ratio_eq_inv_cos
end W2.W2b
