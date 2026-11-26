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

public import W2.W2b.GapRatio

@[expose] public section

namespace W2.W2b

/-- The quadratic coefficient and an explicit uniform remainder on all periodic sides L ≥ 4. -/
theorem free_artifact_constant (L : ℕ) (hL : 4 ≤ L) :
    let t := Real.pi / (L : ℝ)
    |1 / Real.cos t - 1 - Real.sin (2*t)^2 / 8| ≤ 7 * Real.sin (2*t)^4 := by
-- W2 PROOF BEGIN W2.W2b.free_artifact_constant
  dsimp only
  set t := Real.pi / (L : ℝ)
  obtain ⟨hpos, hu⟩ := angle_bounds L hL
  change 0 < t at hpos
  change t ≤ Real.pi / 4 at hu
  have hhalf : 1 / 2 ≤ Real.cos t := by
    rw [← Real.cos_pi_div_three]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hpos.le (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  set h := Real.cos t
  have hh : 0 < h := by linarith
  have h1 : h ≤ 1 := Real.cos_le_one _
  have sq : Real.sin t ^ 2 = 1 - h ^ 2 := by linarith [Real.sin_sq_add_cos_sq t]
  have zsq : Real.sin (2*t) ^ 2 = 4 * (1-h) * (1+h) * h^2 := by
    rw [Real.sin_two_mul]
    change (2 * Real.sin t * h)^2 = _
    linear_combination 4 * h^2 * sq
  have ident : 1/h - 1 - Real.sin (2*t)^2/8 =
      (1-h)^2 * ((2+2*h+2*h^2+h^3)/(2*h)) := by
    rw [zsq]
    field_simp
    ring
  have rnon : 0 ≤ (2+2*h+2*h^2+h^3)/(2*h) := by positivity
  have rle : (2+2*h+2*h^2+h^3)/(2*h) ≤ 7 := by
    apply (div_le_iff₀ (by positivity : 0 < 2*h)).2
    have h2 := (pow_le_one₀ hh.le h1 : h^2 ≤ 1)
    have h3 := (pow_le_one₀ hh.le h1 : h^3 ≤ 1)
    linarith
  have bound : 1-h ≤ Real.sin (2*t)^2 := by
    rw [zsq]
    have q : 1 ≤ 4*h^2 := by nlinarith [sq_nonneg (h-1/2)]
    have j : 1 ≤ (1+h)*(4*h^2) := one_le_mul_of_one_le_of_one_le (by linarith) q
    calc
      1-h = (1-h)*1 := by ring
      _ ≤ (1-h)*((1+h)*(4*h^2)) := mul_le_mul_of_nonneg_left j (by linarith)
      _ = _ := by ring
  rw [ident, abs_of_nonneg (mul_nonneg (sq_nonneg _) rnon)]
  calc
    _ ≤ (1-h)^2 * 7 := mul_le_mul_of_nonneg_left rle (sq_nonneg _)
    _ ≤ (Real.sin (2*t)^2)^2 * 7 := by gcongr
    _ = _ := by ring
-- W2 PROOF END W2.W2b.free_artifact_constant
end W2.W2b
