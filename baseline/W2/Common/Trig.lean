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
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic

@[expose] public section

/-! Free axial lattice clock, shared by W2b.10 and W2a-R.5 at order zero. -/
namespace W2.Common

/-- The quartic cosine upper polynomial follows by integration from the cubic sine lower bound. -/
private theorem cos_le_quartic {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  let f (t : ℝ) := 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t
  have hd (t : ℝ) : deriv f t = -t + t ^ 3 / 6 + Real.sin t := by
    simp (disch := fun_prop) [f]
    ring
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop)
    · exact fun _ _ => by dsimp [f]; fun_prop
    · intro t ht
      rw [hd]
      have ht' : 0 ≤ t := interior_subset ht
      linarith [Real.sin_ge_sub_cube ht']
  have he := hm (show (0 : ℝ) ∈ Set.Ici 0 by simp) hx hx
  simpa [f, sub_nonneg] using he

private theorem sin_le_quintic {x : ℝ} (hx : 0 ≤ x) :
    Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  let f (t : ℝ) := t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t
  have hd (t : ℝ) : deriv f t = 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t := by
    simp (disch := fun_prop) [f]
    ring
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop)
    · exact fun _ _ => by dsimp [f]; fun_prop
    · intro t ht
      rw [hd]
      exact sub_nonneg.mpr (cos_le_quartic (interior_subset ht))
  have he := hm (show (0 : ℝ) ∈ Set.Ici 0 by simp) hx hx
  simpa [f, sub_nonneg] using he

/-- For every periodic side `L ≥ 2`, the free clock is exactly sinc. Its error after
subtracting `1 − (π/L)²/6` is between zero and `(π/L)⁴/120`. The last clause
recovers its square from free dispersion for any energy origin and rest mass. -/
theorem free_clock_sinc_bounds (L : ℕ) (hL : 2 ≤ L) :
    let t := Real.pi / (L : ℝ)
    freeClock L = Real.sin t / t ∧
      0 ≤ freeClock L - (1 - t ^ 2 / 6) ∧
      freeClock L - (1 - t ^ 2 / 6) ≤ t ^ 4 / 120 ∧
      (∀ E₀ m : ℝ, 0 ≤ m → boxClockSq L E₀ (E₀ + m)
        (E₀ + Real.sqrt (m ^ 2 + (2 * Real.sin (p₁ L / 2)) ^ 2)) = (freeClock L) ^ 2) := by
-- W2 PROOF BEGIN W2.Common.free_clock_sinc_bounds
  let t := Real.pi / (L : ℝ)
  change freeClock L = Real.sin t / t ∧ _
  have hL' : 0 < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have ht : 0 < t := div_pos Real.pi_pos hL'
  have hp : p₁ L = 2 * t := by unfold p₁ t; ring
  have he : freeClock L = Real.sin t / t := by
    rw [freeClock, hp, show 2 * t / 2 = t by ring]
    field_simp
  rw [he]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · apply sub_nonneg.mpr
    apply (le_div_iff₀ ht).mpr
    linarith only [Real.sin_ge_sub_cube ht.le, show (1 - t ^ 2 / 6) * t = t - t ^ 3 / 6 by ring]
  · apply sub_le_iff_le_add.mpr
    apply (div_le_iff₀ ht).mpr
    linarith only [sin_le_quintic ht.le,
      show (t ^ 4 / 120 + (1 - t ^ 2 / 6)) * t = t - t ^ 3 / 6 + t ^ 5 / 120 by ring]
  · intro E₀ m _
    rw [← he, boxClockSq, freeClock, add_sub_cancel_left, add_sub_cancel_left,
      Real.sq_sqrt (by positivity), add_sub_cancel_left, div_pow]
-- W2 PROOF END W2.Common.free_clock_sinc_bounds

end W2.Common
