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
import W2.W2cR.FreeGap
import W2.W2cR.Hessian
import W2.W2cR.Separation
import W2.W2f.Assembly

namespace W2.W2cR

-- @result B.1 L1
theorem commutator_relative_obstruction (defect C p : ℝ) (h : 0 < defect) :
    ¬ defect ≤ C*p*(0:ℝ) := by
  simpa using (not_le_of_gt h)

-- @result B.2 L1
theorem precision_relative_gap (a b n f : ℝ) (ha : 0<a) (hn : 0<n)
    (hcs : a^2 ≤ b*n) (hf : f ≤ a/n) : f ≤ b/a := by
  apply hf.trans
  rw [div_le_div_iff₀ hn ha]
  nlinarith only [hcs]

-- @result B.3 L1
theorem homogeneous_chaos_floor {n : ℕ} (lam : Fin n → ℝ) (l : ℝ)
    (h : ∀ i, l ≤ lam i) (k : Fin n → ℕ) :
    l*(∑ i, (k i : ℝ)) ≤ ∑ i, lam i*(k i : ℝ) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (h i) (Nat.cast_nonneg _)

-- @result B.3 L1
theorem single_mode_attains (l : ℝ) (n : ℕ) : l*(n:ℝ)=(n:ℝ)*l := by
  ring

-- @result B.4 Def
noncomputable def quadraticCompression (x y : ℝ) : ℝ × ℝ :=
  (4*x-Real.sqrt 2*y, 4*y-Real.sqrt 2*x)

-- @result B.4 L1
theorem mixed_quadratic_minimum (x y : ℝ) :
    (4-Real.sqrt 2)*(x^2+y^2) ≤ 4*x^2-2*Real.sqrt 2*x*y+4*y^2 := by
  have h := mul_nonneg (Real.sqrt_nonneg 2) (sq_nonneg (x-y))
  nlinarith only [h]

-- @result B.4 L1
theorem joint_quadratic_below_double : 4-Real.sqrt (2:ℝ)<2*2 ∧
    quadraticCompression 1 1=(4-Real.sqrt 2,4-Real.sqrt 2) := by
  constructor
  · have h := Real.sqrt_pos.2 (by norm_num : (0:ℝ)<2)
    linarith
  · unfold quadraticCompression
    norm_num

-- @result B.5 L1
theorem quadratic_colour_contraction {n : ℕ} (x : Fin n → ℝ) :
    (∑ i, ((x i)^2-1))=(∑ i, (x i)^2)-(n:ℝ) := by
  simp [Finset.sum_sub_distrib]

-- @result B.5 L1
theorem orthogonal_colour_contraction {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (U : E ≃ₗᵢ[ℝ] E) (x y : E) :
    inner ℝ (U x) (U y)=inner ℝ x y := by
  exact U.inner_map_map x y

-- @result B.6 L1
theorem third_chaos_exclusion (e q : ℝ) (n : ℕ) (hn : 3≤n) (he : 0 ≤ e)
    (hq : q<3*e) : q<(n:ℝ)*e := by
  apply hq.trans_le
  apply mul_le_mul_of_nonneg_right _ he
  exact_mod_cast hn

-- @result B.8 L1
theorem conditional_block_monotone (h q : ℝ) (a b : ℝ) (hh : 0≤h) (hab : a≤b) :
    q+h*a ≤ q+h*b := by
  linarith [mul_le_mul_of_nonneg_left hab hh]

end W2.W2cR
