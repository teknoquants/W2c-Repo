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

-- @result C.1 Supplemental
theorem path_sum_square {n : ℕ} (a : Fin n → ℝ) :
    (∑ i, a i)^2 ≤ (n:ℝ)*(∑ i, (a i)^2) := by
  simpa using (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin n => (1:ℝ)) a)

-- @result C.1 Supplemental
theorem box_incidence_estimate (v e curl : ℝ) (h₁ : v ≤ 36*e) (h₂ : e ≤ 24*8*curl) :
    v ≤ 6912*curl := by
  linarith

-- @result C.2 L1
theorem operator_norm_twelve : Real.sqrt (12:ℝ)<4 := by
  rw [Real.sqrt_lt' (by norm_num : (0:ℝ)<4)]
  norm_num

-- @result C.2 Supplemental
theorem energy_floor_of_norm (c q N : ℝ) (hN : 0<N) (h : c ≤ N*q) : c/N≤q := by
  exact (div_le_iff₀ hN).2 (by simpa [mul_comm] using h)

-- @result C.3 L1
theorem tangential_rational_floor (n c e : ℝ) (h : n ≤ 6912*c) (hh : c≤4*e) :
    n/27648≤e := by
  linarith

-- @result C.3 L1
theorem gaussian_trial_upper (t : ℝ) (h : t≤Real.sqrt 12) : 2*t < 7 := by
  have hs : Real.sqrt (12:ℝ)<7/2 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  linarith

-- @result C.3 L1
theorem physical_gap_infimum_bounds {s : Set ℝ} (hs : s.Nonempty)
    (low : ∀ x ∈ s, (1:ℝ)/27648 ≤ x) (high : ∃ x ∈ s, x≤7) :
    (1:ℝ)/27648 ≤ sInf s ∧ sInf s ≤ 7 := by
  refine ⟨le_csInf hs low, ?_⟩
  obtain ⟨x,hx,h⟩ := high
  exact (csInf_le ⟨_,low⟩ hx).trans h

-- @result C.4 Supplemental
theorem certificate_without_enumeration (n c e : ℝ) (h : n≤96*c) (hh : c≤4*e) : n/384≤e := by
  linarith

-- @result C.4 Supplemental
theorem certificate_improved (n c e : ℝ) (h : n≤16*c) (hh : c≤4*e) : n/64≤e := by
  linarith

-- @result C.7 L1
theorem nested_grid_minimum {s t : Set ℝ} (hs : s.Nonempty) (ht : BddBelow t)
    (incl : s ⊆ t) : sInf t ≤ sInf s := by
  exact le_csInf hs (fun x hx => csInf_le ht (incl hx))

-- @result C.8 L1
theorem certificate_dimension (d swaps incident : ℝ) :
    ((2*d)*swaps^2)*incident=2*d*incident*swaps^2 := by
  ring

-- @result C.8 L1
theorem certificate_three : (36:ℝ)*24*8*4=27648 := by
  norm_num

end W2.W2cR
