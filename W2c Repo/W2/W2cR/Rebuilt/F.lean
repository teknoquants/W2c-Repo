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

-- @result F.1 L1
theorem trial_gap_upper {S : Set ℝ} (bounded : BddBelow S) (r : ℝ) (test : r∈S) :
    sInf S≤r := by
  exact csInf_le bounded test

-- @result F.1 L1
theorem su2_cut_half_angle (t : ℝ) : 4*(1-Real.cos (2*t))=8*(Real.sin t)^2 := by
  rw [Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq t]

-- @result F.1 L1
theorem normalized_trial_interval (z k a b : ℝ) (hz : 0≤z) (ha : 0<a) (h₁ : a≤k) (h₂ : k≤b) :
    z/b≤z/k ∧ z/k≤z/a := by
  exact ⟨div_le_div_of_nonneg_left hz (ha.trans_le h₁) h₂, div_le_div_of_nonneg_left hz ha h₁⟩

end W2.W2cR
