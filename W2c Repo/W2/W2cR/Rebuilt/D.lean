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

-- @result D.2 Supplemental
theorem fixed_volume_loss (C rho : ℝ) (hc : 0<C) (h : rho < 1/C) : C*rho<1 := by
  have hh := (lt_div_iff₀ hc).1 h
  linarith [mul_comm rho C]

-- @result D.3 L1
theorem marginal_schur_square (u t r : ℝ) :
    u^2+2*r*u*t+t^2=(t+r*u)^2+(1-r^2)*u^2 := by
  ring

-- @result D.3 L1
theorem covariance_subtraction_strict (r : ℝ) (hr : r ≠ 0) : 1-r^2<1 := by
  linarith [sq_pos_of_ne_zero hr]

-- @result D.7 Def
structure BlockMixingHyp (I : Type*) (A : I → Prop) (V T x : I → ℝ) where
  localFloor : ℝ
  rowNorm : ℝ
  local_pos : 0 < localFloor
  rows_nonneg : 0 ≤ rowNorm
  contraction : rowNorm < 1
  tensorization : ∀ i, A i → (1-rowNorm)^2*localFloor*V i ≤ x i*T i

-- @result D.7 L2
theorem uniform_of_block_mixing {I : Type*} {A : I → Prop} {V T x : I → ℝ}
    (h : BlockMixingHyp I A V T x) :
    ∃ c : ℝ, 0<c ∧ ∀ i, A i → c*V i ≤ x i*T i := by
  refine ⟨(1-h.rowNorm)^2*h.localFloor, ?_, h.tensorization⟩
  exact mul_pos (sq_pos_of_pos (sub_pos.mpr h.contraction)) h.local_pos

end W2.W2cR
