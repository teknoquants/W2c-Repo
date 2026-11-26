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

-- @result A.1 Def
structure AdmittedIndex (W Test Version Cut : Type*) (canonical : W → Version → Prop)
    (allowed : W → Cut → Test → Prop) where
  halfSides : Fin 3 → ℕ
  positiveSides : ∀ i, 0 < halfSides i
  scale : ℕ
  fineSpacing : ℝ
  initialCutoff : ℝ
  squaredCoupling : ℝ
  spacing_pos : 0 < fineSpacing
  cutoff_pos : 0 < initialCutoff
  weak : 0 < squaredCoupling ∧ squaredCoupling ≤ 1 / 6
  coarse : W
  version : Version
  canonical_version : canonical coarse version
  cut : Cut
  test : Test
  inDomain : allowed coarse cut test

-- @result A.1 Def
def boxVertices (a b c : ℕ) := (a+1)*(b+1)*(c+1)

-- @result A.1 Def
def boxLinks (a b c : ℕ) := a*(b+1)*(c+1)+(a+1)*b*(c+1)+(a+1)*(b+1)*c

-- @result A.2 L1
theorem midpoint_preserves_product {G : Type*} [Group G] (u v h : G) : (u*h⁻¹)*(h*v)=u*v := by
  group

-- @result A.2 L1
theorem midpoint_tangent_metric {E : Type*} [SeminormedAddCommGroup E] (v : E) :
    ‖v‖^2 + ‖-v‖^2 = 2*‖v‖^2 := by
  rw [norm_neg]
  ring

-- @result A.3 L1
theorem stabilizer_propagates {G : Type*} [Group G] (u v h : G) (a : u*h*v = u*v) : h=1 := by
  have h₁ : u*h=u := mul_right_cancel a
  exact mul_left_cancel (show u*h=u*1 by simpa using h₁)

-- @result A.3 L1
theorem rectangular_quotient_count (a b c : ℕ) :
    boxLinks (2*a) (2*b) (2*c) + boxVertices a b c =
    boxLinks a b c + boxVertices (2*a) (2*b) (2*c) + 14*a*b*c+3*(a*b+a*c+b*c) := by
  unfold boxLinks boxVertices
  ring

-- @result A.3 L1
theorem cube_from_rectangular (n : ℕ) : 14*n*n*n+3*(n*n+n*n+n*n)=14*n^3+9*n^2 := by
  ring

-- @result A.4 Supplemental
theorem ricci_coefficient_su (N t : ℝ) : -(2*N*t)/4=N*(-t/2) := by
  ring

-- @result A.4 Supplemental
theorem midpoint_ricci_half (N h : ℝ) : (N/2)*(2*h)=N*h := by
  ring

-- @result A.4 Supplemental
theorem oneill_nonneg_term (v : ℝ) : 0 ≤ 3*v^2/4 := by
  positivity

-- @result A.5 L1
theorem two_atom_variance (a b : ℝ) :
    ((a-(a+b)/2)^2+(b-(a+b)/2)^2)/2=(a-b)^2/4 := by
  ring

-- @result A.5 L1
theorem zero_energy_obstructs_poincare (a b C : ℝ) (h : a≠b) : ¬ (a-b)^2/4 ≤ C*0 := by
  have hp := sq_pos_of_ne_zero (sub_ne_zero.mpr h)
  linarith

-- @result A.8 L1
theorem integrated_of_pointwise {n : ℕ} (w v t : Fin n → ℝ) (C : ℝ)
    (hw : ∀ i, 0 ≤ w i) (h : ∀ i, v i ≤ C*t i) :
    (∑ i, w i*v i) ≤ C*∑ i, w i*t i := by
  calc
    (∑ i, w i*v i) ≤ ∑ i, w i*(C*t i) := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (h i) (hw i))
    _ = ∑ i, C*(w i*t i) := Finset.sum_congr rfl fun _ _ => by ring
    _ = _ := (Finset.mul_sum ..).symm

-- @result A.8 L2
theorem pointwise_of_integrated_cont {X : Type*} [TopologicalSpace X]
    (good : Set X) (v t : X → ℝ) (C : ℝ) (hd : Dense good)
    (hv : Continuous v) (ht : Continuous t) (h : ∀ x ∈ good, v x ≤ C*t x) :
    ∀ x, v x ≤ C*t x := by
  intro x
  have hc : IsClosed {y | v y ≤ C*t y} := isClosed_le hv (continuous_const.mul ht)
  exact (closure_minimal (show good ⊆ {y | v y ≤ C*t y} from h) hc) (hd x)

end W2.W2cR
