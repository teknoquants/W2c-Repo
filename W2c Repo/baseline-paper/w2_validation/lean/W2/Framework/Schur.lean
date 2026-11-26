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
namespace W2.Framework

/-- Schur's criterion after diagonalization of a finite positive eliminated block. -/
theorem schur_criterion {ι : Type*} [Fintype ι] (A : ℝ) (d b : ι → ℝ) (hd : ∀ i, 0 < d i) :
    (∀ x : ℝ, ∀ y : ι → ℝ, 0 ≤ A*x^2 + ∑ i, (2*x*b i*y i + d i*(y i)^2)) ↔
      (∑ i, (b i)^2/d i) ≤ A := by
-- W2 PROOF BEGIN W2.Framework.schur_criterion
  have identity (x : ℝ) (y : ι → ℝ) :
      A*x^2 + ∑ i, (2*x*b i*y i + d i*(y i)^2) =
      (A-∑ i, (b i)^2/d i)*x^2 + ∑ i, d i*(y i+x*b i/d i)^2 := by
    rw [sub_mul, Finset.sum_mul]
    have each (i : ι) : 2*x*b i*y i+d i*(y i)^2 =
        d i*(y i+x*b i/d i)^2 - (b i)^2/d i*x^2 := by field_simp [(hd i).ne']; ring
    simp_rw [each,Finset.sum_sub_distrib]
    ring
  constructor
  · intro nonneg
    have h := nonneg 1 (fun i => -(b i/d i))
    rw [identity] at h
    simpa using h
  · intro bound x y
    rw [identity]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr bound) (sq_nonneg _))
      (Finset.sum_nonneg (fun i _ => mul_nonneg (hd i).le (sq_nonneg _)))
-- W2 PROOF END W2.Framework.schur_criterion

theorem uniform_score_lift (J c gap m E h : ℝ) (hg : 0 < gap-m) (hc : 0 ≤ 2*c)
    (hb : h ≤ J*E) : 2*c*h/(gap-m) ≤ (2*c*J/(gap-m))*E := by
-- W2 PROOF BEGIN W2.Framework.uniform_score_lift
  calc
    _ ≤ 2*c*(J*E)/(gap-m) := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb hc) hg.le
    _ = _ := by ring
-- W2 PROOF END W2.Framework.uniform_score_lift
/-- All retained vectors, after diagonalizing the positive eliminated block. -/
theorem schur_all_retained {X ι : Type*} [Fintype ι] (A : X → ℝ)
    (d : ι → ℝ) (b : X → ι → ℝ) (hd : ∀ i, 0 < d i) :
    (∀ v : X, ∀ w : ι → ℝ, 0 ≤ A v + ∑ i, (2*b v i*w i + d i*(w i)^2)) ↔
      ∀ v, (∑ i, (b v i)^2/d i) ≤ A v := by
-- W2 PROOF BEGIN W2.Framework.schur_all_retained
  constructor
  · intro nonneg v
    have h := nonneg v (fun i => -(b v i/d i))
    have f (i : ι) : 2*b v i*(-(b v i/d i))+d i*(-(b v i/d i))^2 = -((b v i)^2/d i) := by
      field_simp [(hd i).ne']; ring
    simp_rw [f,Finset.sum_neg_distrib] at h
    linarith
  · intro bound v w
    simpa using (schur_criterion (A v) d (b v) hd).2 (bound v) 1 w
-- W2 PROOF END W2.Framework.schur_all_retained

end W2.Framework
