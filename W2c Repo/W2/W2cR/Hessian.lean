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
import W2.Research.Obligations
import W2.W2c.EliminatedGap
 
namespace W2.W2cR
 
open W2.Research
 
/-- Cited input (Bakry–Émery on a finite-dimensional fibre): a curvature lower bound `K > 0`
gives the Poincaré inequality `K · Var ≤ Dirichlet integral`. Index `i` runs over admitted fibres. -/
def BakryEmery {ι : Type*} (curvLB : ι → ℝ → Prop) (V T : ι → ℝ) : Prop :=
  ∀ i K, 0 < K → curvLB i K → K * V i ≤ T i
 
/-- Theorem W2c-R.4 as a hypothesis structure: on every admitted fibre the curvature
(Ricci plus Hessian of the potential) is at least `(1 - δ i) · 2κ₀ / g i ^ 2`. -/
structure HessianLowerBoundHyp {ι : Type*} (admitted : ι → Prop) (g : ι → ℝ)
    (curvLB : ι → ℝ → Prop) where
  κ₀ : ℝ
  δ : ι → ℝ
  δmax : ℝ
  hκ₀ : 0 < κ₀
  hδmax : δmax < 1
  hδ : ∀ i, admitted i → δ i ≤ δmax
  hg : ∀ i, admitted i → 0 < g i
  curv : ∀ i, admitted i → curvLB i ((1 - δ i) * (2 * κ₀) / g i ^ 2)
 
/-- Corollary W2c-R.5: the Hessian bound and Bakry–Émery discharge `uniformFibrePoincare`
with `c = (1 - δmax) · 2κ₀`. -/
theorem fibre_poincare_of_hessian {ι : Type*} (admitted : ι → Prop) (g V T : ι → ℝ)
    (curvLB : ι → ℝ → Prop) (H : HessianLowerBoundHyp admitted g curvLB)
    (BE : BakryEmery curvLB V T) (hT : ∀ i, admitted i → 0 ≤ T i) :
    uniformFibrePoincare admitted g V T := by
-- W2 PROOF BEGIN W2.W2cR.fibre_poincare_of_hessian
  have hbase : 0 < 2 * H.κ₀ := mul_pos (by norm_num) H.hκ₀
  have hc := mul_pos (sub_pos.mpr H.hδmax) hbase
  refine ⟨_, hc, fun i hi => ?_⟩
  have hp := sq_pos_of_pos (H.hg i hi)
  have hiδ := H.hδ i hi
  have hcoef := mul_le_mul_of_nonneg_right (sub_le_sub_left hiδ 1) hbase.le
  have hpoint := BE i _ (div_pos (mul_pos (sub_pos.mpr (hiδ.trans_lt H.hδmax)) hbase) hp)
    (H.curv i hi)
  by_cases hv : 0 ≤ V i
  · have hsmall := (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hcoef hp.le) hv).trans hpoint
    rw [div_mul_eq_mul_div, div_le_iff₀ hp] at hsmall
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    linarith only [hsmall]
  · exact (le_of_not_ge hv).trans (mul_nonneg (div_nonneg hp.le hc.le) (hT i hi))
-- W2 PROOF END W2.W2cR.fibre_poincare_of_hessian
 
/-- Corollary W2c-R.6: with the energy relation of W2c.4, the eliminated gap is uniform
(`uniformEliminated` with `κ = c / 2`), where the gap is the Rayleigh quotient `E / V`. -/
theorem eliminated_gap_small_field {ι : Type*} (admitted : ι → Prop) (g a V T E : ι → ℝ)
    (ha : ∀ i, admitted i → 0 < a i) (hV : ∀ i, admitted i → 0 < V i)
    (hE : ∀ i, admitted i → g i ^ 2 / (2 * a i) * T i ≤ E i)
    (hP : uniformFibrePoincare admitted g V T) :
    uniformEliminated admitted a (fun i => E i / V i) := by
-- W2 PROOF BEGIN W2.W2cR.eliminated_gap_small_field
  obtain ⟨c, hc, h⟩ := hP
  refine ⟨c / 2, by positivity, fun i hi => ?_⟩
  have hbound := W2.W2c.eliminated_gap_of_fibre_poincare (g i) (a i) c (V i)
    (T i) (E i) (ha i hi) hc (h i hi) (hE i hi)
  have ha' := ha i hi
  have hv := hV i hi
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 2 * a i)] at hbound
  rw [← mul_div_assoc, le_div_iff₀ hv]
  linarith only [hbound]
-- W2 PROOF END W2.W2cR.eliminated_gap_small_field
 
/-- Non-vacuity, curvature field of the free model: the required curvature `(1 - 0) · 2 · 1 / 1 ^ 2`
does not exceed the model's curvature `2`. -/
theorem freeModel_curv : ((1 : ℝ) - 0) * (2 * 1) / 1 ^ 2 ≤ 2 := by
-- W2 PROOF BEGIN W2.W2cR.freeModel_curv
  norm_num
-- W2 PROOF END W2.W2cR.freeModel_curv
 
/-- Non-vacuity: a one-fibre free model satisfies `HessianLowerBoundHyp`. -/
def freeModelHyp : HessianLowerBoundHyp (fun _ : Unit => True) (fun _ => (1 : ℝ))
    (fun _ K => K ≤ 2) where
  κ₀ := 1
  δ := fun _ => 0
  δmax := 0
  hκ₀ := one_pos
  hδmax := zero_lt_one
  hδ := fun _ _ => le_rfl
  hg := fun _ _ => one_pos
  curv := fun _ _ => freeModel_curv
 
/-- Non-vacuity: the same model satisfies `BakryEmery` with variance `1/2` and Dirichlet integral `1`. -/
theorem freeModel_bakryEmery :
    BakryEmery (fun (_ : Unit) (K : ℝ) => K ≤ 2) (fun _ => (1 : ℝ) / 2) (fun _ => 1) := by
-- W2 PROOF BEGIN W2.W2cR.freeModel_bakryEmery
  intro i K _ h
  change K ≤ 2 at h
  change K * (1 / 2 : ℝ) ≤ 1
  linarith
-- W2 PROOF END W2.W2cR.freeModel_bakryEmery
 
end W2.W2cR
