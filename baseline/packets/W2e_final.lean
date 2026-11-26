-- W2-PACKET {"audit":["W2.W2e.resolvent_ratio_clock_invariant","W2.W2e.loss_of_mixed_bound","W2.Framework.schur_criterion","W2.Framework.uniform_score_lift","W2.Framework.schur_all_retained"],"editable":[],"module":null,"prelude":false,"unit":"W2e"}
module
public import Mathlib
@[expose] public section

-- Source W2/W2e/ClockInvariance.lean
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

namespace W2.W2e
/-- Clock scaling of the resolvent ratio, in a positive diagonal eigenbasis. -/
theorem resolvent_ratio_clock_invariant {ι : Type*} [Fintype ι]
    (z c A lam : ℝ) (d w : ι → ℝ) (hz : 0 < z) :
    (2*z*c)^2 * (∑ i, (w i)^2/(z*d i-z*lam))/(z*A) =
      (2*c)^2 * (∑ i, (w i)^2/(d i-lam))/A := by
-- W2 PROOF BEGIN W2.W2e.resolvent_ratio_clock_invariant
  have each (i : ι) : (w i)^2/(z*d i-z*lam) = z⁻¹*((w i)^2/(d i-lam)) := by
    rw [←mul_sub,div_eq_mul_inv,mul_inv_rev]
    ring
  simp_rw [each]
  rw [←Finset.mul_sum]
  simp [div_eq_mul_inv, mul_inv_rev]
  field_simp [hz.ne']
-- W2 PROOF END W2.W2e.resolvent_ratio_clock_invariant
end W2.W2e

-- Source W2/W2e/Loss.lean
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

namespace W2.W2e

theorem loss_of_mixed_bound (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    1-(1-a)*(1-b) ≤ a+b := by
-- W2 PROOF BEGIN W2.W2e.loss_of_mixed_bound
  nlinarith [mul_nonneg ha hb]
-- W2 PROOF END W2.W2e.loss_of_mixed_bound

end W2.W2e

-- Source W2/Framework/Schur.lean
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

-- Source W2/Research/Obligations.lean
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


/-! The case index comprises the admitted theory, finite box, RG scale, cutoff,
fibre/observable and (for spectral data) the identified branch. Constants precede cases.
These predicates express research targets. Creating a predicate supplies no witness. -/
namespace W2.Research

def uniformFibrePoincare {ι : Type*} (admitted : ι → Prop) (g V T : ι → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ i, admitted i → V i ≤ g i ^ 2 / c * T i

def uniformDefect {ι : Type*} (admitted : ι → Prop) (g a m V excess defect : ι → ℝ) : Prop :=
  ∃ S A : ℝ, 0 ≤ S ∧ 0 ≤ A ∧ ∀ i, admitted i →
    -(excess i)/2 - (S*(g i)^4 + A*(a i*m i)^2) * m i * V i ≤ defect i

def uniformTransport {ι : Type*} (admitted : ι → Prop) (weightedDerivativeError rate : ι → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ i, admitted i → weightedDerivativeError i ≤ C * rate i

def completeMismatch {ι : Type*} (admitted : ι → Prop) (coefficient coupling clock : ι → ℝ) : Prop :=
  ∃ u v : ℝ, ∀ i, admitted i → coefficient i = u * coupling i + v * clock i

def dispersionAtOneLoop {ι : Type*} (admitted : ι → Prop)
    (x a p reference measured : ι → ℝ) : Prop :=
  ∃ U V : ℝ, 0 ≤ U ∧ 0 ≤ V ∧ ∀ i, admitted i →
    |measured i - reference i| ≤ U * |reference i| * x i ^ 2 + V * (a i * p i)^2

def scoreBounds {ι : Type*} (admitted : ι → Prop) (g scoreNorm : ι → ℝ) (power : ℤ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ i, admitted i → scoreNorm i ≤ C * g i ^ power

def uniformMixedBound {ι : Type*} (admitted : ι → Prop)
    (g a m retained correction : ι → ℝ) : Prop :=
  ∃ M A : ℝ, 0 ≤ M ∧ 0 ≤ A ∧ ∀ i, admitted i →
    correction i ≤ (M * g i^4 + A * (a i * m i)^2) * retained i

def uniformScoreRoute {ι : Type*} (admitted : ι → Prop) (g loss : ι → ℝ) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ i, admitted i → loss i ≤ M * g i ^ 4

def uniformEliminated {ι : Type*} (admitted : ι → Prop) (spacing gap : ι → ℝ) : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ ∀ i, admitted i → κ ≤ spacing i * gap i

def polynomialKernelBound {ι : Type*} (admitted : ι → Prop) (distance norm : ι → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ i, admitted i → norm i * (1 + distance i)^4 ≤ C

def positiveWeakClock (c : ℝ → ℝ) (xs slope : ℝ) : Prop :=
  c 0 = 1 ∧ ContDiffOn ℝ 2 c (Set.Icc 0 xs) ∧
  ∃ floor remainder : ℝ, 0 < floor ∧ 0 ≤ remainder ∧
    ∀ x ∈ Set.Icc 0 xs, floor ≤ c x ∧ |c x-1-slope*x| ≤ remainder*x^2

/-- The trial λ, normalization and observable are part of the indexed case.
E and C denote the retained energy and nonnegative resolvent correction. -/
def uniformSignedSchur {ι : Type*} (admitted : ι → Prop)
    (g a m var E C : ι → ℝ) : Prop :=
  ∃ S A : ℝ, 0 ≤ S ∧ 0 ≤ A ∧ ∀ i, admitted i →
    (1-S*(g i)^4-A*(a i*m i)^2)*m i*var i ≤ E i-C i

end W2.Research

#eval Lean.versionString
#check W2.Research.uniformFibrePoincare
#check W2.Research.uniformDefect
#check W2.Research.uniformTransport
#check W2.Research.completeMismatch
#check W2.Research.dispersionAtOneLoop
#check W2.Research.scoreBounds
#check W2.Research.uniformMixedBound
#check W2.Research.uniformScoreRoute
#check W2.Research.uniformEliminated
#check W2.Research.polynomialKernelBound
#check W2.Research.positiveWeakClock
#check W2.Research.uniformSignedSchur
#print axioms W2.W2e.resolvent_ratio_clock_invariant
#print axioms W2.W2e.loss_of_mixed_bound
#print axioms W2.Framework.schur_criterion
#print axioms W2.Framework.uniform_score_lift
#print axioms W2.Framework.schur_all_retained
#eval "W2 packet 438aac8e070158e9596036802db92ac2729dac8c613e2e900f53dd5d3ab13224"
