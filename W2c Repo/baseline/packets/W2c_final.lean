-- W2-PACKET {"audit":["W2.W2c.midpoint_preserves_product","W2.W2c.fibre_dimension_count","W2.W2c.open_dimension_count","W2.W2c.eliminated_gap_of_fibre_poincare","W2.W2c.cor_5_separation","W2.W2c.negative_control"],"editable":[],"module":null,"prelude":false,"unit":"W2c"}
module
public import Mathlib
@[expose] public section

-- Source W2/W2c/DimensionCount.lean
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

namespace W2.W2c

theorem midpoint_preserves_product {G : Type*} [Group G] (u v h : G) : (u*h⁻¹)*(h*v)=u*v := by
-- W2 PROOF BEGIN W2.W2c.midpoint_preserves_product
  group
-- W2 PROOF END W2.W2c.midpoint_preserves_product

theorem fibre_dimension_count (V d : ℕ) :
    24*V*d - 3*V*d = 21*V*d ∧ 21*V*d - 7*V*d = 14*V*d := by
-- W2 PROOF BEGIN W2.W2c.fibre_dimension_count
  simp only [Nat.mul_assoc]
  omega
-- W2 PROOF END W2.W2c.fibre_dimension_count
/-- The boundary term for an open cubical box of n coarse links per axis. -/
theorem open_dimension_count (n : ℕ) :
    3*(2*n)*(2*n+1)^2+(n+1)^3 =
    3*n*(n+1)^2+(2*n+1)^3+(14*n^3+9*n^2) := by
-- W2 PROOF BEGIN W2.W2c.open_dimension_count
  ring
-- W2 PROOF END W2.W2c.open_dimension_count

end W2.W2c

-- Source W2/W2c/EliminatedGap.lean
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

namespace W2.W2c

theorem eliminated_gap_of_fibre_poincare (g a c V T E : ℝ) (ha : 0 < a) (hc : 0 < c)
    (hV : V ≤ g^2 / c * T) (hE : g^2/(2*a)*T ≤ E) : c/(2*a)*V ≤ E := by
-- W2 PROOF BEGIN W2.W2c.eliminated_gap_of_fibre_poincare
  calc
    _ ≤ c/(2*a)*(g^2/c*T) := mul_le_mul_of_nonneg_left hV (by positivity)
    _ = _ := by field_simp
    _ ≤ E := hE
-- W2 PROOF END W2.W2c.eliminated_gap_of_fibre_poincare

theorem cor_5_separation (κ a m Λ : ℝ) (hk : 0 < κ) (ha : 0 < a) (hm : 0 < m)
    (h : κ ≤ a*Λ) : 1 - a*m/κ ≤ 1 - m/Λ := by
-- W2 PROOF BEGIN W2.W2c.cor_5_separation
  have hΛ : 0 < Λ := pos_of_mul_pos_right (lt_of_lt_of_le hk h) ha.le
  have h' : m/Λ ≤ a*m/κ := (div_le_div_iff₀ hΛ hk).2 (by nlinarith [mul_le_mul_of_nonneg_left h hm.le])
  linarith
-- W2 PROOF END W2.W2c.cor_5_separation

/-- Ratio of an inner-gradient mass bound to an outer variance lower bound. -/
theorem negative_control (s A B E V : ℝ) (hB : 0 < B) (hA : 0 ≤ A)
    (hE : E ≤ A*Real.exp (s/16)) (hV : B*Real.exp (s/4) ≤ V) :
    E/V ≤ A/B * Real.exp (-(3*s/16)) := by
-- W2 PROOF BEGIN W2.W2c.negative_control
  have hv := lt_of_lt_of_le (mul_pos hB (Real.exp_pos _)) hV
  calc
    E/V ≤ (A*Real.exp (s/16))/(B*Real.exp (s/4)) := by
      exact div_le_div₀ (by positivity) hE (by positivity) hV
    _ = A/B*(Real.exp (s/16)/Real.exp (s/4)) := by ring
    _ = _ := by rw [←Real.exp_sub]; congr 2; ring
-- W2 PROOF END W2.W2c.negative_control
end W2.W2c

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
#print axioms W2.W2c.midpoint_preserves_product
#print axioms W2.W2c.fibre_dimension_count
#print axioms W2.W2c.open_dimension_count
#print axioms W2.W2c.eliminated_gap_of_fibre_poincare
#print axioms W2.W2c.cor_5_separation
#print axioms W2.W2c.negative_control
#eval "W2 packet 33c3a8285204ab699d1f1565315994b87bf6d03f52367c3c7119f14525f8abc2"
