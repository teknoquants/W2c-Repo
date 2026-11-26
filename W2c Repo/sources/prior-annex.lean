-- W2CR {"audit": ["W2.W2cR.gaussian_chaos_gap", "W2.W2cR.gaussian_chaos_gap_pos", "W2.W2cR.hessian_floor", "W2.W2cR.hessian_floor_matrix", "W2.W2cR.fibre_poincare_of_hessian", "W2.W2cR.eliminated_gap_small_field", "W2.W2cR.freeModel_curv", "W2.W2cR.freeModelHyp", "W2.W2cR.freeModel_bakryEmery", "W2.W2cR.curvature_excludes_collapse", "W2.W2cR.separation_explicit"], "mode": "check", "module": null}
module
public import Mathlib
@[expose] public section

-- Source W2/Common/Basic.lean
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




/-! Shared W2a-R conventions. Every clock takes the **squared** coupling `x = g²`.
Index `k` increases from the ultraviolet toward the infrared. -/
namespace W2.Common

abbrev Clock := ℝ → ℝ
abbrev Trajectory := ℕ → ℝ

noncomputable def A (N : ℕ) : ℝ := 11 * (N : ℝ) * Real.log 2 / (12 * Real.pi ^ 2)

def weak (xs x : ℝ) : Prop := 0 < x ∧ x ≤ xs

noncomputable def fullClock (c : Clock) (x : ℝ) : ℝ := 1 / c x

def truncClock (c₁ x : ℝ) : ℝ := 1 - c₁ * x

/-- `speed h x z` is the speed measured after blocking with input clock `z`.
The output time unit is determined by matching to the reference at `y`. -/
noncomputable def matchedClock {ι : Type*} (c : Clock) (speed : ι → ℝ → ℝ → ℝ)
    (h : ι) (x y z : ℝ) : ℝ := speed h x z / c y

/-- Physical response once time covariance and exact preservation of speed are imposed. -/
noncomputable def physicalRatio (c : Clock) (x y z : ℝ) : ℝ := z * c x / c y

noncomputable def oneLoopBack (b a : ℝ) (n : ℕ) : ℝ := 1 / (b + a * n)

/-- Paper's quadratic product includes both endpoints `0` and `K`. -/
noncomputable def driftProduct (b a κ : ℝ) (K : ℕ) : ℝ :=
  ∏ n ∈ Finset.range (K + 1), (1 + κ * oneLoopBack b a n)

def aPlus (a B xs : ℝ) : ℝ := a + B * xs

noncomputable def stepQ (a B xs : ℝ) : ℝ := 1 / (1 - aPlus a B xs * xs)

noncomputable def clockFloor (s M xs : ℝ) : ℝ := 1 - |s| * xs - M * xs ^ 2

noncomputable def stepConstant (a B xs s M : ℝ) : ℝ :=
  (|s| * aPlus a B xs * stepQ a B xs + M * (1 + stepQ a B xs ^ 2)) /
    clockFloor s M xs

noncomputable def matchConstant (a B xs c₁ Mc : ℝ) : ℝ :=
  Mc * (1 + stepQ a B xs ^ 2) / clockFloor (-c₁) Mc xs

def blockConstant (C M xs : ℝ) : ℝ := C + M + C * M * xs ^ 2

def stepData (a B xs x y : ℝ) : Prop :=
  weak xs x ∧ weak xs y ∧ 0 ≤ B ∧ 0 < a - B * xs ∧ aPlus a B xs * xs < 1 ∧
  |1 / y - 1 / x + a| ≤ B * x

/-- Uniform remainder of a calibrated clock on the weak interval. -/
def hasRemainder (u : Clock) (xs s M : ℝ) : Prop :=
  0 ≤ M ∧ ∀ x, weak xs x → |u x - (1 + s * x)| ≤ M * x ^ 2

/-- Axial lattice momentum in units of one fine link. -/
noncomputable def p₁ (L : ℕ) : ℝ := 2 * Real.pi / L

/-- Quotient of free lattice energy `2 sin(p/2)` by continuum momentum. -/
noncomputable def freeClock (L : ℕ) : ℝ := 2 * Real.sin (p₁ L / 2) / p₁ L

/-- Squared clock from energy gaps in a fixed momentum and centre-flux sector.
The zero-momentum excitation is on the same branch as the moving excitation. -/
noncomputable def boxClockSq (L : ℕ) (E₀ Erest Emoving : ℝ) : ℝ :=
  ((Emoving - E₀) ^ 2 - (Erest - E₀) ^ 2) / (p₁ L) ^ 2

end W2.Common

-- Source W2/Common/Hypotheses.lean
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




/-! Physical and trajectory inputs used by W2a-R. The structures are predicates on
specified data. Constructing them for a particular gauge theory is a separate task. -/
namespace W2.Common

/-- R.10-type regularity on the closed squared-coupling interval, using a normalized
extension to zero. `M` is uniform in `x`. The direct and inverse remainders differ. -/
structure ClockRegularityHyp (c : Clock) (xs c₁ : ℝ) : Prop where
  cutoff_pos : 0 < xs
  normalized : c 0 = 1
  positive : ∀ x, weak xs x → 0 < c x
  smooth : ContDiffOn ℝ 2 c (Set.Icc 0 xs)
  remainder : ∃ M : ℝ, hasRemainder c xs c₁ M

/-- The extra cubic remainder in the published W2a Theorem 15, with `x = g²`. -/
def cubicClockExpansion (c : Clock) (xs c₁ : ℝ) : Prop :=
  ∃ c₂ D : ℝ, 0 ≤ D ∧ ∀ x, weak xs x →
    |c x - (1 + c₁ * x + c₂ * x ^ 2)| ≤ D * x ^ 3

/-- Hypotheses (i) and (ii) of W2a Theorem 15. `h` ranges over every admitted
incoming effective datum. `speed` is measured in physical units. -/
structure DispersionHyp {ι : Type*} (c : Clock) (speed : ι → ℝ → ℝ → ℝ)
    (xs : ℝ) : Prop where
  preserves : ∀ h x, weak xs x → speed h x 1 = c x
  time_covariant : ∀ h x z, weak xs x → 0 < z → speed h x z = z * speed h x 1

/-- Backward inverse-coupling increment, imposed stepwise through a finite weak run.
No bound on its summed losses is supplied by this structure. -/
structure RunningBoundHyp (x : Trajectory) (J : ℕ) (xs amin : ℝ) : Prop where
  amin_pos : 0 < amin
  cutoff_pos : 0 < xs
  values : ∀ k ≤ J, weak xs (x k)
  decrement : ∀ k < J, amin ≤ 1 / x k - 1 / x (k + 1)

/-- The interacting finite-box estimate R.5 as an optional input. Both constants
are chosen before the box size and the coupling. -/
def finiteVolumeBound (c : Clock) (cL : ℕ → Clock) (xs : ℝ) : Prop :=
  ∃ U V : ℝ, 0 ≤ U ∧ 0 ≤ V ∧ ∀ L : ℕ, 2 ≤ L → ∀ x, weak xs x →
    |cL L x - c x| ≤ (U + V * x ^ 2) / (L : ℝ) ^ 2

end W2.Common

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

-- Source W2/W2d/Artifact.lean
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

namespace W2.W2d

theorem lattice_artifact_decay (d b last : ℝ) (n : ℕ) (hb : 0 < b) (h : 0 ≤ last)
    (run : d ≤ (n:ℝ)*(6*b*Real.log 2)) :
    last/(2:ℝ)^n ≤ last*Real.exp (-d/(6*b)) := by
-- W2 PROOF BEGIN W2.W2d.lattice_artifact_decay
  have h' : -((n:ℝ)*Real.log 2) ≤ -d/(6*b) := by
    apply (le_div_iff₀ (by positivity)).2
    linarith
  have eq : Real.exp (-((n:ℝ)*Real.log 2)) = ((2:ℝ)^n)⁻¹ := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num)]
  simpa [eq,div_eq_mul_inv] using mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h') h
-- W2 PROOF END W2.W2d.lattice_artifact_decay

theorem artifact_geometric_sum {J : ℕ} {a v : ℕ → ℝ} {aw m : ℝ}
    (hm : 0 ≤ m) (pos : ∀ k < J, 0 < a k)
    (dbl : ∀ k, k+1 < J → a (k+1) = 2*a k) (last : 0 < J → a (J-1) ≤ aw)
    (vlim : ∀ k < J, 0 ≤ v (k+1) ∧ v (k+1) ≤ m) :
    (∑ k ∈ Finset.range J, (a k*v (k+1))^2) ≤ (4/3)*(aw*m)^2 := by
-- W2 PROOF BEGIN W2.W2d.artifact_geometric_sum
  have series (n : ℕ) (hn : n < J) :
      (∑ k ∈ Finset.range (n+1), (a k*v (k+1))^2) ≤ (4/3)*(a n*m)^2 := by
    have one (k) (hk : k < J) : (a k*v (k+1))^2 ≤ (a k*m)^2 := by
      exact pow_le_pow_left₀ (mul_nonneg (pos k hk).le (vlim k hk).1)
        (mul_le_mul_of_nonneg_left (vlim k hk).2 (pos k hk).le) 2
    induction n with
    | zero => simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]; nlinarith only [one 0 hn,sq_nonneg (a 0*m)]
    | succ k ih =>
      rw [Finset.sum_range_succ]
      have h := add_le_add (ih (by omega)) (one (k+1) hn)
      rw [dbl k hn] at h ⊢
      linarith only [h]
  cases J with
  | zero => simp; positivity
  | succ n =>
    apply (series n (by omega)).trans
    have hlast : a n ≤ aw := by simpa using last (Nat.zero_lt_succ n)
    gcongr; exact mul_nonneg (pos n (by omega)).le hm
-- W2 PROOF END W2.W2d.artifact_geometric_sum


end W2.W2d

-- Source W2/W2cR/FreeGap.lean
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
 
namespace W2.W2cR
 
open Matrix
 
/-- W2c-R.2 (arithmetic core). On the chaos with occupation numbers `k`, the Ornstein–Uhlenbeck
eigenvalue is `∑ k i * lam i`; it is at least `(∑ k i) * ℓ` when every first-chaos eigenvalue is `≥ ℓ`. -/
theorem gaussian_chaos_gap {n : ℕ} (lam : Fin n → ℝ) (ℓ : ℝ) (hℓ : ∀ i, ℓ ≤ lam i)
    (k : Fin n → ℕ) :
    (∑ i, (k i : ℝ)) * ℓ ≤ ∑ i, (k i : ℝ) * lam i := by
-- W2 PROOF BEGIN W2.W2cR.gaussian_chaos_gap
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hℓ i) (Nat.cast_nonneg _)
-- W2 PROOF END W2.W2cR.gaussian_chaos_gap
 
/-- W2c-R.2 (gap form). Every chaos of order `≥ 1` has eigenvalue `≥ ℓ` when `ℓ ≥ 0`. -/
theorem gaussian_chaos_gap_pos {n : ℕ} (lam : Fin n → ℝ) (ℓ : ℝ) (hℓ0 : 0 ≤ ℓ)
    (hℓ : ∀ i, ℓ ≤ lam i) (k : Fin n → ℕ) (hk : 1 ≤ ∑ i, k i) :
    ℓ ≤ ∑ i, (k i : ℝ) * lam i := by
-- W2 PROOF BEGIN W2.W2cR.gaussian_chaos_gap_pos
  have h : (1 : ℝ) ≤ ∑ i, (k i : ℝ) := by exact_mod_cast hk
  calc
    ℓ = 1 * ℓ := (one_mul _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right h hℓ0
    _ ≤ _ := gaussian_chaos_gap lam ℓ hℓ k
-- W2 PROOF END W2.W2cR.gaussian_chaos_gap_pos
 
/-- W2c-R.4 → R.5 (quadratic-form step). A relative Hessian bound transfers the Gaussian floor. -/
theorem hessian_floor {E : Type*} (Q Q₀ nrm : E → ℝ) (κ δ : ℝ) (hδ : δ ≤ 1)
    (hfree : ∀ v, κ * nrm v ≤ Q₀ v) (hrel : ∀ v, (1 - δ) * Q₀ v ≤ Q v) :
    ∀ v, (1 - δ) * κ * nrm v ≤ Q v := by
-- W2 PROOF BEGIN W2.W2cR.hessian_floor
  intro v
  simpa only [mul_assoc] using
    (mul_le_mul_of_nonneg_left (hfree v) (sub_nonneg.mpr hδ)).trans (hrel v)
-- W2 PROOF END W2.W2cR.hessian_floor
 
/-- The same step for symmetric matrices on a finite-dimensional fibre (gauge-fixed coordinates). -/
theorem hessian_floor_matrix {n : ℕ} (H H₀ : Matrix (Fin n) (Fin n) ℝ) (κ δ : ℝ) (hδ : δ ≤ 1)
    (hfree : ∀ v : Fin n → ℝ, κ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (H₀ *ᵥ v))
    (hrel : ∀ v : Fin n → ℝ, (1 - δ) * (v ⬝ᵥ (H₀ *ᵥ v)) ≤ v ⬝ᵥ (H *ᵥ v)) :
    ∀ v : Fin n → ℝ, (1 - δ) * κ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (H *ᵥ v) := by
-- W2 PROOF BEGIN W2.W2cR.hessian_floor_matrix
  exact hessian_floor (fun v => v ⬝ᵥ (H *ᵥ v)) (fun v => v ⬝ᵥ (H₀ *ᵥ v))
    (fun v => v ⬝ᵥ v) κ δ hδ hfree hrel
-- W2 PROOF END W2.W2cR.hessian_floor_matrix
 
end W2.W2cR

-- Source W2/W2cR/Hessian.lean
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

-- Source W2/W2cR/Separation.lean
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
 
namespace W2.W2cR
 
/-- Proposition W2c-R.7: a uniform curvature floor `K > 0` on the Rayleigh quotients is
incompatible with the collapse `R s ≤ C · exp(-3s/16)` of W2c.6. -/
theorem curvature_excludes_collapse (R : ℝ → ℝ) (K C : ℝ) (hK : 0 < K)
    (hR : ∀ s, K ≤ R s) (hcollapse : ∀ s, R s ≤ C * Real.exp (-(3 * s / 16))) : False := by
-- W2 PROOF BEGIN W2.W2cR.curvature_excludes_collapse
  by_cases hC : 0 < C
  · let t := 2 * C / K
    have ht : 0 < t := div_pos (by positivity) hK
    let s := (16 / 3 : ℝ) * Real.log t
    have he : -(3 * s / 16) = -Real.log t := by dsimp [s]; ring
    have h := (hR s).trans (hcollapse s)
    rw [he, Real.exp_neg, Real.exp_log ht, ← div_eq_mul_inv, le_div_iff₀ ht] at h
    dsimp [t] at h
    field_simp [ne_of_gt hK] at h
    nlinarith
  · have h := (hR 0).trans (hcollapse 0)
    simp at h
    linarith
-- W2 PROOF END W2.W2cR.curvature_excludes_collapse
 
/-- Corollary W2c-R.8: explicit separation along a weak trajectory, `aₖ = a_K / 2 ^ n`. -/
theorem separation_explicit (κ aK m Λ d b : ℝ) (n : ℕ) (hk : 0 < κ) (haK : 0 < aK)
    (hm : 0 < m) (hb : 0 < b) (run : d ≤ (n : ℝ) * (6 * b * Real.log 2))
    (hgap : κ ≤ (aK / 2 ^ n) * Λ) :
    1 - aK * m * Real.exp (-d / (6 * b)) / κ ≤ 1 - m / Λ := by
-- W2 PROOF BEGIN W2.W2cR.separation_explicit
  have hsep := W2.W2c.cor_5_separation κ (aK / 2 ^ n) m Λ hk (by positivity) hm hgap
  have hd := W2.W2d.lattice_artifact_decay d b (aK * m) n hb (by positivity) run
  have hmul : aK / 2^n * m = (aK * m) / 2^n := by ring
  rw [hmul] at hsep
  exact (sub_le_sub_left (div_le_div_of_nonneg_right hd hk.le) 1).trans hsep
-- W2 PROOF END W2.W2cR.separation_explicit
 
end W2.W2cR

#eval Lean.versionString
#print axioms W2.W2cR.gaussian_chaos_gap
#print axioms W2.W2cR.gaussian_chaos_gap_pos
#print axioms W2.W2cR.hessian_floor
#print axioms W2.W2cR.hessian_floor_matrix
#print axioms W2.W2cR.fibre_poincare_of_hessian
#print axioms W2.W2cR.eliminated_gap_small_field
#print axioms W2.W2cR.freeModel_curv
#print axioms W2.W2cR.freeModelHyp
#print axioms W2.W2cR.freeModel_bakryEmery
#print axioms W2.W2cR.curvature_excludes_collapse
#print axioms W2.W2cR.separation_explicit
#eval "W2cR b319e107c6d891ed1626ad03f5c571ae3414ddc85f5dcea6c0d71c7a725dd75c"
