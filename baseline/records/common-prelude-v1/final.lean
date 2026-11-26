-- W2-PACKET {"audit":["W2.Common.Clock","W2.Common.Trajectory","W2.Common.A","W2.Common.weak","W2.Common.fullClock","W2.Common.truncClock","W2.Common.matchedClock","W2.Common.physicalRatio","W2.Common.oneLoopBack","W2.Common.driftProduct","W2.Common.aPlus","W2.Common.stepQ","W2.Common.clockFloor","W2.Common.stepConstant","W2.Common.matchConstant","W2.Common.blockConstant","W2.Common.stepData","W2.Common.hasRemainder","W2.Common.p\u2081","W2.Common.freeClock","W2.Common.boxClockSq","W2.Common.ClockRegularityHyp","W2.Common.cubicClockExpansion","W2.Common.DispersionHyp","W2.Common.RunningBoundHyp","W2.Common.finiteVolumeBound"],"editable":[],"module":null,"prelude":true,"unit":"Common"}
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

#eval Lean.versionString
#check W2.Common.Clock
#check W2.Common.Trajectory
#check W2.Common.A
#check W2.Common.weak
#check W2.Common.fullClock
#check W2.Common.truncClock
#check W2.Common.matchedClock
#check W2.Common.physicalRatio
#check W2.Common.oneLoopBack
#check W2.Common.driftProduct
#check W2.Common.aPlus
#check W2.Common.stepQ
#check W2.Common.clockFloor
#check W2.Common.stepConstant
#check W2.Common.matchConstant
#check W2.Common.blockConstant
#check W2.Common.stepData
#check W2.Common.hasRemainder
#check W2.Common.p₁
#check W2.Common.freeClock
#check W2.Common.boxClockSq
#check W2.Common.ClockRegularityHyp
#check W2.Common.cubicClockExpansion
#check W2.Common.DispersionHyp
#check W2.Common.RunningBoundHyp
#check W2.Common.finiteVolumeBound
#print axioms W2.Common.Clock
#print axioms W2.Common.Trajectory
#print axioms W2.Common.A
#print axioms W2.Common.weak
#print axioms W2.Common.fullClock
#print axioms W2.Common.truncClock
#print axioms W2.Common.matchedClock
#print axioms W2.Common.physicalRatio
#print axioms W2.Common.oneLoopBack
#print axioms W2.Common.driftProduct
#print axioms W2.Common.aPlus
#print axioms W2.Common.stepQ
#print axioms W2.Common.clockFloor
#print axioms W2.Common.stepConstant
#print axioms W2.Common.matchConstant
#print axioms W2.Common.blockConstant
#print axioms W2.Common.stepData
#print axioms W2.Common.hasRemainder
#print axioms W2.Common.p₁
#print axioms W2.Common.freeClock
#print axioms W2.Common.boxClockSq
#print axioms W2.Common.ClockRegularityHyp
#print axioms W2.Common.cubicClockExpansion
#print axioms W2.Common.DispersionHyp
#print axioms W2.Common.RunningBoundHyp
#print axioms W2.Common.finiteVolumeBound
#eval "W2 packet c491b993a51f9683cf51922b8327b2e88b08ea2ce4182d1b492fb04157357a27"
