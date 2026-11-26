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

public import W2.Common.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs

@[expose] public section

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
