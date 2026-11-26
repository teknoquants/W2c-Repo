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

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

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
