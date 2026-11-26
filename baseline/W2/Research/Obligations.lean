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
