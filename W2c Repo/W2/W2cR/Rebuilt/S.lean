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
import W2.W2cR.Hessian
import W2.W2f.Assembly

namespace W2.W2cR

-- @result A.7 Def
def LocalBoundaryControl {I : Type*} (A : I → Prop) (bad bulk rho : I → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ i, A i → bad i ≤ C*rho i*bulk i

-- @result B.8 L1
theorem conditional_form_comparison {V W : Type*} (embed : W → V) (Q R : V → ℝ)
    (δ : ℝ) (relative : ∀ v, (1-δ)*Q v ≤ R v) : ∀ w, (1-δ)*Q (embed w) ≤ R (embed w) := by
  exact fun w => relative (embed w)

-- @result C.5 L1
theorem bloch_scalar_comparison (h s w : ℝ) (hw : 0 < w) (hs : 0 < s) :
    h-w/s ≤ 0 ↔ s*h/w ≤ 1 := by
  rw [div_le_iff₀ hw, sub_nonpos, le_div_iff₀ hs]
  simp [mul_comm]

-- @result D.2 Def
def FixedBoxHessianRemainder (err rho : ℝ → ℝ) : Prop :=
  ∃ C x₀ : ℝ, 0 < C ∧ 0 < x₀ ∧ ∀ x, 0 < x → x ≤ x₀ → err x ≤ C*rho x

-- @result D.3 Def
def MarginalCoercivity {I : Type*} (A : I → Prop)
    (meanH cov free δ : I → ℝ) : Prop :=
  ∃ m : ℝ, m < 1 ∧ ∀ i, A i → δ i ≤ m ∧ (1-δ i)*free i ≤ meanH i-cov i

-- @result D.4 Def
def WittenRemainder {I : Type*} (A : I → Prop)
    (perturb boundary reference : I → ℝ) : Prop :=
  ∃ d : ℝ, 0 ≤ d ∧ d < 1 ∧ ∀ i, A i → |perturb i|+boundary i ≤ d*reference i

-- @result D.5 Def
def HorizontalDensityFloor {I : Type*} (A : I → Prop)
    (ricci hess potentialFloor : I → ℝ) : Prop :=
  ∀ i, A i → potentialFloor i ≤ ricci i+hess i

-- @result D.8 Supplemental
theorem pinned_energy_barrier (x c : ℝ) (hx : 0<x) (hweak : x≤1/6) (hc : c≤1) :
    (3:ℝ)/2 ≤ 3*c/2+(1-c)/x := by
  have h₁ : 0 ≤ 1-c := by linarith
  have h₂ : 0 ≤ 1-3*x/2 := by linarith
  have hh := mul_nonneg h₁ h₂
  suffices hz : 3/2-3*c/2 ≤ (1-c)/x by linarith
  apply (le_div_iff₀ hx).2
  nlinarith only [hh]

-- @result D.8 Supplemental
theorem radial_curvature_floor (x c Lp Lpp s extra : ℝ)
    (hx : 0<x) (hc : 0≤c) (hs : 0 ≤ s) (he : 0≤extra)
    (h₁ : 1/x ≤ Lp) (h₂ : Lpp≤0) :
    4*c/x ≤ extra+4*(c*Lp-s*Lpp) := by
  have hprod := (div_le_iff₀ hx).mp h₁
  have hcprod := mul_le_mul_of_nonneg_left hprod hc
  have hneg := mul_nonpos_of_nonneg_of_nonpos hs h₂
  have hrem := mul_nonneg (sub_nonneg.mpr (le_trans (mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0:ℝ) ≤ 4) hneg) he)) hx.le
  apply (div_le_iff₀ hx).2
  nlinarith only [hcprod,hrem]

-- @result E.7 L2
theorem assembly_with_gap (loss retained mixed x u c : ℝ) (K : W2.W2f.W2Constants)
    (floor : 0<c) (combine : loss≤retained+mixed)
    (hret : retained≤K.CS*x^2+K.Ca*u^2)
    (transport : 0<c → mixed≤K.CM*x^2+K.Cmix*u^2) :
    loss ≤ (K.CS+K.CM)*x^2+(K.Ca+K.Cmix)*u^2 := by
  exact W2.W2f.small_field_loss loss retained mixed x u K combine hret (transport floor)

end W2.W2cR
