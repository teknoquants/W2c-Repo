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
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.LinearAlgebra.Eigenspace.Basic
-- W2 PROOF IMPORTS
public import Mathlib.Tactic
-- W2 END IMPORTS

@[expose] public section
namespace W2.W2aR

/-- A gap above the entire ground eigenspace. Multiplicity within a level is allowed. -/
def firstGap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (H : Module.End ℂ E) (e δ : ℝ) : Prop :=
  0 < δ ∧ H.HasEigenvalue (e : ℂ) ∧ H.HasEigenvalue ((e + δ : ℝ) : ℂ) ∧
    ∀ t : ℝ, H.HasEigenvalue (t : ℂ) → e ≤ t ∧ (e < t → e + δ ≤ t)

/-- W2a Prop. 1. Quantification includes self-adjoint Hamiltonians with a
multiple ground level. The gap clause applies whenever there is a second level. -/
def time_unit_scaling.statement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T V : Module.End ℂ E),
    T.IsSymmetric → V.IsSymmetric → ∀ gE gB : ℝ, 0 < gE → 0 < gB →
    let x := gE * gB
    let ξ := gE / gB
    let H := ((x / 2 : ℝ) : ℂ) • T + ((1 / x : ℝ) : ℂ) • V
    let Hξ := ((gE ^ 2 / 2 : ℝ) : ℂ) • T + ((1 / gB ^ 2 : ℝ) : ℂ) • V
    Hξ = (ξ : ℂ) • H ∧
    (∀ (e : ℝ) (v : E), Hξ.HasEigenvector ((ξ * e : ℝ) : ℂ) v ↔ H.HasEigenvector (e : ℂ) v) ∧
    (∀ e δ : ℝ, firstGap Hξ (ξ * e) (ξ * δ) ↔ firstGap H e δ)

/-- W2a Cor. 2. Squared couplings `x,y`, fine spacing `a`, and two positive clocks.
The certificate inequality fixes the orientation of the time ratio. -/
def kinetic_ratio_clock.statement : Prop :=
  ∀ x y a z z' gap m η : ℝ, 0 < x → 0 < y → 0 < a → 0 < z → 0 < z' →
    let ck := x / (2 * a)
    let ck' := y / (2 * (2 * a))
    (z * gap) / a = z * (gap / a) ∧
    2 * ck / ck' = 4 * x / y ∧
    2 * (z * ck) / (z' * ck') = (z / z') * (2 * ck / ck') ∧
    ((1 - η) * (z' * m) ≤ z * (gap / a) ↔ (1 - η) * (z' / z) * m ≤ gap / a)

end W2.W2aR

-- W2 IMPLEMENTATION
namespace W2.W2aR
open Module.End
private theorem eig_scale {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (H : Module.End ℂ E) {z : ℝ} (hz : 0 < z) (e : ℝ) (v : E) :
    ((z : ℂ) • H).HasEigenvector ((z * e : ℝ) : ℂ) v ↔ H.HasEigenvector (e : ℂ) v := by
  have hn : (z : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
  simp only [hasEigenvector_iff, mem_eigenspace_iff, LinearMap.smul_apply, Complex.ofReal_mul,
    mul_smul, smul_right_inj hn]

private theorem eigval_scale {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (H : Module.End ℂ E) {z : ℝ} (hz : 0 < z) (e : ℝ) :
    ((z : ℂ) • H).HasEigenvalue ((z * e : ℝ) : ℂ) ↔ H.HasEigenvalue (e : ℂ) := by
  constructor <;> intro he <;> obtain ⟨v,hv⟩ := he.exists_hasEigenvector
  · exact hasEigenvalue_of_hasEigenvector ((eig_scale H hz e v).mp hv)
  · exact hasEigenvalue_of_hasEigenvector ((eig_scale H hz e v).mpr hv)

theorem time_unit_scaling : time_unit_scaling.statement := by
-- W2 PROOF BEGIN W2.W2aR.time_unit_scaling
  intro E _ _ _ T V _ _ gE gB he hb
  dsimp only
  let z := gE / gB
  let H := ((gE*gB/2 : ℝ) : ℂ) • T + ((1/(gE*gB) : ℝ) : ℂ) • V
  have hz : 0 < z := div_pos he hb
  have hf : ((gE^2/2 : ℝ) : ℂ) • T + ((1/gB^2 : ℝ) : ℂ) • V = (z : ℂ) • H := by
    dsimp only [H,z]; rw [smul_add, smul_smul, smul_smul, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 2 <;> congr 1 <;> field_simp
  refine ⟨hf, ?_, ?_⟩
  · intro e v; rw [hf]; exact eig_scale H hz e v
  · intro e δ; rw [hf]; unfold firstGap
    change (0 < z*δ ∧ _ ∧ ((z : ℂ) • H).HasEigenvalue ((z*e+z*δ : ℝ) : ℂ) ∧ _) ↔ _
    rw [← mul_add, eigval_scale H hz, eigval_scale H hz, mul_pos_iff_of_pos_left hz]
    apply and_congr_right; intro _; apply and_congr_right; intro _; apply and_congr_right; intro _
    constructor
    · intro h t ht
      obtain ⟨h₁,h₂⟩ := h (z*t) ((eigval_scale H hz t).mpr ht)
      exact ⟨(mul_le_mul_iff_right₀ hz).mp h₁, fun hh => (mul_le_mul_iff_right₀ hz).mp (h₂ ((mul_lt_mul_iff_right₀ hz).mpr hh))⟩
    · intro h t ht
      have ht' : z*(t/z) = t := by field_simp
      rw [← ht'] at ht ⊢
      obtain ⟨h₁,h₂⟩ := h (t/z) ((eigval_scale H hz _).mp ht)
      exact ⟨(mul_le_mul_iff_right₀ hz).mpr h₁, fun hh => (mul_le_mul_iff_right₀ hz).mpr (h₂ ((mul_lt_mul_iff_right₀ hz).mp hh))⟩
-- W2 PROOF END W2.W2aR.time_unit_scaling

theorem kinetic_ratio_clock : kinetic_ratio_clock.statement := by
-- W2 PROOF BEGIN W2.W2aR.kinetic_ratio_clock
  intro x y a z z' gap m η hx hy ha hz hz'
  dsimp only
  refine ⟨by ring, by field_simp; ring, by field_simp, ?_⟩
  have he : (1-η)*(z'*m) = z*((1-η)*(z'/z)*m) := by field_simp
  rw [he, mul_le_mul_iff_right₀ hz]
-- W2 PROOF END W2.W2aR.kinetic_ratio_clock

end W2.W2aR
