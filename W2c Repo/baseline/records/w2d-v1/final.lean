-- W2-PACKET {"audit":["W2.W2d.lattice_artifact_decay","W2.W2d.artifact_geometric_sum","W2.W2b.quadratic_coupling_cancel","W2.W2b.oscillator_variance","W2.W2b.angle_bounds","W2.W2b.gap_ratio_eq_inv_cos","W2.W2b.free_artifact_constant","W2.W2b.axis_alias_reduction","W2.W2b.axialRatio_zero","W2.W2b.axis_ratio_slope","W2.W2b.normalization_scalar","W2.W2b.axis_transport_slope","W2.W2b.alias_background_is_scalar","W2.Framework.schur_criterion","W2.Framework.uniform_score_lift","W2.Framework.schur_all_retained","W2.W2b.axial_harmonic_mean","W2.W2b.normalized_defect_slope","W2.W2b.resolvent_remainder","W2.W2b.raw_schur_limit","W2.W2b.resolvent_entry_identity","W2.W2d.free_Ca_matches","W2.W2d.retained_of_defect","W2.W2d.no_quadratic_term","W2.W2d.upward_shift_witness","W2.W2d.speed_from_squared_gap"],"editable":[],"module":null,"prelude":false,"unit":"W2d"}
module
public import Mathlib
@[expose] public section

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

-- Source W2/W2b/GapRatio.lean
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




namespace W2.W2b

/-- Cancellation before diagonalizing the free Hamiltonian, for one field component. -/
theorem quadratic_coupling_cancel (g e b : ℝ) (hg : g ≠ 0) :
    g ^ 2 / 2 * (e / g) ^ 2 + (g * b) ^ 2 / (2 * g ^ 2) = (e ^ 2 + b ^ 2) / 2 := by
-- W2 PROOF BEGIN W2.W2b.quadratic_coupling_cancel
  field_simp
-- W2 PROOF END W2.W2b.quadratic_coupling_cancel

/-- A positive harmonic frequency fixes the variance of its normalized position Gaussian. -/
theorem oscillator_variance (ω v : ℝ) (hω : 0 < ω) :
    2 * ω * v = 1 ↔ v = 1 / (2 * ω) := by
-- W2 PROOF BEGIN W2.W2b.oscillator_variance
  rw [eq_div_iff (by positivity : 2 * ω ≠ 0), mul_comm v]
-- W2 PROOF END W2.W2b.oscillator_variance

theorem angle_bounds (L : ℕ) (hL : 4 ≤ L) :
    0 < Real.pi / L ∧ Real.pi / L ≤ Real.pi / 4 := by
-- W2 PROOF BEGIN W2.W2b.angle_bounds
  have h : (4 : ℝ) ≤ L := by exact_mod_cast hL
  exact ⟨by positivity, div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) h⟩
-- W2 PROOF END W2.W2b.angle_bounds

/-- The nonzero periodic transverse gap ratio in matched physical units. -/
theorem gap_ratio_eq_inv_cos (L : ℕ) (hL : 4 ≤ L) (a : ℝ) (ha : 0 < a) :
    (2 * Real.sin (Real.pi / L) / a) / (Real.sin (2 * (Real.pi / L)) / a) =
      1 / Real.cos (Real.pi / L) := by
-- W2 PROOF BEGIN W2.W2b.gap_ratio_eq_inv_cos
  obtain ⟨ht, ht'⟩ := angle_bounds L hL
  have hs := Real.sin_pos_of_pos_of_lt_pi ht (by linarith [Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo (show Real.pi / (L:ℝ) ∈ Set.Ioo (-(Real.pi/2)) (Real.pi/2) from
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
  rw [Real.sin_two_mul]
  field_simp
-- W2 PROOF END W2.W2b.gap_ratio_eq_inv_cos
end W2.W2b

-- Source W2/W2b/Artifact.lean
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




namespace W2.W2b

/-- The quadratic coefficient and an explicit uniform remainder on all periodic sides L ≥ 4. -/
theorem free_artifact_constant (L : ℕ) (hL : 4 ≤ L) :
    let t := Real.pi / (L : ℝ)
    |1 / Real.cos t - 1 - Real.sin (2*t)^2 / 8| ≤ 7 * Real.sin (2*t)^4 := by
-- W2 PROOF BEGIN W2.W2b.free_artifact_constant
  dsimp only
  set t := Real.pi / (L : ℝ)
  obtain ⟨hpos, hu⟩ := angle_bounds L hL
  change 0 < t at hpos
  change t ≤ Real.pi / 4 at hu
  have hhalf : 1 / 2 ≤ Real.cos t := by
    rw [← Real.cos_pi_div_three]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hpos.le (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  set h := Real.cos t
  have hh : 0 < h := by linarith
  have h1 : h ≤ 1 := Real.cos_le_one _
  have sq : Real.sin t ^ 2 = 1 - h ^ 2 := by linarith [Real.sin_sq_add_cos_sq t]
  have zsq : Real.sin (2*t) ^ 2 = 4 * (1-h) * (1+h) * h^2 := by
    rw [Real.sin_two_mul]
    change (2 * Real.sin t * h)^2 = _
    linear_combination 4 * h^2 * sq
  have ident : 1/h - 1 - Real.sin (2*t)^2/8 =
      (1-h)^2 * ((2+2*h+2*h^2+h^3)/(2*h)) := by
    rw [zsq]
    field_simp
    ring
  have rnon : 0 ≤ (2+2*h+2*h^2+h^3)/(2*h) := by positivity
  have rle : (2+2*h+2*h^2+h^3)/(2*h) ≤ 7 := by
    apply (div_le_iff₀ (by positivity : 0 < 2*h)).2
    have h2 := (pow_le_one₀ hh.le h1 : h^2 ≤ 1)
    have h3 := (pow_le_one₀ hh.le h1 : h^3 ≤ 1)
    linarith
  have bound : 1-h ≤ Real.sin (2*t)^2 := by
    rw [zsq]
    have q : 1 ≤ 4*h^2 := by nlinarith [sq_nonneg (h-1/2)]
    have j : 1 ≤ (1+h)*(4*h^2) := one_le_mul_of_one_le_of_one_le (by linarith) q
    calc
      1-h = (1-h)*1 := by ring
      _ ≤ (1-h)*((1+h)*(4*h^2)) := mul_le_mul_of_nonneg_left j (by linarith)
      _ = _ := by ring
  rw [ident, abs_of_nonneg (mul_nonneg (sq_nonneg _) rnon)]
  calc
    _ ≤ (1-h)^2 * 7 := mul_le_mul_of_nonneg_left rle (sq_nonneg _)
    _ ≤ (Real.sin (2*t)^2)^2 * 7 := by gcongr
    _ = _ := by ring
-- W2 PROOF END W2.W2b.free_artifact_constant
end W2.W2b

-- Source W2/W2b/Normalization.lean
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




namespace W2.W2b
noncomputable def axialRatio (z : ℝ) : ℝ :=
  Real.cos (z/2) + Real.sin z / 2 *
    (1 / Real.cos (z/2) + 1 / Real.sqrt (1 + Real.sin (z/2)^2) +
      1 / Real.sqrt (1 + Real.cos (z/2)^2))

/-- The complete static covariance ratio for an axial momentum and transverse component. -/
theorem axis_alias_reduction (z : ℝ) (hs : Real.sin (z/2) ≠ 0) :
    Real.sin z/2 * (1/Real.sin (z/2) + 1/Real.cos (z/2) +
      1/Real.sqrt (1 + Real.sin (z/2)^2) + 1/Real.sqrt (1 + Real.cos (z/2)^2)) = axialRatio z := by
-- W2 PROOF BEGIN W2.W2b.axis_alias_reduction
  unfold axialRatio
  have hd : Real.sin z = 2 * Real.sin (z/2) * Real.cos (z/2) := by
    convert Real.sin_two_mul (z/2) using 1
    ring_nf
  rw [hd]
  field_simp [hs]
  ring
-- W2 PROOF END W2.W2b.axis_alias_reduction

@[simp] theorem axialRatio_zero : axialRatio 0 = 1 := by
-- W2 PROOF BEGIN W2.W2b.axialRatio_zero
  simp [axialRatio]
-- W2 PROOF END W2.W2b.axialRatio_zero

/-- At positive axial momentum this derivative is the one-sided physical slope. -/
theorem axis_ratio_slope : HasDerivAt axialRatio (1+1/(2*Real.sqrt 2)) 0 := by
-- W2 PROOF BEGIN W2.W2b.axis_ratio_slope
  let b := fun z : ℝ => 1/Real.cos (z/2) + 1/Real.sqrt (1+Real.sin (z/2)^2) +
    1/Real.sqrt (1+Real.cos (z/2)^2)
  have d : DifferentiableAt ℝ (fun z : ℝ => z/2) 0 := differentiableAt_id.div_const 2
  have ds := d.sin
  have dc := d.cos
  have one : DifferentiableAt ℝ (fun _ : ℝ => (1:ℝ)) 0 := differentiableAt_const _
  have ps := (one.add (ds.pow 2)).sqrt (by norm_num : (1:ℝ) + Real.sin (0/2)^2 ≠ 0)
  have pc := (one.add (dc.pow 2)).sqrt (by norm_num : (1:ℝ) + Real.cos (0/2)^2 ≠ 0)
  have hb : DifferentiableAt ℝ b 0 :=
    ((one.div dc (by norm_num)).add (one.div ps (by norm_num))).add (one.div pc (by norm_num))
  have ht := (hasDerivAt_id (0:ℝ)).div_const 2
  have hc := (Real.hasDerivAt_cos (0/2 : ℝ)).comp 0 ht
  have hp := ((Real.hasDerivAt_sin 0).div_const 2).mul hb.hasDerivAt
  change HasDerivAt (fun z : ℝ => Real.cos (z/2) + Real.sin z / 2 * b z) _ 0
  convert hc.add hp using 1
  · rfl
  · simp [b]
    ring_nf
-- W2 PROOF END W2.W2b.axis_ratio_slope

theorem normalization_scalar (g a : ℝ) (hg : 0 < g) (ha : 0 < a) :
    (2 * (g^2/(2*a))) / (g^2/(2*(2*a))) = 4 := by
-- W2 PROOF BEGIN W2.W2b.normalization_scalar
  field_simp
  ring
-- W2 PROOF END W2.W2b.normalization_scalar

theorem axis_transport_slope :
    HasDerivAt (fun z => (Real.sqrt (axialRatio z))⁻¹) (-(1+1/(2*Real.sqrt 2))/2) 0 := by
-- W2 PROOF BEGIN W2.W2b.axis_transport_slope
  have h := (axis_ratio_slope.sqrt (by simp)).inv (by simp)
  convert h using 1
  simp
  ring
-- W2 PROOF END W2.W2b.axis_transport_slope
/-- The nonzero-alias diagonal background is scalar. Singleton aliases contribute on
both perpendicular axes; each two-axis alias contributes on the missing axis. -/
theorem alias_background_is_scalar (u v : Fin 3 → ℝ) (a b : ℝ) :
    (∑ k : Fin 3, ∑ j : Fin 3, if j = k then 0 else a*u j*v j) +
      (∑ j : Fin 3, b*u j*v j) = (2*a+b)*(∑ j : Fin 3, u j*v j) := by
-- W2 PROOF BEGIN W2.W2b.alias_background_is_scalar
  simp [Fin.sum_univ_succ]
  ring
-- W2 PROOF END W2.W2b.alias_background_is_scalar

end W2.W2b

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

-- Source W2/W2b/SchurBenchmark.lean
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

open Filter Topology
namespace W2.W2b

/-- The factor 4 comes from four equal link form factors. Here T = Σ E₀/Eᵢ. -/
theorem axial_harmonic_mean (e T m R : ℝ) (ht : T ≠ 0) (hm : m ≠ 0)
    (static : R=m*T/e) : (4*e/T)/(4*m)-1 = 1/R-1 := by
-- W2 PROOF BEGIN W2.W2b.axial_harmonic_mean
  rw [static]; field_simp
-- W2 PROOF END W2.W2b.axial_harmonic_mean

theorem normalized_defect_slope : HasDerivAt (fun z => 1/axialRatio z-1)
    (-(1+1/(2*Real.sqrt 2))) 0 := by
-- W2 PROOF BEGIN W2.W2b.normalized_defect_slope
  have h := (axis_ratio_slope.inv (by simp)).sub_const 1
  simpa [one_div] using h
-- W2 PROOF END W2.W2b.normalized_defect_slope

/-- The lowest positive term bounds the harmonic resolvent remainder. -/
theorem resolvent_remainder (h w d : ℝ) (hw : 0 < w) (hd : 0 < d)
    (term : w/d ≤ h) : 0 ≤ 1/h ∧ 1/h ≤ d/w := by
-- W2 PROOF BEGIN W2.W2b.resolvent_remainder
  have hh := lt_of_lt_of_le (div_pos hw hd) term
  exact ⟨by positivity, (div_le_div_iff₀ hh hw).2 (by linarith [(div_le_iff₀ hd).mp term])⟩
-- W2 PROOF END W2.W2b.resolvent_remainder

/-- The limit uses the normalized spectral remainder 0 ≤ b ≤ (1−h)T,
where h=m/E₀ and T=Σ E₀/Eᵢ. The finite Gaussian spectral calculation supplies those data. -/
theorem raw_schur_limit {α : Type*} {l : Filter α} (h T b : α → ℝ)
    (hh : Tendsto h l (𝓝 1)) (hT : Tendsto T l (𝓝 1))
    (bounds : ∀ᶠ i in l, 0 ≤ b i ∧ b i ≤ (1-h i)*T i) :
    Tendsto (fun i => 1-(h i+b i)*T i/4) l (𝓝 (3/4)) := by
-- W2 PROOF BEGIN W2.W2b.raw_schur_limit
  have ub : Tendsto (fun i => (1-h i)*T i) l (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := (1:ℝ))).sub hh).mul hT
  have hb : Tendsto b l (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ub
      (bounds.mono (fun _ q => q.1)) (bounds.mono (fun _ q => q.2))
  convert (tendsto_const_nhds (x := (1:ℝ))).sub (((hh.add hb).mul hT).div_const 4) using 1
  norm_num
-- W2 PROOF END W2.W2b.raw_schur_limit

/-- Inverting the retained scalar resolvent gives the exact signed Schur margin. -/
theorem resolvent_entry_identity (A m correction G : ℝ) (hG : 0 < G)
    (entry : G = (A-m-correction)⁻¹) :
    A-m-correction = 1/G ∧ correction = A-m-1/G ∧ 0 < A-m-correction := by
-- W2 PROOF BEGIN W2.W2b.resolvent_entry_identity
  have eq : A-m-correction = 1/G := by rw [entry,one_div,inv_inv]
  exact ⟨eq,by linarith,eq.symm ▸ (one_div_pos.mpr hG)⟩
-- W2 PROOF END W2.W2b.resolvent_entry_identity

end W2.W2b

-- Source W2/W2d/FreeCheck.lean
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
/-- The gap-ratio benchmark; the separate normalized form defect has nonzero slope. -/
theorem free_Ca_matches (L : ℕ) (hL : 4 ≤ L) :
    let t := Real.pi / (L:ℝ)
    |1/Real.cos t-1-Real.sin (2*t)^2/8| ≤ 7*Real.sin (2*t)^4 := by
-- W2 PROOF BEGIN W2.W2d.free_Ca_matches
  exact W2.W2b.free_artifact_constant L hL
-- W2 PROOF END W2.W2d.free_Ca_matches
end W2.W2d

-- Source W2/W2d/Retained.lean
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
/-- D = retained/r − reference. Positivity of the target controls multiplication by r. -/
theorem retained_of_defect (r retained reference m V b : ℝ) (hr : 1 ≤ r)
    (hm : 0 ≤ m) (hV : 0 ≤ V) (hb : b ≤ 1) (excess : m*V ≤ reference)
    (defect : -(reference-m*V)/2-b*m*V ≤ retained/r-reference) :
    (1-b)*m*V ≤ retained := by
-- W2 PROOF BEGIN W2.W2d.retained_of_defect
  have hr' : 0 < r := by linarith
  have bound : (1-b)*m*V ≤ retained/r := by linarith
  have prod := (le_div_iff₀ hr').mp bound
  exact le_trans (le_mul_of_one_le_right (by positivity : 0 ≤ (1-b)*m*V) hr) prod
-- W2 PROOF END W2.W2d.retained_of_defect

theorem no_quadratic_term (u v k h : ℝ) (hk : k=0) (hh : h=0) : u*k+v*h=0 := by
-- W2 PROOF BEGIN W2.W2d.no_quadratic_term
  simp [hk,hh]
-- W2 PROOF END W2.W2d.no_quadratic_term

/-- A positive first-order change of spectral units is consistent with a one-sided comparison. -/
theorem upward_shift_witness (x : ℝ) (hx : 0 < x) :
    0 < (1+x)^2-1 ∧ (1+x)^2-1 = 2*x+x^2 := by
-- W2 PROOF BEGIN W2.W2d.upward_shift_witness
  constructor <;> nlinarith [sq_nonneg x]
-- W2 PROOF END W2.W2d.upward_shift_witness
/-- A two-sided estimate on squared speeds gives a speed bound when the reference is positive. -/
theorem speed_from_squared_gap (c v e : ℝ) (hc : 0 < c) (hv : 0 ≤ v)
    (bound : |v^2-c^2| ≤ e) : |v-c| ≤ e/c := by
-- W2 PROOF BEGIN W2.W2d.speed_from_squared_gap
  apply (le_div_iff₀ hc).2
  calc
    _ ≤ |v-c| * (v+c) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    _ = |v^2-c^2| := by calc
      _ = |(v-c)*(v+c)| := by rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ v+c)]
      _ = _ := by congr 1; ring
    _ ≤ e := bound
-- W2 PROOF END W2.W2d.speed_from_squared_gap

end W2.W2d

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
#print axioms W2.W2d.lattice_artifact_decay
#print axioms W2.W2d.artifact_geometric_sum
#print axioms W2.W2b.quadratic_coupling_cancel
#print axioms W2.W2b.oscillator_variance
#print axioms W2.W2b.angle_bounds
#print axioms W2.W2b.gap_ratio_eq_inv_cos
#print axioms W2.W2b.free_artifact_constant
#print axioms W2.W2b.axis_alias_reduction
#print axioms W2.W2b.axialRatio_zero
#print axioms W2.W2b.axis_ratio_slope
#print axioms W2.W2b.normalization_scalar
#print axioms W2.W2b.axis_transport_slope
#print axioms W2.W2b.alias_background_is_scalar
#print axioms W2.Framework.schur_criterion
#print axioms W2.Framework.uniform_score_lift
#print axioms W2.Framework.schur_all_retained
#print axioms W2.W2b.axial_harmonic_mean
#print axioms W2.W2b.normalized_defect_slope
#print axioms W2.W2b.resolvent_remainder
#print axioms W2.W2b.raw_schur_limit
#print axioms W2.W2b.resolvent_entry_identity
#print axioms W2.W2d.free_Ca_matches
#print axioms W2.W2d.retained_of_defect
#print axioms W2.W2d.no_quadratic_term
#print axioms W2.W2d.upward_shift_witness
#print axioms W2.W2d.speed_from_squared_gap
#eval "W2 packet 0739fb79df7fc70222db2a5bb762b084e051c231800b70ce685c715205874fa6"
