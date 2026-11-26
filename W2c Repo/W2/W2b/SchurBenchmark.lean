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
public import W2.W2b.Normalization
public import W2.Framework.Schur
@[expose] public section
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
