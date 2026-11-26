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

namespace W2.W2b
open Filter Topology

/-- Switching any nonempty collection of low-momentum components to their aliases raises energy squared. -/
theorem alias_energy_separation (t : Fin 3 → ℝ) (s : Finset (Fin 3)) (hs : s.Nonempty)
    (ht : ∀ j, |t j| < Real.pi / 4) :
    (∑ j, Real.sin (t j)^2) < ∑ j, if j ∈ s then Real.cos (t j)^2 else Real.sin (t j)^2 := by
-- W2 PROOF BEGIN W2.W2b.alias_energy_separation
  have gap (j : Fin 3) : Real.sin (t j)^2 < Real.cos (t j)^2 := by
    obtain ⟨hl,hu⟩ := abs_lt.mp (ht j)
    have h := Real.cos_pos_of_mem_Ioo
      (show 2*t j ∈ Set.Ioo (-(Real.pi/2)) (Real.pi/2) from ⟨by linarith, by linarith⟩)
    rw [Real.cos_two_mul] at h
    linarith [Real.sin_sq_add_cos_sq (t j)]
  apply Finset.sum_lt_sum
  · intro j _
    split_ifs
    · exact (gap j).le
    · exact le_rfl
  · obtain ⟨j,hj⟩ := hs
    exact ⟨j, Finset.mem_univ _, by simpa [hj] using gap j⟩
-- W2 PROOF END W2.W2b.alias_energy_separation

/-- Squared free-phase bound in every direction. t = a p/2 and ρ bounds the component magnitudes. -/
theorem blocked_symbol_speed (t : Fin 3 → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ) (hr : ρ ≤ 1)
    (ht : ∀ j, |t j| ≤ ρ) (pos : 0 < ∑ j, (t j)^2) :
    (1-ρ^2/6)^2 ≤ (∑ j, Real.sin (t j)^2)/(∑ j, (t j)^2) ∧
    (∑ j, Real.sin (t j)^2)/(∑ j, (t j)^2) ≤ 1 := by
-- W2 PROOF BEGIN W2.W2b.blocked_symbol_speed
  have factor : 0 ≤ 1-ρ^2/6 := by nlinarith [(pow_le_one₀ hρ hr : ρ^2 ≤ 1)]
  have low (j : Fin 3) : (1-ρ^2/6)^2 * (t j)^2 ≤ Real.sin (t j)^2 := by
    have hu := ht j
    have hu0 := abs_nonneg (t j)
    have sqle : |t j|^2 ≤ ρ^2 := by gcongr
    have b : (1-ρ^2/6)*|t j| ≤ Real.sin |t j| := by
      nlinarith only [Real.sin_ge_sub_cube hu0, mul_le_mul_of_nonneg_right sqle hu0]
    have b' : (1-ρ^2/6)*|t j| ≤ |Real.sin (t j)| := by
      rcases le_total 0 (t j) with h | h
      · simpa [abs_of_nonneg h] using b.trans (le_abs_self (Real.sin |t j|))
      · rw [abs_of_nonpos h, Real.sin_neg] at b
        rw [abs_of_nonpos h]
        exact b.trans (neg_le_abs _)
    have u := mul_self_le_mul_self (mul_nonneg factor hu0) b'
    simpa [←sq, mul_pow, sq_abs] using u
  have upper (j : Fin 3) : Real.sin (t j)^2 ≤ (t j)^2 := by
    have h := mul_self_le_mul_self (abs_nonneg (Real.sin (t j))) (Real.abs_sin_le_abs (x:=t j))
    simpa [←sq, sq_abs] using h
  constructor
  · apply (le_div_iff₀ pos).mpr
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => low j)
  · exact (div_le_one pos).mpr (Finset.sum_le_sum (fun j _ => upper j))
-- W2 PROOF END W2.W2b.blocked_symbol_speed

/-- After factoring the lowest exponential, a finite positive spectral sum tends to its residue. -/
theorem isolated_pole_limit {ι : Type*} (s : Finset ι) (w E : ι → ℝ) (w₀ E₀ : ℝ)
    (gap : ∀ i ∈ s, E₀ < E i) :
    Tendsto (fun t : ℝ => w₀ + ∑ i ∈ s, w i * Real.exp ((E₀-E i)*t)) atTop (𝓝 w₀) := by
-- W2 PROOF BEGIN W2.W2b.isolated_pole_limit
  have one (i : ι) (hi : i ∈ s) :
      Tendsto (fun t : ℝ => w i * Real.exp ((E₀-E i)*t)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_atBot.comp
      ((tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop).const_mul_atTop_of_neg (sub_neg.mpr (gap i hi)))
    simpa [Function.comp_def] using h.const_mul (w i)
  have all := tendsto_finsetSum s one
  simpa using all.const_add w₀
-- W2 PROOF END W2.W2b.isolated_pole_limit
end W2.W2b
