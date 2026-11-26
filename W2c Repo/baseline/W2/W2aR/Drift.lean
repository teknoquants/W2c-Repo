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
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
-- W2 PROOF IMPORTS
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Tactic
-- W2 END IMPORTS

@[expose] public section
namespace W2.W2aR
open W2.Common Filter
open scoped Topology

/-- W2a Theorem 4, exact finite product. The condition `-b < κ` ensures positivity. -/
def drift_gamma_identity.statement : Prop :=
  ∀ (b a κ : ℝ) (K : ℕ), 0 < b → 0 < a → -b < κ →
    let q := b / a
    let σ := κ / a
    driftProduct b a κ K = Real.Gamma ((K : ℝ) + 1 + q + σ) * Real.Gamma q /
      (Real.Gamma ((K : ℝ) + 1 + q) * Real.Gamma (q + σ))

/-- W2a Theorem 4, L3 stretch target. The ultraviolet limit includes the prefactor. -/
def drift_asymptotic.statement : Prop :=
  ∀ b a κ : ℝ, 0 < b → 0 < a → -b < κ →
    Tendsto (fun K : ℕ => driftProduct b a κ K / (K : ℝ) ^ (κ / a)) atTop
      (𝓝 (Real.Gamma (b / a) / Real.Gamma (b / a + κ / a)))

/-- W2a-R.3 at coefficient level. `κ/a` is the exponent in Theorem 4. -/
def drift_iff_kappa_ne_zero.statement : Prop :=
  ∀ b a κ : ℝ, 0 < b → 0 < a → -b < κ →
    (κ / a ≠ 0 ↔ κ ≠ 0) ∧ ((¬ ∃ s : ℝ, κ + s = s) ↔ κ ≠ 0) ∧
    (κ = 0 → ∀ K, driftProduct b a κ K = 1)

end W2.W2aR

-- W2 IMPLEMENTATION
namespace W2.W2aR
open W2.Common Filter
open scoped Topology
private theorem drift_split (b a κ : ℝ) (hpos : 0 < b) (ha : 0 < a) (K : ℕ) :
    driftProduct b a κ K = (∏ j ∈ Finset.range (K+1), (b/a + κ/a + j)) /
      (∏ j ∈ Finset.range (K+1), (b/a + j)) := by
  rw [← Finset.prod_div_distrib]; apply Finset.prod_congr rfl
  intro j _
  dsimp [oneLoopBack]
  have hb : b+a*(j:ℝ) ≠ 0 := by positivity
  have hq : b/a + j ≠ 0 := by positivity
  field_simp; ring

private theorem gamma_prod (s : ℝ) (hs : 0 < s) (n : ℕ) :
    (∏ j ∈ Finset.range n, (s+j)) * Real.Gamma s = Real.Gamma ((n:ℝ)+s) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Nat.cast_succ, show (n:ℝ)+1+s = (n+s)+1 by ring,
      Real.Gamma_add_one (by positivity : (n:ℝ)+s ≠ 0), ← ih]; ring

theorem drift_gamma_identity : drift_gamma_identity.statement := by
-- W2 PROOF BEGIN W2.W2aR.drift_gamma_identity
  intro b a κ K hb ha hk
  dsimp only
  rw [drift_split b a κ hb ha]
  let q := b / a
  let r := b / a + κ / a
  have hq : 0 < q := div_pos hb ha
  have hr : 0 < r := by dsimp [r]; rw [← add_div]; exact div_pos (by linarith) ha
  have d₁ := gamma_prod r hr (K+1)
  have d₂ := gamma_prod q hq (K+1)
  push_cast at d₁ d₂
  have eqr : (K:ℝ)+1+b/a+κ/a = (K:ℝ)+1+r := by dsimp [r]; ring
  rw [eqr, ← d₁, ← d₂]
  have hn : (∏ j ∈ Finset.range (K+1), (q+j)) ≠ 0 := (Finset.prod_pos fun i _ => by positivity).ne'
  have hs := (Real.Gamma_pos_of_pos hq).ne'
  have ht := (Real.Gamma_pos_of_pos hr).ne'
  change _ / (∏ j ∈ Finset.range (K+1), (q+j)) = _
  change (∏ j ∈ Finset.range (K+1), (r+j)) / (∏ j ∈ Finset.range (K+1), (q+j)) = ((∏ j ∈ Finset.range (K+1), (r+j)) * Real.Gamma r) * Real.Gamma q / (((∏ j ∈ Finset.range (K+1), (q+j)) * Real.Gamma q) * Real.Gamma r)
  field_simp [hs,ht,hn]
-- W2 PROOF END W2.W2aR.drift_gamma_identity

theorem drift_asymptotic : drift_asymptotic.statement := by
-- W2 PROOF BEGIN W2.W2aR.drift_asymptotic
  intro b a κ hb ha hk
  let q := b / a
  let σ := κ / a
  have hq : 0 < q := div_pos hb ha
  have hr : 0 < q+σ := by dsimp [q,σ]; rw [← add_div]; exact div_pos (by linarith) ha
  apply ((Real.GammaSeq_tendsto_Gamma q).div (Real.GammaSeq_tendsto_Gamma (q+σ))
    (Real.Gamma_pos_of_pos hr).ne').congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with K hK
  have hp : 0 < (K:ℝ) := by exact_mod_cast hK
  rw [drift_split b a κ hb ha]
  change Real.GammaSeq q K / Real.GammaSeq (q+σ) K = _ / (K:ℝ)^σ
  rw [Real.GammaSeq,Real.GammaSeq,Real.rpow_add hp]
  have hprod (t : ℝ) (ht : 0 < t) : (∏ j ∈ Finset.range (K+1), (t+j)) ≠ 0 := (Finset.prod_pos fun j _ => by positivity).ne'
  have hfac : (K.factorial:ℝ) ≠ 0 := by positivity
  have hpow := (Real.rpow_pos_of_pos hp q).ne'
  have hs := (Real.rpow_pos_of_pos hp σ).ne'
  change _ = (∏ j ∈ Finset.range (K+1), (q+σ+j)) / (∏ j ∈ Finset.range (K+1), (q+j)) / _
  field_simp [hprod q hq,hprod (q+σ) hr,hfac,hpow,hs]
-- W2 PROOF END W2.W2aR.drift_asymptotic

theorem drift_iff_kappa_ne_zero : drift_iff_kappa_ne_zero.statement := by
-- W2 PROOF BEGIN W2.W2aR.drift_iff_kappa_ne_zero
  intro b a κ _ ha _
  refine ⟨by simp [ha.ne'], ?_, ?_⟩
  · constructor
    · intro h hk; exact h ⟨0, by simp [hk]⟩
    · rintro hk ⟨s,h⟩; apply hk; linarith
  · rintro rfl K; simp [driftProduct]
-- W2 PROOF END W2.W2aR.drift_iff_kappa_ne_zero

end W2.W2aR
