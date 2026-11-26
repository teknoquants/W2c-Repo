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
 
namespace W2.W2cR
 
open Matrix
 
/-- W2c-R.2 (arithmetic core). On the chaos with occupation numbers `k`, the Ornstein–Uhlenbeck
eigenvalue is `∑ k i * lam i`; it is at least `(∑ k i) * ℓ` when every first-chaos eigenvalue is `≥ ℓ`. -/
theorem gaussian_chaos_gap {n : ℕ} (lam : Fin n → ℝ) (ℓ : ℝ) (hℓ : ∀ i, ℓ ≤ lam i)
    (k : Fin n → ℕ) :
    (∑ i, (k i : ℝ)) * ℓ ≤ ∑ i, (k i : ℝ) * lam i := by
-- W2 PROOF BEGIN W2.W2cR.gaussian_chaos_gap
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hℓ i) (Nat.cast_nonneg _)
-- W2 PROOF END W2.W2cR.gaussian_chaos_gap
 
/-- W2c-R.2 (gap form). Every chaos of order `≥ 1` has eigenvalue `≥ ℓ` when `ℓ ≥ 0`. -/
theorem gaussian_chaos_gap_pos {n : ℕ} (lam : Fin n → ℝ) (ℓ : ℝ) (hℓ0 : 0 ≤ ℓ)
    (hℓ : ∀ i, ℓ ≤ lam i) (k : Fin n → ℕ) (hk : 1 ≤ ∑ i, k i) :
    ℓ ≤ ∑ i, (k i : ℝ) * lam i := by
-- W2 PROOF BEGIN W2.W2cR.gaussian_chaos_gap_pos
  have h : (1 : ℝ) ≤ ∑ i, (k i : ℝ) := by exact_mod_cast hk
  calc
    ℓ = 1 * ℓ := (one_mul _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right h hℓ0
    _ ≤ _ := gaussian_chaos_gap lam ℓ hℓ k
-- W2 PROOF END W2.W2cR.gaussian_chaos_gap_pos
 
/-- W2c-R.4 → R.5 (quadratic-form step). A relative Hessian bound transfers the Gaussian floor. -/
theorem hessian_floor {E : Type*} (Q Q₀ nrm : E → ℝ) (κ δ : ℝ) (hδ : δ ≤ 1)
    (hfree : ∀ v, κ * nrm v ≤ Q₀ v) (hrel : ∀ v, (1 - δ) * Q₀ v ≤ Q v) :
    ∀ v, (1 - δ) * κ * nrm v ≤ Q v := by
-- W2 PROOF BEGIN W2.W2cR.hessian_floor
  intro v
  simpa only [mul_assoc] using
    (mul_le_mul_of_nonneg_left (hfree v) (sub_nonneg.mpr hδ)).trans (hrel v)
-- W2 PROOF END W2.W2cR.hessian_floor
 
/-- The same step for symmetric matrices on a finite-dimensional fibre (gauge-fixed coordinates). -/
theorem hessian_floor_matrix {n : ℕ} (H H₀ : Matrix (Fin n) (Fin n) ℝ) (κ δ : ℝ) (hδ : δ ≤ 1)
    (hfree : ∀ v : Fin n → ℝ, κ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (H₀ *ᵥ v))
    (hrel : ∀ v : Fin n → ℝ, (1 - δ) * (v ⬝ᵥ (H₀ *ᵥ v)) ≤ v ⬝ᵥ (H *ᵥ v)) :
    ∀ v : Fin n → ℝ, (1 - δ) * κ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (H *ᵥ v) := by
-- W2 PROOF BEGIN W2.W2cR.hessian_floor_matrix
  exact hessian_floor (fun v => v ⬝ᵥ (H *ᵥ v)) (fun v => v ⬝ᵥ (H₀ *ᵥ v))
    (fun v => v ⬝ᵥ v) κ δ hδ hfree hrel
-- W2 PROOF END W2.W2cR.hessian_floor_matrix
 
end W2.W2cR
