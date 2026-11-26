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
