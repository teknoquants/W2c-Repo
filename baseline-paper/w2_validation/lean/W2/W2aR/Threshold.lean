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

public import W2.Common.Hypotheses
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Algebra.Order.Floor.Ring
-- W2 PROOF IMPORTS
public import W2.W2aR.Estimates
public import Mathlib.Analysis.SpecificLimits.Normed
-- W2 END IMPORTS

@[expose] public section
namespace W2.W2aR
open W2.Common

/-- W2a Prop. 18. Count starts inside the intermediate region. An endpoint
crossing need not stop exactly at the lower inverse-coupling threshold. -/
def intermediate_step_count.statement : Prop :=
  ∀ (M : ℕ) (u : ℕ → ℝ) (lo hi aInt : ℝ), 0 < aInt → lo ≤ hi →
    (∀ k < M, lo < u k ∧ u k ≤ hi) →
    (∀ k, k + 1 < M → aInt ≤ u k - u (k + 1)) →
    M ≤ ⌈(hi - lo) / aInt⌉₊

/-- W2a Theorem 12. `v (k+1)` is the certificate actually propagated at step k.
The running input is local. The loss sum and the ultraviolet certificate are conclusions. -/
def transfer_bound.statement : Prop :=
  ∀ (J : ℕ) (x spacing η v : ℕ → ℝ) (xs amin r C₄ CL Ca c δ aw mbar zL mIR bridge : ℝ),
    RunningBoundHyp x J xs amin → 0 ≤ r → r < 1 →
    0 ≤ C₄ → 0 ≤ CL → 0 ≤ Ca → 0 < c → 0 < δ → δ < 2 →
    0 ≤ aw → 0 ≤ mbar → 0 < zL → 0 < mIR → 0 < bridge →
    (∀ k < J, 0 < spacing k) → (∀ k, k + 1 < J → spacing (k + 1) = 2 * spacing k) →
    (0 < J → spacing (J - 1) ≤ aw) →
    (∀ k < J, 0 ≤ v (k + 1) ∧ v (k + 1) ≤ mbar) →
    (∀ k < J, 0 ≤ η k ∧ η k ≤ r ∧ η k ≤ C₄ * (x k) ^ 2 +
      CL * Real.exp (-c / ((Real.sqrt (x k)) ^ δ)) + Ca * (spacing k * v (k + 1)) ^ 2) →
    (∀ k < J, (1 - η k) * v (k + 1) ≤ v k) → zL * mIR * bridge ≤ v J →
    let D := (4 / (Real.exp 1 * c * δ)) ^ (4 / δ)
    let S := (C₄ + CL * D) * (xs ^ 2 + xs / amin) + (4 / 3) * Ca * (aw * mbar) ^ 2
    (∑' j : ℕ, (1 / 4 : ℝ) ^ j) = 4 / 3 ∧
    (∀ t : ℝ, 0 ≤ t → t ≤ r → -Real.log (1 - t) ≤ t / (1 - r)) ∧
    (∑ k ∈ Finset.range J, η k) ≤ S ∧ zL * mIR * bridge * Real.exp (-S / (1 - r)) ≤ v 0

end W2.W2aR

-- W2 IMPLEMENTATION
namespace W2.W2aR
open W2.Common

theorem intermediate_step_count : intermediate_step_count.statement := by
-- W2 PROOF BEGIN W2.W2aR.intermediate_step_count
  intro M u lo hi a ha _ inside step
  cases M with
  | zero => omega
  | succ n =>
    have bound (k : ℕ) (hk : k ≤ n) : (k:ℝ)*a ≤ u 0-u k := by
      induction k with
      | zero => simp
      | succ k ih =>
        have prev := ih (by omega)
        have inc := step k (by omega)
        push_cast; linarith
    have h : (n:ℝ) < (hi-lo)/a := (lt_div_iff₀ ha).mpr (by
      linarith [bound n le_rfl,(inside n (by omega)).1,(inside 0 (by omega)).2])
    exact Nat.lt_ceil.mpr h
-- W2 PROOF END W2.W2aR.intermediate_step_count

private theorem sum_squares_running {x : Trajectory} {J : ℕ} {xs amin : ℝ}
    (run : RunningBoundHyp x J xs amin) :
    (∑ k ∈ Finset.range J, (x k)^2) ≤ xs/amin := by
  have pref (n : ℕ) (hn : n ≤ J) :
      amin * (∑ k ∈ Finset.range n, (x k)^2) ≤ x n-x 0 := by
    induction n with
    | zero => simp
    | succ k ih =>
      have hk : k < J := by omega
      have hx := (run.values k hk.le).1
      have hy := (run.values _ hn).1
      have h := mul_le_mul_of_nonneg_right (run.decrement k hk) (mul_nonneg hx.le hy.le)
      have e : (1/x k-1/x (k+1))*(x k*x (k+1)) = x (k+1)-x k := by field_simp
      rw [e] at h
      have inc : x k ≤ x (k+1) := by linarith [mul_nonneg run.amin_pos.le (mul_nonneg hx.le hy.le)]
      have sq := mul_le_mul_of_nonneg_left inc (mul_nonneg run.amin_pos.le hx.le)
      rw [Finset.sum_range_succ]; nlinarith only [ih hk.le,h,sq]
  rw [le_div_iff₀ run.amin_pos]
  linarith [pref J le_rfl,(run.values J le_rfl).2,(run.values 0 (Nat.zero_le _)).1]

private theorem sum_artifacts {J : ℕ} {a v : ℕ → ℝ} {aw m : ℝ}
    (hm : 0 ≤ m) (pos : ∀ k < J, 0 < a k)
    (dbl : ∀ k, k+1 < J → a (k+1) = 2*a k) (last : 0 < J → a (J-1) ≤ aw)
    (vlim : ∀ k < J, 0 ≤ v (k+1) ∧ v (k+1) ≤ m) :
    (∑ k ∈ Finset.range J, (a k*v (k+1))^2) ≤ (4/3)*(aw*m)^2 := by
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

private theorem large_field {x c δ : ℝ} (hx : 0 < x) (hc : 0 < c) (hδ : 0 < δ) :
    Real.exp (-c/(Real.sqrt x)^δ) ≤ (4/(Real.exp 1*c*δ))^(4/δ) * x^2 := by
  let p := 4/δ
  let g := Real.sqrt x
  let b := g^δ
  let u := c/(p*b)
  have hp : 0 < p := by dsimp [p]; positivity
  have hg : 0 < g := Real.sqrt_pos.2 hx
  have hb : 0 < b := Real.rpow_pos_of_pos hg _
  have hu : 0 < u := div_pos hc (mul_pos hp hb)
  have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hu) hp.le
  have lu : Real.log u = Real.log c - Real.log p - δ*Real.log g := by
    rw [show u = c/(p*b) by rfl,Real.log_div hc.ne' (mul_pos hp hb).ne',
      Real.log_mul hp.ne' hb.ne',show b = g^δ by rfl,Real.log_rpow hg]; ring
  have coeff : 4/(Real.exp 1*c*δ) = p/(Real.exp 1*c) := by dsimp [p]; ring
  have lg : 2*Real.log g = Real.log x := by dsimp [g]; rw [Real.log_sqrt hx.le]; ring
  have pd : p*δ = 4 := by dsimp [p]; field_simp
  have pu : p*u = c/b := by dsimp [u]; field_simp
  change Real.exp (-c/b) ≤ (4/(Real.exp 1*c*δ))^p * x^2
  rw [coeff,← Real.log_le_log_iff (Real.exp_pos _) (mul_pos (Real.rpow_pos_of_pos (by positivity) _) (by positivity)),
      Real.log_exp,Real.log_mul (Real.rpow_pos_of_pos (by positivity) _).ne' (pow_ne_zero _ hx.ne'),
      Real.log_rpow (by positivity),Real.log_div hp.ne' (mul_pos (Real.exp_pos _) hc).ne',
      Real.log_mul (Real.exp_pos _).ne' hc.ne',Real.log_exp,Real.log_pow]
  rw [lu] at h
  rw [neg_div,← pu]
  have mult : p*δ*Real.log g = 4*Real.log g := by rw [pd]
  norm_num only [Nat.cast_ofNat] at *
  linarith only [h,mult,lg]

private theorem loss_log {r t : ℝ} (hr : r < 1) (ht : 0 ≤ t) (htr : t ≤ r) :
    -Real.log (1-t) ≤ t/(1-r) := by
  have h₁ : 0 < 1-t := by linarith
  have h₂ : 0 < 1-r := by linarith
  have q := Real.log_le_sub_one_of_pos (inv_pos.mpr h₁)
  rw [Real.log_inv] at q
  calc _ ≤ (1-t)⁻¹-1 := q
       _ = t/(1-t) := by field_simp; ring
       _ ≤ t/(1-r) := div_le_div_of_nonneg_left ht h₂ (by linarith)

theorem transfer_bound : transfer_bound.statement := by
-- W2 PROOF BEGIN W2.W2aR.transfer_bound
  intro J x a η v xs amin r C₄ CL Ca c δ aw m zL mIR bridge run hr hr1 hC hL hA hc hδ _ _ hm hz hi hb pos dbl last vlim loss prop terminal
  dsimp only
  let D := (4/(Real.exp 1*c*δ))^(4/δ)
  let S := (C₄+CL*D)*(xs^2+xs/amin)+(4/3)*Ca*(aw*m)^2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hK : 0 ≤ C₄+CL*D := by positivity
  have denom : 0 < 1-r := by linarith
  have hsum : (∑ k ∈ Finset.range J, η k) ≤ S := by
    calc _ ≤ ∑ k ∈ Finset.range J, ((C₄+CL*D)*(x k)^2+Ca*(a k*v (k+1))^2) := by
            apply Finset.sum_le_sum
            intro k hkr
            have hk := Finset.mem_range.mp hkr
            have e := mul_le_mul_of_nonneg_left (large_field (run.values k hk.le).1 hc hδ) hL
            have l := (loss k hk).2.2
            change CL*_ ≤ CL*(D*(x k)^2) at e
            linarith only [e,l]
         _ = (C₄+CL*D)*(∑ k ∈ Finset.range J,(x k)^2)+Ca*(∑ k ∈ Finset.range J,(a k*v (k+1))^2) := by
            rw [Finset.sum_add_distrib,Finset.mul_sum,Finset.mul_sum]
         _ ≤ (C₄+CL*D)*(xs/amin)+Ca*((4/3)*(aw*m)^2) := by
            exact add_le_add (mul_le_mul_of_nonneg_left (sum_squares_running run) hK)
              (mul_le_mul_of_nonneg_left (sum_artifacts hm pos dbl last vlim) hA)
         _ ≤ S := by dsimp [S]; nlinarith only [mul_nonneg hK (sq_nonneg xs)]
  have pref (n : ℕ) (hn : n ≤ J) :
      Real.exp (-(∑ k ∈ Finset.range n, η k)/(1-r))*v n ≤ v 0 := by
    induction n with
    | zero => simp
    | succ k ih =>
      have hk : k < J := by omega
      have l := loss k hk
      have tpos : 0 < 1-η k := by linarith [l.2.1]
      have e : Real.exp (-η k/(1-r)) ≤ 1-η k := by
        rw [← Real.le_log_iff_exp_le tpos]
        simpa only [neg_neg,neg_div] using neg_le_neg (loss_log hr1 l.1 l.2.1)
      rw [Finset.sum_range_succ,neg_add_rev,add_div,Real.exp_add,mul_right_comm]
      calc _ ≤ (1-η k)*v (k+1)*Real.exp (-(∑ i ∈ Finset.range k,η i)/(1-r)) :=
               mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right e (vlim k hk).1) (Real.exp_pos _).le
           _ ≤ v k*Real.exp (-(∑ i ∈ Finset.range k,η i)/(1-r)) := mul_le_mul_of_nonneg_right (prop k hk) (Real.exp_pos _).le
           _ ≤ _ := by simpa [mul_comm] using ih hk.le
  refine ⟨by rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num,
    fun t ht htr => loss_log hr1 ht htr,hsum,?_⟩
  apply le_trans _ (pref J le_rfl)
  rw [mul_comm (zL*mIR*bridge)]
  exact mul_le_mul (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (neg_le_neg hsum) denom.le))
    terminal (by positivity) (Real.exp_pos _).le
-- W2 PROOF END W2.W2aR.transfer_bound

end W2.W2aR
