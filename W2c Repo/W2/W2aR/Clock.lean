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
-- W2 PROOF IMPORTS
public import W2.W2aR.Estimates
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
-- W2 END IMPORTS

@[expose] public section
namespace W2.W2aR
open W2.Common

noncomputable def ratioProduct (u : Clock) (x : Trajectory) (J : ℕ) : ℝ :=
  ∏ k ∈ Finset.range J, u (x (k + 1)) / u (x k)

/-- W2a Theorem 8, including its explicit denominator and uniform remainder. -/
def clock_step_bound.statement : Prop :=
  ∀ (u : Clock) (a B xs x y s M : ℝ), stepData a B xs x y →
    hasRemainder u xs s M → 0 < clockFloor s M xs →
    |u y / u x - 1| ≤ stepConstant a B xs s M * x ^ 2

/-- W2a Cor. 9. The first clause is exact, including the empty product. The second
chooses a single cutoff before all admitted trajectories and calibrations sharing
the given constants, at a fixed terminal squared coupling `xt`. -/
def clock_product_telescope.statement : Prop :=
  (∀ (u : Clock) (x : Trajectory) (J : ℕ), (∀ k ≤ J, u (x k) ≠ 0) →
    ratioProduct u x J = u (x J) / u (x 0)) ∧
  ∀ a B xs s M xt : ℝ, weak xs xt → 0 ≤ B → 0 < a - B * xs →
    0 ≤ M → 0 < clockFloor s M xs → ∀ ε : ℝ, 0 < ε → ∃ J₀ : ℕ,
    ∀ J ≥ J₀, ∀ (u : Clock) (x : Trajectory), hasRemainder u xs s M →
    x J = xt → (∀ k ≤ J, weak xs (x k)) →
    (∀ k < J, stepData a B xs (x k) (x (k + 1))) → |ratioProduct u x J - u xt| < ε

/-- W2a Theorem 15. Speed covariance and preservation are separately quantified
physical inputs. Matching speeds at two successive squared couplings composes. -/
def physical_clock_composes.statement : Prop :=
  ∀ (ι : Type) (c : Clock) (speed : ι → ℝ → ℝ → ℝ) (xs c₁ : ℝ),
    DispersionHyp c speed xs → ClockRegularityHyp c xs c₁ →
    ∀ (h : ι) (x y : ℝ), weak xs x → weak xs y →
    (∀ z : ℝ, 0 < z → matchedClock c speed h x y z = physicalRatio c x y z) ∧
    matchedClock c speed h x y (fullClock c x) = fullClock c y

/-- W2a-R.2. The physical response is already expressed in reference-speed units.
The same cubic-error constant works for every admitted step. The same cutoff
works for every trajectory of length `J` with the stated endpoint. -/
def isotropic_telescopes.statement : Prop :=
  ∀ (c : Clock) (a B xs c₁ : ℝ), ClockRegularityHyp c xs c₁ →
    0 ≤ B → 0 < a - B * xs → aPlus a B xs * xs < 1 →
    (∃ D : ℝ, 0 ≤ D ∧ ∀ x y, stepData a B xs x y →
      |physicalRatio c x y 1 - (1 - c₁ * a * x ^ 2)| ≤ D * x ^ 3) ∧
    (∀ (x : Trajectory) (J : ℕ), (∀ k ≤ J, weak xs (x k)) →
      (∏ k ∈ Finset.range J, physicalRatio c (x k) (x (k + 1)) 1) = c (x 0) / c (x J)) ∧
    (∀ xt : ℝ, weak xs xt → ∀ ε : ℝ, 0 < ε → ∃ J₀ : ℕ, ∀ J ≥ J₀,
      ∀ x : Trajectory, x J = xt → (∀ k ≤ J, weak xs (x k)) →
      (∀ k < J, stepData a B xs (x k) (x (k + 1))) →
      |(∏ k ∈ Finset.range J, physicalRatio c (x k) (x (k + 1)) 1) - 1 / c xt| < ε)

end W2.W2aR

-- W2 IMPLEMENTATION
namespace W2.W2aR
open W2.Common Set

theorem clock_step_bound : clock_step_bound.statement := by
-- W2 PROOF BEGIN W2.W2aR.clock_step_bound
  intro u a B xs x y s M step rest floorpos
  exact clockEstimate step rest floorpos
-- W2 PROOF END W2.W2aR.clock_step_bound

private theorem product_ratio (z : ℕ → ℝ) (J : ℕ) (nz : ∀ k ≤ J, z k ≠ 0) :
    (∏ k ∈ Finset.range J, z (k+1)/z k) = z J/z 0 := by
  induction J with
  | zero => simp [nz 0 le_rfl]
  | succ J ih =>
    rw [Finset.prod_range_succ, ih (fun k hk => nz k (hk.trans (Nat.le_succ J)))]
    field_simp [nz J (Nat.le_succ J),nz 0 (Nat.zero_le _)]

private theorem initial_small (a B xs δ : ℝ) (ha : 0 < a-B*xs) (hδ : 0 < δ) :
    ∃ n : ℕ, ∀ J ≥ n, ∀ x : Trajectory, (∀ k ≤ J, weak xs (x k)) →
      (∀ k < J, stepData a B xs (x k) (x (k+1))) → x 0 < δ := by
  obtain ⟨n,hn⟩ := exists_nat_gt (1/δ/(a-B*xs))
  refine ⟨n,?_⟩
  intro J hJ x values steps
  have pref (k : ℕ) (hk : k ≤ J) : (k:ℝ)*(a-B*xs) ≤ 1/x 0-1/x k := by
    induction k with
    | zero => simp
    | succ k ih =>
      have prev := ih (by omega)
      have incr := (stepBounds (steps k (by omega))).lower
      push_cast; linarith
  have nJ : (n:ℝ) ≤ J := by exact_mod_cast hJ
  have low := (div_lt_iff₀ ha).mp (hn.trans_le nJ)
  have he : 1/δ < 1/x 0 := by linarith [pref J le_rfl,one_div_pos.mpr (values J le_rfl).1]
  exact (one_div_lt_one_div hδ (values 0 (Nat.zero_le _)).1).mp he

private theorem deviation {u : Clock} {s M xs t : ℝ} (rem : hasRemainder u xs s M)
    (ht : weak xs t) : |u t-1| ≤ (|s|+M*xs)*t := by
  have hid : u t-1 = (u t-(1+s*t))+s*t := by ring
  rw [hid]
  calc _ ≤ |u t-(1+s*t)|+|s*t| := abs_add_le .. 
       _ ≤ M*t^2+|s| * t := by rw [abs_mul,abs_of_pos ht.1]; gcongr; exact rem.2 t ht
       _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right ht.2 (mul_nonneg rem.1 ht.1.le)]

theorem clock_product_telescope : clock_product_telescope.statement := by
-- W2 PROOF BEGIN W2.W2aR.clock_product_telescope
  refine ⟨fun u x J hn => product_ratio (u ∘ x) J hn,?_⟩
  intro a B xs s M xt term _ ha hM floorpos ε hε
  let d := clockFloor s M xs
  let K := |s|+M*xs
  let C := (1+K*xs)/d*K
  have hxs := term.1.trans_le term.2
  have hd : 0 < d := floorpos
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨n,hn⟩ := initial_small a B xs (ε/(C+1)) ha (by positivity)
  refine ⟨n,?_⟩
  intro J hJ u x rem last values steps
  have hu (k) (hk : k ≤ J) : d ≤ u (x k) := calibration_floor rem (values k hk)
  have hu0 := hd.trans_le (hu 0 (Nat.zero_le _))
  have small := (lt_div_iff₀ (show 0 < C+1 by positivity)).mp (hn J hJ x values steps)
  have hxt : |u xt| ≤ 1+K*xs := by
    calc |u xt| = |(u xt-1)+1| := by ring_nf
         _ ≤ |u xt-1|+1 := by simpa using abs_add_le (u xt-1) 1
         _ ≤ _ := by linarith [deviation rem term,mul_le_mul_of_nonneg_left term.2 hK]
  change |(∏ k ∈ Finset.range J, (u ∘ x) (k+1)/(u ∘ x) k) - u xt| < ε
  rw [product_ratio (u ∘ x) J (fun k hk => (hd.trans_le (hu k hk)).ne')]
  simp only [Function.comp_apply,last]
  rw [show u xt/u (x 0)-u xt = u xt/u (x 0)*(1-u (x 0)) by field_simp,
    abs_mul,abs_div,abs_of_pos hu0,abs_sub_comm 1]
  calc _ ≤ (1+K*xs)/d*(K*x 0) := mul_le_mul (div_le_div₀ (by positivity) hxt hd (hu 0 (Nat.zero_le _)))
          (deviation rem (values 0 (Nat.zero_le _))) (abs_nonneg _) (by positivity)
       _ = C*x 0 := by dsimp [C]; ring
       _ < ε := by linarith [(values 0 (Nat.zero_le _)).1]
-- W2 PROOF END W2.W2aR.clock_product_telescope

theorem physical_clock_composes : physical_clock_composes.statement := by
-- W2 PROOF BEGIN W2.W2aR.physical_clock_composes
  intro ι c speed xs c₁ disp reg h x y hx _
  have matchEq (z : ℝ) (hz : 0 < z) : matchedClock c speed h x y z = physicalRatio c x y z := by
    simp [matchedClock,physicalRatio,disp.time_covariant h x z hx hz,disp.preserves h x hx]
  have hp := reg.positive x hx
  refine ⟨matchEq,?_⟩
  rw [matchEq (fullClock c x) (one_div_pos.mpr hp)]
  simp [physicalRatio,fullClock,hp.ne']
-- W2 PROOF END W2.W2aR.physical_clock_composes

private theorem physical_product {c : Clock} {xs c₁ : ℝ} (reg : ClockRegularityHyp c xs c₁)
    (x : Trajectory) (J : ℕ) (values : ∀ k ≤ J, weak xs (x k)) :
    (∏ k ∈ Finset.range J, physicalRatio c (x k) (x (k+1)) 1) = c (x 0)/c (x J) := by
  induction J with
  | zero => simp [(reg.positive _ (values 0 le_rfl)).ne']
  | succ J ih =>
    rw [Finset.prod_range_succ, ih (fun k hk => values k (hk.trans (Nat.le_succ J)))]
    simp only [physicalRatio,one_mul]
    field_simp [(reg.positive _ (values J (Nat.le_succ J))).ne']

end W2.W2aR

namespace W2.W2aR
open W2.Common Set

/-- Two secants share a Lipschitz bound for the derivative on the closed interval. -/
private theorem derivative_step {c : Clock} {xs s M : ℝ} (reg : ClockRegularityHyp c xs s)
    (rem : hasRemainder c xs s M) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y, weak xs x → weak xs y → x < y →
      |c y-c x-s*(y-x)| ≤ (M*x+L*y)*(y-x) := by
  let S := Icc 0 xs
  have smooth : ContDiffOn ℝ 1 (derivWithin c S) S :=
    reg.smooth.derivWithin (uniqueDiffOn_Icc reg.cutoff_pos) (by norm_num)
  obtain ⟨L,lip⟩ := smooth.exists_lipschitzOnWith (by norm_num) (convex_Icc 0 xs) isCompact_Icc
  refine ⟨L,L.coe_nonneg,?_⟩
  intro x y hx hy hxy
  have sec (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ xs) (hab : a < b) :
      ∃ t ∈ Ioo a b, derivWithin c S t = (c b-c a)/(b-a) := by
    have sub : Icc a b ⊆ S := fun _ h => ⟨ha.trans h.1,h.2.trans hb⟩
    obtain ⟨t,ht,eq⟩ := exists_deriv_eq_slope c hab (reg.smooth.continuousOn.mono sub)
      ((reg.smooth.differentiableOn (by norm_num)).mono (Ioo_subset_Icc_self.trans sub))
    exact ⟨t,ht,(derivWithin_of_mem_nhds (Icc_mem_nhds (ha.trans_lt ht.1) (ht.2.trans_le hb))).trans eq⟩
  obtain ⟨v,hv,sv⟩ := sec 0 x le_rfl hx.2 hx.1
  obtain ⟨w,hw,sw⟩ := sec x y hx.1.le hy.2 hxy
  rw [reg.normalized,sub_zero] at sv
  have vS : v ∈ S := ⟨hv.1.le,hv.2.le.trans hx.2⟩
  have wS : w ∈ S := ⟨hx.1.le.trans hw.1.le,hw.2.le.trans hy.2⟩
  have lipbound := lip.dist_le_mul w wS v vS
  rw [Real.dist_eq,Real.dist_eq,abs_of_nonneg (by linarith [hv.2,hw.1] : 0 ≤ w-v)] at lipbound
  have dv : |derivWithin c S v-s| ≤ M*x := by
    rw [sv,show (c x-1)/x-s = (c x-(1+s*x))/x by field_simp [hx.1.ne']; ring,abs_div,abs_of_pos hx.1,div_le_iff₀ hx.1]
    nlinarith only [rem.2 x hx]
  have dw : |derivWithin c S w-s| ≤ M*x+L*y := by
    calc _ ≤ |derivWithin c S w-derivWithin c S v|+|derivWithin c S v-s| := abs_sub_le .. 
         _ ≤ (L:ℝ)*(w-v)+M*x := add_le_add lipbound dv
         _ ≤ _ := by linarith [mul_le_mul_of_nonneg_left (show w-v ≤ y by linarith [hw.2,hv.1]) L.coe_nonneg]
  have dpos : 0 < y-x := sub_pos.mpr hxy
  have e := (eq_div_iff dpos.ne').mp sw
  rw [show c y-c x-s*(y-x) = (derivWithin c S w-s)*(y-x) by linarith only [e],
    abs_mul,abs_of_pos dpos]
  exact mul_le_mul_of_nonneg_right dw dpos.le

private theorem cubic_speed {c : Clock} {a B xs s : ℝ} (reg : ClockRegularityHyp c xs s)
    (hB : 0 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x y, stepData a B xs x y →
      |physicalRatio c x y 1 - (1-s*a*x^2)| ≤ D*x^3 := by
  obtain ⟨M,rem⟩ := reg.remainder
  obtain ⟨L,hL,dsec⟩ := derivative_step reg rem
  obtain ⟨m,hm,hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr reg.cutoff_pos.le) reg.smooth.continuousOn
  have hp : 0 < c m := by
    rcases eq_or_lt_of_le hm.1 with h|h
    · rw [← h,reg.normalized]; norm_num
    · exact reg.positive _ ⟨h,hm.2⟩
  let Q := stepQ a B xs
  let H := aPlus a B xs * Q
  let K := |s| + M*xs
  let C := (M+L*Q)*H + |s| * (B*Q+|a| * H) + |s*a| * K*Q
  refine ⟨|C|/c m,by positivity,?_⟩
  intro x y step
  have b := stepBounds step
  have hx := b.x_pos
  have hy := b.y_pos
  have hQ : 0 < Q := b.q_pos
  have hH : 0 ≤ H := mul_nonneg b.ap_pos.le hQ.le
  have hK : 0 ≤ K := add_nonneg (abs_nonneg _) (mul_nonneg rem.1 reg.cutoff_pos.le)
  have hc := reg.positive _ step.2.1
  have hclow : c m ≤ c y := hmin ⟨hy.le,step.2.1.2⟩
  have hxy : x < y := by
    apply lt_of_le_of_ne b.inc
    rintro rfl
    have := b.lower; linarith [step.2.2.2.1]
  have jump : y-x ≤ H*x^2 := b.jump
  have fact : y ≤ Q*x := b.factor
  have s₁ : |c y-c x-s*(y-x)| ≤ ((M+L*Q)*H)*x^3 := by
    apply (dsec x y step.1 step.2.1 hxy).trans
    calc _ ≤ (M*x+L*(Q*x))*(H*x^2) := mul_le_mul (by gcongr) jump (sub_nonneg.mpr b.inc)
             (add_nonneg (mul_nonneg rem.1 hx.le) (mul_nonneg hL (mul_nonneg hQ.le hx.le)))
         _ = _ := by ring
  let d := 1/x-1/y
  have id : d*x*y = y-x := by dsimp [d]; field_simp
  have dd : |d-a| ≤ B*x := by
    rw [← abs_neg,show -(d-a) = 1/y-1/x+a by dsimp [d]; ring]; exact step.2.2.2.2.2
  have s₂ : |(y-x)-a*x^2| ≤ (B*Q+|a| * H)*x^3 := by
    have e : y-x-a*x^2 = (d-a)*x*y+a*x*(y-x) := by linarith only [id]
    rw [e]
    calc _ ≤ |(d-a)*x*y|+|a*x*(y-x)| := abs_add_le ..
         _ ≤ (B*x)*x*(Q*x)+|a| * x*(H*x^2) := by
           simp only [abs_mul,abs_of_pos hx,abs_of_pos hy,abs_of_nonneg (sub_nonneg.mpr b.inc)]
           gcongr
         _ = _ := by ring
  have s₃ : |c y-1| ≤ K*(Q*x) := (deviation rem step.2.1).trans (mul_le_mul_of_nonneg_left fact hK)
  let e := c y-c x-s*(y-x)
  let f := y-x-a*x^2
  have eq : physicalRatio c x y 1-(1-s*a*x^2) = (-e-s*f+s*a*x^2*(c y-1))/c y := by
    dsimp [physicalRatio,e,f]; field_simp; ring
  rw [eq,abs_div,abs_of_pos hc,div_mul_eq_mul_div]
  apply div_le_div₀ (mul_nonneg (abs_nonneg _) (by positivity)) _ hp hclow
  calc _ ≤ |e|+|s| * |f|+|s*a| * x^2*|c y-1| := by
         apply (abs_add_le ..).trans
         simp only [abs_mul,abs_pow,abs_of_pos hx]
         gcongr
         simpa [sub_eq_add_neg,abs_mul] using abs_add_le (-e) (-(s*f))
       _ ≤ ((M+L*Q)*H)*x^3 + |s| * ((B*Q+|a| * H)*x^3) + |s*a| * x^2*(K*(Q*x)) :=
         add_le_add (add_le_add s₁ (mul_le_mul_of_nonneg_left s₂ (abs_nonneg _)))
           (mul_le_mul_of_nonneg_left s₃ (by positivity))
       _ = C*x^3 := by dsimp [C]; ring
       _ ≤ _ := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)

theorem isotropic_telescopes : isotropic_telescopes.statement := by
-- W2 PROOF BEGIN W2.W2aR.isotropic_telescopes
  intro c a B xs s reg hB ha _
  refine ⟨cubic_speed reg hB,physical_product reg,?_⟩
  intro xt hxt ε hε
  obtain ⟨M,rem⟩ := reg.remainder
  let C := (|s| + M*xs)/c xt
  have hc := reg.positive _ hxt
  have hC : 0 ≤ C := div_nonneg (add_nonneg (abs_nonneg _) (mul_nonneg rem.1 reg.cutoff_pos.le)) hc.le
  obtain ⟨n,hn⟩ := initial_small a B xs (ε/(C+1)) ha (by positivity)
  refine ⟨n,?_⟩
  intro J hJ x last values steps
  have small := (lt_div_iff₀ (show 0 < C+1 by positivity)).mp (hn J hJ x values steps)
  rw [physical_product reg x J values,last,← sub_div,abs_div,abs_of_pos hc]
  calc _ ≤ ((|s|+M*xs)*x 0)/c xt := div_le_div_of_nonneg_right (deviation rem (values 0 (Nat.zero_le _))) hc.le
       _ = C*x 0 := by dsimp [C]; ring
       _ < _ := by linarith [(values 0 (Nat.zero_le _)).1]
-- W2 PROOF END W2.W2aR.isotropic_telescopes

end W2.W2aR
