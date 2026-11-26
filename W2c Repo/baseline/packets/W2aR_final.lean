-- W2-PACKET {"audit":["W2.W2aR.stepBounds","W2.W2aR.calibration_floor","W2.W2aR.clockEstimate","W2.W2aR.clock_step_bound","W2.W2aR.product_ratio","W2.W2aR.initial_small","W2.W2aR.deviation","W2.W2aR.clock_product_telescope","W2.W2aR.physical_clock_composes","W2.W2aR.physical_product","W2.W2aR.derivative_step","W2.W2aR.cubic_speed","W2.W2aR.isotropic_telescopes","W2.W2aR.drift_split","W2.W2aR.gamma_prod","W2.W2aR.drift_gamma_identity","W2.W2aR.drift_asymptotic","W2.W2aR.drift_iff_kappa_ne_zero","W2.W2aR.first_order_compat","W2.W2aR.no_regular_clock","W2.W2aR.step_error_schemeA","W2.W2aR.combineFactors","W2.W2aR.step_error_schemeB","W2.W2aR.intermediate_step_count","W2.W2aR.sum_squares_running","W2.W2aR.sum_artifacts","W2.W2aR.large_field","W2.W2aR.loss_log","W2.W2aR.transfer_bound","W2.W2aR.eig_scale","W2.W2aR.eigval_scale","W2.W2aR.time_unit_scaling","W2.W2aR.kinetic_ratio_clock","W2.Common.cos_le_quartic","W2.Common.sin_le_quintic","W2.Common.free_clock_sinc_bounds","W2.Common.A_enclosure","W2.Research.gap_shift_invariant","W2.Research.kernel_group_dependence","W2.Research.local_shift_derivative","W2.Research.reciprocal_remainder"],"editable":[],"module":null,"prelude":false,"unit":"W2aR"}
module
public import Mathlib
@[expose] public section

-- Source W2/Common/Basic.lean
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




/-! Shared W2a-R conventions. Every clock takes the **squared** coupling `x = g²`.
Index `k` increases from the ultraviolet toward the infrared. -/
namespace W2.Common

abbrev Clock := ℝ → ℝ
abbrev Trajectory := ℕ → ℝ

noncomputable def A (N : ℕ) : ℝ := 11 * (N : ℝ) * Real.log 2 / (12 * Real.pi ^ 2)

def weak (xs x : ℝ) : Prop := 0 < x ∧ x ≤ xs

noncomputable def fullClock (c : Clock) (x : ℝ) : ℝ := 1 / c x

def truncClock (c₁ x : ℝ) : ℝ := 1 - c₁ * x

/-- `speed h x z` is the speed measured after blocking with input clock `z`.
The output time unit is determined by matching to the reference at `y`. -/
noncomputable def matchedClock {ι : Type*} (c : Clock) (speed : ι → ℝ → ℝ → ℝ)
    (h : ι) (x y z : ℝ) : ℝ := speed h x z / c y

/-- Physical response once time covariance and exact preservation of speed are imposed. -/
noncomputable def physicalRatio (c : Clock) (x y z : ℝ) : ℝ := z * c x / c y

noncomputable def oneLoopBack (b a : ℝ) (n : ℕ) : ℝ := 1 / (b + a * n)

/-- Paper's quadratic product includes both endpoints `0` and `K`. -/
noncomputable def driftProduct (b a κ : ℝ) (K : ℕ) : ℝ :=
  ∏ n ∈ Finset.range (K + 1), (1 + κ * oneLoopBack b a n)

def aPlus (a B xs : ℝ) : ℝ := a + B * xs

noncomputable def stepQ (a B xs : ℝ) : ℝ := 1 / (1 - aPlus a B xs * xs)

noncomputable def clockFloor (s M xs : ℝ) : ℝ := 1 - |s| * xs - M * xs ^ 2

noncomputable def stepConstant (a B xs s M : ℝ) : ℝ :=
  (|s| * aPlus a B xs * stepQ a B xs + M * (1 + stepQ a B xs ^ 2)) /
    clockFloor s M xs

noncomputable def matchConstant (a B xs c₁ Mc : ℝ) : ℝ :=
  Mc * (1 + stepQ a B xs ^ 2) / clockFloor (-c₁) Mc xs

def blockConstant (C M xs : ℝ) : ℝ := C + M + C * M * xs ^ 2

def stepData (a B xs x y : ℝ) : Prop :=
  weak xs x ∧ weak xs y ∧ 0 ≤ B ∧ 0 < a - B * xs ∧ aPlus a B xs * xs < 1 ∧
  |1 / y - 1 / x + a| ≤ B * x

/-- Uniform remainder of a calibrated clock on the weak interval. -/
def hasRemainder (u : Clock) (xs s M : ℝ) : Prop :=
  0 ≤ M ∧ ∀ x, weak xs x → |u x - (1 + s * x)| ≤ M * x ^ 2

/-- Axial lattice momentum in units of one fine link. -/
noncomputable def p₁ (L : ℕ) : ℝ := 2 * Real.pi / L

/-- Quotient of free lattice energy `2 sin(p/2)` by continuum momentum. -/
noncomputable def freeClock (L : ℕ) : ℝ := 2 * Real.sin (p₁ L / 2) / p₁ L

/-- Squared clock from energy gaps in a fixed momentum and centre-flux sector.
The zero-momentum excitation is on the same branch as the moving excitation. -/
noncomputable def boxClockSq (L : ℕ) (E₀ Erest Emoving : ℝ) : ℝ :=
  ((Emoving - E₀) ^ 2 - (Erest - E₀) ^ 2) / (p₁ L) ^ 2

end W2.Common

-- Source W2/Common/Hypotheses.lean
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




/-! Physical and trajectory inputs used by W2a-R. The structures are predicates on
specified data. Constructing them for a particular gauge theory is a separate task. -/
namespace W2.Common

/-- R.10-type regularity on the closed squared-coupling interval, using a normalized
extension to zero. `M` is uniform in `x`. The direct and inverse remainders differ. -/
structure ClockRegularityHyp (c : Clock) (xs c₁ : ℝ) : Prop where
  cutoff_pos : 0 < xs
  normalized : c 0 = 1
  positive : ∀ x, weak xs x → 0 < c x
  smooth : ContDiffOn ℝ 2 c (Set.Icc 0 xs)
  remainder : ∃ M : ℝ, hasRemainder c xs c₁ M

/-- The extra cubic remainder in the published W2a Theorem 15, with `x = g²`. -/
def cubicClockExpansion (c : Clock) (xs c₁ : ℝ) : Prop :=
  ∃ c₂ D : ℝ, 0 ≤ D ∧ ∀ x, weak xs x →
    |c x - (1 + c₁ * x + c₂ * x ^ 2)| ≤ D * x ^ 3

/-- Hypotheses (i) and (ii) of W2a Theorem 15. `h` ranges over every admitted
incoming effective datum. `speed` is measured in physical units. -/
structure DispersionHyp {ι : Type*} (c : Clock) (speed : ι → ℝ → ℝ → ℝ)
    (xs : ℝ) : Prop where
  preserves : ∀ h x, weak xs x → speed h x 1 = c x
  time_covariant : ∀ h x z, weak xs x → 0 < z → speed h x z = z * speed h x 1

/-- Backward inverse-coupling increment, imposed stepwise through a finite weak run.
No bound on its summed losses is supplied by this structure. -/
structure RunningBoundHyp (x : Trajectory) (J : ℕ) (xs amin : ℝ) : Prop where
  amin_pos : 0 < amin
  cutoff_pos : 0 < xs
  values : ∀ k ≤ J, weak xs (x k)
  decrement : ∀ k < J, amin ≤ 1 / x k - 1 / x (k + 1)

/-- The interacting finite-box estimate R.5 as an optional input. Both constants
are chosen before the box size and the coupling. -/
def finiteVolumeBound (c : Clock) (cL : ℕ → Clock) (xs : ℝ) : Prop :=
  ∃ U V : ℝ, 0 ≤ U ∧ 0 ≤ V ∧ ∀ L : ℕ, 2 ≤ L → ∀ x, weak xs x →
    |cL L x - c x| ≤ (U + V * x ^ 2) / (L : ℝ) ^ 2

end W2.Common

-- Source W2/W2aR/Estimates.lean
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

namespace W2.W2aR
open W2.Common

structure StepBounds (a B xs x y : ℝ) : Prop where
  x_pos : 0 < x
  y_pos : 0 < y
  xs_pos : 0 < xs
  ap_pos : 0 < aPlus a B xs
  q_pos : 0 < stepQ a B xs
  inc : x ≤ y
  factor : y ≤ stepQ a B xs * x
  jump : y - x ≤ aPlus a B xs * stepQ a B xs * x ^ 2
  lower : a - B * xs ≤ 1 / x - 1 / y

theorem stepBounds {a B xs x y : ℝ} (h : stepData a B xs x y) : StepBounds a B xs x y := by
-- W2 PROOF BEGIN W2.W2aR.stepBounds
  obtain ⟨⟨hx,hxs⟩,⟨hy,hys⟩,hB,hm,hmax,hd⟩ := h
  let d := 1 / x - 1 / y
  have d0 : 0 < xs := hx.trans_le hxs
  have dmin : a - B*xs ≤ d := by dsimp [d]; linarith [(abs_le.mp hd).2, mul_le_mul_of_nonneg_left hxs hB]
  have dmax : d ≤ aPlus a B xs := by dsimp [d,aPlus]; linarith [(abs_le.mp hd).1, mul_le_mul_of_nonneg_left hxs hB]
  have hdpos := hm.trans_le dmin
  have hap := hdpos.trans_le dmax
  have hid : d * x * y = y - x := by dsimp [d]; field_simp
  have hinc : x ≤ y := by nlinarith [mul_nonneg (mul_nonneg hdpos.le hx.le) hy.le]
  have he : 0 < 1-aPlus a B xs * xs := by linarith
  have hq : 0 < stepQ a B xs := one_div_pos.mpr he
  have hxf : y ≤ stepQ a B xs * x := by
    rw [stepQ, one_div_mul_eq_div, le_div_iff₀ he]
    have hp : d*x ≤ aPlus a B xs * xs := mul_le_mul dmax hxs hx.le hap.le
    nlinarith [mul_le_mul_of_nonneg_right hp hy.le]
  refine ⟨hx,hy,d0,hap,hq,hinc,hxf,?_,dmin⟩
  calc y-x = d*x*y := hid.symm
       _ ≤ aPlus a B xs * x * (stepQ a B xs * x) := by gcongr
       _ = _ := by ring
-- W2 PROOF END W2.W2aR.stepBounds

theorem calibration_floor {u : Clock} {s M xs x : ℝ} (h : hasRemainder u xs s M)
    (hx : weak xs x) : clockFloor s M xs ≤ u x := by
-- W2 PROOF BEGIN W2.W2aR.calibration_floor
  obtain ⟨hM,hr⟩ := h
  have e := (abs_le.mp (hr x hx)).1
  have a : |s*x| ≤ |s| * xs := by rw [abs_mul,abs_of_pos hx.1]; gcongr; exact hx.2
  have b : M*x^2 ≤ M*xs^2 := by gcongr; exact hx.1.le; exact hx.2
  unfold clockFloor
  linarith [neg_abs_le (s*x)]
-- W2 PROOF END W2.W2aR.calibration_floor

theorem clockEstimate {u : Clock} {a B xs x y s M : ℝ} (step : stepData a B xs x y)
    (rest : hasRemainder u xs s M) (floorpos : 0 < clockFloor s M xs) :
    |u y / u x - 1| ≤ stepConstant a B xs s M * x^2 := by
-- W2 PROOF BEGIN W2.W2aR.clockEstimate
  have b := stepBounds step
  have lower := calibration_floor rest step.1
  have hp := floorpos.trans_le lower
  let Q := stepQ a B xs
  let C := |s| * aPlus a B xs * Q + M * (1 + Q^2)
  have hc : 0 ≤ C := by dsimp [C]; have := b.ap_pos; have : 0 < Q := b.q_pos; have := rest.1; positivity
  have d : |u y-u x| ≤ C*x^2 := by
    calc |u y-u x| = |(u y-(1+s*y)) + s*(y-x) - (u x-(1+s*x))| := by ring_nf
         _ ≤ |u y-(1+s*y)| + |s*(y-x)| + |u x-(1+s*x)| :=
           by
           rw [sub_eq_add_neg (_ + _)]
           exact (abs_add_le ..).trans (by rw [abs_neg]; gcongr; exact abs_add_le ..)
         _ ≤ M*(Q*x)^2 + |s| * (aPlus a B xs*Q*x^2) + M*x^2 := by
           rw [abs_mul,abs_of_nonneg (sub_nonneg.mpr b.inc)]
           have hy2 : y^2 ≤ (Q*x)^2 := by gcongr; exact b.y_pos.le; exact b.factor
           exact add_le_add (add_le_add ((rest.2 y step.2.1).trans (mul_le_mul_of_nonneg_left hy2 rest.1)) (mul_le_mul_of_nonneg_left b.jump (abs_nonneg s))) (rest.2 x step.1)
         _ = _ := by dsimp [C]; ring
  rw [show u y / u x - 1 = (u y-u x) / u x by field_simp, abs_div, abs_of_pos hp]
  change |u y-u x| / u x ≤ C / clockFloor s M xs * x^2
  rw [div_mul_eq_mul_div]
  exact div_le_div₀ (mul_nonneg hc (sq_nonneg _)) d floorpos lower
-- W2 PROOF END W2.W2aR.clockEstimate

end W2.W2aR

-- Source W2/W2aR/Clock.lean
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


-- W2 PROOF IMPORTS
-- W2 END IMPORTS

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

-- Source W2/W2aR/Drift.lean
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


-- W2 PROOF IMPORTS
-- W2 END IMPORTS

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

-- Source W2/W2aR/Matching.lean
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


-- W2 PROOF IMPORTS
-- W2 END IMPORTS

namespace W2.W2aR
open W2.Common

/-- W2a Lemma 6, equality of the first-order output and calibration coefficients. -/
def first_order_compat.statement : Prop :=
  ∀ κ ρ s : ℝ, κ + ρ * s = s ↔ (1 - ρ) * s = κ

/-- W2a Cor. 7 for a time-covariant response, whose input slope is one. -/
def no_regular_clock.statement : Prop :=
  ∀ κ : ℝ, κ ≠ 0 → ¬ ∃ s : ℝ, κ + 1 * s = s

/-- W2a-R.1(A). The full clock's exact matching makes the actual block error
identical to the calibration-ratio error. -/
def step_error_schemeA.statement : Prop :=
  ∀ (c : Clock) (a B xs x y c₁ Mc : ℝ), stepData a B xs x y →
    (∀ t, weak xs t → 0 < c t) → hasRemainder (fullClock c) xs (-c₁) Mc →
    0 < clockFloor (-c₁) Mc xs →
    let u := fullClock c
    let C := stepConstant a B xs (-c₁) Mc
    physicalRatio c x y (u x) = u y ∧
    |u y / u x - 1| ≤ C * x ^ 2 ∧
    |physicalRatio c x y (u x) / u x - 1| ≤ blockConstant C 0 xs * x ^ 2

/-- W2a-R.1(B). The truncated calibration has zero Taylor remainder. Its residual
against the physical response is controlled using the full reciprocal remainder.
The denominator of `matchConstant` includes `Mc * xs²`. -/
def step_error_schemeB.statement : Prop :=
  ∀ (c : Clock) (a B xs x y c₁ Mc : ℝ), stepData a B xs x y →
    (∀ t, weak xs t → 0 < c t) → hasRemainder (fullClock c) xs (-c₁) Mc →
    0 < clockFloor (-c₁) Mc xs → B * xs ≤ a / 2 →
    aPlus a B xs * xs ≤ 1 / 2 → |c₁| * xs ≤ 1 / 2 →
    let u := truncClock c₁
    let C := 6 * a * |c₁|
    let R := matchConstant a B xs c₁ Mc
    hasRemainder u xs (-c₁) 0 ∧ |u y / u x - 1| ≤ C * x ^ 2 ∧
    |physicalRatio c x y (u x) / u y - 1| ≤ R * x ^ 2 ∧
    |physicalRatio c x y (u x) / u x - 1| ≤ blockConstant C R xs * x ^ 2

end W2.W2aR

-- W2 IMPLEMENTATION
namespace W2.W2aR
open W2.Common

theorem first_order_compat : first_order_compat.statement := by
-- W2 PROOF BEGIN W2.W2aR.first_order_compat
  intro κ ρ s; constructor <;> intro h <;> linarith
-- W2 PROOF END W2.W2aR.first_order_compat

theorem no_regular_clock : no_regular_clock.statement := by
-- W2 PROOF BEGIN W2.W2aR.no_regular_clock
  rintro κ hk ⟨s,h⟩; apply hk; linarith
-- W2 PROOF END W2.W2aR.no_regular_clock

theorem step_error_schemeA : step_error_schemeA.statement := by
-- W2 PROOF BEGIN W2.W2aR.step_error_schemeA
  intro c a B xs x y c₁ Mc step hc rem floorpos
  dsimp only
  have he : physicalRatio c x y (fullClock c x) = fullClock c y := by
    simp [physicalRatio,fullClock,(hc _ step.1).ne']
  have hb := clockEstimate step rem floorpos
  exact ⟨he,hb,by simpa [he,blockConstant] using hb⟩
-- W2 PROOF END W2.W2aR.step_error_schemeA

private theorem combineFactors (f v w x xs C R : ℝ) (hv : v ≠ 0) (hw : w ≠ 0)
    (hx : 0 ≤ x) (hxs : x ≤ xs) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (cal : |w/v-1| ≤ C*x^2) (res : |f/w-1| ≤ R*x^2) :
    |f/v-1| ≤ blockConstant C R xs*x^2 := by
  let p := w/v-1
  let q := f/w-1
  have he : f/v-1 = p+q+p*q := by dsimp [p,q]; field_simp; ring
  rw [he]
  calc |p+q+p*q| ≤ |p| + |q| + |p| * |q| := by
         rw [← abs_mul]; exact (abs_add_le ..).trans (add_le_add (abs_add_le ..) le_rfl)
       _ ≤ C*x^2 + R*x^2 + (C*x^2)*(R*x^2) := by gcongr
       _ ≤ blockConstant C R xs*x^2 := by
         unfold blockConstant
         have hpow : x^2 ≤ xs^2 := by gcongr
         nlinarith only [mul_le_mul_of_nonneg_right hpow (show 0 ≤ C*R*x^2 by positivity)]

theorem step_error_schemeB : step_error_schemeB.statement := by
-- W2 PROOF BEGIN W2.W2aR.step_error_schemeB
  intro c a B xs x y c₁ Mc step hc rest hfloor hB hsmall hcs
  dsimp only
  let l := 1 - |c₁| * xs
  let d := clockFloor (-c₁) Mc xs
  let Q := stepQ a B xs
  let v := truncClock c₁
  let p := fun t => fullClock c t / v t
  have b := stepBounds step
  have hM := rest.1
  have hq : 0 < Q := b.q_pos
  have hd : 0 < d := hfloor
  have de : d = l - Mc*xs^2 := by simp [d,l,clockFloor]
  have hl : 0 < l := by dsimp [l]; linarith
  have vlo (t : ℝ) (ht : weak xs t) : l ≤ v t := by
    dsimp [v,truncClock,l]
    have he := le_abs_self (c₁*t)
    rw [abs_mul,abs_of_pos ht.1] at he
    linarith [mul_le_mul_of_nonneg_left ht.2 (abs_nonneg c₁)]
  have vp (t : ℝ) (ht : weak xs t) := hl.trans_le (vlo t ht)
  have rr : hasRemainder v xs (-c₁) 0 := by
    refine ⟨le_rfl,fun t _ => ?_⟩; simp [v,truncClock]; ring_nf
  have vf : clockFloor (-c₁) 0 xs = l := by simp [clockFloor,l]
  have hA : 0 < a := by have := step.2.2.2.1; nlinarith [mul_nonneg step.2.2.1 b.xs_pos.le]
  have hQ₂ : Q ≤ 2 := (div_le_iff₀ (by linarith : 0 < 1-aPlus a B xs*xs)).mpr (by linarith)
  have cal : |v y/v x-1| ≤ 6*a*|c₁| * x^2 := by
    apply (clockEstimate step rr (vf ▸ hl)).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    rw [stepConstant,vf,abs_neg,zero_mul,add_zero, div_le_iff₀ hl]
    have hap : aPlus a B xs ≤ 3*a/2 := by dsimp [aPlus]; linarith
    calc |c₁| * aPlus a B xs * Q ≤ |c₁| * (3*a/2)*2 := by gcongr
         _ ≤ 6*a*|c₁| * l := by dsimp [l]; nlinarith [mul_le_mul_of_nonneg_left hcs (show 0 ≤ 6*a*|c₁| by positivity)]
  have pr (t : ℝ) (ht : weak xs t) : |p t-1| ≤ Mc*t^2/l := by
    have vv := vp t ht
    have he : p t-1 = (fullClock c t-v t)/v t := by dsimp [p]; field_simp
    rw [he,abs_div,abs_of_pos vv]
    apply div_le_div₀ (by positivity) _ hl (vlo t ht)
    simpa [v,truncClock,sub_eq_add_neg] using rest.2 t ht
  have plow : d/l ≤ p x := by
    have hr := (abs_le.mp (pr x step.1)).1
    have hpow : x^2 ≤ xs^2 := by gcongr; exact b.x_pos.le; exact step.1.2
    rw [de,sub_div,div_self hl.ne']
    linarith [div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hM) hl.le]
  have ppos := (div_pos hd hl).trans_le plow
  have resid : |physicalRatio c x y (v x)/v y-1| ≤ matchConstant a B xs c₁ Mc*x^2 := by
    have e : physicalRatio c x y (v x)/v y-1 = (p y-p x)/p x := by
      dsimp [p,fullClock,physicalRatio]; field_simp [(hc _ step.1).ne',(hc _ step.2.1).ne',(vp _ step.1).ne',(vp _ step.2.1).ne']
    have hdiff : |p y-p x| ≤ Mc*(1+Q^2)*x^2/l := by
      calc |p y-p x| ≤ |p y-1| + |p x-1| := by simpa [abs_sub_comm (1:ℝ) (p x)] using abs_sub_le (p y) 1 (p x)
           _ ≤ Mc*y^2/l + Mc*x^2/l := add_le_add (pr y step.2.1) (pr x step.1)
           _ ≤ Mc*(Q*x)^2/l + Mc*x^2/l := by gcongr; exact b.y_pos.le; exact b.factor
           _ = _ := by ring
    rw [e,abs_div,abs_of_pos ppos]
    apply (div_le_div₀ (by positivity : 0 ≤ Mc*(1+Q^2)*x^2/l) hdiff (div_pos hd hl) plow).trans_eq
    change _ = (Mc*(1+Q^2)/d)*x^2
    field_simp
  refine ⟨rr,cal,resid,combineFactors _ _ _ _ _ _ _ (vp _ step.1).ne' (vp _ step.2.1).ne' b.x_pos.le step.1.2 (by positivity) ?_ cal resid⟩
  change 0 ≤ Mc * (1+Q^2) / d; positivity
-- W2 PROOF END W2.W2aR.step_error_schemeB

end W2.W2aR

-- Source W2/W2aR/Threshold.lean
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


-- W2 PROOF IMPORTS
-- W2 END IMPORTS

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

-- Source W2/W2aR/TimeUnit.lean
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


-- W2 PROOF IMPORTS
-- W2 END IMPORTS

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

-- Source W2/Common/Trig.lean
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




/-! Free axial lattice clock, shared by W2b.10 and W2a-R.5 at order zero. -/
namespace W2.Common

/-- The quartic cosine upper polynomial follows by integration from the cubic sine lower bound. -/
private theorem cos_le_quartic {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  let f (t : ℝ) := 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t
  have hd (t : ℝ) : deriv f t = -t + t ^ 3 / 6 + Real.sin t := by
    simp (disch := fun_prop) [f]
    ring
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop)
    · exact fun _ _ => by dsimp [f]; fun_prop
    · intro t ht
      rw [hd]
      have ht' : 0 ≤ t := interior_subset ht
      linarith [Real.sin_ge_sub_cube ht']
  have he := hm (show (0 : ℝ) ∈ Set.Ici 0 by simp) hx hx
  simpa [f, sub_nonneg] using he

private theorem sin_le_quintic {x : ℝ} (hx : 0 ≤ x) :
    Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  let f (t : ℝ) := t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t
  have hd (t : ℝ) : deriv f t = 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t := by
    simp (disch := fun_prop) [f]
    ring
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop)
    · exact fun _ _ => by dsimp [f]; fun_prop
    · intro t ht
      rw [hd]
      exact sub_nonneg.mpr (cos_le_quartic (interior_subset ht))
  have he := hm (show (0 : ℝ) ∈ Set.Ici 0 by simp) hx hx
  simpa [f, sub_nonneg] using he

/-- For every periodic side `L ≥ 2`, the free clock is exactly sinc. Its error after
subtracting `1 − (π/L)²/6` is between zero and `(π/L)⁴/120`. The last clause
recovers its square from free dispersion for any energy origin and rest mass. -/
theorem free_clock_sinc_bounds (L : ℕ) (hL : 2 ≤ L) :
    let t := Real.pi / (L : ℝ)
    freeClock L = Real.sin t / t ∧
      0 ≤ freeClock L - (1 - t ^ 2 / 6) ∧
      freeClock L - (1 - t ^ 2 / 6) ≤ t ^ 4 / 120 ∧
      (∀ E₀ m : ℝ, 0 ≤ m → boxClockSq L E₀ (E₀ + m)
        (E₀ + Real.sqrt (m ^ 2 + (2 * Real.sin (p₁ L / 2)) ^ 2)) = (freeClock L) ^ 2) := by
-- W2 PROOF BEGIN W2.Common.free_clock_sinc_bounds
  let t := Real.pi / (L : ℝ)
  change freeClock L = Real.sin t / t ∧ _
  have hL' : 0 < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have ht : 0 < t := div_pos Real.pi_pos hL'
  have hp : p₁ L = 2 * t := by unfold p₁ t; ring
  have he : freeClock L = Real.sin t / t := by
    rw [freeClock, hp, show 2 * t / 2 = t by ring]
    field_simp
  rw [he]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · apply sub_nonneg.mpr
    apply (le_div_iff₀ ht).mpr
    linarith only [Real.sin_ge_sub_cube ht.le, show (1 - t ^ 2 / 6) * t = t - t ^ 3 / 6 by ring]
  · apply sub_le_iff_le_add.mpr
    apply (div_le_iff₀ ht).mpr
    linarith only [sin_le_quintic ht.le,
      show (t ^ 4 / 120 + (1 - t ^ 2 / 6)) * t = t - t ^ 3 / 6 + t ^ 5 / 120 by ring]
  · intro E₀ m _
    rw [← he, boxClockSq, freeClock, add_sub_cancel_left, add_sub_cancel_left,
      Real.sq_sqrt (by positivity), add_sub_cancel_left, div_pow]
-- W2 PROOF END W2.Common.free_clock_sinc_bounds

end W2.Common

-- Source W2/Common/Constants.lean
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


-- W2 PROOF IMPORTS
-- W2 END IMPORTS

namespace W2.Common

/-- W2a Def. 1, §8. Both rational intervals have width `10⁻⁹`. -/
def A_enclosure.statement : Prop :=
  128755903 / 10^9 < A 2 ∧ A 2 < 128755904 / 10^9 ∧
  193133855 / 10^9 < A 3 ∧ A 3 < 193133856 / 10^9

end W2.Common

-- W2 IMPLEMENTATION
namespace W2.Common
theorem A_enclosure : A_enclosure.statement := by
-- W2 PROOF BEGIN W2.Common.A_enclosure
  have hp := Real.pi_pos
  have hl := Real.log_two_gt_d9
  have hu := Real.log_two_lt_d9
  have hp₁ := Real.pi_gt_d20
  have hp₂ := Real.pi_lt_d20
  have hsq₁ := mul_self_lt_mul_self (by norm_num : (0:ℝ) ≤ 3.14159265358979323846) hp₁
  have hsq₂ := mul_self_lt_mul_self hp.le hp₂
  unfold A_enclosure.statement A
  norm_num only [Nat.cast_ofNat]
  have hd : 0 < 12*Real.pi^2 := by positivity
  constructor
  · apply (lt_div_iff₀ hd).mpr; nlinarith only [hsq₂,hl]
  constructor
  · apply (div_lt_iff₀ hd).mpr; nlinarith only [hsq₁,hu]
  constructor
  · apply (lt_div_iff₀ hd).mpr; nlinarith only [hsq₂,hl]
  · apply (div_lt_iff₀ hd).mpr; nlinarith only [hsq₁,hu]
-- W2 PROOF END W2.Common.A_enclosure

end W2.Common

-- Source W2/Research/ClockSupplement.lean
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

namespace W2.Research
theorem gap_shift_invariant (rest moving vacuum shift p : ℝ) :
    (((moving+shift)-(vacuum+shift))^2-((rest+shift)-(vacuum+shift))^2)/p^2 =
    ((moving-vacuum)^2-(rest-vacuum)^2)/p^2 := by
-- W2 PROOF BEGIN W2.Research.gap_shift_invariant
  ring
-- W2 PROOF END W2.Research.gap_shift_invariant

theorem kernel_group_dependence (I₁ I₂ N : ℝ) (hN : N ≠ 0) :
    -4*N*((1-1/N^2)*I₁/24-7*I₂/288+(I₂/3-I₁/6)/48+(4*I₂-8*I₁/3)/128)
      = -(5*I₁+4*I₂)/72*N+(I₁/6)/N := by
-- W2 PROOF BEGIN W2.Research.kernel_group_dependence
  field_simp [hN]; ring
-- W2 PROOF END W2.Research.kernel_group_dependence

theorem local_shift_derivative (F d : ℝ → ℝ) (δ : ℝ) (hF : HasDerivAt F 0 0)
    (hF₀ : F 0 = 1) (hd : HasDerivAt d (-δ) 0) :
    HasDerivAt (fun x => F x*d x) (-δ) 0 := by
-- W2 PROOF BEGIN W2.Research.local_shift_derivative
  simpa [hF₀,Pi.mul_def] using hF.mul hd
-- W2 PROOF END W2.Research.local_shift_derivative

theorem reciprocal_remainder (c : ℝ → ℝ) (a M m xs : ℝ) (hm : 0 < m) (hM : 0 ≤ M)
    (floorBound : ∀ x ∈ Set.Icc 0 xs, m ≤ c x)
    (remainder : ∀ x ∈ Set.Icc 0 xs, |c x-(1+a*x)| ≤ M*x^2) :
    ∀ x ∈ Set.Icc 0 xs, |1/c x-(1-a*x)| ≤ ((a^2+(1+ |a| * xs)*M)/m)*x^2 := by
-- W2 PROOF BEGIN W2.Research.reciprocal_remainder
  intro x hx
  have hx₀ : 0 ≤ x := hx.1
  have hxs : 0 ≤ xs := hx₀.trans hx.2
  have hc : 0 < c x := hm.trans_le (floorBound x hx)
  have factor : |1-a*x| ≤ 1+ |a| * xs := calc
    |1-a*x| ≤ |(1 : ℝ)|+ |a*x| := abs_sub _ _
    _ ≤ 1+ |a| * xs := by
      rw [abs_one,abs_mul,abs_of_nonneg hx₀]
      exact add_le_add_right (mul_le_mul_of_nonneg_left hx.2 (abs_nonneg _)) _
  have algebra : 1-c x*(1-a*x)=a^2*x^2-(c x-(1+a*x))*(1-a*x) := by ring
  have num : |1-c x*(1-a*x)| ≤ (a^2+(1+ |a| * xs)*M)*x^2 := calc
    _ = _ := congrArg abs algebra
    _ ≤ |a^2*x^2|+ |(c x-(1+a*x))*(1-a*x)| := abs_sub _ _
    _ ≤ a^2*x^2+(M*x^2)*(1+ |a| * xs) := by
      rw [abs_of_nonneg (mul_nonneg (sq_nonneg a) (sq_nonneg x)),abs_mul]
      exact add_le_add_right (mul_le_mul (remainder x hx) factor (abs_nonneg _) (mul_nonneg hM (sq_nonneg _))) _
    _ = _ := by ring
  have q : 1/c x-(1-a*x)=(1-c x*(1-a*x))/c x := by field_simp
  rw [q,abs_div,abs_of_pos hc]
  calc
    _ ≤ ((a^2+(1+ |a| * xs)*M)*x^2)/c x := div_le_div_of_nonneg_right num hc.le
    _ ≤ ((a^2+(1+ |a| * xs)*M)*x^2)/m := div_le_div_of_nonneg_left (by positivity) hm (floorBound x hx)
    _ = _ := by ring
-- W2 PROOF END W2.Research.reciprocal_remainder
end W2.Research

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
#print axioms W2.W2aR.stepBounds
#print axioms W2.W2aR.calibration_floor
#print axioms W2.W2aR.clockEstimate
#print axioms W2.W2aR.clock_step_bound
#print axioms W2.W2aR.product_ratio
#print axioms W2.W2aR.initial_small
#print axioms W2.W2aR.deviation
#print axioms W2.W2aR.clock_product_telescope
#print axioms W2.W2aR.physical_clock_composes
#print axioms W2.W2aR.physical_product
#print axioms W2.W2aR.derivative_step
#print axioms W2.W2aR.cubic_speed
#print axioms W2.W2aR.isotropic_telescopes
#print axioms W2.W2aR.drift_split
#print axioms W2.W2aR.gamma_prod
#print axioms W2.W2aR.drift_gamma_identity
#print axioms W2.W2aR.drift_asymptotic
#print axioms W2.W2aR.drift_iff_kappa_ne_zero
#print axioms W2.W2aR.first_order_compat
#print axioms W2.W2aR.no_regular_clock
#print axioms W2.W2aR.step_error_schemeA
#print axioms W2.W2aR.combineFactors
#print axioms W2.W2aR.step_error_schemeB
#print axioms W2.W2aR.intermediate_step_count
#print axioms W2.W2aR.sum_squares_running
#print axioms W2.W2aR.sum_artifacts
#print axioms W2.W2aR.large_field
#print axioms W2.W2aR.loss_log
#print axioms W2.W2aR.transfer_bound
#print axioms W2.W2aR.eig_scale
#print axioms W2.W2aR.eigval_scale
#print axioms W2.W2aR.time_unit_scaling
#print axioms W2.W2aR.kinetic_ratio_clock
#print axioms W2.Common.cos_le_quartic
#print axioms W2.Common.sin_le_quintic
#print axioms W2.Common.free_clock_sinc_bounds
#print axioms W2.Common.A_enclosure
#print axioms W2.Research.gap_shift_invariant
#print axioms W2.Research.kernel_group_dependence
#print axioms W2.Research.local_shift_derivative
#print axioms W2.Research.reciprocal_remainder
#eval "W2 packet de49eda96d77fff3c76fe3530c2b5a08817082e982c5b3d0fca47319e22af28b"
