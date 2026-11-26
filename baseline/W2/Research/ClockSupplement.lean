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
