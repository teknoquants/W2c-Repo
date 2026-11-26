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
namespace W2.W2e
/-- Clock scaling of the resolvent ratio, in a positive diagonal eigenbasis. -/
theorem resolvent_ratio_clock_invariant {ι : Type*} [Fintype ι]
    (z c A lam : ℝ) (d w : ι → ℝ) (hz : 0 < z) :
    (2*z*c)^2 * (∑ i, (w i)^2/(z*d i-z*lam))/(z*A) =
      (2*c)^2 * (∑ i, (w i)^2/(d i-lam))/A := by
-- W2 PROOF BEGIN W2.W2e.resolvent_ratio_clock_invariant
  have each (i : ι) : (w i)^2/(z*d i-z*lam) = z⁻¹*((w i)^2/(d i-lam)) := by
    rw [←mul_sub,div_eq_mul_inv,mul_inv_rev]
    ring
  simp_rw [each]
  rw [←Finset.mul_sum]
  simp [div_eq_mul_inv, mul_inv_rev]
  field_simp [hz.ne']
-- W2 PROOF END W2.W2e.resolvent_ratio_clock_invariant
end W2.W2e
