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

/-- A three-dimensional shell with O(n²) sites and O(n⁻⁴) entries has a summable majorant. -/
theorem shell_bound (n count size C K : ℝ) (hn : 0 < n) (_hk : 0 ≤ K) (hc : 0 ≤ count)
    (sites : count ≤ K*n^2) (entry : size ≤ C/n^4) (hC : 0 ≤ C) :
    count*size ≤ K*C/n^2 := by
-- W2 PROOF BEGIN W2.W2b.shell_bound
  calc
    _ ≤ count*(C/n^4) := mul_le_mul_of_nonneg_left entry hc
    _ ≤ (K*n^2)*(C/n^4) := mul_le_mul_of_nonneg_right sites (by positivity)
    _ = _ := by field_simp
-- W2 PROOF END W2.W2b.shell_bound

/-- Actual positive polynomial tails are inconsistent with a faster upper envelope. -/
theorem tail_obstruction {f lower upper : ℕ → ℝ} (hf : ∀ n, lower n ≤ f n)
    (crossing : ∃ n, upper n < lower n) : ¬ ∀ n, f n ≤ upper n := by
-- W2 PROOF BEGIN W2.W2b.tail_obstruction
  intro h; obtain ⟨n,hn⟩ := crossing; exact (not_lt_of_ge ((hf n).trans (h n))) hn
-- W2 PROOF END W2.W2b.tail_obstruction
end W2.W2b
