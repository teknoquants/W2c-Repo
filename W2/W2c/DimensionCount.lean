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
namespace W2.W2c

theorem midpoint_preserves_product {G : Type*} [Group G] (u v h : G) : (u*h⁻¹)*(h*v)=u*v := by
-- W2 PROOF BEGIN W2.W2c.midpoint_preserves_product
  group
-- W2 PROOF END W2.W2c.midpoint_preserves_product

theorem fibre_dimension_count (V d : ℕ) :
    24*V*d - 3*V*d = 21*V*d ∧ 21*V*d - 7*V*d = 14*V*d := by
-- W2 PROOF BEGIN W2.W2c.fibre_dimension_count
  simp only [Nat.mul_assoc]
  omega
-- W2 PROOF END W2.W2c.fibre_dimension_count
/-- The boundary term for an open cubical box of n coarse links per axis. -/
theorem open_dimension_count (n : ℕ) :
    3*(2*n)*(2*n+1)^2+(n+1)^3 =
    3*n*(n+1)^2+(2*n+1)^3+(14*n^3+9*n^2) := by
-- W2 PROOF BEGIN W2.W2c.open_dimension_count
  ring
-- W2 PROOF END W2.W2c.open_dimension_count

end W2.W2c
