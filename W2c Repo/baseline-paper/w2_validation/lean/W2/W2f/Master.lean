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
public import W2.W2f.Assembly
public import W2.Framework.Schur
@[expose] public section
namespace W2.W2f

/-- Sufficient signed retained-minus-mixed estimate at a prescribed trial gap. -/
theorem master_small_field {ι : Type*} [Fintype ι] (A m x u : ℝ) (c : W2Constants)
    (d b : ι → ℝ) (hd : ∀ i, 0 < d i)
    (signedEstimate : m * (1-(c.CS+c.CM)*x^2-(c.Ca+c.Cmix)*u^2) +
      (∑ i, (b i)^2 / d i) ≤ A) :
    ∀ v : ℝ, ∀ w : ι → ℝ,
      0 ≤ (A-m*(1-(c.CS+c.CM)*x^2-(c.Ca+c.Cmix)*u^2))*v^2 +
        ∑ i, (2*v*b i*w i + d i*(w i)^2) := by
-- W2 PROOF BEGIN W2.W2f.master_small_field
  apply (W2.Framework.schur_criterion _ d b hd).2
  linarith
-- W2 PROOF END W2.W2f.master_small_field

end W2.W2f
