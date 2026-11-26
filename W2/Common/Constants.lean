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

public import W2.Common.Basic
-- W2 PROOF IMPORTS
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic
-- W2 END IMPORTS

@[expose] public section
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
