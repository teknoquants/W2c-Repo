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
/-- Differentiating the Gaussian verifies the oscillator ground-state equation pointwise. -/
noncomputable def gaussian (ω x : ℝ) := Real.exp (-ω*x^2/2)

theorem gaussian_derivative (ω x : ℝ) : HasDerivAt (gaussian ω) (-ω*x*gaussian ω x) x := by
-- W2 PROOF BEGIN W2.W2b.gaussian_derivative
  have h := ((((hasDerivAt_id x).pow 2).const_mul (-ω)).div_const 2).exp
  change HasDerivAt (fun t : ℝ => Real.exp (-ω*t^2/2)) _ x
  convert h using 1 <;> simp [gaussian, Pi.pow_apply]; ring
-- W2 PROOF END W2.W2b.gaussian_derivative

theorem oscillator_ground_equation (ω x : ℝ) :
    -(deriv (deriv (gaussian ω)) x)/2 + ω^2*x^2*gaussian ω x/2 = ω/2*gaussian ω x := by
-- W2 PROOF BEGIN W2.W2b.oscillator_ground_equation
  have all : deriv (gaussian ω) = (fun t => -ω*t*gaussian ω t) :=
    funext (fun t => (gaussian_derivative ω t).deriv)
  have hp := (((hasDerivAt_id x).const_mul (-ω)).mul (gaussian_derivative ω x)).deriv
  rw [all]
  change -deriv (fun t : ℝ => -ω*t*gaussian ω t) x/2 + _ = _
  change deriv (fun t : ℝ => -ω*t*gaussian ω t) x = _ at hp
  rw [hp]
  dsimp only [id_eq]
  ring
-- W2 PROOF END W2.W2b.oscillator_ground_equation

/-- Fourth Taylor coefficient of the dimensionless squared lattice frequency in one direction. -/
theorem lattice_fourth_derivative (z : ℝ) :
    deriv^[4] (fun x : ℝ => 2*(1-Real.cos x)) z = -2*Real.cos z := by
-- W2 PROOF BEGIN W2.W2b.lattice_fourth_derivative
  have one : deriv (fun x : ℝ => 2*(1-Real.cos x)) = (fun x => 2*Real.sin x) := by
    funext x
    convert (((hasDerivAt_const x (1:ℝ)).sub (Real.hasDerivAt_cos x)).const_mul 2).deriv using 1
    ring
  have two : deriv (fun x : ℝ => 2*Real.sin x) = (fun x => 2*Real.cos x) :=
    funext (fun x => ((Real.hasDerivAt_sin x).const_mul 2).deriv)
  have three : deriv (fun x : ℝ => 2*Real.cos x) = (fun x => -2*Real.sin x) := by
    funext x
    convert ((Real.hasDerivAt_cos x).const_mul 2).deriv using 1
    ring
  change deriv (deriv (deriv (deriv (fun x : ℝ => 2*(1-Real.cos x))))) z = _
  rw [one,two,three,((Real.hasDerivAt_sin z).const_mul (-2:ℝ)).deriv]
-- W2 PROOF END W2.W2b.lattice_fourth_derivative
end W2.W2b
