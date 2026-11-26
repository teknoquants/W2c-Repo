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

import Mathlib
import W2.W2cR.FreeGap
import W2.W2cR.Hessian
import W2.W2cR.Separation
import W2.W2f.Assembly

namespace W2.W2cR

-- @result E.2 L2
theorem fibre_poincare_reindex {I J : Type*} {A : I → Prop} (B : J → Prop)
    (map : J → I) (incl : ∀ j, B j → A (map j)) (g V T : I → ℝ)
    (h : W2.Research.uniformFibrePoincare A g V T) :
    W2.Research.uniformFibrePoincare B (g ∘ map) (V ∘ map) (T ∘ map) := by
  obtain ⟨c,hc,h⟩ := h
  exact ⟨c,hc,fun j hj => h (map j) (incl j hj)⟩

-- @result E.3 L2
theorem pointwise_eliminated_floor (k d x a V T E : ℝ) (hx : 0<x) (ha : 0<a) (hv : 0<V)
    (hK : ((1-d)*(2*k)/x)*V ≤ T) (hE : x/(2*a)*T ≤ E) : (1-d)*k≤a*(E/V) := by
  rw [div_mul_eq_mul_div, div_le_iff₀ hx] at hK
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 2*a)] at hE
  rw [← mul_div_assoc, le_div_iff₀ hv]
  nlinarith only [hK,hE]

-- @result E.3 L1
theorem uniform_le_pointwise (k d m : ℝ) (hk : 0≤k) (hd : d ≤ m) :
    (1-m)*k≤(1-d)*k := by
  exact mul_le_mul_of_nonneg_right (sub_le_sub_left hd 1) hk

-- @result E.3 L1
theorem uniform_eliminated_reindex {I J : Type*} (p : I → ℝ) (map : J → I)
    (c : ℝ) (h : ∀ i, c≤p i) : ∀ j, c≤p (map j) := by
  exact fun j => h (map j)

-- @result E.5 L2
theorem herbst_tail_of_lsi (K r M tail : ℝ) (hK : 0<K)
    (mgf : M≤Real.exp ((K*r)^2/(2*K))) (markov : tail≤Real.exp (-(K*r)*r)*M) :
    tail≤Real.exp (-K*r^2/2) := by
  apply markov.trans
  apply (mul_le_mul_of_nonneg_left mgf (Real.exp_pos _).le).trans_eq
  rw [← Real.exp_add]
  congr 1
  field_simp
  ring

-- @result E.6 L1
theorem separation_mono (a m k K : ℝ) (ha : 0≤a) (hm : 0 ≤ m) (hk : 0<k) (h : k≤K) :
    1-a*m/k ≤ 1-a*m/K := by
  have hK := hk.trans_le h
  have hh := div_le_div_of_nonneg_left (mul_nonneg ha hm) hk h
  linarith

-- @result E.6 L1
theorem scalar_resolvent_margin (a m k : ℝ) (ha : 0<a) (h : a*m<k) :
    0<a/(k-a*m) := by
  exact div_pos ha (sub_pos.mpr h)

-- @result E.7 L2
theorem small_field_loss_of_hessian (loss α ζ x u : ℝ) (c : W2.W2f.W2Constants)
    (combine : loss ≤ α+ζ) (retained : α≤c.CS*x^2+c.Ca*u^2)
    (mixedFromFloor : ζ≤c.CM*x^2+c.Cmix*u^2) :
    loss ≤ (c.CS+c.CM)*x^2+(c.Ca+c.Cmix)*u^2 := by
  exact W2.W2f.small_field_loss loss α ζ x u c combine retained mixedFromFloor

end W2.W2cR
