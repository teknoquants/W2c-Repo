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
public import W2.W2b.Artifact
public import W2.W2b.SchurBenchmark
@[expose] public section
namespace W2.W2d
/-- The gap-ratio benchmark; the separate normalized form defect has nonzero slope. -/
theorem free_Ca_matches (L : ℕ) (hL : 4 ≤ L) :
    let t := Real.pi / (L:ℝ)
    |1/Real.cos t-1-Real.sin (2*t)^2/8| ≤ 7*Real.sin (2*t)^4 := by
-- W2 PROOF BEGIN W2.W2d.free_Ca_matches
  exact W2.W2b.free_artifact_constant L hL
-- W2 PROOF END W2.W2d.free_Ca_matches
end W2.W2d
