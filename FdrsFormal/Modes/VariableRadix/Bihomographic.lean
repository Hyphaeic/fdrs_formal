/-
Copyright 2026 Hyphaeic SPC.

Licensed under the Hyphaeic Public License, Version 1.0 (the
"License"); you may not use this file except in compliance with
the License. You may obtain a copy of the License at

https://github.com/hyphaeic/hpl

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
implied. See the License for the specific language governing
permissions and limitations under the License.

# Bihomographic tensor — the two-stream mediator (Timeline C)

Gosper's rank-3 (2×2×2) bihomographic tensor: the exact-real combinator that absorbs
two incommensurate input streams `x` (Timeline A) and `y` (Timeline B) and emits a
single output stream (Timeline C), all in exact `ℤ` arithmetic. It represents

  z = (a·xy + b·x + c·y + d) / (e·xy + f·x + g·y + h)

with input tails `x, y ∈ [1,∞)`.

* `absorbX p` — read partial quotient `p` from A: `x ↦ p + 1/x` (right-multiply the
  `x`-leg by `[[p,1],[1,0]]`).
* `absorbY p` — read `p` from B: `y ↦ p + 1/y`.
* `emit q` — write `q` to C: `z ↦ 1/(z − q)` (left-multiply by `[[0,1],[1,-q]]`).
* `emitDigit` / `emitReady` — the output is forced when the integer floor agrees at all
  **four corners** `(x,y) ∈ {1,∞}²` of the input plane.

Representation: a flat 8-field `ℤ` structure (NOT a `Matrix`), so every law is a
polynomial identity closed by `ring` (Mathlib's matrix product hides a `Finset.sum`
that `ring` can't see through). The headline correctness facts — proved here — are the
**channel commutations**: the two input reads and the output write all pairwise commute,
i.e. the mediator is an asynchronous, non-blocking transducer (A, B, C interleave freely).
-/
import FdrsFormal.Modes.VariableRadix.HomographicCarry

namespace FdrsFormal.Modes.VariableRadix

/-- Gosper's bihomographic tensor `z = (a·xy + b·x + c·y + d)/(e·xy + f·x + g·y + h)`.
Numerator coefficients `(a,b,c,d)` and denominator `(e,f,g,h)` of the monomials
`(xy, x, y, 1)`. -/
structure BihTensor where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  e : ℤ
  f : ℤ
  g : ℤ
  h : ℤ
  deriving Repr, DecidableEq, Inhabited

namespace BihTensor

/-- **Absorb A**: read input quotient `p` from Timeline A (`x ↦ p + 1/x`). -/
def absorbX (p : ℤ) (T : BihTensor) : BihTensor where
  a := T.a * p + T.c
  b := T.b * p + T.d
  c := T.a
  d := T.b
  e := T.e * p + T.g
  f := T.f * p + T.h
  g := T.e
  h := T.f

/-- **Absorb B**: read input quotient `p` from Timeline B (`y ↦ p + 1/y`). -/
def absorbY (p : ℤ) (T : BihTensor) : BihTensor where
  a := T.a * p + T.b
  b := T.a
  c := T.c * p + T.d
  d := T.c
  e := T.e * p + T.f
  f := T.e
  g := T.g * p + T.h
  h := T.g

/-- **Emit C**: write output quotient `q` to Timeline C (`z ↦ 1/(z − q)`). -/
def emit (q : ℤ) (T : BihTensor) : BihTensor where
  a := T.e
  b := T.f
  c := T.g
  d := T.h
  e := T.a - q * T.e
  f := T.b - q * T.f
  g := T.c - q * T.g
  h := T.d - q * T.h

/-- The candidate output quotient: the floor at the `(∞,∞)` corner, `⌊a/e⌋ = a.fdiv e`
(floor division — NOT `/`, which truncates toward zero and would misfire once the inner
coordinates swing negative under the `emit` inverse shift). -/
def emitDigit (T : BihTensor) : ℤ := T.a.fdiv T.e

/-- **Emission is ready** when the candidate digit `k = emitDigit` *traps* every corner:
positive corner-denominators, and `k·denom ≤ numer < (k+1)·denom` at all four corners
`(∞,∞), (∞,1), (1,∞), (1,1)`. These are exactly the hypotheses of `emit_traps`, so a
`true` here *certifies* the emission (`emitReady_traps`) — the guess is verified, not
trusted, so the `fdiv` semantics can't make it lie. -/
def emitReady (T : BihTensor) : Bool :=
  0 < T.e && 0 < T.e + T.f && 0 < T.e + T.g && 0 < T.e + T.f + T.g + T.h &&
    emitDigit T * T.e ≤ T.a && emitDigit T * (T.e + T.f) ≤ T.a + T.b &&
    emitDigit T * (T.e + T.g) ≤ T.a + T.c &&
    emitDigit T * (T.e + T.f + T.g + T.h) ≤ T.a + T.b + T.c + T.d &&
    T.a < (emitDigit T + 1) * T.e && T.a + T.b < (emitDigit T + 1) * (T.e + T.f) &&
    T.a + T.c < (emitDigit T + 1) * (T.e + T.g) &&
    T.a + T.b + T.c + T.d < (emitDigit T + 1) * (T.e + T.f + T.g + T.h)

/-- **Inputs commute.** Reading from Timeline A and from Timeline B commute — the two
input channels are independent (`x` and `y` are substituted independently). -/
theorem absorbX_absorbY_comm (p p' : ℤ) (T : BihTensor) :
    absorbX p (absorbY p' T) = absorbY p' (absorbX p T) := by
  cases T; simp only [absorbX, absorbY]; congr 1 <;> ring

/-- **Output is independent of input A.** Emitting to C and reading from A commute. -/
theorem emit_absorbX_comm (q p : ℤ) (T : BihTensor) :
    emit q (absorbX p T) = absorbX p (emit q T) := by
  cases T; simp only [emit, absorbX]; congr 1 <;> ring

/-- **Output is independent of input B.** Emitting to C and reading from B commute. -/
theorem emit_absorbY_comm (q p : ℤ) (T : BihTensor) :
    emit q (absorbY p T) = absorbY p (emit q T) := by
  cases T; simp only [emit, absorbY]; congr 1 <;> ring

end BihTensor

end FdrsFormal.Modes.VariableRadix
