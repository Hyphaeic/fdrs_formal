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

# Bihomographic emission soundness — the 4-corner bound, with no analysis

Safety for `BihTensor.emit`: when the integer floor agrees at all four corners of the
input plane, the emitted digit is *forced* — the true output value is trapped in
`[k, k+1)` for every input tail `x, y ≥ 1`.

The infinite horizons `(x,y) → (∞,·)` are formalized as **leading-coefficient sign
conditions**, never as limits. The whole argument lives over a generic ordered ring
(`[CommRing] [LinearOrder] [IsStrictOrderedRing]`; ℚ is enough — no `Real`, no
`Filter`/`nhds`, no topology); the tail variables `x, y` are inert order-carriers.
Everything reduces to `nlinarith`.
-/
import FdrsFormal.Modes.VariableRadix.Bihomographic

namespace FdrsFormal.Modes.VariableRadix.BihTensor

/-- **The bilinear-form bound (no limits).** Over an ordered ring, a bilinear form
`α·xy + β·x + γ·y + δ` is `≥` its `(1,1)`-value on the entire quadrant `x, y ≥ 1`,
provided the three leading corner-coefficients — `α` (the `xy`/`(∞,∞)` coeff), `α+β`
(the `(∞,1)` coeff), `α+γ` (the `(1,∞)` coeff) — are non-negative.

Proof identity: `αxy+βx+γy+δ = α(x−1)(y−1) + (α+β)(x−1) + (α+γ)(y−1) + (α+β+γ+δ)`,
each added term non-negative. The infinite corners are leading coefficients. -/
theorem bilinear_ge_const {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K] {α β γ δ x y : K}
    (hα : 0 ≤ α) (hαβ : 0 ≤ α + β) (hαγ : 0 ≤ α + γ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    α + β + γ + δ ≤ α * x * y + β * x + γ * y + δ := by
  nlinarith [mul_nonneg hα (mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hy)),
             mul_nonneg hαβ (sub_nonneg.2 hx), mul_nonneg hαγ (sub_nonneg.2 hy)]

/-- **Emission soundness — the value is trapped.** If the integer floor agrees at all
four corners (`k ≤ corner` and `corner < k+1`, as eight integer inequalities on the
tensor coefficients), then for EVERY input tail `x, y ≥ 1` the true output value `N/D`
is trapped in `[k, k+1)`: `k·D ≤ N` and `N < (k+1)·D`. So emitting `k` never
hallucinates a digit, regardless of the unread tails of A and B.

No reals, no limits, no topology — pure ordered-ring algebra; `x, y` are inert. -/
theorem emit_traps {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K] (T : BihTensor) (k : ℤ)
    (lo1 : k * T.e ≤ T.a) (lo2 : k * (T.e + T.f) ≤ T.a + T.b)
    (lo3 : k * (T.e + T.g) ≤ T.a + T.c)
    (lo4 : k * (T.e + T.f + T.g + T.h) ≤ T.a + T.b + T.c + T.d)
    (hi1 : T.a < (k + 1) * T.e) (hi2 : T.a + T.b < (k + 1) * (T.e + T.f))
    (hi3 : T.a + T.c < (k + 1) * (T.e + T.g))
    (hi4 : T.a + T.b + T.c + T.d < (k + 1) * (T.e + T.f + T.g + T.h))
    {x y : K} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    (k : K) * ((T.e : K) * x * y + T.f * x + T.g * y + T.h)
        ≤ (T.a : K) * x * y + T.b * x + T.c * y + T.d ∧
      (T.a : K) * x * y + T.b * x + T.c * y + T.d
        < (k + 1 : K) * ((T.e : K) * x * y + T.f * x + T.g * y + T.h) := by
  -- cast the integer corner bounds into K
  have l1 : (k : K) * T.e ≤ T.a := by exact_mod_cast lo1
  have l2 : (k : K) * ((T.e : K) + T.f) ≤ (T.a : K) + T.b := by exact_mod_cast lo2
  have l3 : (k : K) * ((T.e : K) + T.g) ≤ (T.a : K) + T.c := by exact_mod_cast lo3
  have l4 : (k : K) * ((T.e : K) + T.f + T.g + T.h) ≤ (T.a : K) + T.b + T.c + T.d := by
    exact_mod_cast lo4
  have u1 : (T.a : K) < (k + 1) * T.e := by exact_mod_cast hi1
  have u2 : (T.a : K) + T.b < (k + 1) * ((T.e : K) + T.f) := by exact_mod_cast hi2
  have u3 : (T.a : K) + T.c < (k + 1) * ((T.e : K) + T.g) := by exact_mod_cast hi3
  have u4 : (T.a : K) + T.b + T.c + T.d < (k + 1) * ((T.e : K) + T.f + T.g + T.h) := by
    exact_mod_cast hi4
  refine ⟨?_, ?_⟩
  · -- k·D ≤ N : apply the bound to N − k·D (coeffs a−ke, b−kf, c−kg, d−kh)
    have h := bilinear_ge_const (K := K)
      (α := (T.a : K) - (k : K) * T.e) (β := (T.b : K) - (k : K) * T.f)
      (γ := (T.c : K) - (k : K) * T.g) (δ := (T.d : K) - (k : K) * T.h)
      (by linarith) (by nlinarith [l2]) (by nlinarith [l3]) hx hy
    nlinarith [h, l4]
  · -- N < (k+1)·D : apply the bound to (k+1)·D − N
    have h := bilinear_ge_const (K := K)
      (α := (k + 1 : K) * T.e - T.a) (β := (k + 1 : K) * T.f - T.b)
      (γ := (k + 1 : K) * T.g - T.c) (δ := (k + 1 : K) * T.h - T.d)
      (by linarith) (by nlinarith [u2]) (by nlinarith [u3]) hx hy
    nlinarith [h, u4]

/-- **The driver's emissions are certified (the boolean ⇄ proposition padlock).** A `true`
from the *executable* `emitReady` discharges exactly the hypotheses of `emit_traps`: the
output value is trapped in `[k, k+1)` (with `k = emitDigit T`) for every tail `x, y ≥ 1`.
The boolean check the driver runs and the proposition `emit_traps` proves are now welded —
every digit the engine physically emits carries its correctness proof. No `Int.fdiv ↔ ⌊⌋`
lemma and no `ℚ` detour: `emitReady` *verifies* the guess via the trapping inequalities, so
the decode is just `Bool.and_eq_true` + `emit_traps`. -/
theorem emitReady_traps {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]
    (T : BihTensor) (h : emitReady T = true) {x y : K} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    (emitDigit T : K) * ((T.e : K) * x * y + T.f * x + T.g * y + T.h)
        ≤ (T.a : K) * x * y + T.b * x + T.c * y + T.d ∧
      (T.a : K) * x * y + T.b * x + T.c * y + T.d
        < (emitDigit T + 1 : K) * ((T.e : K) * x * y + T.f * x + T.g * y + T.h) := by
  simp only [emitReady, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨_, _, _, _, lo1, lo2, lo3, lo4, hi1, hi2, hi3, hi4⟩ := h
  exact emit_traps T (emitDigit T) lo1 lo2 lo3 lo4 hi1 hi2 hi3 hi4 hx hy

end FdrsFormal.Modes.VariableRadix.BihTensor
