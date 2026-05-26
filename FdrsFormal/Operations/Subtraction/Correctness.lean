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

# Subtraction Operator (Mixed-Radix Subtraction)

This file defines the subtraction operator with borrow semantics.

## References

- fdrs.md, Phase 1 Fragment 2, Section 2.2 (lines 363-386)
- Definition 13: Subtraction (⊖, partial)
- Proposition 9: Correctness and basic laws

## Status

SCAFFOLDING ONLY - proofs not yet attempted
-/

import FdrsFormal.Core.Infinite
import FdrsFormal.Operations.Predecessor

namespace FdrsFormal.Operations.Subtraction

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite FdrsFormal.Core.Infinite
open FdrsFormal.Operations.Predecessor

/-!
## Subtraction with Borrow

Subtraction with borrow, defined using encode/decode transport (like Tick and pred).
-/

/--
Subtraction operator: τ ⊖ σ = enc(dec(τ) - dec(σ))
Defined when dec(σ) ≤ dec(τ)
-/
noncomputable def subtract (b : RadixSeq) (τ σ : DirectLimitSpace b)
    (h : decode b σ ≤ decode b τ) : DirectLimitSpace b :=
  encode b (decode b τ - decode b σ)

infixl:65 " ⊖ " => subtract

/-! ## Proposition 9: Correctness and Laws -/

/--
**Proposition 9(1)**: Correctness
dec(τ ⊖ σ) = dec(τ) - dec(σ)
-/
theorem subtract_decode_correct (b : RadixSeq) (τ σ : DirectLimitSpace b)
    (h : decode b σ ≤ decode b τ) :
    decode b (subtract b τ σ h) = decode b τ - decode b σ := by
  simp only [subtract]
  exact decode_encode (decode b τ - decode b σ)

/--
**Proposition 9(2)**: Right identity
τ ⊖ 0 = τ
-/
theorem subtract_zero (b : RadixSeq) (τ : DirectLimitSpace b)
    (h : decode b (0 : DirectLimitSpace b) ≤ decode b τ) :
    subtract b τ 0 h = τ := by
  apply decode_injective
  rw [subtract_decode_correct]
  simp only [decode_zero, Nat.sub_zero, decode_encode]

/-- Variant without the hypothesis (which is always true) -/
theorem subtract_zero' (b : RadixSeq) (τ : DirectLimitSpace b) :
    subtract b τ 0 (by simp [decode_zero] : decode b 0 ≤ decode b τ) = τ :=
  subtract_zero b τ _

/--
**Proposition 9(3)**: Self-subtraction
τ ⊖ τ = 0
-/
theorem subtract_self (b : RadixSeq) (τ : DirectLimitSpace b)
    (h : decode b τ ≤ decode b τ) :
    subtract b τ τ h = 0 := by
  apply decode_injective
  rw [subtract_decode_correct, decode_zero]
  exact Nat.sub_self (decode b τ)

/-- Variant using reflexivity -/
theorem subtract_self' (b : RadixSeq) (τ : DirectLimitSpace b) :
    subtract b τ τ (le_refl _) = 0 :=
  subtract_self b τ _

/-! ## Additional Properties -/

/-- Subtraction by predecessor equals subtraction by 1 -/
theorem subtract_one_eq_predecessor (b : RadixSeq) (τ : DirectLimitSpace b)
    (h : 1 ≤ decode b τ) :
    subtract b τ (encode b 1) (by rw [decode_encode]; exact h) = predecessor b τ := by
  apply decode_injective
  rw [subtract_decode_correct, predecessor_decode_of_pos b τ h]
  simp only [decode_encode]

/-- Subtraction with encode is clean -/
theorem subtract_encode (b : RadixSeq) (τ : DirectLimitSpace b) (n : ℕ)
    (h : n ≤ decode b τ) :
    subtract b τ (encode b n) (by rw [decode_encode]; exact h) = encode b (decode b τ - n) := by
  apply decode_injective
  rw [subtract_decode_correct, decode_encode, decode_encode]

/-- Monotonicity: if τ ≥ σ, then τ ⊖ ρ ≥ σ ⊖ ρ when both are defined -/
theorem subtract_le_subtract_right (b : RadixSeq) (τ σ ρ : DirectLimitSpace b)
    (hτρ : decode b ρ ≤ decode b τ) (hσρ : decode b ρ ≤ decode b σ)
    (hτσ : decode b σ ≤ decode b τ) :
    decode b (subtract b σ ρ hσρ) ≤ decode b (subtract b τ ρ hτρ) := by
  repeat rw [subtract_decode_correct]
  omega

end FdrsFormal.Operations.Subtraction
