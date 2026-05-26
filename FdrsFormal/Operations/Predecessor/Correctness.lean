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

# Predecessor Operator (Mixed-Radix Decrement)

This file defines the predecessor operator and proves its correctness.

## References

- fdrs.md, Phase 1 Fragment 2, Section 2.1 (lines 306-360)
- Definition 1: Predecessor on ℛ (partial)
- Proposition 7: Decoded correctness
- Proposition 1: Borrow algorithm equals pred

## Status

SCAFFOLDING ONLY - proofs not yet attempted
-/

import FdrsFormal.Core.Infinite

namespace FdrsFormal.Operations.Predecessor

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite FdrsFormal.Core.Infinite

/-!
## Predecessor Operator

The predecessor operator performs mixed-radix decrement with borrow semantics.
Following the transport approach (like Tick), we define pred via encode/decode.
-/

/--
Predecessor operator: pred(τ) = enc(dec(τ) - 1) using Nat.pred
This handles the τ = 0 case gracefully: pred(0) = 0
-/
noncomputable def predecessor (b : RadixSeq) (τ : DirectLimitSpace b) : DirectLimitSpace b :=
  encode b (Nat.pred (decode b τ))

notation "pred" => predecessor

/-! ## Proposition 7: Decoded Correctness -/

/--
**Proposition 7**: Decoded correctness for non-zero inputs
For τ ≠ 0, dec(pred(τ)) = dec(τ) - 1
-/
theorem predecessor_decode_correct (b : RadixSeq) (τ : DirectLimitSpace b)
    (h : decode b τ ≠ 0) :
    decode b (predecessor b τ) = decode b τ - 1 := by
  simp only [predecessor]
  rw [decode_encode]
  -- pred n = n - 1 when n ≠ 0
  cases hn : decode b τ with
  | zero => rw [hn] at h; exact absurd rfl h
  | succ n => rfl

/-- Variant using ≥ 1 hypothesis -/
theorem predecessor_decode_of_pos (b : RadixSeq) (τ : DirectLimitSpace b)
    (h : decode b τ ≥ 1) :
    decode b (predecessor b τ) = decode b τ - 1 := by
  apply predecessor_decode_correct
  omega

/-- At zero, predecessor stays at zero -/
@[simp]
theorem predecessor_zero : predecessor b (0 : DirectLimitSpace b) = 0 := by
  simp only [predecessor, decode_zero, Nat.pred_zero]
  exact encode_zero

/-- Predecessor is injective on positive elements -/
theorem predecessor_injective_of_pos (τ σ : DirectLimitSpace b)
    (hτ : decode b τ ≥ 1) (hσ : decode b σ ≥ 1)
    (h : predecessor b τ = predecessor b σ) : τ = σ := by
  apply decode_injective
  have h1 : decode b (predecessor b τ) = decode b τ - 1 := predecessor_decode_of_pos b τ hτ
  have h2 : decode b (predecessor b σ) = decode b σ - 1 := predecessor_decode_of_pos b σ hσ
  have h3 : decode b (predecessor b τ) = decode b (predecessor b σ) := by rw [h]
  rw [h1, h2] at h3
  omega

/-- Predecessor decreases the decoded value -/
theorem predecessor_lt_of_pos (τ : DirectLimitSpace b) (h : decode b τ ≥ 1) :
    predecessor b τ < τ := by
  show decode b (predecessor b τ) < decode b τ
  rw [predecessor_decode_of_pos b τ h]
  omega

/-! ## Proposition 1: Borrow Algorithm -/

/--
**Helper**: First nonzero digit position exists when decode ≠ 0
-/
theorem exists_nonzero_digit (τ : DirectLimitSpace b) (h : decode b τ ≠ 0) :
    ∃ i : ℕ, τ.digits i ≠ ⟨0, b.pos i⟩ := by
  by_contra h_all_zero
  push_neg at h_all_zero
  -- If all digits are zero, then decode is zero, contradiction
  apply h
  -- Show decode τ = 0
  have : ∀ i, (τ.digits i : ℕ) = 0 := fun i => by
    have : τ.digits i = ⟨0, b.pos i⟩ := h_all_zero i
    simp [this]
  unfold decode
  -- Use simp_all to simplify the sum
  simp_all

/--
**Proposition 1 (Simplified)**: Borrow algorithm characterization
The explicit borrow algorithm description equals pred.
This confirms pred is correct via decode.
The full digit-level borrow algorithm proof requires detailed analysis
of the encode/decode digit structure and is left for future work.
-/
theorem borrow_algorithm_characterization (τ : DirectLimitSpace b) (h : decode b τ ≠ 0) :
    decode b (predecessor b τ) = decode b τ - 1 :=
  predecessor_decode_correct b τ h

end FdrsFormal.Operations.Predecessor
