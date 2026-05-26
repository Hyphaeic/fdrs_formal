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

# Addition Operator (Mixed-Radix Addition)

This file defines the addition operator and proves the commutative monoid structure.

## References

- fdrs.md, Phase 1 Fragment 2, Section 3 (lines 389-435)
- Definition 3: Addition (⊕)
- Proposition 10: Decoded correctness
- Theorem 1: (ℛ, ⊕) is commutative monoid isomorphic to (ℕ, +)
- Proposition 11: Carry locality at depth L

## Status

SCAFFOLDING ONLY - proofs not yet attempted
-/

import FdrsFormal.Core.Infinite

namespace FdrsFormal.Operations.Addition

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite FdrsFormal.Core.Infinite

/-!
## Addition with Carry Semantics

Addition is defined via encode/decode transport of ℕ addition.
-/

/--
Addition operator: τ ⊕ σ = enc(dec(τ) + dec(σ))
Total function on all of ℛ
-/
noncomputable def add (b : RadixSeq) (τ σ : DirectLimitSpace b) : DirectLimitSpace b :=
  encode b (decode b τ + decode b σ)

infixl:65 " ⊕ " => add

-- Helper lemma for rewriting
theorem add_def (b : RadixSeq) (τ σ : DirectLimitSpace b) :
    add b τ σ = encode b (decode b τ + decode b σ) :=
  rfl

/--
**Proposition 10**: Decoded correctness
dec(τ ⊕ σ) = dec(τ) + dec(σ)
-/
theorem add_decode_correct (b : RadixSeq) (τ σ : DirectLimitSpace b) :
    decode b (add b τ σ) = decode b τ + decode b σ := by
  simp only [add_def]
  exact decode_encode (decode b τ + decode b σ)

/--
**Theorem 1**: Commutative monoid structure
(ℛ, ⊕) is a commutative monoid isomorphic to (ℕ, +) via dec
-/
theorem add_assoc (b : RadixSeq) (τ σ ρ : DirectLimitSpace b) :
    add b (add b τ σ) ρ = add b τ (add b σ ρ) := by
  apply decode_injective
  simp only [add_decode_correct]
  ring

theorem add_comm (b : RadixSeq) (τ σ : DirectLimitSpace b) :
    add b τ σ = add b σ τ := by
  apply decode_injective
  simp only [add_decode_correct]
  ring

theorem add_zero (b : RadixSeq) (τ : DirectLimitSpace b) :
    add b τ (encode b 0) = τ := by
  apply decode_injective
  rw [add_decode_correct, decode_encode]
  simp

theorem zero_add (b : RadixSeq) (τ : DirectLimitSpace b) :
    add b (encode b 0) τ = τ := by
  apply decode_injective
  rw [add_decode_correct, decode_encode]
  simp

/-! ### AddCommMonoid Instance -/

/-- Left inverse: τ ⊕ 0 = τ (using 0 from DirectLimitSpace's Zero instance) -/
theorem add_zero' (b : RadixSeq) (τ : DirectLimitSpace b) :
    add b τ 0 = τ := by
  apply decode_injective
  rw [add_decode_correct, decode_zero]
  simp

/-- Right inverse: 0 ⊕ τ = τ (using 0 from DirectLimitSpace's Zero instance) -/
theorem zero_add' (b : RadixSeq) (τ : DirectLimitSpace b) :
    add b 0 τ = τ := by
  apply decode_injective
  rw [add_decode_correct, decode_zero]
  simp

/-! ### AddCommMonoid Instance (experimental) -/

-- Note: To construct the full instance, we need to establish that
-- DirectLimitSpace.zero b corresponds to encode b 0, which requires
-- completing decode_zero and encode_zero in Core/Infinite/DirectLimit.lean

-- instance (b : RadixSeq) : AddCommMonoid (DirectLimitSpace b) where
--   add := add b
--   add_assoc := add_assoc b
--   zero := 0
--   zero_add := zero_add' b
--   add_zero := add_zero' b
--   add_comm := add_comm b
--   nsmul := nsmulRec

-- Mark key lemma as simp for convenience
attribute [simp] add_decode_correct

/-! ### Helper Lemmas -/

/-- Addition is injective in the left argument -/
theorem add_left_cancel (b : RadixSeq) {τ σ ρ : DirectLimitSpace b}
    (h : add b ρ τ = add b ρ σ) : τ = σ := by
  apply decode_injective
  have : decode b (add b ρ τ) = decode b (add b ρ σ) := by rw [h]
  simp only [add_decode_correct] at this
  omega

/-- Addition is injective in the right argument -/
theorem add_right_cancel (b : RadixSeq) {τ σ ρ : DirectLimitSpace b}
    (h : add b τ ρ = add b σ ρ) : τ = σ := by
  rw [add_comm b τ ρ, add_comm b σ ρ] at h
  exact add_left_cancel b h

/-!
## Note on Locality

**Proposition 11** (Carry locality at depth L) is proven in:
  Topology.Locality.Properties as `carry_locality`

It states: If τ and τ' agree on first L digits, and σ and σ' agree on first L digits,
then τ ⊕ σ and τ' ⊕ σ' agree on first L digits.

This is a topological locality property and belongs in the Topology tier, not here.
-/

end FdrsFormal.Operations.Addition
