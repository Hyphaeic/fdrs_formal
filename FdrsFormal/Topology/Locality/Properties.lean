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

# Engineering Corollaries and Locality

This file formalizes multi-rate execution principles and finite dependence.

## References

- fdrs.md, Phase 1 Fragment 2, Section 5 (lines 508-524)
- Corollary 3: Finite dependence / multi-rate execution

## Status

SCAFFOLDING ONLY - proofs not yet attempted
-/

import FdrsFormal.Topology.Continuity

namespace FdrsFormal.Topology.Locality

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite FdrsFormal.Core.Infinite
open FdrsFormal.Operations.Tick FdrsFormal.Operations.Predecessor FdrsFormal.Operations.Addition
open FdrsFormal.Topology.PrefixCongruence FdrsFormal.Topology.Continuity

/-!
## Engineering Corollaries (Theorem-Backed)

These corollaries establish the formal foundation for hierarchical scheduling
and multi-rate execution.
-/

/--
**Corollary 3**: Finite dependence / multi-rate execution

To compute the first L digits of:
* T(τ)
* pred(τ) (if τ ≠ 0)
* τ ⊕ σ

it suffices to know only the first L digits of the inputs.
No higher digits can affect the prefix outcome.

This is the formal backbone for hierarchical scheduling and locality by radix prefix.
-/
theorem finite_dependence_tick (b : RadixSeq) (L : ℕ) (τ τ' : DirectLimitSpace b)
    (h : prefixProjection b L τ = prefixProjection b L τ') :
    prefixProjection b L (tick b τ) = prefixProjection b L (tick b τ') :=
  tick_preserves_prefix b L τ τ' h

theorem finite_dependence_pred (b : RadixSeq) (L : ℕ) (τ τ' : DirectLimitSpace b)
    (hτ : decode b τ ≠ 0) (hτ' : decode b τ' ≠ 0)
    (h : prefixProjection b L τ = prefixProjection b L τ') :
    prefixProjection b L (predecessor b τ) = prefixProjection b L (predecessor b τ') :=
  pred_preserves_prefix b L τ τ' hτ hτ' h

/--
**Proposition 11**: Carry locality at depth L

If τ and τ' agree on first L digits, and σ and σ' agree on first L digits,
then τ ⊕ σ and τ' ⊕ σ' agree on first L digits.

This expresses that the first L digits of the sum depend only on the first L digits
of the inputs (finite dependence / multi-rate execution).

fdrs.md reference: Phase 1 Fragment 2, lines 420-435
-/
theorem carry_locality (b : RadixSeq) (L : ℕ)
    (τ τ' σ σ' : DirectLimitSpace b)
    (hτ : prefixProjection b L τ = prefixProjection b L τ')
    (hσ : prefixProjection b L σ = prefixProjection b L σ') :
    prefixProjection b L (add b τ σ) = prefixProjection b L (add b τ' σ') := by
  -- Strategy: Use prefix_congruence_equiv to convert prefix equality to congruence mod B_L
  -- Then show that addition preserves congruence

  -- Step 1: Convert prefix equalities to congruences
  have h1 : decode b τ % placeValue b L = decode b τ' % placeValue b L := by
    have h1a := (prefix_congruence_equiv b L τ (prefixProjection b L τ)).mp rfl
    have h1b := (prefix_congruence_equiv b L τ' (prefixProjection b L τ)).mp hτ.symm
    calc decode b τ % placeValue b L
        = PrefixCongruence.prefixResidue b L (prefixProjection b L τ) % placeValue b L := h1a
      _ = decode b τ' % placeValue b L := h1b.symm

  have h2 : decode b σ % placeValue b L = decode b σ' % placeValue b L := by
    have h2a := (prefix_congruence_equiv b L σ (prefixProjection b L σ)).mp rfl
    have h2b := (prefix_congruence_equiv b L σ' (prefixProjection b L σ)).mp hσ.symm
    calc decode b σ % placeValue b L
        = PrefixCongruence.prefixResidue b L (prefixProjection b L σ) % placeValue b L := h2a
      _ = decode b σ' % placeValue b L := h2b.symm

  -- Step 2: Show that the sums are congruent mod B_L
  have h_sum : (decode b τ + decode b σ) % placeValue b L =
               (decode b τ' + decode b σ') % placeValue b L := by
    calc (decode b τ + decode b σ) % placeValue b L
      _ = ((decode b τ % placeValue b L) + (decode b σ % placeValue b L)) % placeValue b L :=
          Nat.add_mod _ _ _
      _ = ((decode b τ' % placeValue b L) + (decode b σ' % placeValue b L)) % placeValue b L :=
          by rw [h1, h2]
      _ = (decode b τ' + decode b σ') % placeValue b L :=
          (Nat.add_mod _ _ _).symm

  -- Step 3: Use addition correctness: decode(τ ⊕ σ) = decode τ + decode σ
  have h_add_τσ : decode b (add b τ σ) = decode b τ + decode b σ := add_decode_correct b τ σ
  have h_add_τ'σ' : decode b (add b τ' σ') = decode b τ' + decode b σ' := add_decode_correct b τ' σ'

  -- Step 4: Combine to get congruence of the sums
  have h_add_congr : decode b (add b τ σ) % placeValue b L =
                     decode b (add b τ' σ') % placeValue b L := by
    rw [h_add_τσ, h_add_τ'σ']
    exact h_sum

  -- Step 5: Convert back to prefix equality using prefix_congruence_equiv
  have h_result := (prefix_congruence_equiv b L (add b τ' σ') (prefixProjection b L (add b τ σ))).mpr
  have h_final : prefixProjection b L (add b τ' σ') = prefixProjection b L (add b τ σ) := by
    apply h_result
    have h_τσ := (prefix_congruence_equiv b L (add b τ σ) (prefixProjection b L (add b τ σ))).mp rfl
    rw [← h_add_congr]
    exact h_τσ
  exact h_final.symm

theorem finite_dependence_add (b : RadixSeq) (L : ℕ)
    (τ τ' σ σ' : DirectLimitSpace b)
    (hτ : prefixProjection b L τ = prefixProjection b L τ')
    (hσ : prefixProjection b L σ = prefixProjection b L σ') :
    prefixProjection b L (add b τ σ) = prefixProjection b L (add b τ' σ') :=
  carry_locality b L τ τ' σ σ' hτ hσ

/-!
## Interpretation

These theorems establish that computations at "resolution L" cannot be influenced
by deeper scales. This is the mathematical foundation for:
- Hierarchical scheduling
- Locality by radix prefix
- Multi-rate execution systems
-/

end FdrsFormal.Topology.Locality
