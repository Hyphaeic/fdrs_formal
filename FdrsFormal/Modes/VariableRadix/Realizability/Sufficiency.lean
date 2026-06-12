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

# Sufficiency of Realizability Conditions

This file proves the backward direction of THEOREM B:
If an ultrametric satisfies the three conditions, then it equals δ_ω for some SU ω.

## Mathematical Content (fdrs.md lines 5396-5402)

Given an ultrametric δ satisfying cylinder correspondence, monotone refinement,
and finite branching:
1. Construct ω by assigning radices equal to branching factors at each cylinder
2. Cylinder correspondence ensures this is well-defined
3. Monotone refinement ensures β_ω matches ball radii
4. SU follows from uniform ball radii for siblings

## References

- fdrs.md, Phase 6, Section 6.6 (lines 5396-5402)
- Paper (external draft): Theorem B (§6.3), sufficiency direction
-/

import FdrsFormal.Modes.VariableRadix.Realizability.Necessity

namespace FdrsFormal.Modes.VariableRadix

/-!
## Abstract Ultrametric Structure
-/

/-- An abstract ultrametric on a product space -/
structure AbstractUltrametric where
  /-- The digit sets at each position -/
  digitSets : ℕ → Type
  /-- The digit sets are finite -/
  digitSets_finite : ∀ i, Finite (digitSets i)
  /-- The distance function -/
  dist : (∀ i, digitSets i) → (∀ i, digitSets i) → ℝ
  /-- Non-negativity -/
  dist_nonneg : ∀ x y, 0 ≤ dist x y
  /-- Identity of indiscernibles -/
  dist_eq_zero_iff : ∀ x y, dist x y = 0 ↔ x = y
  /-- Symmetry -/
  dist_symm : ∀ x y, dist x y = dist y x
  /-- Strong triangle inequality -/
  dist_ultrametric : ∀ x y z, dist x z ≤ max (dist x y) (dist y z)

/-!
## Realizability Conditions on an Abstract Ultrametric

The full Theorem 43 sufficiency direction needs three conditions on `δ`:
**cylinder correspondence**, **monotone refinement**, and **finite branching**.
The first two require an alignment of `δ`'s underlying type
`∀ i, δ.digitSets i` with the prefix-cylinder structure used in the rest of the
formalization — infrastructure that is not yet provided at the `AbstractUltrametric`
level. We therefore capture only the **branching slice** of the conditions here,
in a form that supports a non-trivial construction of a sibling-uniform radix
law from `δ`. The structure is left open so additional conditions can be added
without breaking downstream signatures.
-/

/--
Abstract realizability conditions on `δ : AbstractUltrametric`.

Currently captures the branching-content of Theorem 43 sufficiency: each digit
set has at least two elements, the natural abstract analogue of "the radix is at
least 2 everywhere". Cylinder correspondence and monotone refinement are not
expressible directly on `AbstractUltrametric` without additional alignment
infrastructure (cylinders, ball radii on `∀ i, δ.digitSets i`).
-/
structure AbstractRealizabilityConditions (δ : AbstractUltrametric) : Prop where
  /--
  Each digit set has at least 2 elements. Necessary because the constructed
  radix law must satisfy `ω.radix s ≥ 2` everywhere.
  -/
  digitSets_geTwo : ∀ i, 2 ≤ Nat.card (δ.digitSets i)

/-!
## Construction of a Sibling-Uniform Radix Law from an Abstract Ultrametric
-/

/--
The radix law derived from `δ`: at any prefix of length `L`, the radix equals
the cardinality of `δ.digitSets L`.

This is the "branching-only" content of Theorem 43 sufficiency: the construction
is position-only (depends on `s.length`, not on the digits of `s`), which is the
strongest form of sibling uniformity. The full Theorem 43 would additionally
characterize the cardinalities by ball-refinement counts on `δ`, but the
construction itself is well-defined from digit-set cardinalities alone.
-/
noncomputable def radixLawFromUltrametric (δ : AbstractUltrametric)
    (h : AbstractRealizabilityConditions δ) : RadixLaw where
  radix := fun s => Nat.card (δ.digitSets s.length)
  radix_ge_two := fun s => h.digitSets_geTwo s.length

/--
The radix law `radixLawFromUltrametric δ h` is sibling-uniform at every depth.

The construction is position-only by design — `ω.radix` depends only on
`s.length` — and position-only radix laws are sibling-uniform at every depth
(`positionOnly_siblingUniform`).
-/
theorem radixLawFromUltrametric_su (δ : AbstractUltrametric)
    (h : AbstractRealizabilityConditions δ) (k : ℕ) :
    isSiblingUniform (radixLawFromUltrametric δ h) k := by
  apply positionOnly_siblingUniform
  intro s t hlen
  show Nat.card (δ.digitSets s.length) = Nat.card (δ.digitSets t.length)
  rw [hlen]

/-!
## Sufficiency Theorem (Branching Slice)
-/

/--
**Theorem 43 sufficiency — branching slice**.

Given an abstract ultrametric `δ` whose digit sets all have at least two
elements, there exists a sibling-uniform radix law `ω` whose radix at every
prefix `s` matches the cardinality of `δ.digitSets s.length`.

The full Theorem 43 additionally asserts `δ = δ_ω` as ultrametrics; that
equality requires aligning `∀ i, δ.digitSets i` with `InfiniteVariableSpace ω`,
which is not yet provided at the `AbstractUltrametric` level. The combinatorial
side of the correspondence — that the branching schedule of `ω` matches the
digit-set cardinalities of `δ` — is established here.
-/
theorem theoremB_sufficiency (δ : AbstractUltrametric)
    (h : AbstractRealizabilityConditions δ) :
    ∃ (ω : RadixLaw),
      (∀ k, isSiblingUniform ω k) ∧
      (∀ s : PrefixWord, ω.radix s = Nat.card (δ.digitSets s.length)) := by
  refine ⟨radixLawFromUltrametric δ h, ?_, ?_⟩
  · intro k; exact radixLawFromUltrametric_su δ h k
  · intro _; rfl

/-!
## Remaining work for the full Theorem 43 (`δ = δ_ω`)

`theoremB_sufficiency` establishes the combinatorial (branching-schedule) half of
Theorem 43. Upgrading it to the full *metric* statement `δ = δ_ω` requires, in order:

1. **Cylinders and ball radii on `∀ i, δ.digitSets i`** — the abstract analogue of
   the prefix-cylinder structure used in `InducedUltrametric`.
2. **Encode the two remaining realizability conditions** as `Prop`s on `δ`:
   *cylinder correspondence* (every `δ`-ball is a finite union of cylinders) and
   *monotone refinement* (containment orders ball radii). (*Finite branching* is
   already captured by `digitSets_geTwo`.)
3. **Derive the metric form**: from (2), `δ.dist x y` equals the inverse prefix
   weight at the first position where `x` and `y` differ — i.e. `δ` is the
   first-difference ultrametric. This is the crux, and it is FALSE for an arbitrary
   `AbstractUltrametric`; that is precisely why the present
   `AbstractRealizabilityConditions` (carrying only `digitSets_geTwo`) is insufficient
   to conclude `δ = δ_ω`, and why this file proves the branching slice only.
4. **Space alignment** `(∀ i, δ.digitSets i) ≃ InfiniteVariableSpace ω` via the
   pointwise `δ.digitSets i ≃ Fin (Nat.card (δ.digitSets i))` (finite sets of equal
   cardinality).
5. **Transport** the metric equality of (3) across the alignment of (4) to conclude
   `δ = δ_ω`.

Mathematically this is the classical ultrametric ↔ rooted-tree (dendrogram)
correspondence; the outstanding work is the Lean infrastructure, not new mathematics.
-/

/-!
## Uniqueness
-/

/-- Prefix weights uniquely determine the radix function:
if two radix laws have the same prefix weights everywhere,
they have the same radix function. -/
theorem radixLaw_unique (ω₁ ω₂ : RadixLaw)
    (hpw : ∀ s, prefixWeight ω₁ s = prefixWeight ω₂ s) :
    ∀ s, ω₁.radix s = ω₂.radix s := by
  intro s
  have h1 := prefixWeight_append ω₁ s 0
  have h2 := prefixWeight_append ω₂ s 0
  have : prefixWeight ω₁ s * ω₁.radix s = prefixWeight ω₁ s * ω₂.radix s := by
    rw [← h1, hpw (s ++ [0]), h2, hpw s]
  exact mul_left_cancel₀ (prefixWeight_pos ω₁ s).ne' this

end FdrsFormal.Modes.VariableRadix
