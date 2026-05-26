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

# Contextual Sibling Uniformity (CSU)

This file defines contextual sibling uniformity for extended oracles.

## Mathematical Content (fdrs.md lines 5511-5521)

**Definition 86 (Contextual sibling uniformity - CSU)**:
Ω satisfies CSU if:

∀ c ∈ 𝒞, ∀ s ∈ Σ_L, ∀ d, e ∈ D_L: ω_c(s ∥ d) = ω_c(s ∥ e)

**Interpretation**: Within any fixed context c, siblings have the same radix.
Standard SU holds at each "snapshot" of context.

**Critical property**: This allows context to change over time while preserving
odometer properties at each instant.

## References

- fdrs.md, Phase 7, Section 7.1 (lines 5511-5521)
- DEPENDENCY_BASED_STRUCTURE.md, Modes/ContextDependent/Basic
-/

import FdrsFormal.Modes.ContextDependent.Basic.ExtendedOracle

namespace FdrsFormal.Modes.ContextDependent

open FdrsFormal.Modes.VariableRadix

/-!
## Contextual Sibling Uniformity
-/

/--
**Definition 86**: Contextual sibling uniformity (CSU).

An oracle Ω satisfies CSU if for each fixed context c,
the induced RadixLaw ω_c satisfies standard SU.
-/
def hasCSU {C : Type*} [ContextSpace C] (Ω : ExtendedOracle C) : Prop :=
  ∀ c : C, ∀ k : ℕ, isSiblingUniform (Ω.atContext c) k

/-- CSU at a specific context and depth -/
def hasCSU_at {C : Type*} [ContextSpace C]
    (Ω : ExtendedOracle C) (c : C) (k : ℕ) : Prop :=
  isSiblingUniform (Ω.atContext c) k

/-!
## CSU Properties
-/

/-- CSU implies SU for each context snapshot -/
theorem csu_implies_su {C : Type*} [ContextSpace C]
    (Ω : ExtendedOracle C) (hcsu : hasCSU Ω) (c : C) (k : ℕ) :
    isSiblingUniform (Ω.atContext c) k :=
  hcsu c k

/--
SU inheritance under position-only radix laws.

**Mathematical Note**: For general radix laws, SU is NOT monotone in depth (see
SiblingUniformity/Definition.lean for a counterexample). However, for position-only
radix laws (where radix depends only on prefix length, not prefix content), SU holds
at all depths automatically.

**Proof**: Delegates to `positionOnly_siblingUniform`, which proves SU at all
depths for position-only laws. The hypothesis `h` (SU at k+1) is not needed—
it's included for API compatibility but the result follows from position-only alone.
-/
theorem siblingUniform_of_succ (ω : RadixLaw) (k : ℕ)
    (h_posOnly : ∀ s t : PrefixWord, s.length = t.length → ω.radix s = ω.radix t)
    (_h : isSiblingUniform ω (k + 1)) :
    isSiblingUniform ω k :=
  positionOnly_siblingUniform ω k h_posOnly

/-- CSU is inherited from larger depths for position-only oracles. -/
theorem csu_of_succ {C : Type*} [ContextSpace C]
    (Ω : ExtendedOracle C) (c : C) (k : ℕ)
    (h_posOnly : ∀ s t : PrefixWord, s.length = t.length →
      (Ω.atContext c).radix s = (Ω.atContext c).radix t)
    (h : hasCSU_at Ω c (k + 1)) :
    hasCSU_at Ω c k :=
  siblingUniform_of_succ (Ω.atContext c) k h_posOnly h

/--
Context-independent oracle satisfies CSU iff the underlying RadixLaw satisfies SU.

**Proof**: If the oracle is context-independent, `Ω.atContext c` is the same
RadixLaw for all `c`. CSU reduces to SU at any single context.
-/
theorem contextIndependent_csu_iff {C : Type*} [ContextSpace C]
    (Ω : ExtendedOracle C) (hΩ : Ω.isContextIndependent) :
    hasCSU Ω ↔ ∀ k, isSiblingUniform (Ω.atContext (Classical.choice ContextSpace.nonempty)) k := by
  constructor
  · exact fun h k => h _ k
  · intro h c k
    have hradix : (Ω.atContext c).radix = (Ω.atContext (Classical.choice ContextSpace.nonempty)).radix :=
      funext fun s => hΩ s c _
    have : Ω.atContext c = Ω.atContext (Classical.choice ContextSpace.nonempty) := by
      unfold ExtendedOracle.atContext; congr 1
    rw [this]
    exact h k

/-!
## CSU and Odometer Charts
-/

/-- Under CSU, each context admits an odometer chart -/
theorem csu_admits_chart {C : Type*} [ContextSpace C]
    (Ω : ExtendedOracle C) (hcsu : hasCSU Ω) (c : C) (k : ℕ) :
    ∃ (φ : FiniteVariableSpace (Ω.atContext c) k ≃ Fin (completionCount (Ω.atContext c) k emptyPrefix)),
      Function.Bijective φ := by
  use finiteVariableRadixEquiv (Ω.atContext c) k
  exact (finiteVariableRadixEquiv (Ω.atContext c) k).bijective

/-- CSU ensures well-defined block sizes at each context -/
theorem csu_blockSize_wellDefined {C : Type*} [ContextSpace C]
    (Ω : ExtendedOracle C) (hcsu : hasCSU Ω) (c : C) (k : ℕ)
    (s : PrefixWord) (hs : s.length < k) (d : ℕ) (hd : d < (Ω.atContext c).radix s) :
    blockSize (Ω.atContext c) k s =
      completionCount (Ω.atContext c) k (s ++ [d]) :=
  blockSize_eq_completionCount (Ω.atContext c) k (hcsu c k) s hs d hd

end FdrsFormal.Modes.ContextDependent
