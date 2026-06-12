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

# Extended Radix Oracle

This file defines the extended radix oracle for context-dependent systems.

## Mathematical Content (fdrs.md lines 5499-5509)

**Definition 85 (Extended radix oracle)**:
An extended radix oracle is a function:

Ω : Σ* × 𝒞 → ℕ≥2

that maps (prefix, context) pairs to radix values.

Key properties:
- Generalizes RadixLaw by adding context parameter
- For fixed context c, Ω(·, c) is a standard RadixLaw
- Enables adaptive/reactive sizing

## References

- fdrs.md, Phase 7, Section 7.1 (lines 5499-5509)
-/

import FdrsFormal.Modes.ContextDependent.Basic.ContextSpace

namespace FdrsFormal.Modes.ContextDependent

open FdrsFormal.Modes.VariableRadix

/-!
## Extended Radix Oracle
-/

/--
**Definition 85**: An extended radix oracle.

Ω : Σ* × 𝒞 → ℕ≥2

Maps (prefix, context) pairs to radix values ≥ 2.
-/
structure ExtendedOracle (C : Type*) [ContextSpace C] where
  /-- The oracle function -/
  radix : PrefixWord → C → ℕ
  /-- Radix is always at least 2 -/
  radix_ge_two : ∀ s c, 2 ≤ radix s c

/-- Extract a RadixLaw for a fixed context -/
def ExtendedOracle.atContext {C : Type*} [ContextSpace C]
    (Ω : ExtendedOracle C) (c : C) : RadixLaw where
  radix := fun s => Ω.radix s c
  radix_ge_two := fun s => Ω.radix_ge_two s c

/-- Notation for oracle at fixed context -/
notation:max Ω "[" c "]" => ExtendedOracle.atContext Ω c

/-!
## Oracle Properties
-/

/-- An oracle is context-independent if it doesn't depend on context -/
def ExtendedOracle.isContextIndependent {C : Type*} [ContextSpace C]
    (Ω : ExtendedOracle C) : Prop :=
  ∀ s c₁ c₂, Ω.radix s c₁ = Ω.radix s c₂

/-- Convert a RadixLaw to a context-independent oracle -/
def RadixLaw.toOracle {C : Type*} [ContextSpace C] (ω : RadixLaw) : ExtendedOracle C where
  radix := fun s _ => ω.radix s
  radix_ge_two := fun s _ => ω.radix_ge_two s

/-- A context-independent oracle comes from a RadixLaw -/
theorem ExtendedOracle.contextIndependent_iff_fromRadixLaw {C : Type*} [ContextSpace C]
    (Ω : ExtendedOracle C) :
    Ω.isContextIndependent ↔
      ∃ ω : RadixLaw, ∀ s c, Ω.radix s c = ω.radix s := by
  constructor
  · -- Forward: if context-independent, extract a RadixLaw
    intro hci
    -- Pick any context to define the RadixLaw
    haveI : Nonempty C := ContextSpace.nonempty (C := C)
    use Ω.atContext (Classical.arbitrary C)
    intro s c
    -- By context-independence, Ω.radix s c = Ω.radix s c₀
    exact hci s c (Classical.arbitrary C)
  · -- Backward: if comes from RadixLaw, then context-independent
    intro ⟨ω, hω⟩
    intro s c₁ c₂
    rw [hω s c₁, hω s c₂]

/-!
## Context-Indexed Family
-/

/--
**fdrs.md**: Definition 87 (Context-indexed mixed-radix family) [§7.1.4 · Phase 7] (lines 5523-5525)

For each context c ∈ 𝒞, we get a standard RadixLaw ω_c := Ω(·, c).
-/
def ExtendedOracle.family {C : Type*} [ContextSpace C]
    (Ω : ExtendedOracle C) : C → RadixLaw :=
  fun c => Ω.atContext c

/-- The family is consistent: same oracle gives same RadixLaw -/
theorem ExtendedOracle.family_consistent {C : Type*} [ContextSpace C]
    (Ω : ExtendedOracle C) (c : C) :
    (Ω.family c).radix = fun s => Ω.radix s c := by
  rfl

end FdrsFormal.Modes.ContextDependent
