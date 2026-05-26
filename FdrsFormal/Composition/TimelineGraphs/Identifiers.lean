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

# Timeline Identifier Space and Graph Structure

Defines the timeline identifier space and timeline graph tuple (𝒯, 𝒥, ρ).

## Mathematical Content (fdrs.md lines 5920-5948)

**Definition 107**: Timeline identifier space
**Definition 108**: Timeline graph structure 𝒢 = (𝒯, 𝒥, ρ)

## References

- fdrs.md, Phase 8, Section 8.1 (lines 5920-5948)
- DEPENDENCY_BASED_STRUCTURE.md, Tier 22
-/

import FdrsFormal.Composition.TimelineGraphs.Definition

namespace FdrsFormal.Composition.TimelineGraphs

/-! ## Definition 107: Timeline identifier space -/

/--
**fdrs.md**: Definition 107 (Timeline identifier space) [§8.1.1 · Phase 8] (lines 5920-5931)

A timeline identifier space is a set 𝒯. May be:
- Finite: 𝒯 = {T₁,...,T_n} (static system)
- Countable: 𝒯 = ℕ (dynamic spawning allowed)

Each T ∈ 𝒯 has a radix oracle Ω_T, context space 𝒞_T, and state space ℛ_T.

**Axiomatized**: Abstract type with decidable equality.
-/
structure TimelineIdentifierSpace where
  /-- The carrier type of timeline identifiers -/
  Carrier : Type
  /-- Decidable equality on identifiers -/
  decEq : DecidableEq Carrier
  /-- Whether the space is finite or countable -/
  isFinite : Bool

/-! ## Definition 108: Timeline graph structure -/

/--
**fdrs.md**: Definition 108 (Timeline graph structure) [§8.1.2 · Phase 8] (lines 5934-5948)

A timeline graph is a tuple 𝒢 := (𝒯, 𝒥, ρ) where:
- 𝒯 is the timeline identifier space
- 𝒥 ⊆ 𝒯 × Σ* × 𝒯 × Σ* is the set of junctions
- ρ is the routing function specifying actual transfers

A junction (A, s_A, B, s_B) ∈ 𝒥 connects source timeline A at cylinder
prefix s_A to target timeline B at cylinder prefix s_B.

**Axiomatized**: Composite structure over timeline identifiers and routing.
-/
structure TimelineGraphSpec where
  /-- Timeline identifier space -/
  identifiers : TimelineIdentifierSpace
  /-- Number of junctions (simplified) -/
  numJunctions : ℕ
  /-- Whether routing is static (table-based) or dynamic -/
  staticRouting : Bool

end FdrsFormal.Composition.TimelineGraphs
