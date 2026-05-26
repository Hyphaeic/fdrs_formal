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

# Realization Strategies

This file defines lazy vs eager realization strategies.

## Mathematical Content (fdrs.md lines 5613-5627)

**Definition 92 (Lazy vs eager realization)**:
For a context-dependent system 𝒮:

**Eager realization**: All cylinders at depth ≤ L are pre-allocated for all
contexts in some finite reachable set 𝒞_reach ⊆ 𝒞.

**Lazy realization**: Cylinders are materialized only when accessed:
  Materialized(t) := {U_c(s) : s accessed by time t, c ∈ {c₀, ..., c_t}}

**Trade-off**:
- Eager: O(|𝒞_reach| · B_L) memory, O(1) access
- Lazy: O(accessed) memory, potential cache miss

## References

- fdrs.md, Phase 7, Section 7.3 (lines 5613-5627)
- DEPENDENCY_BASED_STRUCTURE.md, Modes/ContextDependent/Realization
-/

import FdrsFormal.Modes.ContextDependent.Evolution.Evolution

namespace FdrsFormal.Modes.ContextDependent

open FdrsFormal.Modes.VariableRadix

/-!
## Access Patterns
-/

/-- An access to the radix structure -/
structure Access (C : Type*) where
  /-- The prefix being accessed -/
  «prefix» : PrefixWord
  /-- The context at access time -/
  context : C

/-- An access pattern is a sequence of accesses -/
abbrev AccessPattern (C : Type*) := List (Access C)

/-- The set of accesses up to time t -/
def AccessPattern.upTo {C : Type*} (pattern : AccessPattern C) (t : ℕ) : List (Access C) :=
  pattern.take t

/-!
## Eager Realization
-/

/--
**Eager realization**: Pre-allocate all cylinders at depth ≤ L for all reachable contexts.
-/
structure EagerRealization (C : Type*) (E : Type*)
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) where
  /-- Maximum depth to pre-allocate -/
  depth : ℕ
  /-- The set of reachable contexts to pre-allocate -/
  reachable : Finset C
  /-- Initial context is reachable -/
  initial_reachable : c₀ ∈ reachable
  /-- Pre-allocated cylinder data for each (context, prefix) pair -/
  data : (c : C) → (c ∈ reachable) → (s : PrefixWord) → (s.length ≤ depth) → ℕ

/-- Memory cost of eager realization -/
def EagerRealization.memoryCost {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    {𝒮 : StatefulSystem C E} (eager : EagerRealization C E 𝒮) : ℕ :=
  eager.reachable.card * (completionCount (𝒮.radixAt c₀) eager.depth ([] : PrefixWord))

/-- Access cost for eager realization (constant) -/
def EagerRealization.accessCost {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    {𝒮 : StatefulSystem C E} (_eager : EagerRealization C E 𝒮) : ℕ :=
  1

/-!
## Lazy Realization
-/

/--
**Lazy realization**: Materialize cylinders only when accessed.
-/
structure LazyRealization (C : Type*) (E : Type*)
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) where
  /-- The set of materialized (context, prefix) pairs -/
  materialized : Finset (C × PrefixWord)
  /-- Cached radix values -/
  cache : (c : C) → (s : PrefixWord) → ((c, s) ∈ materialized) → ℕ

/-- Initial lazy realization (nothing materialized) -/
def LazyRealization.initial {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) : LazyRealization C E 𝒮 where
  materialized := ∅
  cache := fun _ _ h => absurd h (by simp)

/-- Materialize a new (context, prefix) pair -/
def LazyRealization.materialize {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E] [DecidableEq C]
    {𝒮 : StatefulSystem C E} (lazy : LazyRealization C E 𝒮)
    (c : C) (s : PrefixWord) : LazyRealization C E 𝒮 := by
  refine ⟨Insert.insert (c, s) lazy.materialized, ?cache⟩
  intro c' s' h
  by_cases heq : (c', s') = (c, s)
  · exact 𝒮.oracle.radix s' c'
  · have : (c', s') ∈ lazy.materialized := by
      simp only [Finset.mem_insert] at h
      exact h.resolve_left heq
    exact lazy.cache c' s' this

/-- Memory cost of lazy realization -/
def LazyRealization.memoryCost {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    {𝒮 : StatefulSystem C E} (lazy : LazyRealization C E 𝒮) : ℕ :=
  lazy.materialized.card

/-!
## Realization State
-/

/-- A realization strategy -/
inductive RealizationStrategy
  | eager
  | lazy

/-- The value returned by accessing (c, s) -/
def accessValue {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) (c : C) (s : PrefixWord) : ℕ :=
  𝒮.oracle.radix s c

end FdrsFormal.Modes.ContextDependent
