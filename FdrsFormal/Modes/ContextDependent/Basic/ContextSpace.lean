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

# Context Space Definition

This file defines the context space for context-dependent radix systems.

## Mathematical Content (fdrs.md lines 5481-5497)

**Definition 84 (Context space)**:
A context space is a set 𝒞 representing possible "states of the world"
that can influence the radix function.

Contexts can represent:
- Computational resources (memory availability)
- External inputs (sensor data)
- Time-varying parameters
- Stochastic states

## References

- fdrs.md, Phase 7, Section 7.1 (lines 5481-5497)
-/

import FdrsFormal.Modes.VariableRadix.VariableRadix

namespace FdrsFormal.Modes.ContextDependent

/-!
## Context Space
-/

/--
**Definition 84**: A context space.

A context space 𝒞 is a type representing possible external states
that can influence the radix function.
-/
class ContextSpace (C : Type*) where
  /-- Context space is nonempty -/
  nonempty : Nonempty C

/-- The context space has a distinguished initial context -/
class InitialContext (C : Type*) [ContextSpace C] where
  /-- The initial context c₀ -/
  initial : C

/-- Notation for the initial context -/
notation "c₀" => InitialContext.initial

/-!
## Context Space Properties
-/

/-- A finite context space -/
class FiniteContextSpace (C : Type*) extends ContextSpace C where
  /-- The context space is finite -/
  finite : Finite C

/-- A countable context space -/
class CountableContextSpace (C : Type*) extends ContextSpace C where
  /-- The context space is countable -/
  countable : Countable C

/-- Finite implies countable -/
instance (C : Type*) [FiniteContextSpace C] : CountableContextSpace C where
  countable := by
    haveI : Finite C := FiniteContextSpace.finite
    infer_instance

/-!
## Examples
-/

/-- The trivial context space with one element -/
instance : ContextSpace Unit where
  nonempty := ⟨()⟩

instance : InitialContext Unit where
  initial := ()

/-- Natural numbers as a context space (infinite) -/
instance : ContextSpace ℕ where
  nonempty := ⟨0⟩

instance : InitialContext ℕ where
  initial := 0

instance : CountableContextSpace ℕ where
  countable := instCountableNat

/-- Fin n as a finite context space -/
instance (n : ℕ) [NeZero n] : ContextSpace (Fin n) where
  nonempty := ⟨0⟩

instance (n : ℕ) [NeZero n] : InitialContext (Fin n) where
  initial := 0

instance (n : ℕ) [NeZero n] : FiniteContextSpace (Fin n) where
  finite := inferInstance

end FdrsFormal.Modes.ContextDependent
