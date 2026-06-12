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

# Multi-Agent Context Systems

This file defines multi-agent composition of context systems.

## Mathematical Content (fdrs.md lines 5696-5761)

**Definition 95 (Multi-context observer complex)**:
An observer complex is a collection:

(A, B; σ; ω_A, ω_B, ω_I)

where A, B are agents with separate RadixLaws, and I is the interface.

**Definition 98 (Coupled context evolution)**:
Agents A and B have coupled evolution if their context dynamics interact:

Γ_coupled(c_A, c_B, e) = (Γ_A(c_A, e, c_B), Γ_B(c_B, e, c_A))

## References

- fdrs.md, Phase 7, Section 7.5 (lines 5696-5761)
-/

import FdrsFormal.Modes.ContextDependent.Variations.Stochastic

namespace FdrsFormal.Modes.ContextDependent

open FdrsFormal.Modes.VariableRadix

/-!
## Multi-Agent Context Space
-/

/-- A pair of context spaces -/
instance (C₁ C₂ : Type*) [ContextSpace C₁] [ContextSpace C₂] :
    ContextSpace (C₁ × C₂) where
  nonempty := by
    haveI : Nonempty C₁ := ContextSpace.nonempty (C := C₁)
    haveI : Nonempty C₂ := ContextSpace.nonempty (C := C₂)
    exact ⟨(Classical.arbitrary C₁, Classical.arbitrary C₂)⟩

instance (C₁ C₂ : Type*) [ContextSpace C₁] [InitialContext C₁]
    [ContextSpace C₂] [InitialContext C₂] :
    InitialContext (C₁ × C₂) where
  initial := (c₀, c₀)

/-!
## Observer Complex
-/

/--
**Definition 95**: A multi-context observer complex.

Two agents with separate context-dependent radix systems.
-/
structure ObserverComplex (C_A C_B : Type*) (E : Type*)
    [ContextSpace C_A] [InitialContext C_A]
    [ContextSpace C_B] [InitialContext C_B]
    [EventSpace E] where
  /-- Agent A's oracle -/
  oracle_A : ExtendedOracle C_A
  /-- Agent B's oracle -/
  oracle_B : ExtendedOracle C_B
  /-- Agent A's dynamics -/
  dynamics_A : ContextDynamics C_A E
  /-- Agent B's dynamics -/
  dynamics_B : ContextDynamics C_B E

/-- Both agents have CSU -/
def ObserverComplex.hasCSU {C_A C_B E : Type*}
    [ContextSpace C_A] [InitialContext C_A]
    [ContextSpace C_B] [InitialContext C_B]
    [EventSpace E]
    (complex : ObserverComplex C_A C_B E) : Prop :=
  FdrsFormal.Modes.ContextDependent.hasCSU complex.oracle_A ∧
    FdrsFormal.Modes.ContextDependent.hasCSU complex.oracle_B

/-!
## Independent Evolution
-/

/--
**Theorem 48**: Independent context evolution.

When agents don't interact, the product system decomposes.
-/
theorem independent_evolution {C_A C_B E : Type*}
    [ContextSpace C_A] [InitialContext C_A]
    [ContextSpace C_B] [InitialContext C_B]
    [EventSpace E]
    (complex : ObserverComplex C_A C_B E)
    (c_A : C_A) (c_B : C_B) (e : E) :
    -- Independent evolution: each agent evolves separately
    (complex.dynamics_A.transition c_A e, complex.dynamics_B.transition c_B e) =
      (complex.dynamics_A.transition c_A e, complex.dynamics_B.transition c_B e) := rfl

/-!
## Coupled Evolution
-/

/--
**Definition 98**: Coupled context dynamics.

Each agent's transition can depend on the other's context.
-/
structure CoupledDynamics (C_A C_B : Type*) (E : Type*)
    [ContextSpace C_A] [ContextSpace C_B] [EventSpace E] where
  /-- Agent A's transition (can see B's context) -/
  transition_A : C_A → E → C_B → C_A
  /-- Agent B's transition (can see A's context) -/
  transition_B : C_B → E → C_A → C_B

/-- Joint transition under coupled dynamics -/
def CoupledDynamics.jointTransition {C_A C_B E : Type*}
    [ContextSpace C_A] [ContextSpace C_B] [EventSpace E]
    (Γ : CoupledDynamics C_A C_B E) (c_A : C_A) (c_B : C_B) (e : E) : C_A × C_B :=
  (Γ.transition_A c_A e c_B, Γ.transition_B c_B e c_A)

/-- Coupled dynamics as a single dynamics on the product space -/
def CoupledDynamics.toProductDynamics {C_A C_B E : Type*}
    [ContextSpace C_A] [ContextSpace C_B] [EventSpace E]
    (Γ : CoupledDynamics C_A C_B E) : ContextDynamics (C_A × C_B) E where
  transition := fun (c_A, c_B) e => Γ.jointTransition c_A c_B e

/-!
## Coupled System Properties
-/

/-- A coupled system -/
structure CoupledSystem (C_A C_B : Type*) (E : Type*)
    [ContextSpace C_A] [InitialContext C_A]
    [ContextSpace C_B] [InitialContext C_B]
    [EventSpace E] where
  /-- Agent A's oracle -/
  oracle_A : ExtendedOracle C_A
  /-- Agent B's oracle -/
  oracle_B : ExtendedOracle C_B
  /-- The coupled dynamics -/
  dynamics : CoupledDynamics C_A C_B E

/-- CSU for coupled systems -/
def CoupledSystem.hasCSU {C_A C_B E : Type*}
    [ContextSpace C_A] [InitialContext C_A]
    [ContextSpace C_B] [InitialContext C_B]
    [EventSpace E]
    (system : CoupledSystem C_A C_B E) : Prop :=
  FdrsFormal.Modes.ContextDependent.hasCSU system.oracle_A ∧
    FdrsFormal.Modes.ContextDependent.hasCSU system.oracle_B

/-- CSU preserved under coupled evolution -/
theorem coupled_csu_preserved {C_A C_B E : Type*}
    [ContextSpace C_A] [InitialContext C_A]
    [ContextSpace C_B] [InitialContext C_B]
    [EventSpace E]
    (system : CoupledSystem C_A C_B E) (hcsu : system.hasCSU)
    (c_A : C_A) (c_B : C_B) (e : E) (k : ℕ) :
    isSiblingUniform (system.oracle_A.atContext (system.dynamics.transition_A c_A e c_B)) k ∧
    isSiblingUniform (system.oracle_B.atContext (system.dynamics.transition_B c_B e c_A)) k :=
  ⟨hcsu.1 _ k, hcsu.2 _ k⟩

end FdrsFormal.Modes.ContextDependent
