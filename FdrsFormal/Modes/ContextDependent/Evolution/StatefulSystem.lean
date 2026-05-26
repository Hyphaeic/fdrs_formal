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

# Stateful Context-Dependent System

This file defines the complete stateful radix system.

## Mathematical Content (fdrs.md lines 5552-5574)

**Definition 89 (Stateful context-dependent system)**:
A stateful radix system is a tuple:

𝒮 := (Ω, 𝒞, c₀, Γ, ℰ)

where:
- Ω is an extended radix oracle
- 𝒞 is a context space
- c₀ ∈ 𝒞 is the initial context
- Γ : 𝒞 × ℰ → 𝒞 is the context dynamics
- ℰ is the event space

## References

- fdrs.md, Phase 7, Section 7.2 (lines 5552-5574)
- DEPENDENCY_BASED_STRUCTURE.md, Modes/ContextDependent/Evolution
-/

import FdrsFormal.Modes.ContextDependent.Evolution.ContextDynamics

namespace FdrsFormal.Modes.ContextDependent

open FdrsFormal.Modes.VariableRadix

/-!
## Stateful System
-/

/--
**Definition 89**: A stateful context-dependent radix system.

𝒮 = (Ω, 𝒞, c₀, Γ, ℰ)
-/
structure StatefulSystem (C : Type*) (E : Type*) [ContextSpace C] [InitialContext C] [EventSpace E] where
  /-- The extended radix oracle -/
  oracle : ExtendedOracle C
  /-- The context dynamics -/
  dynamics : ContextDynamics C E

/-- Get the initial context -/
def StatefulSystem.initialContext {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (_𝒮 : StatefulSystem C E) : C :=
  c₀

/-- Get the RadixLaw at a specific context -/
def StatefulSystem.radixAt {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) (c : C) : RadixLaw :=
  𝒮.oracle.atContext c

/-- Get the RadixLaw at the initial context -/
def StatefulSystem.initialRadix {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) : RadixLaw :=
  𝒮.radixAt c₀

/-!
## System State
-/

/-- The state of a running system at time t -/
structure SystemState (C : Type*) (E : Type*)
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) where
  /-- Current context -/
  context : C
  /-- Event history -/
  history : List E

/-- Initial system state -/
def StatefulSystem.initialState {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) : SystemState C E 𝒮 where
  context := c₀
  history := []

/-- Apply an event to the system state -/
def SystemState.step {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    {𝒮 : StatefulSystem C E} (state : SystemState C E 𝒮) (e : E) :
    SystemState C E 𝒮 where
  context := 𝒮.dynamics.transition state.context e
  history := e :: state.history

/-- The RadixLaw at the current system state -/
def SystemState.currentRadix {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    {𝒮 : StatefulSystem C E} (state : SystemState C E 𝒮) : RadixLaw :=
  𝒮.radixAt state.context

/-!
## System Properties
-/

/-- A system has CSU if its oracle has CSU -/
def StatefulSystem.hasCSU {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) : Prop :=
  FdrsFormal.Modes.ContextDependent.hasCSU 𝒮.oracle

/-- A system is context-independent if its oracle is -/
def StatefulSystem.isContextIndependent {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) : Prop :=
  𝒮.oracle.isContextIndependent

end FdrsFormal.Modes.ContextDependent
