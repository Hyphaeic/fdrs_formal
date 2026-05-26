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

# Context Dynamics

This file defines the dynamics of context evolution.

## Mathematical Content (fdrs.md lines 5540-5550)

**Definition 88 (Context dynamics)**:
A context dynamics is a function:

Γ : 𝒞 × ℰ → 𝒞

where ℰ is an event space. Γ(c, e) = c' means:
"In context c, event e causes transition to context c'."

## References

- fdrs.md, Phase 7, Section 7.2 (lines 5540-5550)
- DEPENDENCY_BASED_STRUCTURE.md, Modes/ContextDependent/Evolution
-/

import FdrsFormal.Modes.ContextDependent.Basic.Basic

namespace FdrsFormal.Modes.ContextDependent

/-!
## Event Space
-/

/-- An event space -/
class EventSpace (E : Type*) where
  /-- Event space is nonempty -/
  nonempty : Nonempty E

/-- The trivial event space (no events) -/
instance : EventSpace Unit where
  nonempty := ⟨()⟩

/-!
## Context Dynamics
-/

/--
**Definition 88**: Context dynamics.

Γ : 𝒞 × ℰ → 𝒞

Describes how events cause context transitions.
-/
structure ContextDynamics (C : Type*) (E : Type*) [ContextSpace C] [EventSpace E] where
  /-- The transition function -/
  transition : C → E → C

/-- Apply a single transition -/
def ContextDynamics.step {C E : Type*} [ContextSpace C] [EventSpace E]
    (Γ : ContextDynamics C E) (c : C) (e : E) : C :=
  Γ.transition c e

/-- Notation for context transition -/
notation:50 c " ⟶[" e "] " Γ => ContextDynamics.step Γ c e

/-!
## Dynamics Properties
-/

/-- A dynamics is trivial if it never changes context -/
def ContextDynamics.isTrivial {C E : Type*} [ContextSpace C] [EventSpace E]
    (Γ : ContextDynamics C E) : Prop :=
  ∀ c e, Γ.transition c e = c

/-- A dynamics is deterministic: same inputs always produce same output.
    Always true for our function-based definition; included for API completeness. -/
def ContextDynamics.isDeterministic {C E : Type*} [ContextSpace C] [EventSpace E]
    (Γ : ContextDynamics C E) : Prop :=
  ∀ c : C, ∀ e : E, ∀ c₁ c₂ : C,
    Γ.transition c e = c₁ → Γ.transition c e = c₂ → c₁ = c₂

/-- Every context dynamics is deterministic (functions are deterministic by construction). -/
theorem ContextDynamics.isDeterministic_always {C E : Type*} [ContextSpace C] [EventSpace E]
    (Γ : ContextDynamics C E) : Γ.isDeterministic :=
  fun _ _ _ _ h₁ h₂ => h₁.symm.trans h₂

/-- The trivial dynamics that never changes context -/
def ContextDynamics.trivial (C : Type*) (E : Type*) [ContextSpace C] [EventSpace E] :
    ContextDynamics C E where
  transition := fun c _ => c

theorem ContextDynamics.trivial_isTrivial (C E : Type*) [ContextSpace C] [EventSpace E] :
    (ContextDynamics.trivial C E).isTrivial := by
  intro c e
  rfl

/-!
## Multi-Step Dynamics
-/

/-- Apply a sequence of events -/
def ContextDynamics.applySeq {C E : Type*} [ContextSpace C] [EventSpace E]
    (Γ : ContextDynamics C E) (c : C) : List E → C
  | [] => c
  | e :: es => Γ.applySeq (Γ.transition c e) es

/-- The empty sequence leaves context unchanged -/
theorem ContextDynamics.applySeq_nil {C E : Type*} [ContextSpace C] [EventSpace E]
    (Γ : ContextDynamics C E) (c : C) :
    Γ.applySeq c ([] : List E) = c := rfl

/-- Sequential application is associative -/
theorem ContextDynamics.applySeq_append {C E : Type*} [ContextSpace C] [EventSpace E]
    (Γ : ContextDynamics C E) (c : C) (es₁ es₂ : List E) :
    Γ.applySeq c (es₁ ++ es₂) = Γ.applySeq (Γ.applySeq c es₁) es₂ := by
  induction es₁ generalizing c with
  | nil => rfl
  | cons e es ih => simp only [List.cons_append, applySeq, ih]

end FdrsFormal.Modes.ContextDependent
