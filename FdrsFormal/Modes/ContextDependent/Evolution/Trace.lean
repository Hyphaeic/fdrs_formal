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

# System Traces

This file defines traces (event sequences) for stateful systems.

## Mathematical Content (fdrs.md lines 5576-5587)

**Definition 90 (Trace of a stateful system)**:
A trace is a sequence of events (e₀, e₁, ...) that induces a sequence
of contexts (c₀, c₁, ...) where c_{i+1} = Γ(c_i, e_i).

The trace captures the complete history of context evolution.

## References

- fdrs.md, Phase 7, Section 7.2 (lines 5576-5587)
- DEPENDENCY_BASED_STRUCTURE.md, Modes/ContextDependent/Evolution
-/

import FdrsFormal.Modes.ContextDependent.Evolution.StatefulSystem

namespace FdrsFormal.Modes.ContextDependent

/-!
## Finite Traces
-/

/--
**Definition 90**: A finite trace of a stateful system.

A trace is a sequence of events together with the induced context sequence.
-/
structure FiniteTrace (C : Type*) (E : Type*)
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) where
  /-- The sequence of events -/
  events : List E
  /-- The sequence of contexts (length = events.length + 1) -/
  contexts : List C
  /-- Contexts starts with initial context -/
  contexts_init : contexts.head? = some c₀
  /-- Contexts has correct length -/
  contexts_length : contexts.length = events.length + 1
  /-- Contexts are consistent with dynamics -/
  contexts_consistent : ∀ i : ℕ, (hi : i < events.length) →
    contexts[i + 1]? = some (𝒮.dynamics.transition (contexts[i]'(by omega)) (events[i]'hi))

/-- The empty trace (no events) -/
def StatefulSystem.emptyTrace {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) : FiniteTrace C E 𝒮 where
  events := []
  contexts := [c₀]
  contexts_init := rfl
  contexts_length := rfl
  contexts_consistent := fun i hi => absurd hi (Nat.not_lt_zero i)

/-- The final context of a trace -/
def FiniteTrace.finalContext {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    {𝒮 : StatefulSystem C E} (trace : FiniteTrace C E 𝒮) : C :=
  trace.contexts.getLast (List.ne_nil_of_length_pos (by
    have h := trace.contexts_length; omega))

/-- Build a trace from an event sequence -/
def StatefulSystem.buildTrace {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) (events : List E) : FiniteTrace C E 𝒮 := by
  refine ⟨events, ?contexts, ?init, ?len, ?consist⟩
  · -- Build context sequence
    exact events.scanl (fun c e => 𝒮.dynamics.transition c e) c₀
  · -- Initial context
    cases events with
    | nil => rfl
    | cons e es => simp [List.scanl]
  · -- Length
    simp only [List.length_scanl]
  · -- Consistency
    intro i hi
    -- contexts = events.scanl f c₀ where f = transition
    -- Need: contexts[i+1] = f (contexts[i]) (events[i])
    have hlen : (events.scanl (fun c e => 𝒮.dynamics.transition c e) c₀).length = events.length + 1 :=
      List.length_scanl
    have hi1 : i + 1 < (events.scanl (fun c e => 𝒮.dynamics.transition c e) c₀).length := by
      rw [hlen]; omega
    have hi0 : i < (events.scanl (fun c e => 𝒮.dynamics.transition c e) c₀).length := by
      rw [hlen]; omega
    rw [List.getElem?_eq_some_iff]
    use hi1
    rw [List.getElem_scanl, List.getElem_scanl]
    -- Now: foldl f c₀ (events.take (i+1)) = f (foldl f c₀ (events.take i)) events[i]
    have htake : events.take (i + 1) = events.take i ++ [events[i]'hi] := by
      rw [List.take_add_one]
      simp only [List.getElem?_eq_getElem hi, Option.toList_some]
    rw [htake, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]

/-!
## Infinite Traces
-/

/-- An infinite trace (stream of events) -/
structure InfiniteTrace (C : Type*) (E : Type*)
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) where
  /-- The infinite event stream -/
  events : ℕ → E
  /-- The induced context stream -/
  contexts : ℕ → C
  /-- Initial context -/
  contexts_init : contexts 0 = c₀
  /-- Contexts are consistent with dynamics -/
  contexts_succ : ∀ n, contexts (n + 1) = 𝒮.dynamics.transition (contexts n) (events n)

/-- Build an infinite trace from an event stream -/
def StatefulSystem.buildInfiniteTrace {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) (events : ℕ → E) : InfiniteTrace C E 𝒮 where
  events := events
  contexts := fun n => 𝒮.dynamics.applySeq c₀ (List.ofFn (fun i : Fin n => events i))
  contexts_init := by simp [ContextDynamics.applySeq]
  contexts_succ := fun n => by
    -- contexts n = applySeq c₀ (List.ofFn (events up to n))
    -- contexts (n+1) = applySeq c₀ (List.ofFn (events up to n+1))
    -- Need: contexts (n+1) = transition (contexts n) (events n)
    show _ = _
    -- List.ofFn for n+1 elements = List.ofFn for n elements ++ [events n]
    have h_split : List.ofFn (fun i : Fin (n + 1) => events i.val) =
        List.ofFn (fun i : Fin n => events i.val) ++ [events n] := by
      conv_lhs => rw [List.ofFn_succ']
      simp only [List.concat_eq_append, Fin.last, Fin.val_castSucc]
    rw [h_split, ContextDynamics.applySeq_append]
    -- applySeq c [e] = transition c e
    simp only [ContextDynamics.applySeq]

/-!
## Trace Properties
-/

/-- A trace is context-stationary if context never changes -/
def FiniteTrace.isStationary {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    {𝒮 : StatefulSystem C E} (trace : FiniteTrace C E 𝒮) : Prop :=
  ∀ c ∈ trace.contexts, c = c₀

/-- A trace visits a context -/
def FiniteTrace.visits {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    {𝒮 : StatefulSystem C E} (trace : FiniteTrace C E 𝒮) (c : C) : Prop :=
  c ∈ trace.contexts

end FdrsFormal.Modes.ContextDependent
