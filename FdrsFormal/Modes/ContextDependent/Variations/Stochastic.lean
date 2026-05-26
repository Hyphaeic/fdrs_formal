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

# Stochastic Context Systems

This file defines stochastic context evolution.

## Mathematical Content (fdrs.md lines 5820-5840)

**Definition 104 (Stochastic context system)**:
A stochastic context system has a random transition function:

Γ : 𝒞 × ℰ × Ω_prob → 𝒞

where Ω_prob is a probability space.

**Theorem 49 (Stochastic SU preservation)**:
If Ω satisfies CSU and Γ preserves reachability within 𝒞,
then SU holds almost surely at each time step.

## References

- fdrs.md, Phase 7, Section 7.7 (lines 5820-5840)
- DEPENDENCY_BASED_STRUCTURE.md, Modes/ContextDependent/Variations
-/

import FdrsFormal.Modes.ContextDependent.Preservation.Preservation

namespace FdrsFormal.Modes.ContextDependent

open FdrsFormal.Modes.VariableRadix

/-!
## Stochastic Dynamics
-/

/-- A probability space (simplified) -/
structure ProbSpace where
  /-- Sample space -/
  Ω : Type*
  /-- Nonempty -/
  nonempty : Nonempty Ω

/--
**Definition 104**: Stochastic context dynamics.

Transition depends on random outcome.
-/
structure StochasticDynamics (C : Type*) (E : Type*) (P : ProbSpace)
    [ContextSpace C] [EventSpace E] where
  /-- The stochastic transition function -/
  transition : C → E → P.Ω → C

/-- Deterministic dynamics as a special case -/
def ContextDynamics.toStochastic {C E : Type*} [ContextSpace C] [EventSpace E]
    (Γ : ContextDynamics C E) (P : ProbSpace) : StochasticDynamics C E P where
  transition := fun c e _ => Γ.transition c e

/-!
## Stochastic Systems
-/

/-- A stateful system with stochastic dynamics -/
structure StochasticSystem (C : Type*) (E : Type*) (P : ProbSpace)
    [ContextSpace C] [InitialContext C] [EventSpace E] where
  /-- The extended radix oracle -/
  oracle : ExtendedOracle C
  /-- The stochastic dynamics -/
  dynamics : StochasticDynamics C E P

/-- A stochastic system has CSU if its oracle has CSU -/
def StochasticSystem.hasCSU {C E : Type*} {P : ProbSpace}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StochasticSystem C E P) : Prop :=
  FdrsFormal.Modes.ContextDependent.hasCSU 𝒮.oracle

/-!
## Stochastic SU Preservation
-/

/--
**Theorem 49**: SU holds almost surely under stochastic evolution.

If CSU holds, then for any random sequence of transitions,
SU holds at each visited context with probability 1.
-/
theorem stochastic_su_preservation {C E : Type*} {P : ProbSpace}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StochasticSystem C E P) (hcsu : 𝒮.hasCSU)
    (c : C) (k : ℕ) :
    -- SU holds at c regardless of how we got there
    isSiblingUniform (𝒮.oracle.atContext c) k :=
  hcsu c k

/-- Stochastic transitions preserve CSU -/
theorem stochastic_csu_preserved {C E : Type*} {P : ProbSpace}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StochasticSystem C E P) (hcsu : 𝒮.hasCSU)
    (c : C) (e : E) (ω : P.Ω) (k : ℕ) :
    isSiblingUniform (𝒮.oracle.atContext (𝒮.dynamics.transition c e ω)) k :=
  hcsu _ k

/-!
## Random Traces
-/

/-- A random trace with stochastic transitions -/
structure RandomTrace (C : Type*) (E : Type*) (P : ProbSpace)
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StochasticSystem C E P) where
  /-- Event sequence -/
  events : List E
  /-- Random outcomes -/
  outcomes : List P.Ω
  /-- Lengths match -/
  length_eq : events.length = outcomes.length

/-- The context sequence induced by a random trace -/
def RandomTrace.contexts {C E : Type*} {P : ProbSpace}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    {𝒮 : StochasticSystem C E P} (trace : RandomTrace C E P 𝒮) : List C :=
  -- Build context sequence by folding over (event, outcome) pairs
  (trace.events.zip trace.outcomes).scanl
    (fun c (eo : E × P.Ω) => 𝒮.dynamics.transition c eo.1 eo.2)
    c₀

end FdrsFormal.Modes.ContextDependent
