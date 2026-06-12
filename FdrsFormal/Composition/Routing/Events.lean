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

# Event Space and Routing Function

Defines the event types for timeline communication and the routing function signature.

## Mathematical Content (fdrs.md lines 5976-6004)

**Definition 111**: Event space for timeline graphs
**Definition 112**: Routing function type

## References

- fdrs.md, Phase 8, Section 8.2 (lines 5976-6004)
-/

import FdrsFormal.Composition.Routing.Definition

namespace FdrsFormal.Composition.Routing

/-! ## Definition 111: Event space -/

/--
**fdrs.md**: Definition 111 (Event space for timeline graphs) [§8.2.1 · Phase 8] (lines 5976-5986)

The event space is:
  𝓔 := {(TICK, T), (OVERFLOW, T, s), (INJECT, T, s, payload)}

Event types:
- TICK: Timeline advances one local step
- OVERFLOW: Timeline's cylinder at prefix s overflows
- INJECT: External payload arrives at timeline's cylinder s
-/
inductive Event where
  /-- Timeline advances one local step -/
  | TICK (timeline : ℕ) : Event
  /-- Cylinder at prefix s overflows (carry propagates beyond s) -/
  | OVERFLOW (timeline : ℕ) (cylPrefix : List ℕ) : Event
  /-- External payload arrives at timeline's cylinder s -/
  | INJECT (timeline : ℕ) (cylPrefix : List ℕ) (payload : ℕ) : Event
  deriving DecidableEq, Repr

/-! ## Definition 112: Routing function -/

/--
**fdrs.md**: Definition 112 (Routing function) [§8.2.2 · Phase 8] (lines 5989-6004)

A routing function is:
  ρ: 𝒯 × Σ* × 𝓔_trigger × 𝒞_global → 𝒫(𝒯 × Σ* × TransferType × PayloadTransform)

Given source timeline A, source cylinder prefix s_A, triggering event e,
and current global context c, returns set of target specifications (B, s_B, τ, φ).

**Implementation**: Returns list of (target timeline, target prefix, transfer payload) triples.
-/
def routingFunction (_source : ℕ) (_prefix : List ℕ) (event : Event) :
    List (ℕ × List ℕ × ℕ) :=
  match event with
  | .TICK _ => []
  | .OVERFLOW timeline cylPrefix => [(timeline, cylPrefix, 0)]
  | .INJECT timeline cylPrefix payload => [(timeline, cylPrefix, payload)]

end FdrsFormal.Composition.Routing
