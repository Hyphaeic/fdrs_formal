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

# Junction Point Types

This file defines junction point types for timeline coupling.

## Mathematical Content (fdrs.md lines 5951-5972)

**Definition 109 (Junction point types)**:

A **junction point** is a triple (T, s, dir) where:
- T ∈ 𝒯 is a timeline
- s ∈ Σ*_T is a cylinder prefix in T's mixed-radix space
- dir ∈ {OUT, IN} specifies direction

**Notation:**
- **(A, s_A)^OUT**: source/outflow point (overflow exits here)
- **(B, s_B)^IN**: target/inflow point (injection enters here)

**Definition 110 (Active cylinder in timeline)**:

A cylinder U_T(s) is **active** at global time t if:
  π_{|s|}(τ_T(t)) = s

## References

- fdrs.md, Phase 8, Section 8.1 (lines 5951-5972)
-/

import FdrsFormal.Composition.TimelineGraphs.Definition

namespace FdrsFormal.Composition.Junctions

/-!
## Junction Direction
-/

/--
Junction direction: inflow or outflow.

**fdrs.md lines 5955-5956**: OUT for source, IN for target.
-/
inductive JunctionDirection where
  | OUT  -- Outflow/source junction
  | IN   -- Inflow/target junction
  deriving DecidableEq, Repr

/-!
## Junction Points
-/

/--
A junction point in a timeline at a specific cylinder prefix.

**fdrs.md Definition 109 (lines 5953-5961)**:
Junction = (timeline, cylinder prefix, direction)

**Axiomatized**: Full structure requires timeline and prefix formalizations.
-/
structure JunctionPoint where
  /-- Timeline identifier -/
  timeline : ℕ
  /-- Cylinder prefix depth -/
  prefixDepth : ℕ
  /-- Prefix value (simplified - actual should be PrefixWord) -/
  prefixValue : ℕ
  /-- Direction: IN or OUT -/
  direction : JunctionDirection

/--
Active cylinder predicate.

**fdrs.md Definition 110 (lines 5964-5972)**:
Cylinder U_T(s) is active at global time t if the timeline's current state τ_T(t)
has its prefix matching the junction point's prefix: π_{|s|}(τ_T(t)) = s.

**Implementation**: Given a timeline state function, checks prefix equality.
The predicate takes a state oracle mapping (timeline, time) → prefix value.
-/
def isActiveCylinder (jp : JunctionPoint) (globalTime : ℕ)
    (timelineState : ℕ → ℕ → ℕ) : Prop :=
  timelineState jp.timeline globalTime = jp.prefixValue

end FdrsFormal.Composition.Junctions
