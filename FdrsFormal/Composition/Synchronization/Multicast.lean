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

# Multicast Routing

This file defines multicast routing (one-to-many event distribution).

## Mathematical Content (fdrs.md lines 6316-6326)

**Definition 128 (Multicast routing)**:

Routing at (A, s_A) is **multicast** if:
  |ρ(A, s_A, e, c)| > 1

The same triggering event routes to multiple distinct targets.

**Example**: Timer overflow broadcasts to CPU, LED controller, network module simultaneously.

## References

- fdrs.md, Phase 8, Section 8.7 (lines 6316-6326)
-/

import FdrsFormal.Composition.Routing.Definition
import FdrsFormal.Composition.RoutingGraph.Graph

namespace FdrsFormal.Composition.Synchronization

open FdrsFormal.Composition.Verification

/-!
## Multicast Routing
-/

/--
Multicast predicate: routing has multiple targets.

**fdrs.md Definition 128 (lines 6317-6322)**: |ρ(A, s_A, e, c)| > 1.

Defined as a proposition parameterized by a fanout oracle.
-/
def isMulticast (fanout : ℕ → ℕ → ℕ) (sourceTimeline sourceCylinder : ℕ) : Prop :=
  fanout sourceTimeline sourceCylinder > 1

/--
Fanout count: number of targets for a multicast.

**fdrs.md line 6320**: `|ρ(A, s_A, e, c)|` = fanout, the number of routing
actions out of junction `(sourceTimeline, sourceCylinder)` in `G_ρ`.
-/
def multicastFanout (spec : RoutingSpecification) (sourceTimeline sourceCylinder : ℕ) : ℕ :=
  RoutingGraph.fanout spec (sourceTimeline, sourceCylinder)

/--
Multicast example: timer overflow.

**fdrs.md line 6324**: Timer broadcasts to multiple modules.

Example: a fanout function where source 0 multicasts to 3 targets.
-/
theorem timerOverflow_multicast :
    ∃ source, isMulticast (fun _ _ => 3) source 0 :=
  ⟨0, by norm_num [isMulticast]⟩

end FdrsFormal.Composition.Synchronization
