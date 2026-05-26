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

# Terminate Operation

This file defines the terminate operation for timeline destruction.

## Mathematical Content (fdrs.md lines 6265-6276)

**Definition 126 (Terminate operation)**:

**Terminate**(T, final_residue) destroys timeline T:

1. Compute routing: ρ(T, ROOT, TERMINATE, c_global) determines destinations
2. Inject final_residue into target timelines
3. Set lifecycle: lifecycle_T ← TERMINATED
4. Remove from active routing graph

**Interpretation**: Timeline destruction with cleanup - final state routed to continuations.

## References

- fdrs.md, Phase 8, Section 8.6 (lines 6265-6276)
-/

import FdrsFormal.Composition.Lifecycle.States

namespace FdrsFormal.Composition.Lifecycle

/-!
## Terminate Operation
-/

/--
Terminate operation: destroy timeline with final residue routing.

**fdrs.md Definition 126 (lines 6267-6275)**: Four-step destruction protocol.

1. Compute final routing based on TERMINATE event
2. Distribute final_residue to continuation points
3. Mark timeline TERMINATED
4. Remove from active set

The `finalResidue` parameter is used by the routing step (steps 1-2) which
is abstracted away in this simplified model. The core effect is the state
transition to TERMINATED.
-/
def terminate (timeline : Nat) (_finalResidue : Nat)
  (lifecycles : LifecycleMap) : LifecycleMap where
  state t := if t = timeline then .TERMINATED else lifecycles.state t

/--
Terminated timeline enters TERMINATED state.

**fdrs.md line 6272**: lifecycle_T ← TERMINATED.
-/
theorem terminated_is_terminated (timeline finalResidue : Nat) (lifecycles : LifecycleMap) :
  (terminate timeline finalResidue lifecycles).state timeline = .TERMINATED := by
  simp [terminate]

/--
Terminate preserves other timelines' state.

**fdrs.md line 6274**: Final state routed to continuation points. The terminate
operation only modifies the target timeline's lifecycle, leaving all other
timelines unchanged (routing distributes the final residue before transition).
-/
def terminate_routes_final_state (timeline finalResidue : Nat) : Prop :=
  ∀ lifecycles : LifecycleMap, ∀ t : Nat, t ≠ timeline →
    (terminate timeline finalResidue lifecycles).state t = lifecycles.state t

/-- Proof that terminate preserves other timelines. -/
theorem terminate_routes_final_state_holds (timeline finalResidue : Nat) :
    terminate_routes_final_state timeline finalResidue := by
  intro lifecycles t ht
  simp [terminate, ht]

end FdrsFormal.Composition.Lifecycle
