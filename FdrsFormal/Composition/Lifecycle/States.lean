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

# Timeline Lifecycle States

This file defines the lifecycle state machine for timelines.

## Mathematical Content (fdrs.md lines 6239-6248)

**Definition 124 (Timeline lifecycle states)**:

A timeline T has **lifecycle status:**
  Lifecycle_T ∈ {DORMANT, ACTIVE, TERMINATED}

**State transitions:**
- DORMANT →^SPAWN ACTIVE (timeline created)
- ACTIVE →^TERMINATE TERMINATED (timeline destroyed)

## References

- fdrs.md, Phase 8, Section 8.6 (lines 6239-6248)
-/

namespace FdrsFormal.Composition.Lifecycle

/-!
## Lifecycle State Enumeration
-/

/--
Timeline lifecycle state.

**fdrs.md Definition 124 (line 6241)**: Three-state lifecycle.
-/
inductive LifecycleState where
  | DORMANT     -- Not yet created or destroyed
  | ACTIVE      -- Currently executing
  | TERMINATED  -- Finished execution
  deriving DecidableEq, Repr

/-!
## Lifecycle Transitions
-/

/--
Valid lifecycle transition.

**fdrs.md lines 6245-6247**: Only DORMANT→ACTIVE and ACTIVE→TERMINATED allowed.

**Axiomatized**: Transition validity predicate.
-/
def isValidTransition (fromState toState : LifecycleState) : Bool :=
  match fromState, toState with
  | .DORMANT, .ACTIVE => true
  | .ACTIVE, .TERMINATED => true
  | _, _ => false

/--
Lifecycle state for each timeline.

**Axiomatized**: Global lifecycle map (timeline → state).
-/
structure LifecycleMap where
  /-- Current lifecycle state per timeline -/
  state : Nat → LifecycleState

end FdrsFormal.Composition.Lifecycle
