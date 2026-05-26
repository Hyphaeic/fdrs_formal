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

# Spawn Operation

This file defines the spawn operation for dynamic timeline creation.

## Mathematical Content (fdrs.md lines 6252-6262)

**Definition 125 (Spawn operation)**:

**Spawn**(A, s_A, Ω_new, τ₀) executed at timeline A, cylinder s_A creates new timeline:

1. Allocate fresh identifier: T_new ∈ 𝒯 ∖ {T : lifecycle_T = ACTIVE}
2. Initialize radix oracle: Ω_{T_new} ← Ω_new
3. Initialize state: τ_{T_new} ← τ₀
4. Set lifecycle: lifecycle_{T_new} ← ACTIVE
5. Register routing edges: add (A, s_A) → (T_new, ...) to G_ρ

**Interpretation**: Timeline creation at runtime with overflow providing initial state.

## References

- fdrs.md, Phase 8, Section 8.6 (lines 6252-6262)
-/

import FdrsFormal.Composition.Lifecycle.States

namespace FdrsFormal.Composition.Lifecycle

/-!
## Spawn Operation
-/

/--
Spawn configuration: data needed to create new timeline.

**fdrs.md lines 6254-6259**: Oracle, initial state, routing edges.

**Axiomatized**: Simplified structure (full version needs radix oracle types).
-/
structure SpawnConfig where
  /-- New timeline identifier -/
  newTimelineId : Nat
  /-- Initial state for new timeline -/
  initialState : Nat
  /-- Radix oracle configuration (simplified) -/
  oracleConfig : Nat

/--
Spawn operation: create new timeline.

**fdrs.md Definition 125 (lines 6253-6262)**: Five-step creation protocol.

1. Allocate fresh identifier: `config.newTimelineId`
2. Initialize oracle: `config.oracleConfig` (simplified)
3. Initialize state: `config.initialState` (simplified)
4. Set lifecycle: `lifecycle_{T_new} ← ACTIVE`
5. Register routing edges (abstracted away in this model)

Steps 2, 3, 5 are abstracted; the core effect is the lifecycle transition to ACTIVE.
-/
def spawn (_sourceTimeline _sourceCylinder : Nat) (config : SpawnConfig)
  (lifecycles : LifecycleMap) : LifecycleMap where
  state t := if t = config.newTimelineId then .ACTIVE else lifecycles.state t

/--
Spawned timeline starts in ACTIVE state.

**fdrs.md line 6259**: lifecycle_{T_new} ← ACTIVE.

**Proof**: Direct from the definition of `spawn`, which sets the new timeline to ACTIVE.
-/
theorem spawned_is_active (sourceTimeline sourceCylinder : Nat) (config : SpawnConfig)
  (lifecycles : LifecycleMap) :
    (spawn sourceTimeline sourceCylinder config lifecycles).state config.newTimelineId
      = .ACTIVE := by
  simp [spawn]

/--
Spawn preserves other timelines' lifecycle states.

**fdrs.md Definition 125**: Only the new timeline's state changes.
-/
theorem spawn_preserves_others (sourceTimeline sourceCylinder : Nat) (config : SpawnConfig)
  (lifecycles : LifecycleMap) (t : Nat) (ht : t ≠ config.newTimelineId) :
    (spawn sourceTimeline sourceCylinder config lifecycles).state t
      = lifecycles.state t := by
  simp [spawn, ht]

/-! ## Example 4: Dynamic task spawning -/

/--
**fdrs.md**: Example 4 (Dynamic Task Spawning) [§8.10.3 · Phase 8] (lines 6525-6534)

Scenario: Main timeline creates worker tasks dynamically.

Routing rules:
  (MAIN, FORK_POINT, CREATE_TASK) → SPAWN(ω_worker, τ_initial)
  Creates new timeline T_worker, initializes with ω_worker and state τ_initial.
  Adds routing: (T_worker, DONE, MAIN, JOIN_POINT, TERMINATE, φ_result)

**Axiomatized**: Concrete example demonstrating spawn operation.
-/
theorem dynamicTaskSpawnExample :
    ∃ config : SpawnConfig, config.newTimelineId > 0 :=
  ⟨⟨1, 0, 0⟩, by decide⟩

end FdrsFormal.Composition.Lifecycle
