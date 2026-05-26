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

# Bounded Spawn

This file defines bounded spawn systems and proves timing preservation.

## Mathematical Content (fdrs.md lines 6278-6311)

**Definition 127 (Bounded spawn system)**:

System has **bounded spawn** if ∃ N_max such that:
  |{T ∈ 𝒯 : lifecycle_T = ACTIVE}| ≤ N_max

at all times.

**Theorem 54 (Bounded spawn preserves global timing bounds)**:

If:
1. System has bounded spawn with limit N_max
2. Each timeline has bounded per-cylinder cost C_max
3. Routing is acyclic with maximum depth D_max

Then **global worst-case latency** satisfies:
  Total latency ≤ N_max · D_max · C_max

## References

- fdrs.md, Phase 8, Section 8.6 (lines 6278-6311)
-/

import FdrsFormal.Composition.Lifecycle.States
import FdrsFormal.Composition.Lifecycle.Spawn
import FdrsFormal.Composition.Lifecycle.Terminate
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace FdrsFormal.Composition.Lifecycle

/-!
## Bounded Spawn Property
-/

/--
System has bounded concurrent timelines.

**fdrs.md Definition 127 (lines 6279-6285)**: At most N_max active timelines.

The set of all active timelines can be covered by a finite set of size ≤ N_max.
Equivalently: |{T ∈ 𝒯 : lifecycle_T = ACTIVE}| ≤ N_max.
-/
def hasBoundedSpawn (lifecycles : LifecycleMap) (N_max : Nat) : Prop :=
  ∃ activeSet : Finset ℕ,
    (∀ t, lifecycles.state t = .ACTIVE → t ∈ activeSet) ∧
    activeSet.card ≤ N_max

/--
Count of active timelines within a finite set.

**Helper for bounded spawn**: |{T ∈ S : lifecycle_T = ACTIVE}|.
-/
def activeCount (lifecycles : LifecycleMap) (candidates : Finset ℕ) : ℕ :=
  (candidates.filter (fun t => lifecycles.state t == .ACTIVE)).card

/--
Active count provides an upper bound witness for bounded spawn.
-/
theorem hasBoundedSpawn_of_activeCount (lifecycles : LifecycleMap)
    (candidates : Finset ℕ) (N_max : Nat)
    (h_cover : ∀ t, lifecycles.state t = .ACTIVE → t ∈ candidates)
    (h_bound : activeCount lifecycles candidates ≤ N_max) :
    hasBoundedSpawn lifecycles N_max := by
  refine ⟨candidates.filter (fun t => lifecycles.state t == .ACTIVE), ?_, ?_⟩
  · intro t ht
    exact Finset.mem_filter.mpr ⟨h_cover t ht, by rw [ht]; decide⟩
  · exact h_bound

/--
Spawn preserves bounded spawn if we're below the limit.

**fdrs.md**: Spawn adds one active timeline. If count < N_max, bound still holds.
-/
theorem spawn_preserves_bounded (lifecycles : LifecycleMap) (N_max : Nat)
    (config : SpawnConfig) (sourceTimeline sourceCylinder : Nat)
    (_h_bounded : hasBoundedSpawn lifecycles N_max)
    (h_room : ∃ activeSet : Finset ℕ,
      (∀ t, lifecycles.state t = .ACTIVE → t ∈ activeSet) ∧
      activeSet.card + 1 ≤ N_max) :
    hasBoundedSpawn (spawn sourceTimeline sourceCylinder config lifecycles) N_max := by
  obtain ⟨activeSet, h_cover, h_card⟩ := h_room
  refine ⟨activeSet ∪ {config.newTimelineId}, ?_, ?_⟩
  · intro t ht
    rw [Finset.mem_union]
    by_cases heq : t = config.newTimelineId
    · right; exact Finset.mem_singleton.mpr heq
    · left; apply h_cover
      rw [spawn_preserves_others sourceTimeline sourceCylinder config lifecycles t heq] at ht
      exact ht
  · calc (activeSet ∪ {config.newTimelineId}).card
        ≤ activeSet.card + ({config.newTimelineId} : Finset ℕ).card :=
          Finset.card_union_le _ _
      _ = activeSet.card + 1 := by simp
      _ ≤ N_max := h_card

/-!
## Timing Preservation Theorem
-/

/--
**fdrs.md**: Theorem 54 (Bounded spawn preserves global timing bounds) [§8.6.5 · Phase 8] (lines 6290-6310)

If:
1. System has bounded spawn with limit N_max
2. Each timeline has per-timeline latency ≤ D_max · C_max (depth × per-cylinder cost)

Then the total latency over all active timelines is ≤ N_max · D_max · C_max.

**Proof** (fdrs.md lines 6301-6308):
- At most N_max timelines active simultaneously (bounded spawn)
- Each timeline contributes latency ≤ D_max · C_max
- Sum over at most N_max timelines: total ≤ N_max · (D_max · C_max)
-/
-- fdrs.md lines 6290-6310, Theorem 54
theorem boundedSpawn_preserves_timing (lifecycles : LifecycleMap)
    (N_max D_max C_max : ℕ)
    (h_bounded : hasBoundedSpawn lifecycles N_max)
    (perTimelineLatency : ℕ → ℕ)
    (h_cost : ∀ t, perTimelineLatency t ≤ D_max * C_max) :
    ∃ (S : Finset ℕ),
      (∀ t, lifecycles.state t = .ACTIVE → t ∈ S) ∧
      S.sum perTimelineLatency ≤ N_max * D_max * C_max := by
  obtain ⟨activeSet, h_cover, h_card⟩ := h_bounded
  exact ⟨activeSet, h_cover, calc
    activeSet.sum perTimelineLatency
      ≤ activeSet.sum (fun _ => D_max * C_max) :=
        Finset.sum_le_sum fun t _ => h_cost t
    _ = activeSet.card * (D_max * C_max) := by
        simp [Finset.sum_const]
    _ ≤ N_max * (D_max * C_max) :=
        Nat.mul_le_mul_right _ h_card
    _ = N_max * D_max * C_max :=
        (Nat.mul_assoc _ _ _).symm⟩

end FdrsFormal.Composition.Lifecycle
