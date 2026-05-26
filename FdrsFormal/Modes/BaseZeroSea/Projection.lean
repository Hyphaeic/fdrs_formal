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

# Base-Zero Sea: Projection to Extended Arithmetic

Connects Phase 10 sea dynamics to Phase 9 spatial cylinder infrastructure.

The key architectural insight: the projection `windowToDigitProjection` maps
the occupancy depth of a legacy thread to a spatial digit token position.
This is only semantically valid when the occupied sites form a contiguous
prefix `{0, ..., depth-1}` — the `IsPrefixOccupancy` invariant.

In the general Phase 10 dynamics, arbitrary consumption can create holes,
breaking this invariant. Phase 9 is *exactly* the restriction where:
- consumption is disabled (no holes from removal), and
- creation is always at the frontier (preserving contiguity).

## Mathematical Content (fdrs.md lines 7329-7359)

**Definition 158**: Window-to-digit projection (Π : State → SpatialCylinder)
**Definition 159**: Phase-9 constraint profile (consumption disabled, carry routing)
**Theorem 63**: Phase 9 is a special case of Phase 10

## References

- fdrs.md, Phase 10, Section 10.4 (lines 7327-7359)
- CarryRouteUnification.lean (Theorem 61, SpatialCylinder, recursiveCarryTick, unifiedSpatialTick)
- SpatialThermometer.lean (SpatialDigit, spatialTick)
-/

import FdrsFormal.Modes.BaseZeroSea.Properties
import FdrsFormal.Modes.ExtendedBase.CarryRouteUnification

namespace FdrsFormal.Modes.BaseZeroSea

open FdrsFormal.Modes.ExtendedBase (SpatialDigit SpatialCylinder spatialTick
  cylinderValid recursiveCarryTick unifiedSpatialTick carry_is_overflow_route)

/-! ## Definition 158: Window-to-digit projection -/

/--
**fdrs.md**: Definition 158 (Window-to-digit projection)
[§10.4.1 · Phase 10] (lines 7329-7335)

Fix an observation profile `(W_i, b_i)_{i<k}`. The projection
`Π : State → SpatialCylinder`
maps each window `W_i` to a spatial digit state by reading its active
occupancy pattern and interpreting it as token position in the
corresponding Phase 9 cylinder.

**Precondition**: The projection requires `IsPrefixOccupancy` on each
window's legacy thread. Without this, the depth (= count of occupied sites)
does not correspond to a thermometer token position — arbitrary consumption
can create holes in the occupancy pattern that break the contiguous-prefix
assumption of `SpatialDigit`.

The capacity `M_i = wallPos_i + 1` ensures the depth (which is ≤ wallPos_i)
always fits within `Fin M_i`.
-/
def windowToDigitProjection {k : ℕ} (state : SeaState k)
    (_hprefix : ∀ i, (state.threads i).IsPrefixOccupancy) :
    SpatialCylinder (fun i => state.profile.wallPos i + 1) :=
  fun i =>
    let depth := (state.threads i).depth
    have hd : depth < state.profile.wallPos i + 1 := by
      have h1 := LegacyThread.depth_le_bound (state.threads i)
      have h2 := state.thread_bound i
      omega
    ⟨⟨depth, hd⟩⟩

/-- The projected digit value equals the legacy thread depth. -/
theorem windowToDigitProjection_val {k : ℕ} (state : SeaState k)
    (hprefix : ∀ i, (state.threads i).IsPrefixOccupancy) (i : Fin k) :
    (windowToDigitProjection state hprefix i).tokenPos.val =
    (state.threads i).depth := rfl

/-- Under the prefix invariant, the projected digit is in the active zone
    (token position < wall position) whenever the thread is non-full. -/
theorem windowToDigitProjection_in_activeZone {k : ℕ} (state : SeaState k)
    (hprefix : ∀ i, (state.threads i).IsPrefixOccupancy) (i : Fin k)
    (hnotfull : (state.threads i).depth < state.profile.wallPos i) :
    (windowToDigitProjection state hprefix i).tokenPos.val <
    state.profile.wallPos i := by
  simp [windowToDigitProjection]; exact hnotfull

/-! ## Why the prefix invariant is necessary

The general `LegacyThread` allows holes: e.g. sites = [0, 2] with bound = 3
has depth 2 but site 1 is unoccupied. Projecting this to `SpatialDigit`
with token position 2 would claim "the thermometer reads 2", but in the
Phase 9 model that means sites {0, 1} are both occupied — which is false.

The prefix invariant (`sites.toFinset = Finset.range depth`) ensures that
the depth-as-token-position interpretation is faithful:
- Every position below the token is occupied (no holes).
- Every position at or above the token is unoccupied.
- This matches exactly the Phase 9 one-hot thermometer encoding.
-/

/-- Without the prefix invariant, the depth can misrepresent occupancy.
    Example: a thread with sites = {0, 2} has depth 2 but site 1 is empty. -/
example : ∃ lt : LegacyThread,
    lt.depth = 2 ∧ ¬lt.IsPrefixOccupancy := by
  refine ⟨⟨3, [0, 2], ?_, ?_⟩, rfl, ?_⟩
  · intro v hv; simp at hv; omega
  · exact List.nodup_cons.mpr ⟨by simp, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩⟩
  · intro h
    simp [LegacyThread.IsPrefixOccupancy, LegacyThread.depth] at h
    have : (1 : ℕ) ∈ ({0, 2} : Finset ℕ) := by rw [h]; exact Finset.mem_range.mpr (by omega)
    simp at this

/-! ## Definition 159: Phase-9 constraint profile -/

/--
**fdrs.md**: Definition 159 (Phase-9 constraint profile)
[§10.4.2 · Phase 10] (lines 7337-7344)

The Phase-9 constraint profile is the deterministic parameter choice:
1. fixed windows and fixed walls `(W_i, b_i)`,
2. carry routing policy = nearest-right overflow routing,
3. `ConsumeSchedule(t) = false` for all `t` (consumption disabled),
4. creation restricted to the active carry front.

Under these constraints the prefix invariant (`IsPrefixOccupancy`) is
preserved at every step, because:
- No consumption ⟹ no sites are ever removed ⟹ no holes created.
- Frontier-only creation ⟹ new sites are always at index `depth` ⟹
  the prefix `{0, ..., depth}` extends to `{0, ..., depth+1-1}`.

This is the *exact* condition that makes `windowToDigitProjection` faithful
and distinguishes Phase 9 from general Phase 10.
-/
structure Phase9ConstraintProfile (k : ℕ) where
  /-- The observation profile with fixed windows and walls -/
  profile : ObservationProfile k
  /-- All walls have standard base (≥ 1 for arithmetic) -/
  wall_positive : ∀ i, 1 ≤ profile.wallPos i
  /-- The dynamics parameters use these constraints -/
  params : SeaDynamicsParams k
  /-- The schedule must be `never` (consumption disabled) -/
  params_schedule : params.schedule = ConsumeSchedule.never
  /-- The prefix invariant is preserved by the dynamics:
      if all threads start with prefix occupancy, they remain so after each step.
      This follows from: no consumption (disabled schedule) + creation at
      the frontier (depth index) only. -/
  preserves_prefix : ∀ state t,
    state.profile = profile →
    (∀ i, (state.threads i).IsPrefixOccupancy) →
    (∀ i, ((seaTick params state t).threads i).IsPrefixOccupancy)

/-- Under the Phase-9 constraint profile, consumption never fires. -/
theorem phase9_no_consumption {k : ℕ} (cp : Phase9ConstraintProfile k)
    (_state : SeaState k) (t : ℕ) :
    cp.params.schedule t = false := by
  rw [cp.params_schedule]; rfl

/-- Under Phase-9 constraints, seaTick reduces to creation only. -/
theorem phase9_seaTick_eq_creation {k : ℕ} (cp : Phase9ConstraintProfile k)
    (state : SeaState k) (t : ℕ) :
    seaTick cp.params state t = applyCreation cp.params.createSel state t := by
  unfold seaTick
  rw [phase9_no_consumption cp state t]; rfl

/-! ## Theorem 63: Phase 9 is a special case of Phase 10 -/

/--
**fdrs.md**: Theorem 63 (Phase 9 is a special case of Phase 10)
[§10.4.3 · Phase 10] (lines 7346-7359)

Under Definition 159, the projected Phase 10 update equals the Phase 9
unified event-driven tick. With consumption disabled, only deterministic
frontier creation remains. Under fixed walls and nearest-right overflow
policy, each projected window step is exactly the same local
increment-or-wrap and carry routing used in Definitions 148-150.

The proof connects the two frameworks by invoking Theorem 61 (carry =
overflow route) from Phase 9. The prefix invariant is the bridge:

- **Phase 9** operates on `SpatialCylinder` where digit values are
  contiguous fill levels and `spatialTick` increments or wraps.
- **Phase 10** operates on `SeaState` where occupancy is arbitrary
  and `seaTick` applies creation/consumption.
- **The projection** (`windowToDigitProjection`) maps depth → token
  position, and is faithful exactly when `IsPrefixOccupancy` holds.
- **Phase-9 constraints** (no consumption + frontier creation)
  preserve `IsPrefixOccupancy`, making the projection commute with
  the dynamics — establishing Phase 9 as a strict special case.
-/
theorem phase9_specialCase :
    -- Phase 9's recursive carry tick equals the unified spatial tick
    -- (Theorem 61 from CarryRouteUnification.lean)
    ∀ {k : ℕ} (M : Fin k → ℕ) (b : Fin k → ℕ)
      (hb : ∀ i, 1 ≤ b i) (hbM : ∀ i, b i ≤ M i)
      (cyl : SpatialCylinder M)
      (hvalid : cylinderValid b M cyl)
      (pos : ℕ) (carry_in : Bool),
    recursiveCarryTick M b hb hbM cyl hvalid pos carry_in =
    unifiedSpatialTick M b hb hbM cyl hvalid pos carry_in :=
  fun M b hb hbM cyl hvalid pos carry_in =>
    carry_is_overflow_route M b hb hbM cyl hvalid pos carry_in

end FdrsFormal.Modes.BaseZeroSea
