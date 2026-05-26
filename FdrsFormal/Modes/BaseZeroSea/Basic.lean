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

# Base-Zero Sea: Basic Definitions

Foundational types for Phase 10 — deterministic base-zero sea dynamics.

## Mathematical Content (fdrs.md lines 7197-7230)

**Definition 151**: Base-zero sea — countable graph with binary occupancy
**Definition 152**: Observation windows and radix walls — ordered vertex windows with wall positions
**Definition 153**: Legacy thread — time-ordered instantiated active sites per window

## References

- fdrs.md, Phase 10, Sections 10.1.1–10.1.3 (lines 7197-7230)
-/

import FdrsFormal.Core

namespace FdrsFormal.Modes.BaseZeroSea

/-! ## Definition 151: Base-zero sea -/

/--
**fdrs.md**: Definition 151 (Base-zero sea) [§10.1.1 · Phase 10] (lines 7197-7207)

A base-zero sea is a countable graph `(V, E)` together with an occupancy map
`σ : V → Bool` where:
- `σ(v) = false` means `v` is uninstantiated base-zero potential,
- `σ(v) = true` means `v` is an instantiated base-one site.

We model V as `ℕ` (countable vertex set) and E as a symmetric adjacency predicate.
-/
structure Sea where
  /-- Symmetric adjacency: `adj v w` means v and w are neighbors -/
  adj : ℕ → ℕ → Prop
  /-- Adjacency is symmetric -/
  adj_symm : ∀ v w, adj v w → adj w v
  /-- No self-loops -/
  adj_irrefl : ∀ v, ¬adj v v
  /-- Occupancy map: true = instantiated (base-1), false = potential (base-0) -/
  occupancy : ℕ → Bool

/-- The set of instantiated vertices in a sea. -/
def Sea.instantiated (sea : Sea) : Set ℕ :=
  {v | sea.occupancy v = true}

/-- The set of uninstantiated (potential) vertices in a sea. -/
def Sea.potential (sea : Sea) : Set ℕ :=
  {v | sea.occupancy v = false}

/-- Instantiate a vertex: set its occupancy to true. -/
def Sea.instantiate (sea : Sea) (v : ℕ) : Sea :=
  { sea with occupancy := fun w => if w = v then true else sea.occupancy w }

/-- Revert a vertex: set its occupancy to false. -/
def Sea.revert (sea : Sea) (v : ℕ) : Sea :=
  { sea with occupancy := fun w => if w = v then false else sea.occupancy w }

@[simp]
theorem Sea.instantiate_at (sea : Sea) (v : ℕ) :
    (sea.instantiate v).occupancy v = true := by
  simp [Sea.instantiate]

@[simp]
theorem Sea.instantiate_ne (sea : Sea) (v w : ℕ) (h : w ≠ v) :
    (sea.instantiate v).occupancy w = sea.occupancy w := by
  simp [Sea.instantiate, h]

@[simp]
theorem Sea.revert_at (sea : Sea) (v : ℕ) :
    (sea.revert v).occupancy v = false := by
  simp [Sea.revert]

@[simp]
theorem Sea.revert_ne (sea : Sea) (v w : ℕ) (h : w ≠ v) :
    (sea.revert v).occupancy w = sea.occupancy w := by
  simp [Sea.revert, h]

theorem Sea.instantiate_adj (sea : Sea) (v : ℕ) :
    (sea.instantiate v).adj = sea.adj := rfl

theorem Sea.revert_adj (sea : Sea) (v : ℕ) :
    (sea.revert v).adj = sea.adj := rfl

/-! ## Definition 152: Observation windows and radix walls -/

/--
**fdrs.md**: Definition 152 (Observation windows and radix walls)
[§10.1.2 · Phase 10] (lines 7208-7221)

An observation profile is a finite family of ordered windows
`W_0, W_1, ..., W_{k-1}` where `W_i = (v_{i,0}, ..., v_{i,M_i-1})`
with associated wall positions `b_i` satisfying `0 ≤ b_i ≤ M_i`.

Each window induces:
- **Wall** if `b_i = 0`,
- **Wire** if `b_i = 1`,
- **Standard digit** if `b_i ≥ 2`.
-/
structure ObservationProfile (k : ℕ) where
  /-- Window sizes: M_i is the number of vertices in window i -/
  windowSize : Fin k → ℕ
  /-- Window vertex maps: W_i(j) gives the j-th vertex in window i -/
  windowVertex : (i : Fin k) → Fin (windowSize i) → ℕ
  /-- Wall positions: b_i for each window, with 0 ≤ b_i ≤ M_i -/
  wallPos : Fin k → ℕ
  /-- Wall positions are bounded by window sizes -/
  wall_le_size : ∀ i, wallPos i ≤ windowSize i

/-- Classification of a window's base type from its wall position. -/
inductive BaseType where
  /-- b = 0: no active cells, digit is uninhabited -/
  | wall : BaseType
  /-- b = 1: one cell, token fixed at 0 -/
  | wire : BaseType
  /-- b ≥ 2: full digit with b states -/
  | standard : BaseType
  deriving DecidableEq, Repr

/-- Classify a window by its wall position. -/
def classifyBase (wallPos : ℕ) : BaseType :=
  if wallPos = 0 then .wall
  else if wallPos = 1 then .wire
  else .standard

theorem classifyBase_zero : classifyBase 0 = .wall := rfl
theorem classifyBase_one : classifyBase 1 = .wire := rfl

theorem classifyBase_standard (b : ℕ) (hb : 2 ≤ b) : classifyBase b = .standard := by
  unfold classifyBase
  have h0 : b ≠ 0 := by omega
  have h1 : b ≠ 1 := by omega
  simp [h0, h1]

/-- The active zone of a window: vertex indices in `[0, b_i)`. -/
def ObservationProfile.activeZone {k : ℕ} (prof : ObservationProfile k)
    (i : Fin k) : Finset ℕ :=
  Finset.range (prof.wallPos i)

/-! ## Definition 153: Legacy thread -/

/--
**fdrs.md**: Definition 153 (Legacy thread) [§10.1.3 · Phase 10] (lines 7222-7230)

For each window `W_i`, a legacy thread `L_i(t)` at step `t` is the ordered
list of currently instantiated active sites in `[0, b_i)`, ordered by
instantiation time.

Its length `ℓ_i(t) := |L_i(t)|` is the local persistent occupancy depth.

We model the legacy thread as a `List ℕ` of vertex indices within the active zone,
maintained in instantiation order.
-/
structure LegacyThread where
  /-- Bound (wall position) for this thread -/
  bound : ℕ
  /-- Ordered list of instantiated active-zone vertex indices -/
  sites : List ℕ
  /-- All sites are within the active zone bound -/
  sites_bound : ∀ v ∈ sites, v < bound
  /-- All sites are distinct (no duplicate occupancy) -/
  sites_nodup : sites.Nodup

/-- The occupancy depth (length) of a legacy thread. -/
def LegacyThread.depth (lt : LegacyThread) : ℕ := lt.sites.length

/-- An empty legacy thread (no instantiated sites). -/
def LegacyThread.empty (bound : ℕ) : LegacyThread where
  bound := bound
  sites := []
  sites_bound := by simp
  sites_nodup := List.nodup_nil

theorem LegacyThread.empty_depth (b : ℕ) : (LegacyThread.empty b).depth = 0 := rfl

/-- The depth of a legacy thread is bounded by the wall position. -/
theorem LegacyThread.depth_le_bound (lt : LegacyThread) :
    lt.depth ≤ lt.bound := by
  unfold depth
  -- The sites list is a nodup list of naturals all < bound.
  -- Convert to a Finset and compare cardinalities.
  have hnd := lt.sites_nodup
  have hb := lt.sites_bound
  have hsub : lt.sites.toFinset ⊆ Finset.range lt.bound := by
    intro v hv
    exact Finset.mem_range.mpr (hb v (List.mem_toFinset.mp hv))
  calc lt.sites.length = lt.sites.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ ≤ (Finset.range lt.bound).card := Finset.card_le_card hsub
    _ = lt.bound := Finset.card_range lt.bound

/-! ## Prefix occupancy invariant -/

/--
The **prefix occupancy invariant**: the occupied sites form exactly the
contiguous prefix `{0, 1, ..., depth-1}` of the active zone.

This is the structural invariant that distinguishes Phase 9 thermometer
semantics (where the digit value IS the contiguous fill level) from the
general Phase 10 dynamics (where arbitrary consumption can create holes).

When this invariant holds, `depth` faithfully encodes the token position
of a `SpatialDigit`, and the projection `windowToDigitProjection` is
semantically valid — not just type-correct.

Formally: `v` is occupied iff `v < depth`.
-/
def LegacyThread.IsPrefixOccupancy (lt : LegacyThread) : Prop :=
  lt.sites.toFinset = Finset.range lt.depth

/-- The empty thread trivially satisfies the prefix invariant. -/
theorem LegacyThread.empty_isPrefixOccupancy (b : ℕ) :
    (LegacyThread.empty b).IsPrefixOccupancy := by
  simp [IsPrefixOccupancy, empty, depth]

/-- Under the prefix invariant, every index below depth is occupied. -/
theorem LegacyThread.IsPrefixOccupancy.mem_of_lt {lt : LegacyThread}
    (hpre : lt.IsPrefixOccupancy) {v : ℕ} (hv : v < lt.depth) :
    v ∈ lt.sites := by
  rw [← List.mem_toFinset]
  rw [hpre]
  exact Finset.mem_range.mpr hv

/-- Under the prefix invariant, every occupied index is below depth. -/
theorem LegacyThread.IsPrefixOccupancy.lt_of_mem {lt : LegacyThread}
    (hpre : lt.IsPrefixOccupancy) {v : ℕ} (hv : v ∈ lt.sites) :
    v < lt.depth := by
  have := List.mem_toFinset.mpr hv
  rw [hpre] at this
  exact Finset.mem_range.mp this

/-- Under the prefix invariant, depth < bound implies the frontier index
    (= depth) is unoccupied — this is the next creation site. -/
theorem LegacyThread.IsPrefixOccupancy.frontier_unoccupied {lt : LegacyThread}
    (hpre : lt.IsPrefixOccupancy) (_hlt : lt.depth < lt.bound) :
    lt.depth ∉ lt.sites := by
  intro hmem
  exact Nat.lt_irrefl lt.depth (hpre.lt_of_mem hmem)

/-! ## Sea State -/

/--
Combined sea state: a sea together with an observation profile and
per-window legacy threads. This is the full state for Phase 10 dynamics.
-/
structure SeaState (k : ℕ) where
  /-- The underlying sea (graph + occupancy) -/
  sea : Sea
  /-- The observation profile (windows + wall positions) -/
  profile : ObservationProfile k
  /-- Per-window legacy threads -/
  threads : (i : Fin k) → LegacyThread
  /-- Thread bounds match wall positions -/
  thread_bound : ∀ i, (threads i).bound = profile.wallPos i

/-- Validity predicate for a sea state: occupancy is boolean (automatic),
    legacy threads track only instantiated active sites, ordering is consistent. -/
structure SeaState.Valid {k : ℕ} (state : SeaState k) : Prop where
  /-- Each legacy thread contains only instantiated sites -/
  sites_instantiated : ∀ (i : Fin k) (v : ℕ) (hv : v ∈ (state.threads i).sites),
    let idx : Fin (state.profile.windowSize i) :=
      ⟨v, by
        have hb := (state.threads i).sites_bound v hv
        rw [state.thread_bound i] at hb
        exact Nat.lt_of_lt_of_le hb (state.profile.wall_le_size i)⟩
    state.sea.occupancy (state.profile.windowVertex i idx) = true

end FdrsFormal.Modes.BaseZeroSea
