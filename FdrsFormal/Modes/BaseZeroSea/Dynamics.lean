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

# Base-Zero Sea: Dynamics

Deterministic creation and reversion dynamics for Phase 10.

## Mathematical Content (fdrs.md lines 7232-7282)

**Definition 154**: Deterministic creation step — creation selector function
**Definition 155**: Consumption target rule — deterministic reversion selector
**Definition 156**: Consumption schedule — deterministic trigger function
**Definition 157**: Unified deterministic sea tick — combined update

## References

- fdrs.md, Phase 10, Sections 10.1.4, 10.2.1–10.2.3 (lines 7232-7282)
-/

import FdrsFormal.Modes.BaseZeroSea.Basic

namespace FdrsFormal.Modes.BaseZeroSea

/-! ## Definition 154: Deterministic creation step -/

/--
**fdrs.md**: Definition 154 (Deterministic creation step) [§10.1.4 · Phase 10] (lines 7232-7245)

A creation selector is a deterministic function
`CreateTarget : SeaState k × ℕ → Option ℕ`
such that when `CreateTarget(state, t) = some v`:
- `σ(v) = false` (v is uninstantiated),
- `v` is adjacent to the current active frontier (1-Lipschitz locality),
- updating sets `σ(v) := true`.

If `CreateTarget` returns `none`, no creation occurs.
-/
structure CreateSelector (k : ℕ) where
  /-- The selection function: given state and time step, optionally pick a vertex -/
  target : SeaState k → ℕ → Option ℕ

/-- A creation selector is valid if it only targets uninstantiated vertices
    that are adjacent to an instantiated vertex (frontier locality). -/
structure CreateSelector.Valid {k : ℕ} (sel : CreateSelector k) : Prop where
  /-- Target must be uninstantiated -/
  target_uninstantiated : ∀ state t v,
    sel.target state t = some v → state.sea.occupancy v = false
  /-- Target must be adjacent to some instantiated vertex (1-Lipschitz locality) -/
  target_adjacent : ∀ state t v,
    sel.target state t = some v →
    ∃ w, state.sea.occupancy w = true ∧ state.sea.adj v w

/-- Apply a creation step: if the selector picks a vertex, instantiate it. -/
def applyCreation {k : ℕ} (sel : CreateSelector k) (state : SeaState k) (t : ℕ) :
    SeaState k :=
  match sel.target state t with
  | none => state
  | some v => { state with sea := state.sea.instantiate v }

/-- Creation preserves the graph structure. -/
theorem applyCreation_adj {k : ℕ} (sel : CreateSelector k) (state : SeaState k) (t : ℕ) :
    (applyCreation sel state t).sea.adj = state.sea.adj := by
  unfold applyCreation
  cases sel.target state t with
  | none => rfl
  | some v => exact Sea.instantiate_adj state.sea v

/-! ## Definition 155: Consumption target rule -/

/--
**fdrs.md**: Definition 155 (Consumption target rule) [§10.2.1 · Phase 10] (lines 7250-7261)

A consumption target rule is a deterministic function selecting which
thread index to revert (if any). Examples include:
- Oldest, Newest, Index(k), Pattern(f).

The rule takes the current site list and time step, returning an optional
index into the site list.
-/
structure ConsumeTargetRule where
  /-- Given a site list and time step, optionally select an index to revert -/
  target : List ℕ → ℕ → Option ℕ
  /-- Selected index must be within the site list -/
  target_valid : ∀ sites t idx, target sites t = some idx → idx < sites.length

/-- Oldest-first consumption: revert the first (oldest) site. -/
def ConsumeTargetRule.oldest : ConsumeTargetRule where
  target sites _t := if sites.length > 0 then some 0 else none
  target_valid := by
    intro sites t idx h
    split at h <;> simp_all

/-- Newest-first consumption: revert the last (newest) site. -/
def ConsumeTargetRule.newest : ConsumeTargetRule where
  target sites _t := if sites.length > 0 then some (sites.length - 1) else none
  target_valid := by
    intro sites t idx h
    split at h <;> simp_all
    omega

/-! ## Definition 156: Consumption schedule -/

/--
**fdrs.md**: Definition 156 (Consumption schedule) [§10.2.2 · Phase 10] (lines 7263-7269)

A consumption schedule is a deterministic trigger
`ConsumeSchedule : ℕ → Bool`
where `ConsumeSchedule(t) = true` means a consumption attempt occurs at step `t`.
-/
def ConsumeSchedule := ℕ → Bool

/-- The always-disabled schedule (no consumption ever). -/
def ConsumeSchedule.never : ConsumeSchedule := fun _ => false

/-- The always-enabled schedule (consumption attempted every step). -/
def ConsumeSchedule.always : ConsumeSchedule := fun _ => true

/-- Periodic schedule: consume every `p` steps (at t = 0, p, 2p, ...). -/
def ConsumeSchedule.periodic (p : ℕ) (_ : 0 < p) : ConsumeSchedule :=
  fun t => t % p == 0

/-! ## Definition 157: Unified deterministic sea tick -/

/--
**fdrs.md**: Definition 157 (Unified deterministic sea tick) [§10.2.3 · Phase 10] (lines 7271-7282)

Given `(CreateTarget, ConsumeTarget, ConsumeSchedule)`, one global step
`SeaTick : SeaState k × ℕ → SeaState k`
performs, in order:
1. deterministic creation (Definition 154),
2. if `ConsumeSchedule(t) = true`, deterministic reversion using Definition 155.

Reversion sets the chosen instantiated site back to `σ(v) := false`.
-/
structure SeaDynamicsParams (k : ℕ) where
  /-- Creation selector -/
  createSel : CreateSelector k
  /-- Per-window consumption target rules -/
  consumeRule : Fin k → ConsumeTargetRule
  /-- Consumption schedule -/
  schedule : ConsumeSchedule

/-- Apply consumption to a single window: if the rule selects a site, revert it
    in the sea and remove it from the thread. -/
def applyWindowConsume {k : ℕ} (state : SeaState k) (rule : ConsumeTargetRule)
    (i : Fin k) (t : ℕ) : SeaState k :=
  match h : rule.target (state.threads i).sites t with
  | none => state
  | some idx =>
    let hidx := rule.target_valid (state.threads i).sites t idx h
    let thread := state.threads i
    let siteVal := thread.sites.get ⟨idx, hidx⟩
    have hbound : siteVal < state.profile.windowSize i := by
      have hb := thread.sites_bound siteVal (List.get_mem thread.sites ⟨idx, hidx⟩)
      have htb : thread.bound = state.profile.wallPos i := state.thread_bound i
      have hwl := state.profile.wall_le_size i
      rw [← htb] at hwl
      exact Nat.lt_of_lt_of_le hb hwl
    let v := state.profile.windowVertex i ⟨siteVal, hbound⟩
    let sea' := state.sea.revert v
    let sites' := thread.sites.eraseIdx idx
    have hsites_bound : ∀ w ∈ sites', w < thread.bound := by
      intro w hw; exact thread.sites_bound w (List.mem_of_mem_eraseIdx hw)
    have hsites_nodup : sites'.Nodup :=
      thread.sites_nodup.sublist (List.eraseIdx_sublist thread.sites idx)
    let thread' : LegacyThread := {
      bound := thread.bound
      sites := sites'
      sites_bound := hsites_bound
      sites_nodup := hsites_nodup
    }
    { sea := sea'
      profile := state.profile
      threads := fun j => if j = i then thread' else state.threads j
      thread_bound := by
        intro j
        by_cases hj : j = i
        · subst hj; show (if j = j then thread' else state.threads j).bound = _
          rw [if_pos rfl]; exact state.thread_bound j
        · show (if j = i then thread' else state.threads j).bound = _
          rw [if_neg hj]; exact state.thread_bound j }

/-- Apply consumption across all windows, processing window 0, 1, ..., k-1 in order. -/
def consumeWindows {k : ℕ} (state : SeaState k) (rules : Fin k → ConsumeTargetRule)
    (t : ℕ) (n : ℕ) : SeaState k :=
  if hn : n < k then
    let state' := applyWindowConsume state (rules ⟨n, hn⟩) ⟨n, hn⟩ t
    consumeWindows state' rules t (n + 1)
  else
    state
termination_by k - n

/-- The unified deterministic sea tick: creation then optional consumption. -/
def seaTick {k : ℕ} (params : SeaDynamicsParams k) (state : SeaState k) (t : ℕ) :
    SeaState k :=
  -- Step 1: Apply creation
  let afterCreate := applyCreation params.createSel state t
  -- Step 2: Apply consumption if scheduled
  if params.schedule t then
    consumeWindows afterCreate params.consumeRule t 0
  else
    afterCreate

/-- SeaTick produces a deterministic successor: it is a pure function. -/
theorem seaTick_deterministic {k : ℕ} (params : SeaDynamicsParams k)
    (state : SeaState k) (t : ℕ) :
    ∀ s₁ s₂, seaTick params state t = s₁ → seaTick params state t = s₂ → s₁ = s₂ :=
  fun _ _ h₁ h₂ => h₁.symm.trans h₂

end FdrsFormal.Modes.BaseZeroSea
