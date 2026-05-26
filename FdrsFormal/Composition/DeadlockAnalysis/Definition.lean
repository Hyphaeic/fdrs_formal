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

# Deadlock Analysis

This file defines deadlock detection and prevention for composed programs.

## Mathematical Content (fdrs.md Phase 8)

**Deadlock**: A state where no progress can be made due to circular dependencies.

**Key Results**:
- FDRS programs are deadlock-free by construction
- Time-monotone operations prevent circular waits

## References

- fdrs.md, Phase 8, Section 5.5 (Deadlock Analysis)
- fdrs.md, Phase 8, Section 5.6 (Liveness Properties)
-/

import FdrsFormal.Core
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

namespace FdrsFormal.Composition.DeadlockAnalysis

/-!
## Dependency Graphs
-/

/--
A dependency: one operation waiting for another.

**fdrs.md**: Dependencies arise from data flow and synchronization.
-/
structure Dependency where
  waiting : ℕ      -- Operation ID that is waiting
  waitingFor : ℕ   -- Operation ID being waited for
  resource : ℕ     -- Resource ID involved

/--
A dependency graph: all dependencies in a system.
-/
structure DependencyGraph where
  dependencies : Set Dependency

/--
A path in the dependency graph: a sequence of dependencies where each
waiting operation is the next waitingFor.
-/
inductive DependencyPath (dg : DependencyGraph) : ℕ → ℕ → Prop where
  | refl (op : ℕ) : DependencyPath dg op op
  | step (d : Dependency) (hd : d ∈ dg.dependencies)
      (p : DependencyPath dg d.waitingFor op) : DependencyPath dg d.waiting op

/--
A cycle in the dependency graph: a non-trivial path from an operation to itself.

**fdrs.md**: Cycles indicate potential deadlocks.
-/
def hasCycle (dg : DependencyGraph) : Prop :=
  ∃ op d, d ∈ dg.dependencies ∧ d.waiting = op ∧ DependencyPath dg d.waitingFor op

/-!
## Deadlock Freedom
-/

/--
A system is deadlock-free if its dependency graph is acyclic.

**fdrs.md**: No cycles ⟹ no deadlock.
-/
def isDeadlockFree (dg : DependencyGraph) : Prop :=
  ¬hasCycle dg

/--
Time-ordered dependencies are acyclic.

**fdrs.md**: If all dependencies go forward in time, no cycles exist.
-/
structure TimeOrderedDependencies (dg : DependencyGraph) where
  timeOf : ℕ → ℕ  -- Time of each operation
  forward : ∀ d ∈ dg.dependencies, timeOf d.waiting > timeOf d.waitingFor

/--
Time along a dependency path is non-increasing, and strictly decreasing if non-trivial.
-/
theorem path_time_le (dg : DependencyGraph) (h : TimeOrderedDependencies dg)
    {op₁ op₂ : ℕ} (p : DependencyPath dg op₁ op₂) :
    h.timeOf op₁ ≥ h.timeOf op₂ := by
  induction p with
  | refl op => exact Nat.le_refl _
  | step d hd _ ih =>
    have h_step := h.forward d hd
    exact Nat.le_trans ih (Nat.le_of_lt h_step)

/--
Time-ordered dependencies imply deadlock freedom.

**Proof**: If there were a cycle op → d.waitingFor → ... → op, then
by time ordering we'd have timeOf(op) > timeOf(d.waitingFor) ≥ timeOf(op),
which is a contradiction.
-/
theorem time_ordered_deadlock_free (dg : DependencyGraph)
    (h : TimeOrderedDependencies dg) : isDeadlockFree dg := by
  intro ⟨op, d, hd, hwait, p⟩
  -- We have: op → d.waitingFor → ... → op (a cycle)
  have h_step := h.forward d hd
  -- h_step: h.timeOf d.waiting > h.timeOf d.waitingFor
  rw [hwait] at h_step
  -- h_step: h.timeOf op > h.timeOf d.waitingFor
  have h_path := path_time_le dg h p
  -- h_path: h.timeOf d.waitingFor ≥ h.timeOf op
  -- Combining: h.timeOf op > h.timeOf d.waitingFor ≥ h.timeOf op
  -- This means h.timeOf op > h.timeOf op, contradiction
  exact Nat.not_lt.mpr h_path h_step

/-!
## FDRS Deadlock Freedom
-/

/--
FDRS operations are inherently time-ordered.

**fdrs.md**: Tick advances time; Dirichlet transforms are instantaneous.

This is a placeholder theorem stating a trivial property.
The actual time-ordering property is captured by `TimeOrderedDependencies`.
-/
theorem fdrs_time_ordered (deps : DependencyGraph)
    (h : TimeOrderedDependencies deps) :
    isDeadlockFree deps :=
  time_ordered_deadlock_free deps h

/--
FDRS programs are deadlock-free.

**fdrs.md Theorem**: All FDRS programs terminate or make progress.

The substantive version is `deadlock_free_makes_progress` below, which proves
that any finite system with acyclic dependencies makes progress.
-/
theorem fdrs_deadlock_free (deps : DependencyGraph)
    (h : TimeOrderedDependencies deps) :
    ¬hasCycle deps :=
  time_ordered_deadlock_free deps h

/-!
## Liveness Properties
-/

/--
A system state with pending operations.
-/
structure SystemState where
  /-- Set of pending operation IDs -/
  pending : Set ℕ
  /-- Dependency graph of pending operations -/
  deps : DependencyGraph

/--
A system makes progress if it's either complete or some operation can run.

**fdrs.md**: Liveness = something good eventually happens.

An operation can run if it has no unsatisfied dependencies (nothing it's waiting for).
-/
def makesProgress (s : SystemState) : Prop :=
  s.pending = ∅ ∨
  ∃ op ∈ s.pending, ∀ d ∈ s.deps.dependencies, d.waiting = op → d.waitingFor ∉ s.pending

/-!
## Finite System States

For proving progress properties, we need finiteness assumptions.
Real systems always have finite pending operations.
-/

/--
A finite system state with a Finset of pending operations.
-/
structure FiniteSystemState where
  /-- Finite set of pending operation IDs -/
  pending : Finset ℕ
  /-- Dependency graph of pending operations -/
  deps : DependencyGraph

/--
Convert a finite system state to a general system state.
-/
def FiniteSystemState.toSystemState (s : FiniteSystemState) : SystemState :=
  { pending := ↑s.pending, deps := s.deps }

/--
Progress for finite systems: either complete or some operation can run.
-/
def makesProgressFinite (s : FiniteSystemState) : Prop :=
  s.pending = ∅ ∨
  ∃ op ∈ s.pending, ∀ d ∈ s.deps.dependencies, d.waiting = op → d.waitingFor ∉ s.pending

/--
The set of operations that a given operation depends on (within the pending set).
-/
def pendingDependenciesOf (s : FiniteSystemState) (op : ℕ) : Set ℕ :=
  { waitedFor | ∃ d ∈ s.deps.dependencies, d.waiting = op ∧ d.waitingFor = waitedFor ∧ waitedFor ∈ s.pending }

/--
An operation is runnable if it has no pending dependencies.
-/
def isRunnable (s : FiniteSystemState) (op : ℕ) : Prop :=
  op ∈ s.pending ∧ ∀ d ∈ s.deps.dependencies, d.waiting = op → d.waitingFor ∉ s.pending

/--
A path in the dependency graph restricted to pending operations.
-/
inductive PendingPath (s : FiniteSystemState) : ℕ → ℕ → Prop where
  | refl (op : ℕ) (h : op ∈ s.pending) : PendingPath s op op
  | step (d : Dependency) (hd : d ∈ s.deps.dependencies)
      (hw : d.waiting ∈ s.pending) (hwf : d.waitingFor ∈ s.pending)
      (p : PendingPath s d.waitingFor op) : PendingPath s d.waiting op

/--
A cycle in the pending operations: an operation waits (through dependencies)
for itself, all within the pending set.
-/
def hasPendingCycle (s : FiniteSystemState) : Prop :=
  ∃ op d, d ∈ s.deps.dependencies ∧ d.waiting = op ∧ d.waiting ∈ s.pending ∧
    d.waitingFor ∈ s.pending ∧ PendingPath s d.waitingFor op

/--
Convert a PendingPath to a DependencyPath (forgets pending constraints).
-/
theorem pendingPath_to_dependencyPath (s : FiniteSystemState) {a b : ℕ}
    (p : PendingPath s a b) : DependencyPath s.deps a b := by
  induction p with
  | refl op _ => exact DependencyPath.refl op
  | step d hd _ _ _ ih => exact DependencyPath.step d hd ih

/--
If the dependency graph is acyclic, there are no pending cycles.
-/
theorem no_pending_cycle_of_acyclic (s : FiniteSystemState) (hfree : isDeadlockFree s.deps) :
    ¬hasPendingCycle s := by
  intro ⟨op, d, hd, hwait, _, _, ppath⟩
  apply hfree
  use op, d, hd, hwait
  exact pendingPath_to_dependencyPath s ppath

/--
Key lemma: In a non-empty finite system without pending cycles,
there exists a runnable operation.

**Mathematical Proof**:
1. Assume for contradiction that no operation is runnable.
2. Then every op ∈ pending has a dependency on some op' ∈ pending.
3. This defines a successor function next : pending → pending.
4. Starting from any element, iterate k+1 times (where k = |pending|).
5. By the pigeonhole principle, some element repeats: seq(i) = seq(j) for i < j.
6. The path from seq(i+1) through seq(j) = seq(i) forms a cycle.
7. This contradicts the acyclicity assumption.

This is a standard theorem in graph theory (DAGs have source nodes).
The proof uses the pigeonhole principle and is constructive in mathematics,
but the Lean 4 formalization is technically involved due to dependent types.

**Proof**: By contradiction. If no op is runnable, every op ∈ pending has a
pending dependency. Iterating this |pending|+1 times, pigeonhole gives a
repeated element, hence a cycle in the pending dependencies.
-/
theorem exists_runnable_of_no_pending_cycle (s : FiniteSystemState)
    (hne : s.pending.Nonempty) (hno_cycle : ¬hasPendingCycle s) :
    ∃ op, isRunnable s op := by
  by_contra h_none
  push_neg at h_none
  -- Every op ∈ pending has a pending dependency
  have h_has_dep : ∀ op, op ∈ s.pending → ∃ d, d ∈ s.deps.dependencies ∧
      d.waiting = op ∧ d.waitingFor ∈ s.pending := by
    intro op hop
    have h := h_none op
    unfold isRunnable at h
    push_neg at h
    obtain ⟨d, hd, hw, hwf⟩ := h hop
    exact ⟨d, hd, hw, hwf⟩
  -- Choose a dependency witness for each pending op
  choose dep h_dep_in h_dep_wait h_dep_next using h_has_dep
  -- Build sequence into the subtype { op // op ∈ s.pending }
  obtain ⟨op₀, hop₀⟩ := hne
  let build : ℕ → { op : ℕ // op ∈ s.pending } :=
    fun n => Nat.rec ⟨op₀, hop₀⟩
      (fun _ ⟨op, hop⟩ => ⟨(dep op hop).waitingFor, h_dep_next op hop⟩) n
  -- Project out the sequence and membership
  let seq : ℕ → ℕ := fun n => (build n).val
  have h_in : ∀ n, seq n ∈ s.pending := fun n => (build n).property
  -- Key property: seq(k+1) = (dep (seq k) _).waitingFor
  have h_step : ∀ k, seq (k + 1) = (dep (seq k) (h_in k)).waitingFor := by
    intro k; rfl
  -- Pigeonhole: Fin (card + 1) → s.pending can't be injective
  let f : Fin (s.pending.card + 1) → s.pending := fun i => ⟨seq i, h_in i⟩
  have h_not_inj : ¬Function.Injective f := by
    intro hinj
    have := Fintype.card_le_of_injective f hinj
    simp [Fintype.card_fin] at this
  rw [Function.Injective] at h_not_inj
  push_neg at h_not_inj
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩, heq, hne_ij⟩ := h_not_inj
  simp only [f, Subtype.mk.injEq] at heq
  -- Get i < j or j < i (they're not equal)
  have hne_nat : i ≠ j := fun h => hne_ij (Fin.ext h)
  -- Build PendingPath from seq(a) to seq(a+k) by induction on k
  have chain : ∀ k a, PendingPath s (seq a) (seq (a + k)) := by
    intro k
    induction k with
    | zero => intro a; simp; exact PendingPath.refl _ (h_in a)
    | succ k ih =>
      intro a
      have hrw : a + (k + 1) = (a + 1) + k := by omega
      rw [hrw]
      -- dep(seq a).waiting = seq a, dep(seq a).waitingFor = seq(a+1)
      -- Use subst-friendly approach: rewrite goal then close
      suffices h : PendingPath s (dep (seq a) (h_in a)).waiting (seq ((a + 1) + k)) by
        rwa [h_dep_wait (seq a) (h_in a)] at h
      exact PendingPath.step (dep (seq a) (h_in a)) (h_dep_in (seq a) (h_in a))
        (by rw [h_dep_wait]; exact h_in a)
        (h_dep_next (seq a) (h_in a))
        (by rw [show (dep (seq a) (h_in a)).waitingFor = seq (a + 1) from (h_step a).symm]
            exact ih (a + 1))
  -- Build a cycle using the repeated element
  -- Get the smaller index as the cycle start
  obtain hij | hji := Nat.lt_or_gt_of_ne hne_nat
  · -- i < j: cycle from seq(i) through seq(i+1)...seq(j)=seq(i)
    apply hno_cycle
    refine ⟨seq i, dep (seq i) (h_in i), h_dep_in _ (h_in i),
      h_dep_wait _ (h_in i), ?_, h_dep_next _ (h_in i), ?_⟩
    · rw [h_dep_wait]; exact h_in i
    · -- Need PendingPath from (dep (seq i) _).waitingFor to seq(i)
      rw [show (dep (seq i) (h_in i)).waitingFor = seq (i + 1) from (h_step i).symm]
      rw [show seq i = seq j from heq]
      have hk : j = (i + 1) + (j - i - 1) := by omega
      rw [hk]
      exact chain (j - i - 1) (i + 1)
  · -- j < i: symmetric
    apply hno_cycle
    refine ⟨seq j, dep (seq j) (h_in j), h_dep_in _ (h_in j),
      h_dep_wait _ (h_in j), ?_, h_dep_next _ (h_in j), ?_⟩
    · rw [h_dep_wait]; exact h_in j
    · rw [show (dep (seq j) (h_in j)).waitingFor = seq (j + 1) from (h_step j).symm]
      rw [show seq j = seq i from heq.symm]
      have hk : i = (j + 1) + (i - j - 1) := by omega
      rw [hk]
      exact chain (i - j - 1) (j + 1)

/--
Deadlock-free finite systems make progress.

**Proof**: Combines acyclicity → no pending cycles → exists runnable operation.
-/
theorem deadlock_free_makes_progress_finite (s : FiniteSystemState)
    (hne : s.pending.Nonempty) (hfree : isDeadlockFree s.deps) :
    makesProgressFinite s := by
  have h_no_cycle := no_pending_cycle_of_acyclic s hfree
  obtain ⟨op, h_runnable⟩ := exists_runnable_of_no_pending_cycle s hne h_no_cycle
  right
  exact ⟨op, h_runnable.1, h_runnable.2⟩

/--
Deadlock-free systems make progress: if there are pending operations
and the system is deadlock-free, then some operation can run.

**Proof**: For finite pending sets, use `deadlock_free_makes_progress_finite`.
The general statement follows from the finite case since we only need to
find ONE runnable operation, which can always be done in a finite subset.

In practice, all real systems have finite pending operations.
-/
theorem deadlock_free_makes_progress (s : SystemState) (hne : s.pending.Nonempty)
    (hfree : isDeadlockFree s.deps)
    (hfin : ∃ ps : Finset ℕ, ↑ps = s.pending) : makesProgress s := by
  obtain ⟨ps, hps⟩ := hfin
  let fs : FiniteSystemState := { pending := ps, deps := s.deps }
  -- Show fs.pending is nonempty
  have hne_fs : fs.pending.Nonempty := by
    -- s.pending is nonempty and equals ↑ps, so ps is nonempty
    obtain ⟨x, hx⟩ := hne
    rw [← hps] at hx
    exact ⟨x, hx⟩
  have hprog := deadlock_free_makes_progress_finite fs hne_fs hfree
  cases hprog with
  | inl hemp =>
    -- fs.pending = ∅ means ps = ∅, so s.pending = ↑ps = ∅
    left
    rw [← hps]
    -- hemp : fs.pending = ∅, and fs.pending = ps (by definition)
    -- So ps = ∅, and we need ↑∅ = ∅ which is Finset.coe_empty
    have : ps = ∅ := hemp
    rw [this, Finset.coe_empty]
  | inr hex =>
    right
    obtain ⟨op, hop, hrun⟩ := hex
    use op
    constructor
    · -- op ∈ fs.pending = ps, and ↑ps = s.pending
      rw [← hps]
      exact hop
    · -- hrun says: ∀ d ∈ fs.deps.dependencies, d.waiting = op → d.waitingFor ∉ fs.pending
      -- fs.deps = s.deps and fs.pending = ps with ↑ps = s.pending
      intro d hd hw
      have h := hrun d hd hw
      rw [← hps]
      exact h

/--
FDRS programs always make progress (liveness).

**fdrs.md**: FDRS programs have time-ordered dependencies (tick advances time,
transforms are instantaneous), so they are automatically deadlock-free.

Note: Requires finiteness of the pending set. All physical FDRS programs
have finite pending operations at any point in execution.
-/
theorem fdrs_liveness (s : SystemState) (h_time_ordered : TimeOrderedDependencies s.deps)
    (hfin : ∃ ps : Finset ℕ, ↑ps = s.pending) :
    makesProgress s := by
  by_cases hemp : s.pending = ∅
  · left; exact hemp
  · -- Non-empty pending set with time-ordered dependencies
    have hfree := time_ordered_deadlock_free s.deps h_time_ordered
    have hne : s.pending.Nonempty := Set.nonempty_iff_ne_empty.mpr hemp
    exact deadlock_free_makes_progress s hne hfree hfin

end FdrsFormal.Composition.DeadlockAnalysis
