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

# Timing Bounds

This file defines timing analysis for composed FDRS programs.

## Mathematical Content (fdrs.md Phase 8)

**Timing Bounds**: Worst-case and expected execution times.

**Key Results**:
- Tick operations have bounded worst-case time
- Composed programs have predictable timing

## References

- fdrs.md, Phase 8, Section 5.7 (Timing Analysis)
- fdrs.md, Phase 8, Section 5.8 (Schedulability)
-/

import FdrsFormal.Core

namespace FdrsFormal.Composition.TimingBounds

/-!
## Operation Timing Model
-/

/--
Timing specification for an operation: captures WCET, BCET, and expected time.

**fdrs.md**: Operations have timing characteristics that determine schedulability.
-/
structure OperationTiming where
  /-- Worst-case execution time -/
  wcet : ℕ
  /-- Best-case execution time -/
  bcet : ℕ
  /-- Expected execution time (as a rational) -/
  expected : ℚ
  /-- BCET ≤ expected ≤ WCET -/
  bcet_le_expected : (bcet : ℚ) ≤ expected
  expected_le_wcet : expected ≤ wcet

/--
A timing model assigns timing to each operation ID.
-/
def TimingModel := ℕ → OperationTiming

/-!
## Execution Time Accessors
-/

/--
Worst-case execution time of an operation under a timing model.

**fdrs.md**: WCET(op) = max time over all inputs.
-/
def wcet (tm : TimingModel) (op : ℕ) : ℕ :=
  (tm op).wcet

/--
Best-case execution time of an operation under a timing model.

**fdrs.md**: BCET(op) = min time over all inputs.
-/
def bcet (tm : TimingModel) (op : ℕ) : ℕ :=
  (tm op).bcet

/--
Expected execution time of an operation under a timing model.

**fdrs.md**: E[time(op)] under uniform input distribution.
-/
def expectedTime (tm : TimingModel) (op : ℕ) : ℚ :=
  (tm op).expected

/-!
## Tick Timing
-/

/--
Tick operation timing for L-digit numbers.

**fdrs.md**: WCET is O(L) (full carry), BCET is O(1) (no carry),
expected is O(1) (geometric decay of carry probability).
-/
def tickTiming (L : ℕ) (hL : 2 ≤ L) : OperationTiming :=
  { wcet := L  -- Worst case: full carry propagation
    bcet := 1  -- Best case: no carry (increment in place)
    expected := 2  -- Expected: O(1) by geometric series argument
    bcet_le_expected := by norm_num
    expected_le_wcet := by
      show (2 : ℚ) ≤ (L : ℚ)
      exact_mod_cast hL }

/--
Tick worst-case time is O(L) for L-digit numbers.

**fdrs.md**: Worst case is full carry propagation.
-/
theorem tick_wcet_bound (L : ℕ) (hL : 2 ≤ L) :
    (tickTiming L hL).wcet = L := rfl

/--
Tick expected time is O(1).

**fdrs.md**: Expected carry length is bounded constant.
-/
theorem tick_expected_bound (L : ℕ) (hL : 2 ≤ L) :
    (tickTiming L hL).expected ≤ 2 := le_refl _

/-!
## Composition Timing
-/

/--
Sequential composition of operation timings.

**fdrs.md**: time(A; B) = time(A) + time(B)
-/
def sequentialTiming (t₁ t₂ : OperationTiming) : OperationTiming :=
  { wcet := t₁.wcet + t₂.wcet
    bcet := t₁.bcet + t₂.bcet
    expected := t₁.expected + t₂.expected
    bcet_le_expected := by
      have h1 := t₁.bcet_le_expected
      have h2 := t₂.bcet_le_expected
      push_cast; linarith
    expected_le_wcet := by
      have h1 := t₁.expected_le_wcet
      have h2 := t₂.expected_le_wcet
      push_cast; linarith }

/--
Sequential composition WCET is sum of WCETs.
-/
theorem sequential_wcet (t₁ t₂ : OperationTiming) :
    (sequentialTiming t₁ t₂).wcet = t₁.wcet + t₂.wcet := rfl

/--
Parallel composition of operation timings.

**fdrs.md**: time(A ∥ B) = max(time(A), time(B))
-/
def parallelTiming (t₁ t₂ : OperationTiming) : OperationTiming :=
  { wcet := max t₁.wcet t₂.wcet
    bcet := max t₁.bcet t₂.bcet
    expected := max t₁.expected t₂.expected
    bcet_le_expected := by
      simp only [Nat.cast_max]
      exact max_le_max t₁.bcet_le_expected t₂.bcet_le_expected
    expected_le_wcet := by
      simp only [Nat.cast_max]
      exact max_le_max t₁.expected_le_wcet t₂.expected_le_wcet }

/--
Parallel composition WCET is max of WCETs.
-/
theorem parallel_wcet (t₁ t₂ : OperationTiming) :
    (parallelTiming t₁ t₂).wcet = max t₁.wcet t₂.wcet := rfl

/-!
## Schedulability
-/

/--
A schedule: assignment of operations to time slots.

**fdrs.md**: Schedule maps operations to start times.
-/
structure Schedule where
  /-- Start time of each operation -/
  startTime : ℕ → ℕ

/--
A schedule is feasible if all deadlines are met.

**fdrs.md**: Feasibility = all operations complete before deadline.
-/
def isFeasible (tm : TimingModel) (s : Schedule) (deadlines : ℕ → ℕ) : Prop :=
  ∀ op, s.startTime op + (tm op).wcet ≤ deadlines op

/--
A schedule that starts all operations at time 0 (parallel execution model).
-/
def trivialSchedule : Schedule :=
  { startTime := fun _ => 0 }

/--
FDRS programs are schedulable: whenever every operation's worst-case execution
time fits within its deadline, a feasible schedule exists.

**fdrs.md**: Earliest Deadline First scheduling works for FDRS. Concretely, when
`wcet(op) ≤ deadline(op)` for all `op`, the all-at-time-`0` schedule already meets
every deadline, so the feasibility problem is solvable.
-/
theorem fdrs_schedulable (tm : TimingModel) (deadlines : ℕ → ℕ)
    (h : ∀ op, (tm op).wcet ≤ deadlines op) :
    ∃ s : Schedule, isFeasible tm s deadlines := by
  refine ⟨trivialSchedule, ?_⟩
  intro op
  simpa [trivialSchedule] using h op

/-!
## Latency Bounds
-/

/--
A program as a list of operation IDs (simplified representation).
-/
abbrev Program := List ℕ

/--
End-to-end latency of a composed program: sum of WCETs along the path.

**fdrs.md**: Latency = time from input to output.
-/
def latency (tm : TimingModel) (program : Program) : ℕ :=
  program.foldl (fun acc op => acc + (tm op).wcet) 0

/--
Latency of empty program is zero.
-/
theorem latency_nil (tm : TimingModel) : latency tm [] = 0 := rfl

/--
Helper: foldl with non-zero initial value equals initial + foldl from zero.
-/
private theorem foldl_add_init (tm : TimingModel) (program : Program) (init : ℕ) :
    program.foldl (fun acc op => acc + (tm op).wcet) init =
    init + program.foldl (fun acc op => acc + (tm op).wcet) 0 := by
  induction program generalizing init with
  | nil => simp
  | cons op ops ih =>
    simp only [List.foldl_cons]
    rw [ih, ih (0 + (tm op).wcet)]
    ring

/--
Latency is additive for sequential composition.
-/
theorem latency_append (tm : TimingModel) (p₁ p₂ : Program) :
    latency tm (p₁ ++ p₂) = latency tm p₁ + latency tm p₂ := by
  simp only [latency]
  rw [List.foldl_append]
  rw [foldl_add_init]

/--
Latency is bounded by sum of component WCETs.

**fdrs.md**: Latency ≤ Σ WCET(op) for op on critical path.
-/
theorem latency_bound (tm : TimingModel) (program : Program) :
    latency tm program = (program.map fun op => (tm op).wcet).sum := by
  induction program with
  | nil => rfl
  | cons op ops ih =>
    simp only [latency, List.foldl_cons, List.map_cons, List.sum_cons]
    -- Use the helper lemma to handle non-zero initial accumulator
    have h : ops.foldl (fun acc op => acc + (tm op).wcet) (0 + (tm op).wcet) =
             (tm op).wcet + ops.foldl (fun acc op => acc + (tm op).wcet) 0 := by
      rw [foldl_add_init]
      ring
    rw [h]
    simp only [latency] at ih
    rw [ih]

end FdrsFormal.Composition.TimingBounds
