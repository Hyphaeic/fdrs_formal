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

# Synthetic place complex — the Phase-8 concretization bridge

The corpus carries two network formalizations: the concrete Phase-8 layer
(`Composition/` — timeline graphs, routing tables, injection queues; June) and the
abstract SU7 machine (`SyntheticPlace/Network*` — July). Unbridged, they would
drift into exactly the recreation pattern the SPS series exists to prevent. This
module welds them, in the SU7.0 style — the concrete layer read as an *instance*
of the abstract machine:

* **Shape** — `NetworkShape.ofTimelineGraph`: a Phase-8 `TimelineGraph` IS a
  network shape (places = timeline nodes, coupling edges = the graph's edges).
* **Grading** — `timelineDeps` + `timeline_graded`: a strictly time-monotone
  timeline graph's edge relation, read as a clause-3 dependency declaration, is
  GRADED — the potential is literally the node's `time` field. Phase 8's
  time-ordering and SU7.1's dependency grading are the same mathematics, now as a
  theorem rather than a remark.
* **Rule** — `ComplexRule.ofRouting`: a per-edge `RoutingEntry` assignment reads as
  a coupling rule (the entry's `transform` as the grant weight, all-transport, no
  declared carry — the concrete layer's capacity-grant regime, D8), with
  `ofRouting_fanoutLawful`: its fan-out is unconditionally lawful.
* **THE QUEUE DISCHARGE** — `QueueConfig`: the queue-backed edge register
  (issued/consumed totals + a FIFO buffer, the `Composition/Injection` discipline
  with monoid-valued payloads). `queueReachable_balanced`: the SU6b balance law at
  EVERY capacity — `issued = consumed + buffer.sum`. And the SU7.0-style instance
  theorem **`queueReachable_one_toCurrency`**: a capacity-one queue register IS the
  `CurrencyConfig` register (the projection maps reachable to reachable, issue to
  issue, consume to consume), with `queueBalanced_one_iff` closing the loop. The
  "queue-valued interfaces (capacity > 1)" open of the roadmap is hereby
  discharged as REUSE: the general register exists, its balance law holds, and
  capacity-one is the machine's proven special case. Literal weld to the Phase-8
  artifact: `payloads` + `payloads_enqueue`/`payloads_dequeue` — the
  `InjectionQueue` operations project onto the buffer discipline.

**Honest scope.** `ofRouting` reads `transform` as a grant weight — the declared
interpretation; richer routing semantics (source/sink typing, determinism) live in
the concrete layer and are not re-legislated here. Swapping `CurrencyConfig` for
`QueueConfig` inside `CConfig` (the capacity->1 machine) is the mechanical upgrade
this module licenses but does not perform — the SU7 theorems that would need
re-proving are exactly the per-edge balance transports, whose queue forms are
proven here. Leaf module over SU7.1 + Composition. No `sorry`; axiom-clean.
-/
import FdrsFormal.Modes.SyntheticPlace.NetworkComplexStep
import FdrsFormal.Composition.TimelineGraphs.Definition
import FdrsFormal.Composition.Routing.Definition
import FdrsFormal.Composition.Injection.Queue
import Mathlib.Data.Nat.Pairing

namespace FdrsFormal.Modes.SyntheticPlace

open FdrsFormal.Composition.DeadlockAnalysis

/-! ## 1. Shape: a timeline graph is a network shape -/

instance : DecidableEq Composition.TimelineGraphs.TimelineNode := fun a b =>
  decidable_of_iff (a.time = b.time ∧ a.state = b.state) (by cases a; cases b; simp)

/-- A Phase-8 timeline graph, read as a network shape: places are the timeline
nodes, coupling edges are the graph's edges. -/
def NetworkShape.ofTimelineGraph (G : Composition.TimelineGraphs.TimelineGraph) :
    NetworkShape where
  V := Composition.TimelineGraphs.TimelineNode
  E := {e : Composition.TimelineGraphs.TimelineEdge // e ∈ G.edges}
  src := fun e => e.1.source
  tgt := fun e => e.1.target

/-! ## 2. Grading: Phase-8 time-ordering IS clause-3 dependency grading -/

/-- The timeline graph's edge relation as a clause-3 dependency declaration
(operations coded by `Nat.pair time state`; each edge: the target waits for the
source). -/
def timelineDeps (G : Composition.TimelineGraphs.TimelineGraph) : DepGraph where
  dependencies :=
    {d | ∃ e ∈ G.edges, d.waiting = Nat.pair e.target.time e.target.state ∧
      d.waitingFor = Nat.pair e.source.time e.source.state}

/-- **The weld, grading half**: a strictly time-monotone timeline graph's
dependency declaration is GRADED — the `timeOf` potential is literally the node's
`time` field. Phase 8's time-ordering and SU7.1's well-formedness are one fact. -/
def timeline_graded (G : Composition.TimelineGraphs.TimelineGraph)
    (hstrict : ∀ e ∈ G.edges, e.source.time < e.target.time) :
    TimeOrderedDependencies (timelineDeps G) where
  timeOf := fun op => (Nat.unpair op).1
  forward := by
    rintro d ⟨e, he, hw, hwf⟩
    rw [hw, hwf]
    simpa [Nat.unpair_pair] using hstrict e he

/-! ## 3. Rule: a routing assignment is a coupling rule -/

/-- A per-edge routing assignment read as a coupling rule: the entry's `transform`
is the grant weight (default `1`), all edges transport, no declared carry (the
concrete layer's capacity-grant regime, D8), content windows, dependency
declarations from the graph. -/
def ComplexRule.ofRouting (N : NetworkShape)
    (entry : N.E → Composition.Routing.RoutingEntry) (deps : N.V → DepGraph) :
    ComplexRule N ℕ where
  nodeFiber := fun _ => none
  carry := fun _ => none
  species := fun _ => Species.transport
  token := fun _ => 0
  fanout := fun e _ _ => (entry e).transform.getD 1
  admit := fun _ g d => d < g
  deps := deps

/-- The routing rule's fan-out is unconditionally lawful (no declared carry, no
triggers — mirror of `ofRule_fanoutLawful`). -/
theorem ofRouting_fanoutLawful {N : NetworkShape} [DecidableEq N.V] [Fintype N.E]
    (entry : N.E → Composition.Routing.RoutingEntry) (deps : N.V → DepGraph)
    (cfg : CConfig N ℕ) (v : N.V) (d : ℕ) :
    FanoutLawful (ComplexRule.ofRouting N entry deps) cfg v d := by
  constructor
  · intro c hc
    exact absurd hc (by simp [ComplexRule.ofRouting])
  · intro e _ hs
    exact absurd hs (by simp [ComplexRule.ofRouting])

/-! ## 4. The queue register: capacity->1, balance at every capacity -/

variable {M : Type*} [AddCommMonoid M]

/-- The queue-backed edge register: the `Composition/Injection` FIFO discipline
with monoid-valued payloads and the declared ledger. -/
structure QueueConfig (M : Type*) where
  issued : M
  consumed : M
  buffer : List M

/-- The empty queue register. -/
def QueueConfig.init : QueueConfig M := ⟨0, 0, []⟩

/-- Issue = FIFO enqueue (the `Injection.enqueue` shape) + ledger. -/
def QueueConfig.issue (c : QueueConfig M) (g : M) : QueueConfig M :=
  ⟨c.issued + g, c.consumed, c.buffer ++ [g]⟩

/-- Consume = FIFO dequeue (the `Injection.dequeue` shape) + ledger. -/
def QueueConfig.consume (c : QueueConfig M) : QueueConfig M :=
  match c.buffer with
  | [] => c
  | g :: rest => ⟨c.issued, c.consumed + g, rest⟩

/-- Reachability at capacity `cap`: issue only below capacity, consume only
nonempty. -/
inductive QueueReachable (cap : ℕ) : QueueConfig M → Prop
  | init : QueueReachable cap QueueConfig.init
  | issue {c : QueueConfig M} (g : M) (hlen : c.buffer.length < cap)
      (h : QueueReachable cap c) : QueueReachable cap (c.issue g)
  | consume {c : QueueConfig M} (hne : c.buffer ≠ [])
      (h : QueueReachable cap c) : QueueReachable cap c.consume

/-- Balance for queue registers: everything issued is consumed or in the buffer. -/
def QueueBalanced (c : QueueConfig M) : Prop :=
  c.issued = c.consumed + c.buffer.sum

/-- **The SU6b law at every capacity**: every reachable queue register is balanced. -/
theorem queueReachable_balanced {cap : ℕ} {c : QueueConfig M}
    (h : QueueReachable cap c) : QueueBalanced c := by
  induction h with
  | init => simp [QueueBalanced, QueueConfig.init]
  | @issue c g hlen h ih =>
    show c.issued + g = c.consumed + (c.buffer ++ [g]).sum
    rw [List.sum_append, List.sum_cons, List.sum_nil, add_zero, ih, add_assoc]
  | @consume c hne h ih =>
    rcases hb : c.buffer with _ | ⟨g, rest⟩
    · exact absurd hb hne
    · have hc : c.consume = ⟨c.issued, c.consumed + g, rest⟩ := by
        unfold QueueConfig.consume
        rw [hb]
      rw [QueueBalanced, hc]
      rw [QueueBalanced, hb] at ih
      simp only [List.sum_cons] at ih
      show c.issued = (c.consumed + g) + rest.sum
      rw [ih, add_assoc]

/-- The capacity-one projection onto the `CurrencyConfig` register. -/
def QueueConfig.toCurrency (c : QueueConfig M) : CurrencyConfig M :=
  ⟨c.issued, c.consumed, c.buffer.head?⟩

/-- Capacity-one buffers never exceed one entry. -/
theorem queueReachable_one_length {c : QueueConfig M}
    (h : QueueReachable 1 c) : c.buffer.length ≤ 1 := by
  induction h with
  | init => simp [QueueConfig.init]
  | @issue c g hlen h ih =>
    simp only [QueueConfig.issue, List.length_append, List.length_cons, List.length_nil]
    omega
  | @consume c hne h ih =>
    rcases hb : c.buffer with _ | ⟨g, rest⟩
    · exact absurd hb hne
    · have hc : c.consume = ⟨c.issued, c.consumed + g, rest⟩ := by
        unfold QueueConfig.consume
        rw [hb]
      rw [hc]
      rw [hb] at ih
      simp only [List.length_cons] at ih
      show rest.length ≤ 1
      omega

/-- **THE INSTANCE THEOREM (SU7.0 style)**: a capacity-one queue register IS the
`CurrencyConfig` register — the projection carries reachable states to reachable
states, issues to issues, consumes to consumes. The queue open is discharged as
reuse: the machine's proven register is the capacity-one special case. -/
theorem queueReachable_one_toCurrency {c : QueueConfig M}
    (h : QueueReachable 1 c) :
    CurrencyReachable (Set.univ : Set M) c.toCurrency := by
  induction h with
  | init => exact CurrencyReachable.init
  | @issue c g hlen h ih =>
    have hbe : c.buffer = [] := List.length_eq_zero_iff.mp (by omega)
    have hstep : (c.issue g).toCurrency = c.toCurrency.issue g := by
      simp [QueueConfig.issue, QueueConfig.toCurrency, CurrencyConfig.issue, hbe]
    rw [hstep]
    exact CurrencyReachable.issue _ (Set.mem_univ _)
      (by simp [QueueConfig.toCurrency, hbe]) ih
  | @consume c hne h ih =>
    rcases hb : c.buffer with _ | ⟨g, rest⟩
    · exact absurd hb hne
    · have hre : rest = [] := by
        have := queueReachable_one_length h
        rw [hb] at this
        simpa using List.length_eq_zero_iff.mp (by simpa using this)
      have hstep : c.consume.toCurrency = c.toCurrency.consume := by
        simp [QueueConfig.consume, QueueConfig.toCurrency, CurrencyConfig.consume,
          hb, hre]
      rw [hstep]
      exact CurrencyReachable.consume (g := g) (by simp [QueueConfig.toCurrency, hb]) ih

/-- Balance transfers across the capacity-one projection. -/
theorem queueBalanced_one_iff {c : QueueConfig M} (hlen : c.buffer.length ≤ 1) :
    QueueBalanced c ↔ CurrencyBalanced c.toCurrency := by
  rcases hb : c.buffer with _ | ⟨g, rest⟩
  · simp [QueueBalanced, CurrencyBalanced, QueueConfig.toCurrency, hb]
  · have hre : rest = [] := by
      rw [hb] at hlen
      simpa using List.length_eq_zero_iff.mp (by simpa using hlen)
    simp [QueueBalanced, CurrencyBalanced, QueueConfig.toCurrency, hb, hre]

/-! ## 5. The literal weld to the Phase-8 artifact -/

/-- Project a Phase-8 `InjectionQueue` onto its payload buffer. -/
def payloads (q : Composition.Injection.InjectionQueue) : List ℕ :=
  q.entries.map (·.payload)

theorem payloads_enqueue (q : Composition.Injection.InjectionQueue)
    (e : Composition.Injection.InjectionQueueEntry) :
    payloads (Composition.Injection.enqueue q e) = payloads q ++ [e.payload] := by
  simp [payloads, Composition.Injection.enqueue]

theorem payloads_dequeue (q : Composition.Injection.InjectionQueue)
    {e : Composition.Injection.InjectionQueueEntry}
    {q' : Composition.Injection.InjectionQueue}
    (h : Composition.Injection.dequeue q = some (e, q')) :
    payloads q = e.payload :: payloads q' := by
  unfold Composition.Injection.dequeue at h
  rcases hq : q.entries with _ | ⟨x, xs⟩
  · rw [hq] at h; exact absurd h (by simp)
  · rw [hq] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [payloads, hq]

/-! ## Axiom audit -/

#print axioms timeline_graded
#print axioms ofRouting_fanoutLawful
#print axioms queueReachable_balanced
#print axioms queueReachable_one_toCurrency
#print axioms queueBalanced_one_iff
#print axioms payloads_dequeue

end FdrsFormal.Modes.SyntheticPlace
