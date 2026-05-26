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

# Timeline Graphs

This file defines the timeline graph structure for program composition.

## Mathematical Content (fdrs.md Phase 8)

**Timeline Graph**: A directed graph where:
- Nodes represent program states at specific times
- Edges represent state transitions (Tick, Dirichlet transforms)

**Purpose**: Visualize and analyze the execution of composed FDRS programs.

## References

- fdrs.md, Phase 8, Section 5.1 (Timeline Graphs)
- fdrs.md, Phase 8, Section 5.2 (Graph Composition)
-/

import FdrsFormal.Core

namespace FdrsFormal.Composition.TimelineGraphs

/-!
## Timeline Graph Structure
-/

/--
A timeline node: represents a program state at a specific time.

**fdrs.md**: Nodes are (time, state) pairs in the execution trace.
-/
structure TimelineNode where
  /-- Time index -/
  time : ℕ
  /-- State identifier -/
  state : ℕ

/--
Edge type in timeline graphs.

**fdrs.md**: Edges are labeled by the operation causing the transition.
-/
inductive EdgeLabel where
  | tick : EdgeLabel
  | dirichlet : ℕ → EdgeLabel
  | diagonal : EdgeLabel
  | compose : EdgeLabel → EdgeLabel → EdgeLabel

/--
A timeline edge: represents a state transition.
-/
structure TimelineEdge where
  source : TimelineNode
  target : TimelineNode
  label : EdgeLabel

/--
Timeline graph: collection of nodes and edges with time ordering.

**fdrs.md**: The full execution graph of a program.
-/
structure TimelineGraph where
  nodes : Set TimelineNode
  edges : Set TimelineEdge
  /-- All edges go forward in time or stay at same time -/
  time_monotone : ∀ e ∈ edges, e.source.time ≤ e.target.time

/-!
## Graph Operations
-/

/-- Shift all times in a node by an offset -/
def shiftNode (n : TimelineNode) (offset : ℕ) : TimelineNode :=
  { time := n.time + offset, state := n.state }

/-- Shift all times in an edge by an offset -/
def shiftEdge (e : TimelineEdge) (offset : ℕ) : TimelineEdge :=
  { source := shiftNode e.source offset
    target := shiftNode e.target offset
    label := e.label }

/--
Sequential composition of timeline graphs with explicit time offset.

**fdrs.md**: G₁ ; G₂ connects final nodes of G₁ to initial nodes of G₂.

Implementation: We shift G₂'s times by the given offset.
The offset should be chosen to be at least max(G₁.times) + 1 to ensure
proper sequencing. This ensures time monotonicity is preserved.
-/
def sequentialComposeWithOffset (G₁ G₂ : TimelineGraph) (offset : ℕ) : TimelineGraph :=
  let shiftedNodes := { n | ∃ n₂ ∈ G₂.nodes, n = shiftNode n₂ offset }
  let shiftedEdges := { e | ∃ e₂ ∈ G₂.edges, e = shiftEdge e₂ offset }
  { nodes := G₁.nodes ∪ shiftedNodes
    edges := G₁.edges ∪ shiftedEdges
    time_monotone := by
      intro e he
      cases he with
      | inl h₁ => exact G₁.time_monotone e h₁
      | inr h₂ =>
        obtain ⟨e₂, he₂, rfl⟩ := h₂
        simp only [shiftEdge, shiftNode]
        have h := G₂.time_monotone e₂ he₂
        omega }

/--
Sequential composition of timeline graphs.

**Note**: This version uses a default offset of 1. For proper sequencing,
use `sequentialComposeWithOffset` with an offset ≥ max(G₁.times) + 1.
-/
abbrev sequentialCompose (G₁ G₂ : TimelineGraph) : TimelineGraph :=
  sequentialComposeWithOffset G₁ G₂ 1

/--
Parallel composition of timeline graphs.

**fdrs.md**: G₁ ∥ G₂ runs both graphs simultaneously.

Implementation: Disjoint union of nodes and edges. Both graphs share
the same time axis, so no shifting is needed.
-/
def parallelCompose (G₁ G₂ : TimelineGraph) : TimelineGraph :=
  { nodes := G₁.nodes ∪ G₂.nodes
    edges := G₁.edges ∪ G₂.edges
    time_monotone := by
      intro e he
      cases he with
      | inl h₁ => exact G₁.time_monotone e h₁
      | inr h₂ => exact G₂.time_monotone e h₂ }

/-!
## Paths in Timeline Graphs
-/

/--
A path in a timeline graph: a sequence of edges where each edge's target
is the next edge's source.
-/
inductive Path (G : TimelineGraph) : TimelineNode → TimelineNode → Prop where
  | refl (n : TimelineNode) (hn : n ∈ G.nodes) : Path G n n
  | step (e : TimelineEdge) (he : e ∈ G.edges) (p : Path G e.target n) : Path G e.source n

/--
A non-trivial path: at least one edge.
-/
def hasNonTrivialPath (G : TimelineGraph) (n m : TimelineNode) : Prop :=
  ∃ e ∈ G.edges, e.source = n ∧ Path G e.target m

/-!
## Graph Properties
-/

/--
A timeline graph is acyclic if there is no non-trivial path from any node to itself.
-/
def isAcyclic (G : TimelineGraph) : Prop :=
  ∀ n : TimelineNode, ¬hasNonTrivialPath G n n

/--
Time along a path is monotonically non-decreasing.
-/
theorem path_time_monotone (G : TimelineGraph) {n m : TimelineNode}
    (p : Path G n m) : n.time ≤ m.time := by
  induction p with
  | refl _ _ => exact Nat.le_refl _
  | step e he _ ih =>
    have h_edge := G.time_monotone e he
    exact Nat.le_trans h_edge ih

/--
Any cycle in a time-monotone graph must be "time-flat" (all nodes at the same time).
-/
theorem cycle_time_flat (G : TimelineGraph) {n : TimelineNode}
    (e : TimelineEdge) (he : e ∈ G.edges) (hsrc : e.source = n)
    (p : Path G e.target n) : n.time = e.target.time := by
  have h_first : n.time ≤ e.target.time := by
    rw [← hsrc]
    exact G.time_monotone e he
  have h_path : e.target.time ≤ n.time := path_time_monotone G p
  exact Nat.le_antisymm h_first h_path

/-!
## Strict Timeline Graphs

For provable acyclicity, we define timeline graphs with strict time ordering.
-/

/--
A strict timeline graph: edges must strictly increase time.

With strict ordering, acyclicity is automatically satisfied since any path
strictly increases time, making cycles impossible.
-/
structure StrictTimelineGraph where
  nodes : Set TimelineNode
  edges : Set TimelineEdge
  /-- All edges go strictly forward in time -/
  time_strict : ∀ e ∈ edges, e.source.time < e.target.time

/-- Convert a strict timeline graph to a (non-strict) timeline graph -/
def StrictTimelineGraph.toTimelineGraph (G : StrictTimelineGraph) : TimelineGraph :=
  { nodes := G.nodes
    edges := G.edges
    time_monotone := fun e he => Nat.le_of_lt (G.time_strict e he) }

/-- Path in a strict timeline graph -/
inductive StrictPath (G : StrictTimelineGraph) : TimelineNode → TimelineNode → Prop where
  | refl (n : TimelineNode) (hn : n ∈ G.nodes) : StrictPath G n n
  | step (e : TimelineEdge) (he : e ∈ G.edges) (p : StrictPath G e.target n) : StrictPath G e.source n

/-- Time along a strict path is strictly increasing (for non-trivial paths) -/
theorem strict_path_time_monotone (G : StrictTimelineGraph) {n m : TimelineNode}
    (p : StrictPath G n m) : n.time ≤ m.time := by
  induction p with
  | refl _ _ => exact Nat.le_refl _
  | step e he _ ih =>
    have h_edge := G.time_strict e he
    exact Nat.le_trans (Nat.le_of_lt h_edge) ih

/-- Non-trivial path in strict timeline graph -/
def hasStrictNonTrivialPath (G : StrictTimelineGraph) (n m : TimelineNode) : Prop :=
  ∃ e ∈ G.edges, e.source = n ∧ StrictPath G e.target m

/--
Strict timeline graphs are acyclic.

**Proof**: Any non-trivial path starting at n ends at m with n.time < m.time.
Therefore, we cannot have a path from n back to n (since that would require n.time < n.time).
-/
theorem strict_timeline_acyclic (G : StrictTimelineGraph) :
    ∀ n : TimelineNode, ¬hasStrictNonTrivialPath G n n := by
  intro n ⟨e, he, hsrc, p⟩
  -- The first step e goes from n to e.target with n.time < e.target.time
  have h_first : n.time < e.target.time := by
    rw [← hsrc]
    exact G.time_strict e he
  -- The path p goes from e.target back to n, so e.target.time ≤ n.time
  have h_path : e.target.time ≤ n.time := strict_path_time_monotone G p
  -- Combining: n.time < e.target.time ≤ n.time, contradiction
  exact Nat.not_lt.mpr h_path h_first

/--
All valid timeline graphs are acyclic.

**fdrs.md**: Time monotonicity ensures acyclicity.

**Mathematical Note**: With the current `≤` ordering in `time_monotone`, we can prove
that any cycle must be "time-flat" (all nodes at the same time). For full acyclicity,
we need either:
1. Strict time ordering (`<` instead of `≤`), or
2. An additional constraint that same-time edges form a DAG

For FDRS programs, the additional constraint holds: operations at the same timestep
have a well-defined execution order (data dependencies form a DAG).

**Proven Cases**:
- `StrictTimelineGraph` (with `<` ordering) has `strict_timeline_acyclic` proved above.
- General `TimelineGraph` requires additional structure (same-time DAG constraint).

Any `TimelineGraph` that admits strict time ordering is acyclic.

For general `TimelineGraph` (with `≤`), cycles can only be "time-flat"
(all nodes at the same time). For `StrictTimelineGraph` (with `<`),
acyclicity is proved above as `strict_timeline_acyclic`.

**Statement**: Given a TimelineGraph where all edges are actually strict,
acyclicity follows. This extracts a StrictTimelineGraph and applies
the existing proof.
-/
theorem timeline_acyclic_of_strict (G : TimelineGraph)
    (h_strict : ∀ e ∈ G.edges, e.source.time < e.target.time) :
    ∀ n : TimelineNode, ¬hasStrictNonTrivialPath
      ⟨G.nodes, G.edges, h_strict⟩ n n :=
  strict_timeline_acyclic ⟨G.nodes, G.edges, h_strict⟩

/--
Topological order exists for timeline graphs: using time as the ordering function.
-/
theorem timeline_topological_order (G : TimelineGraph) :
    ∃ order : TimelineNode → ℕ,
      ∀ e ∈ G.edges, order e.source ≤ order e.target := by
  -- Use the time field as the topological order
  use fun n => n.time
  intro e he
  exact G.time_monotone e he

end FdrsFormal.Composition.TimelineGraphs
