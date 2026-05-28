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

# The Routing Graph `G_ρ`

The routing dependency graph induced by a `RoutingSpecification`, together with
the finite-DAG longest-path and reachability machinery used throughout Phase 8
(timing bounds, compile-time verification, synchronization).

## Mathematical Content (fdrs.md lines 6110-6167)

**Definition 119** (Routing dependency graph): vertices are junction points
`(T, s)`; an edge `(A, s_A) → (B, s_B)` exists when some routing rule sends A's
overflow at `s_A` to B at `s_B`.

**Definition 120** (Acyclic routing): `G_ρ` is a DAG.

**Definition 121** (Routing depth): the longest source→`(T, s)` path length.

**Proposition 108** (Finite routing depth): on a finite graph the depth is bounded.

Vertices are modelled as `ℕ × ℕ = (timeline id, cylinder code)`, matching the
`RoutingRule` encoding (and the `ℕ × ℕ` vertex type already used by the
reachability decision API in `Verification/CompileTime.lean`). Because a
specification carries a *finite* `List` of rules, every quantity here is
computable and every graph property is decidable.

## References

- fdrs.md, Phase 8, §8.4 (lines 6110-6167)
-/

import FdrsFormal.Composition.Verification.Specification
import Mathlib.Data.List.Dedup

namespace FdrsFormal.Composition.RoutingGraph

open FdrsFormal.Composition.Verification

/-! ## Vertices and edges -/

/-- A vertex of `G_ρ`: a junction point `(timeline, cylinder code)`. -/
abbrev Vertex := ℕ × ℕ

/-- Source endpoint `(A, s_A)` of a routing rule. -/
def ruleSrc (r : RoutingRule) : Vertex := (r.sourceTimeline, r.sourceCylinder)

/-- Target endpoint `(B, s_B)` of a routing rule. -/
def ruleTgt (r : RoutingRule) : Vertex := (r.targetTimeline, r.targetCylinder)

/--
**fdrs.md Definition 119**: the vertex set `V` of `G_ρ`.

All junction points mentioned by the specification (as a source or a target),
deduplicated.
-/
def vertices (spec : RoutingSpecification) : List Vertex :=
  ((spec.rules.map ruleSrc) ++ (spec.rules.map ruleTgt)).dedup

/--
Out-neighbours of `u`: the target of every rule whose source is `u`.

One entry per matching rule, so `(successors spec u).length` is the routing
action multiplicity `|ρ(A, s_A, _, _)|` (Definition 123 / 128).
-/
def successors (spec : RoutingSpecification) (u : Vertex) : List Vertex :=
  (spec.rules.filter (fun r => decide (ruleSrc r = u))).map ruleTgt

/--
In-neighbours of `v`: the source of every rule whose target is `v`.

This is the multiset of incoming edges `{(A, s_A) : ((A, s_A), v) ∈ E}` used by
Definition 121 (routing depth) and Definition 129 (synchronization point).
-/
def predecessors (spec : RoutingSpecification) (v : Vertex) : List Vertex :=
  (spec.rules.filter (fun r => decide (ruleTgt r = v))).map ruleSrc

/--
**fdrs.md Definition 123/128**: fanout `|ρ(A, s_A, _, _)|`, the number of
routing actions out of `u`.
-/
def fanout (spec : RoutingSpecification) (u : Vertex) : ℕ := (successors spec u).length

/-! ## Routing depth (Definition 121) via DAG longest path -/

/-- `(l.map f).foldr max 0` is bounded by `b` when every `f x` is. -/
private theorem foldr_max_le {α : Type*} (f : α → ℕ) (b : ℕ) :
    ∀ (l : List α), (∀ x ∈ l, f x ≤ b) → (l.map f).foldr max 0 ≤ b := by
  intro l
  induction l with
  | nil => intro _; exact Nat.zero_le b
  | cons x xs ih =>
      intro h
      simp only [List.map_cons, List.foldr_cons]
      exact max_le (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

/--
One longest-path relaxation pass.

A source (no predecessors) has depth `0`; otherwise depth is `1 +` the maximum
predecessor depth under the current estimate `d`.
-/
def depthStep (spec : RoutingSpecification) (d : Vertex → ℕ) (v : Vertex) : ℕ :=
  if (predecessors spec v).isEmpty then 0
  else 1 + ((predecessors spec v).map d).foldr max 0

/--
Iterate `depthStep` `n` times starting from the all-zero estimate.

On a finite DAG, `n = |V|` passes converge to the true longest-path length
(Definition 121); on any graph the result is bounded by `n` (`depthIter_le`).
-/
def depthIter (spec : RoutingSpecification) : ℕ → (Vertex → ℕ)
  | 0     => fun _ => 0
  | n + 1 => fun v => depthStep spec (depthIter spec n) v

/-- After `b`-bounded predecessor estimates, one relaxation pass stays `≤ b + 1`. -/
private theorem depthStep_le (spec : RoutingSpecification) (d : Vertex → ℕ) (v : Vertex)
    (b : ℕ) (h : ∀ u ∈ predecessors spec v, d u ≤ b) : depthStep spec d v ≤ b + 1 := by
  unfold depthStep
  split
  · exact Nat.zero_le _
  · have hb : ((predecessors spec v).map d).foldr max 0 ≤ b := foldr_max_le d b _ h
    omega

/-- Each relaxation pass adds at most one, so `n` passes stay `≤ n`. -/
theorem depthIter_le (spec : RoutingSpecification) :
    ∀ (n : ℕ) (v : Vertex), depthIter spec n v ≤ n := by
  intro n
  induction n with
  | zero => intro v; exact Nat.zero_le _
  | succ n ih =>
      intro v
      have hstep : depthIter spec (n + 1) v = depthStep spec (depthIter spec n) v := rfl
      rw [hstep]
      exact depthStep_le spec (depthIter spec n) v n (fun u _ => ih u)

/-! ## Reachability and acyclicity (Definition 120) -/

/-- One BFS expansion: keep the current frontier and add all its successors. -/
def expand (spec : RoutingSpecification) (S : List Vertex) : List Vertex :=
  (S ++ S.flatMap (successors spec)).dedup

/-- Iterate `expand` `n` times. -/
def reachIter (spec : RoutingSpecification) : ℕ → List Vertex → List Vertex
  | 0,     S => S
  | n + 1, S => reachIter spec n (expand spec S)

/--
Vertices reachable from `u` in at least one routing step.

Starts from `u`'s successors (one edge taken) and saturates within `|V|`
expansions, which suffices on a graph with `|V|` vertices.
-/
def reachableFrom (spec : RoutingSpecification) (u : Vertex) : List Vertex :=
  reachIter spec (vertices spec).length (successors spec u)

/-- `u` reaches `v` along at least one routing edge. -/
def Reaches (spec : RoutingSpecification) (u v : Vertex) : Prop :=
  v ∈ reachableFrom spec u

instance (spec : RoutingSpecification) (u v : Vertex) : Decidable (Reaches spec u v) :=
  inferInstanceAs (Decidable (v ∈ reachableFrom spec u))

/--
**fdrs.md Definition 120**: `G_ρ` is acyclic when no junction can reach itself.
-/
def Acyclic (spec : RoutingSpecification) : Prop :=
  ∀ v ∈ vertices spec, ¬ Reaches spec v v

instance (spec : RoutingSpecification) : Decidable (Acyclic spec) :=
  inferInstanceAs (Decidable (∀ v ∈ vertices spec, ¬ Reaches spec v v))

/--
**fdrs.md Theorem 52**: deadlock-freedom of the system is acyclicity of `G_ρ`
— a set of mutually waiting timelines is exactly a cycle in the routing graph.
-/
def DeadlockFree (spec : RoutingSpecification) : Prop := Acyclic spec

instance (spec : RoutingSpecification) : Decidable (DeadlockFree spec) :=
  inferInstanceAs (Decidable (Acyclic spec))

/-! ## Bounded fanout / depth (Proposition 109 items 2, 3) -/

/-- Fanout is bounded by `B` across all junctions. -/
def BoundedFanout (spec : RoutingSpecification) (B : ℕ) : Prop :=
  ∀ u ∈ vertices spec, fanout spec u ≤ B

instance (spec : RoutingSpecification) (B : ℕ) : Decidable (BoundedFanout spec B) :=
  inferInstanceAs (Decidable (∀ u ∈ vertices spec, fanout spec u ≤ B))

/-- Routing depth is bounded by `D` across all junctions. -/
def BoundedDepth (spec : RoutingSpecification) (D : ℕ) : Prop :=
  ∀ v ∈ vertices spec, depthIter spec (vertices spec).length v ≤ D

instance (spec : RoutingSpecification) (D : ℕ) : Decidable (BoundedDepth spec D) :=
  inferInstanceAs
    (Decidable (∀ v ∈ vertices spec, depthIter spec (vertices spec).length v ≤ D))

end FdrsFormal.Composition.RoutingGraph
