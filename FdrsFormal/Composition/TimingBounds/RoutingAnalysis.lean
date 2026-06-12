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

# Routing Depth and Composite Timing Analysis

Routing depth bounds, local timeline costs, and the main composite timing theorem.

## Mathematical Content (fdrs.md lines 6151-6231)

**Definition 121**: Routing depth
**Proposition 108**: Finite routing depth
**Definition 122**: Local timeline operation cost
**Definition 123**: Routing operation overhead
**Theorem 53**: Composite timing bound (Main Result)
**Corollary 29**: Static routing compile-time bound

## References

- fdrs.md, Phase 8, Sections 8.4-8.5 (lines 6151-6231)
-/

import FdrsFormal.Composition.TimingBounds.Definition
import FdrsFormal.Composition.RoutingGraph.Graph

namespace FdrsFormal.Composition.TimingBounds

open FdrsFormal.Composition.Verification

/-! ## Definition 121: Routing depth -/

/--
**fdrs.md**: Definition 121 (Routing depth) [§8.4.4 · Phase 8] (lines 6151-6158)

The routing depth of junction point `v = (T, s)` is the length of the longest
path from any source to `v` in `G_ρ`; source points (no incoming edges) have
depth `0`.

Computed by `|V|` longest-path relaxation passes over `G_ρ`
(`RoutingGraph.depthIter`), which converge to the longest-path length on a DAG.
-/
def routingDepth (spec : RoutingSpecification) (v : RoutingGraph.Vertex) : ℕ :=
  RoutingGraph.depthIter spec (RoutingGraph.vertices spec).length v

/-! ## Proposition 108: Finite routing depth -/

/--
**fdrs.md**: Proposition 108 (Finite routing depth) [§8.4.5 · Phase 8] (lines 6161-6167)

On the finite routing graph `G_ρ` the routing depth is bounded:
`max_{(T,s) ∈ V} depth_ρ(T, s) < ∞`.

**Proof**: each of the `|V|` relaxation passes adds at most one to the depth
estimate (`RoutingGraph.depthIter_le`), so `|V|` is a uniform bound.
-/
theorem finiteRoutingDepth (spec : RoutingSpecification) :
    ∃ D : ℕ, ∀ v, routingDepth spec v ≤ D :=
  ⟨(RoutingGraph.vertices spec).length, fun v => RoutingGraph.depthIter_le spec _ v⟩

/-! ## Definition 122: Local timeline operation cost -/

/--
**fdrs.md**: Definition 122 (Local timeline operation cost) [§8.5.1 · Phase 8] (lines 6173-6179)

For a timeline processed to cylinder depth `L`:
  `Cost_T(L) := Σ_{i=0}^{L-1} f(ω_T(s_{<i}))`.

Parametric in the cost model `f : ℕ → ℕ` (e.g. `f b = ⌈log b⌉` for digit ops,
`f b = b` for memory access) and the timeline's radix sequence
`radix i := ω_T(s_{<i})`, the radix used at position `i`.
-/
def localTimelineCost (f : ℕ → ℕ) (radix : ℕ → ℕ) (L : ℕ) : ℕ :=
  ∑ i ∈ Finset.range L, f (radix i)

/-! ## Definition 123: Routing operation overhead -/

/--
**fdrs.md**: Definition 123 (Routing operation overhead) [§8.5.2 · Phase 8] (lines 6183-6192)

For the routing step out of junction `u = (A, s_A)`:
  `Cost_ρ(A, s_A) := |ρ(A, s_A, _, _)| · Cost_lookup + Σ_i Cost_{φ_i}`,
where `|ρ(...)|` is the fanout (`RoutingGraph.fanout`), `costLookup` is the
routing-table access cost, and `costφ t` is the payload-transform cost for
target `t`. The sum ranges over the routing actions out of `u`.
-/
def routingOverheadCost (spec : RoutingSpecification) (costLookup : ℕ)
    (costφ : RoutingGraph.Vertex → ℕ) (u : RoutingGraph.Vertex) : ℕ :=
  RoutingGraph.fanout spec u * costLookup + ((RoutingGraph.successors spec u).map costφ).sum

/-! ## Theorem 53: Composite timing bound -/

/-- Membership gives a lower bound on a list's running `max`. -/
private theorem le_foldr_max_of_mem {α : Type*} (g : α → ℕ) {a : α} :
    ∀ {l : List α}, a ∈ l → g a ≤ (l.map g).foldr max 0 := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons b l ih =>
      intro h
      simp only [List.map_cons, List.foldr_cons]
      rcases List.mem_cons.1 h with rfl | h'
      · exact le_max_left _ _
      · exact le_trans (ih h') (le_max_right _ _)

/-- **Layer k** (`fdrs.md` Theorem 53): the junctions at routing depth exactly `k`. -/
def layer (spec : RoutingSpecification) (k : ℕ) : List RoutingGraph.Vertex :=
  (RoutingGraph.vertices spec).filter (fun v => decide (routingDepth spec v = k))

/-- Worst-case per-junction cost within layer `k` (`0` for an empty layer). -/
def layerMax (spec : RoutingSpecification) (cost : RoutingGraph.Vertex → ℕ) (k : ℕ) : ℕ :=
  ((layer spec k).map cost).foldr max 0

/--
The composite latency bound — Theorem 53's right-hand side:
`Σ_{k=0}^{D} max_{(T,s) ∈ layer_k} cost(T, s)`, with
`cost(T, s) = Cost_T(|s|) + Cost_ρ(T, s)`.
-/
def compositeLatencyBound (spec : RoutingSpecification) (cost : RoutingGraph.Vertex → ℕ)
    (D : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (D + 1), layerMax spec cost k

/-- A junction's cost is at most the worst case of its own layer. -/
private theorem cost_le_layerMax (spec : RoutingSpecification) (cost : RoutingGraph.Vertex → ℕ)
    {v : RoutingGraph.Vertex} (hv : v ∈ RoutingGraph.vertices spec) :
    cost v ≤ layerMax spec cost (routingDepth spec v) := by
  have hmem : v ∈ layer spec (routingDepth spec v) := by
    simp only [layer, List.mem_filter]
    exact ⟨hv, by simp⟩
  exact le_foldr_max_of_mem cost hmem

/-- Summing `g` over a `Nodup` list contained in a finite set `S` is at most `∑_{S} g`. -/
private theorem sum_map_le_sum (g : ℕ → ℕ) :
    ∀ (dl : List ℕ) (S : Finset ℕ), dl.Nodup → (∀ x ∈ dl, x ∈ S) →
      (dl.map g).sum ≤ ∑ k ∈ S, g k := by
  intro dl
  induction dl with
  | nil => intro S _ _; simp only [List.map_nil, List.sum_nil]; exact Nat.zero_le _
  | cons a t ih =>
      intro S hnd hsub
      simp only [List.map_cons, List.sum_cons]
      have ha : a ∈ S := hsub a (List.mem_cons.2 (.inl rfl))
      have hcons := List.nodup_cons.1 hnd
      have hbound := ih (S.erase a) hcons.2 (by
        intro x hx
        rw [Finset.mem_erase]
        exact ⟨fun hxa => hcons.1 (hxa ▸ hx), hsub x (List.mem_cons.2 (.inr hx))⟩)
      rw [← Finset.add_sum_erase S g ha]
      exact Nat.add_le_add_left hbound (g a)

/-- Core bound: when the depths along `p` are distinct and `≤ D`, the cost summed
along `p` is at most the layer-max sum up to `D`. -/
private theorem sum_cost_le_of_nodup (spec : RoutingSpecification)
    (cost : RoutingGraph.Vertex → ℕ) (p : List RoutingGraph.Vertex) (D : ℕ)
    (hv : ∀ v ∈ p, v ∈ RoutingGraph.vertices spec)
    (hD : ∀ v ∈ p, routingDepth spec v ≤ D)
    (hnodup : (p.map (routingDepth spec)).Nodup) :
    (p.map cost).sum ≤ compositeLatencyBound spec cost D :=
  calc (p.map cost).sum
      ≤ (p.map fun v => layerMax spec cost (routingDepth spec v)).sum :=
        List.sum_le_sum (fun v hvp => cost_le_layerMax spec cost (hv v hvp))
    _ = ((p.map (routingDepth spec)).map (layerMax spec cost)).sum := by
        rw [List.map_map]; rfl
    _ ≤ ∑ k ∈ Finset.range (D + 1), layerMax spec cost k :=
        sum_map_le_sum (layerMax spec cost) _ _ hnodup (by
          intro x hx
          rw [List.mem_map] at hx
          obtain ⟨v, hvp, rfl⟩ := hx
          rw [Finset.mem_range]
          exact Nat.lt_succ_of_le (hD v hvp))
    _ = compositeLatencyBound spec cost D := rfl

/--
**fdrs.md**: Theorem 53 (Composite timing bound — Main Result) [§8.5.3 · Phase 8] (lines 6196-6213)

For an event whose propagation follows a route `p` through `G_ρ` whose routing
depths strictly increase (`hlayered` — the layered propagation through depths
`0, 1, …, D` of an acyclic routing graph, Definition 120), with every junction
at depth `≤ D`, the total latency along `p` satisfies

  `Σ_{(T,s) ∈ p} cost(T, s) ≤ Σ_{k=0}^{D} max_{(T,s) ∈ layer_k} cost(T, s)`.

**Proof**: strictly increasing depths are distinct, so each junction sits in its
own layer; its cost is bounded by that layer's maximum, and distinct layers
contribute disjoint terms of the right-hand sum (sequential composition across
layers).
-/
theorem compositeTimingBound (spec : RoutingSpecification) (cost : RoutingGraph.Vertex → ℕ)
    (p : List RoutingGraph.Vertex) (D : ℕ)
    (hv : ∀ v ∈ p, v ∈ RoutingGraph.vertices spec)
    (hD : ∀ v ∈ p, routingDepth spec v ≤ D)
    (hlayered : (p.map (routingDepth spec)).Pairwise (· < ·)) :
    (p.map cost).sum ≤ compositeLatencyBound spec cost D := by
  apply sum_cost_le_of_nodup spec cost p D hv hD
  -- Strictly increasing depths along the route are distinct.
  exact hlayered.imp (fun h => ne_of_lt h)

/-! ## Corollary 29: Static routing compile-time bound -/

/-- The maximum routing depth over all junctions (a computable quantity). -/
def maxRoutingDepth (spec : RoutingSpecification) : ℕ :=
  ((RoutingGraph.vertices spec).map (routingDepth spec)).foldr max 0

/--
**fdrs.md**: Corollary 29 (Static routing compile-time bound) [§8.5.4 · Phase 8] (lines 6217-6231)

For a static routing specification (a finite rule list), a single latency bound
`B` — **computable from the specification**, namely
`compositeLatencyBound spec cost (maxRoutingDepth spec)` — upper-bounds the
latency of every layered route (one whose routing depths strictly increase).

**Proof**: every junction has routing depth `≤ maxRoutingDepth spec`, so
Theorem 53 applies with `D = maxRoutingDepth spec`.
-/
theorem staticRoutingCompileTimeBound (spec : RoutingSpecification)
    (cost : RoutingGraph.Vertex → ℕ) :
    ∃ B : ℕ, ∀ (p : List RoutingGraph.Vertex),
      (∀ v ∈ p, v ∈ RoutingGraph.vertices spec) →
      (p.map (routingDepth spec)).Pairwise (· < ·) →
      (p.map cost).sum ≤ B := by
  refine ⟨compositeLatencyBound spec cost (maxRoutingDepth spec), fun p hv hlayered => ?_⟩
  refine compositeTimingBound spec cost p (maxRoutingDepth spec) hv ?_ hlayered
  intro v hvp
  exact le_foldr_max_of_mem (routingDepth spec) (hv v hvp)

end FdrsFormal.Composition.TimingBounds
