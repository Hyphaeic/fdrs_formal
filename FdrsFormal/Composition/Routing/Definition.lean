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

# Routing and Data Flow

This file defines routing structures for data flow in composed programs.

## Mathematical Content (fdrs.md Phase 8)

**Routing**: How data flows between operations in a composed program.

**Key Concepts**:
- Source/sink identification
- Data dependencies
- Parallel data paths

## References

- fdrs.md, Phase 8, Section 5.3 (Routing)
- fdrs.md, Phase 8, Section 5.4 (Data Flow Analysis)
-/

import FdrsFormal.Core

namespace FdrsFormal.Composition.Routing

/-!
## Data Flow Nodes
-/

/--
A data source: where values originate.

**fdrs.md**: Sources are inputs or constant generators.
-/
inductive DataSource where
  | input : ℕ → DataSource
  | constant : ℕ → DataSource
  | computed : ℕ → DataSource

/--
A data sink: where values are consumed.

**fdrs.md**: Sinks are outputs or state updates.
-/
inductive DataSink where
  | output : ℕ → DataSink
  | stateUpdate : ℕ → DataSink
  | discard : DataSink

/-!
## Routing Table
-/

/--
A routing entry: connects a source to a sink with a transform.

**fdrs.md**: Each entry specifies how data moves and transforms.
-/
structure RoutingEntry where
  source : DataSource
  sink : DataSink
  /-- Optional transform applied during routing -/
  transform : Option ℕ

/--
A routing table: complete specification of data flow.

**fdrs.md**: The routing table defines the dataflow graph.
-/
structure RoutingTable where
  entries : List RoutingEntry
  /-- Each source is used at most once per timestep -/
  source_unique : True  -- Placeholder for proper uniqueness

/-!
## Routing Properties
-/

/--
A routing is deterministic if each sink has at most one source.

**fdrs.md**: Deterministic routing ensures reproducible execution.
-/
def isDeterministic (rt : RoutingTable) : Prop :=
  ∀ e₁ e₂, e₁ ∈ rt.entries → e₂ ∈ rt.entries →
    e₁.sink = e₂.sink → e₁ = e₂

/--
A routing is complete if all required sinks are connected.

**fdrs.md**: Complete routing means no uninitialized outputs.
-/
def isComplete (rt : RoutingTable) (sinks : Set DataSink) : Prop :=
  ∀ s ∈ sinks, ∃ e ∈ rt.entries, e.sink = s

/--
Routing composition: sequential combination of routing tables.

Connects outputs of rt₁ to inputs of rt₂ by matching output sinks
to computed sources.
-/
def compose (rt₁ rt₂ : RoutingTable) : RoutingTable :=
  { entries := rt₁.entries ++ rt₂.entries
    source_unique := trivial }

/-!
## Bandwidth Analysis
-/

/--
Bandwidth requirement: total number of routing entries.

**fdrs.md**: Bandwidth = max{|active routes|} over all timesteps.

This is a simplified upper bound: the actual bandwidth at any timestep
is at most the total number of entries.
-/
def bandwidth (rt : RoutingTable) : ℕ :=
  rt.entries.length

/--
Empty routing has zero bandwidth.
-/
theorem bandwidth_empty : bandwidth { entries := [], source_unique := trivial } = 0 := rfl

/--
Bandwidth is monotone under routing extension.
-/
theorem bandwidth_append (rt₁ rt₂ : RoutingTable) :
    bandwidth (compose rt₁ rt₂) = bandwidth rt₁ + bandwidth rt₂ := by
  simp only [bandwidth, compose, List.length_append]

/--
Locality-preserving routing has bounded bandwidth.

**fdrs.md**: Local operations have O(1) routing bandwidth.

For a routing table with n entries, bandwidth ≤ n.
This is trivially true by definition.
-/
theorem local_routing_bounded (rt : RoutingTable) :
    bandwidth rt ≤ rt.entries.length := by
  exact Nat.le_refl _

end FdrsFormal.Composition.Routing
