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

# Compile-Time Decidable Properties

This file proves routing properties are decidable at compile time.

## Mathematical Content (fdrs.md lines 6392-6416)

**Proposition 109 (Compile-time decidable properties)**:

From routing specification Spec, the following are **decidable at compile time:**

1. **Acyclicity**: Is G_ρ a DAG? (cycle detection algorithm)
2. **Bounded fanout**: Is max_{A,s} |ρ(A, s, _, _)| < ∞? (scan specification)
3. **Bounded depth**: Is max_{T,s} depth_ρ(T, s) < ∞? (longest path algorithm)
4. **Reachability**: Can source (A, s_A) reach target (B, s_B)? (graph traversal)
5. **Deadlock freedom**: Are there cycles in wait-for dependencies? (cycle detection)

**Proof**: All reduce to standard graph algorithms on finite G_ρ. All polynomial-time decidable.

## References

- fdrs.md, Phase 8, Section 8.8 (lines 6392-6404)
-/

import FdrsFormal.Composition.Verification.Specification
import FdrsFormal.Composition.DeadlockAnalysis.Definition
import FdrsFormal.Composition.RoutingGraph.Graph

namespace FdrsFormal.Composition.Verification

/-!
## Decidability Theorems
-/

/--
Acyclicity is decidable at compile time.

**fdrs.md Proposition 109 item 1 (line 6396)**: cycle detection on `G_ρ`.

The decision procedure is the `Decidable (RoutingGraph.Acyclic spec)` instance:
`G_ρ` has a finite vertex list and decidable reachability, so checking that no
junction reaches itself is decidable.
-/
def acyclicity_decidable (spec : RoutingSpecification) :
    Decidable (RoutingGraph.Acyclic spec) := inferInstance

/--
Bounded fanout is decidable.

**fdrs.md Proposition 109 item 2 (line 6397)**: scan the specification for max fanout.

A finite scan over `vertices spec` of the rule-derived `fanout` against bound `B`.
-/
def bounded_fanout_decidable (spec : RoutingSpecification) (B : ℕ) :
    Decidable (RoutingGraph.BoundedFanout spec B) := inferInstance

/--
Bounded routing depth is decidable.

**fdrs.md Proposition 109 item 3 (line 6398)**: longest path in the DAG.

Longest-path relaxation (`RoutingGraph.depthIter`) over the finite vertex set,
compared against bound `D`.
-/
def bounded_depth_decidable (spec : RoutingSpecification) (D : ℕ) :
    Decidable (RoutingGraph.BoundedDepth spec D) := inferInstance

/--
Reachability is decidable.

**fdrs.md Proposition 109 item 4 (line 6399)**: graph traversal (BFS/DFS).

Membership of `target` in the bounded reachable set of `source`
(`RoutingGraph.Reaches`).
-/
def reachability_decidable (spec : RoutingSpecification) (source target : ℕ × ℕ) :
    Decidable (RoutingGraph.Reaches spec source target) := inferInstance

/--
Deadlock freedom is decidable.

**fdrs.md Proposition 109 item 5 (line 6400)**: cycle detection in the wait-for graph.

By Theorem 52 deadlock freedom is acyclicity of `G_ρ` (`RoutingGraph.DeadlockFree`),
so it is decided by the same cycle-detection procedure.
-/
def deadlock_freedom_decidable (spec : RoutingSpecification) :
    Decidable (RoutingGraph.DeadlockFree spec) := inferInstance

/--
**fdrs.md Theorem 52 (lines 6131-6145)**: at the decision level, deadlock freedom
of the system coincides with acyclicity of `G_ρ` — a set of mutually waiting
timelines is exactly a cycle in the routing graph.
-/
theorem deadlockFree_iff_acyclic (spec : RoutingSpecification) :
    RoutingGraph.DeadlockFree spec ↔ RoutingGraph.Acyclic spec := Iff.rfl

end FdrsFormal.Composition.Verification
