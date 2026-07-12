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

# Hyper-Gosper clock — coupling N timelines without the 2^N explosion

A single Gosper mediator over `N` input streams would need a rank-`(N+1)` tensor with
`2^(N+1)` integers (2048 for 10 clocks; hopeless). The trick: **never build the flat
N-input tensor.** Instead arrange the verified rank-3 `BihTensor` nodes (8 integers each)
into a **tournament-bracket binary tree** — pair clocks `(A,B), (C,D), …`, emit each
pair to a wire, then pair the wires, and so on. Every node stays at `2×2×2`; you trade
the exponential state-space for linear node count and log-depth cascading latency.

**Payload isolation** is automatic here: a node's output is `run`'s `List ℤ` — the
discrete emitted digit/carry stream, *not* the 8-integer tensor state. The heavy
Archimedean math (fractions, floors, `emit_traps`) stays sealed in each node's black
box; only clean discrete ticks travel up the wires. Each node's emissions remain
certified by `emit_traps` (the certification composes node-by-node).

NOTE (honest scope): the "thermodynamic limit" intuition — that coarsening up an
infinite tree converges to the Gauss/Parry invariant measure — is a *conjecture*, not
proved here, and the link to `Commutant/{OperatorAlgebra,Multiresolution}` is an
analogy. Also: composing finite-fuel `run`s truncates intermediate streams, so deep
trees lose precision in the tail — the bracket (log depth) mitigates this versus a
chain (linear depth), but does not remove it. This file builds the *coupler*; the
limit theorem is future work.
-/
import FdrsFormal.Modes.VariableRadix.BihomographicDriver

namespace FdrsFormal.Modes.VariableRadix.BihTensor

/-- One tournament layer: pair adjacent streams and run each pair through node `T`,
emitting the combined stream. A leftover odd stream passes through unchanged. -/
def pairUp (T : BihTensor) (fuel : ℕ) : List (List ℤ) → List (List ℤ)
  | a :: b :: rest => run T a b true fuel :: pairUp T fuel rest
  | rest => rest

/-- Cascade the tournament layers until a single output stream remains. `depth` bounds
the number of layers (any `depth ≥ ⌈log₂ N⌉` suffices). -/
def coupleTree (T : BihTensor) (fuel : ℕ) : ℕ → List (List ℤ) → List ℤ
  | _, [] => []
  | _, [s] => s
  | 0, _ => []
  | depth + 1, streams => coupleTree T fuel depth (pairUp T fuel streams)

/-- **The hyper-Gosper clock.** Couple a list of `N` input timelines through a
tournament-bracket tree of rank-3 `BihTensor` nodes — every node at 8 integers, only
discrete streams on the wires.

**fdrs.md**: Definition 191 (The hyper-Gosper clock) [§13.6.7 · Phase 13] -/
def coupleAll (T : BihTensor) (fuel : ℕ) (streams : List (List ℤ)) : List ℤ :=
  coupleTree T fuel streams.length streams

/-! ## Demonstrations — N coupled φ-clocks summed exactly through the tree

`φ = [1;1,1,…]`. Summing `N` copies of φ through the bracket gives `Nφ` (leading digits;
deeper trees truncate the tail). -/

private def φ25 : List ℤ := List.replicate 25 1

-- 3φ = 4.854… = [4;1,5,…]
#eval coupleAll addTensor 40 [φ25, φ25, φ25]
-- 4φ = 6.472… = [6;2,…]  (a balanced 2-layer bracket)
#eval coupleAll addTensor 40 [φ25, φ25, φ25, φ25]
-- 8φ = 12.944… = [12;1,…]  (3-layer bracket; every node still 8 integers)
#eval coupleAll addTensor 60 (List.replicate 8 φ25)

end FdrsFormal.Modes.VariableRadix.BihTensor
