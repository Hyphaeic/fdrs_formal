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

# Synchronization and Join Semantics

This file defines synchronization points and join semantics.

## Mathematical Content (fdrs.md lines 6328-6353)

**Definition 129 (Synchronization point)**:

A junction (T, s) is a **synchronization point** if it has multiple incoming edges:
  |{(A, s_A) : ((A, s_A), (T, s)) ∈ E_{G_ρ}}| > 1

**Definition 130 (Join semantics)**:

At synchronization point with k sources:
- **ALL-join (barrier)**: Execute only when ALL sources delivered
- **ANY-join (race)**: Execute when FIRST source delivers
- **COLLECT-join (accumulate)**: Combine payloads: Inject(T, s, combine(p₁, ..., p_k))

## References

- fdrs.md, Phase 8, Section 8.7 (lines 6328-6353)
-/

import FdrsFormal.Composition.Synchronization.Multicast

namespace FdrsFormal.Composition.Synchronization

/-!
## Synchronization Points
-/

/--
Synchronization point: junction with multiple sources.

**fdrs.md Definition 129 (lines 6328-6335)**: Multiple incoming edges.

Defined as a predicate parameterized by a source-count oracle.
-/
def isSynchronizationPoint (sourceCount : ℕ → ℕ → ℕ) (timeline cylinder : ℕ) : Prop :=
  sourceCount timeline cylinder > 1

/--
Source count for synchronization point.

**fdrs.md line 6332**: |{sources}| for synchronization.

Placeholder: actual count depends on routing graph structure.
-/
def synchronizationSourceCount (_timeline _cylinder : ℕ) : ℕ := 0

/-!
## Join Semantics
-/

/--
Join semantic type.

**fdrs.md Definition 130 (lines 6338-6353)**: Three join variants.
-/
inductive JoinSemantics where
  | ALL   -- Barrier: wait for all sources
  | ANY   -- Race: trigger on first arrival
  | COLLECT  -- Accumulate: combine all payloads
  deriving DecidableEq, Repr

/--
ALL-join (barrier synchronization).

**fdrs.md line 6342**: Execute only when ALL sources delivered.

**Example (line 6348)**: Task waits for CPU + DMA + Network all ready.

Defined: all sources must have delivered before injection executes.
-/
def barrierJoin (_timeline _cylinder : ℕ) (sources : List ℕ) (delivered : ℕ → Bool) : Prop :=
  sources.Forall (fun s => delivered s = true)

/--
ANY-join (race semantics).

**fdrs.md line 6343**: Execute when FIRST source delivers.

**Example (line 6349)**: Interrupt handler triggered by any source.

Defined: at least one source has delivered.
-/
def raceJoin (_timeline _cylinder : ℕ) (sources : List ℕ) (delivered : ℕ → Bool) : Prop :=
  sources.any (fun s => delivered s) = true

/--
COLLECT-join (payload accumulation).

**fdrs.md line 6344**: Combine multiple payloads.

**Example (line 6350)**: Aggregate sensor readings.

Defined: combines payloads from all delivered sources.
-/
def collectJoin (_timeline _cylinder : ℕ) (combine : List ℕ → ℕ)
    (payloads : List ℕ) : ℕ :=
  combine payloads

end FdrsFormal.Composition.Synchronization
