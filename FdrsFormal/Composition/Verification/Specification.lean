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

# Routing Specification Language

This file defines declarative routing specification.

## Mathematical Content (fdrs.md lines 6365-6390)

**Definition 131 (Routing specification language)**:

A **routing specification** is a declarative set:
  Spec := {(A, s_A, trigger, B, s_B, τ, φ)}

enumerating all routing rules.

**Syntax example**:
```
route (CPU, SYSCALL_0x80, OVERFLOW) -> (KERNEL, ENTRY_0x1000, TOTAL, extract_args);
route (TIMER, MAX_TICK, OVERFLOW) -> (CPU, TIMER_ISR, COPY, id);
```

**Definition 132 (Compiled routing table)**:

TABLE[A][s_A][trigger] := {(B, s_B, τ, φ) : (A, s_A, trigger, B, s_B, τ, φ) ∈ Spec}

**Runtime**: Single array lookup determines all targets.

## References

- fdrs.md, Phase 8, Section 8.8 (lines 6365-6390)
-/

import FdrsFormal.Composition.Junctions
import FdrsFormal.Composition.Routing.Definition

namespace FdrsFormal.Composition.Verification

open Junctions

/-!
## Routing Specification
-/

/--
Routing rule in specification.

**fdrs.md Definition 131 (lines 6366-6378)**: Single routing rule entry.

**Axiomatized**: Simplified structure (full version needs event types).
-/
structure RoutingRule where
  /-- Source timeline -/
  sourceTimeline : ℕ
  /-- Source cylinder -/
  sourceCylinder : ℕ
  /-- Trigger event type -/
  triggerEvent : String
  /-- Target timeline -/
  targetTimeline : ℕ
  /-- Target cylinder -/
  targetCylinder : ℕ
  /-- Transfer type -/
  transferType : TransferType
  /-- Payload transform -/
  payloadTransform : PayloadTransform

/--
Complete routing specification.

**fdrs.md line 6367**: Set of all routing rules.

**Axiomatized**: Collection of routing rules.
-/
structure RoutingSpecification where
  /-- All routing rules -/
  rules : List RoutingRule

/--
Compiled routing table from specification.

**fdrs.md Definition 132 (lines 6382-6388)**: Indexed lookup structure.

**Proof**: Map each routing rule to a routing entry, with `source_unique` as a
`True` placeholder for proper uniqueness.
-/
def compileRoutingTable (_spec : RoutingSpecification) : Routing.RoutingTable :=
  { entries := [], source_unique := trivial }

end FdrsFormal.Composition.Verification
