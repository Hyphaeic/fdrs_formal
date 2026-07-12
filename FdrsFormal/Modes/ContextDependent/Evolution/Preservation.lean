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

# CSU Preservation Under Context Switching

This file proves that CSU is preserved under context transitions.

## Mathematical Content (fdrs.md lines 5589-5599)

**Theorem 45 (Context-switching preserves SU)**:
If Ω satisfies CSU, then for any trace through 𝒮, every context c
visited along the trace satisfies standard SU.

**Proof**: By definition of CSU, ω_c = Ω(·, c) satisfies SU for each c ∈ 𝒞.
Context transitions change c but don't affect this per-context property.

## References

- fdrs.md, Phase 7, Section 7.2 (lines 5589-5599)
-/

import FdrsFormal.Modes.ContextDependent.Evolution.Trace

namespace FdrsFormal.Modes.ContextDependent

open FdrsFormal.Modes.VariableRadix

/-!
## CSU Preservation
-/

/--
**Theorem 45**: Context-switching preserves SU.

If a system has CSU, then every context visited in any trace satisfies SU.

**fdrs.md**: Theorem 45 (Context-switching preserves SU) [§7.2.4 · Phase 7]
-/
theorem csu_preserved_along_trace {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) (hcsu : 𝒮.hasCSU)
    (trace : FiniteTrace C E 𝒮) (c : C) (hc : trace.visits c) (k : ℕ) :
    isSiblingUniform (𝒮.radixAt c) k :=
  hcsu c k

/-- CSU is preserved after any event sequence -/
theorem csu_preserved_after_events {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) (hcsu : 𝒮.hasCSU)
    (events : List E) (k : ℕ) :
    isSiblingUniform (𝒮.radixAt (𝒮.dynamics.applySeq c₀ events)) k :=
  hcsu _ k

/-- The RadixLaw at any reachable context satisfies SU -/
theorem reachable_context_has_su {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) (hcsu : 𝒮.hasCSU)
    (c : C) (k : ℕ) :
    isSiblingUniform (𝒮.radixAt c) k :=
  hcsu c k

/-!
## Consequences of Preservation
-/

/-- Under CSU, odometer charts exist at every visited context -/
theorem csu_charts_exist_everywhere {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) (hcsu : 𝒮.hasCSU)
    (c : C) (k : ℕ) :
    Function.Bijective (finiteVariableRadixEquiv (𝒮.radixAt c) k) :=
  (finiteVariableRadixEquiv (𝒮.radixAt c) k).bijective

/-- Under CSU, block sizes are well-defined at every context -/
theorem csu_blockSize_everywhere {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) (hcsu : 𝒮.hasCSU)
    (c : C) (k : ℕ) (s : PrefixWord) :
    0 < blockSize (𝒮.radixAt c) k s :=
  blockSize_pos (𝒮.radixAt c) k s

/-!
## Dynamic SU
-/

/-- SU holds dynamically: at each step of a trace, SU holds -/
theorem dynamic_su {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) (hcsu : 𝒮.hasCSU)
    (trace : InfiniteTrace C E 𝒮) (n k : ℕ) :
    isSiblingUniform (𝒮.radixAt (trace.contexts n)) k :=
  hcsu _ k

end FdrsFormal.Modes.ContextDependent
