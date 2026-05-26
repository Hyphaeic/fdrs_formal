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

# Preservation Module (THEOREM F)

Aggregator for structure preservation results.

## Contents

- `DepthL`: Definition 93 - Structure-preserving transitions
- `MonotoneRefinement`: Definition 94, Proposition 98 - Monotone refinement
- `OperatorPreserved`: Theorem 47 - THEOREM F: Operators preserved

## Main Result

**THEOREM F (Depth-L Operators Preserved)**:
If transition c → c' is structure-preserving at depth L, then:
1. All L-local gates remain valid
2. Ultrametric δ_c agrees with δ_{c'} on Σ_L-indexed points
3. Projection operators P_L commute with context switch

## References

- fdrs.md, Phase 7, Section 7.4 (lines 5639-5694)
- DEPENDENCY_BASED_STRUCTURE.md, Modes/ContextDependent/Preservation
- Paper: THEOREM F
-/

import FdrsFormal.Modes.ContextDependent.Preservation.DepthL
import FdrsFormal.Modes.ContextDependent.Preservation.MonotoneRefinement
import FdrsFormal.Modes.ContextDependent.Preservation.OperatorPreserved
