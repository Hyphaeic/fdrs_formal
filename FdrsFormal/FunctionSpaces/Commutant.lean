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

# FunctionSpaces.Commutant - Commutant and Multiresolution Theory

Aggregator for the Commutant submodule.

## Mathematical Content

**fdrs.md Phase 2, Fragments 2-3** (lines 773-1278):
- Finite-horizon function spaces and cylinders
- Block projections P_L^(k) and detail operators Δ_L^(k)
- Operator norm bounds (contraction theory)
- Commutant characterization (operators commuting with P_L)
- Multiresolution decomposition (orthogonal direct sum H_k = C_0 ⊕ D_0 ⊕ ... ⊕ D_k)
- Locality vs commutation (strict separations and intersection)
- Tick pullback dynamics on finite spaces

## Module Structure

```
Commutant/
├── FiniteHorizon.lean       ✅ Finite cylinders U_k(s), uniform measure μ_k
├── FiniteProjection.lean    ✅ P_L^(k), Δ_L^(k), projection algebra
├── Contraction.lean         🔴 Lp norm bounds (Thm 4.1)
├── BlockDiagonal.lean       🔴 Commutation theorem (Thm 5.2)
├── Compatibility.lean       🔴 Truncation/embedding (Prop 6.2)
├── Multiresolution.lean     🔴 Coarse/detail subspaces (Defs 1.1-1.2)
├── OrthogonalDecomp.lean    🔴 Orthogonal decomposition (Thm 1.4)
├── MultiLevelCommutant.lean 🔴 Multi-level commutant (Thm 2.2)
├── LocalityVsCommutation.lean 🔴 Locality theory (Props 3.3-3.4, Thm 3.5)
└── TickPullback.lean        🔴 Tick dynamics (Thm 4.5, Props 4.3-4.4)
```

## Current Status

- **Implemented**: FiniteHorizon, FiniteProjection (453 lines)
- **Sorries**: 10 (need triage)
- **Remaining**: 8 files to implement (~1000-1200 lines estimated)

## References

- fdrs.md: Phase 2, Fragments 2-3 (lines 773-1278)
- THEOREM_MAPPING.md: FunctionSpaces/Commutant section
- DEPENDENCY_BASED_STRUCTURE.md: Tier 6-9 (FunctionSpaces module)
-/

import FdrsFormal.FunctionSpaces.Commutant.FiniteHorizon
import FdrsFormal.FunctionSpaces.Commutant.FiniteProjection
import FdrsFormal.FunctionSpaces.Commutant.Contraction
import FdrsFormal.FunctionSpaces.Commutant.BlockDiagonal
import FdrsFormal.FunctionSpaces.Commutant.Compatibility
import FdrsFormal.FunctionSpaces.Commutant.Multiresolution
import FdrsFormal.FunctionSpaces.Commutant.OrthogonalDecomp
import FdrsFormal.FunctionSpaces.Commutant.MultiLevelCommutant
import FdrsFormal.FunctionSpaces.Commutant.LocalityVsCommutation
import FdrsFormal.FunctionSpaces.Commutant.TickPullback
import FdrsFormal.FunctionSpaces.Commutant.OperatorAlgebra
