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

# FunctionSpaces Module (Tier 6-9)

Mixed-radix complexes: function spaces 𝕋(V) with hierarchical structure.

## Contents

1. **Basic/**: Tensor spaces, cylinders, block-constant subspaces, refinements
2. **Measure/**: Uniform product measure on R̂
3. **Projections/**: Block projections P_L, detail operators Δ_L, telescoping
4. **LocalOperators/**: L-local operators and locality theory
5. **Commutant/**: Finite-horizon versions and commutant structure

## Mathematical Content

Implements **Phase 2** from fdrs.md (lines 533-1278):
- Fragment 1: Tensor spaces and block structure (lines 533-772)
- Fragment 2: Finite-horizon discrete operators (lines 773-1026)
- Fragment 3: Multiresolution decomposition (lines 1034-1278)

## Status

✅ **COMPLETE** (2026-01-23)
- Basic/: ✅ Complete (0 open proofs)
- Measure/: 🔵 Axiomatized (4 axioms - Kolmogorov extension)
- Projections/: ✅ Complete (0 open proofs, 13 axioms)
- LocalOperators/: ✅ Complete (0 open proofs)
- Commutant/: ✅ Complete (0 open proofs, 24 axioms)

**Total**: 0 open proofs, ~41 axioms (all documented with proof sketches)

## References

- fdrs.md, Phase 2 (lines 533-1278)
- DEPENDENCY_BASED_STRUCTURE.md, Tier 6-9
- THEOREM_MAPPING.md, FunctionSpaces sections
-/

import FdrsFormal.FunctionSpaces.Basic
import FdrsFormal.FunctionSpaces.Measure
import FdrsFormal.FunctionSpaces.Projections
import FdrsFormal.FunctionSpaces.LocalOperators
import FdrsFormal.FunctionSpaces.Commutant
