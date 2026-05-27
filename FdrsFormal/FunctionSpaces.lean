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

Built and machine-checked against Mathlib; the earlier "axiomatized / N axioms" status
is obsolete (this module has no axioms). One Lᵖ-convergence result in `Projections/`
remains a placeholder (`blockProjection_Lp_convergence_placeholder`). Run
`python3 scripts/fdrs-summary` for the live, authoritative status — axioms, sorries,
and scaffold declarations — rather than relying on counts written here.

## References

- fdrs.md, Phase 2 (lines 533-1278)
-/

import FdrsFormal.FunctionSpaces.Basic
import FdrsFormal.FunctionSpaces.Measure
import FdrsFormal.FunctionSpaces.Projections
import FdrsFormal.FunctionSpaces.LocalOperators
import FdrsFormal.FunctionSpaces.Commutant
