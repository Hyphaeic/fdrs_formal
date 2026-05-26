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

# FunctionSpaces Basic Module

This module provides the fundamental definitions for mixed-radix function spaces.

## Contents

1. **PrefixSet**: The prefix index set Σ_L = ∏_{i=0}^{L-1} D_i
2. **Cylinder**: Cylinder sets U(s) for s ∈ Σ_L
3. **TensorSpace**: The tensor space 𝕋(V) = {f : R̂ → V}
4. **BlockConstant**: Block-constant subspaces 𝕋_L(V)
5. **CoordinateRep**: The isomorphism Φ_L : 𝕋_L(V) ≅ V^{Σ_L}
6. **Refinement**: Refinement embeddings ι_{L→L+1}

## Mathematical References

- fdrs.md, Section 1-2 (lines 549-614)
- THEOREM_MAPPING.md, FunctionSpaces section

## Dependencies

- Core/Primitives (RadixSeq, PlaceValue)
- Core/Infinite (DirectLimit, CompletedSpace)
-/

import FdrsFormal.FunctionSpaces.Basic.PrefixSet
import FdrsFormal.FunctionSpaces.Basic.Cylinder
import FdrsFormal.FunctionSpaces.Basic.TensorSpace
import FdrsFormal.FunctionSpaces.Basic.BlockConstant
import FdrsFormal.FunctionSpaces.Basic.CoordinateRep
import FdrsFormal.FunctionSpaces.Basic.Refinement
