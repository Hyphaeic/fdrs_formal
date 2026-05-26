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

# FunctionSpaces Measure Module

This module provides measure-theoretic foundations for mixed-radix function spaces.

## Contents

1. **ProductMeasure**: The uniform product probability measure μ on R̂
2. **LpNorm**: Lp norm definitions and properties (triangle inequality)

## Mathematical References

- fdrs.md, Section 3, Definition 21 (lines 621-627)
- fdrs.md, Phase 2 Fragment 2 (lines 877-918) for Lp norms
- THEOREM_MAPPING.md, FunctionSpaces/Measure section

## Dependencies

- FunctionSpaces/Basic (TensorSpace, cylinders)
- Topology/Filtration (σ-algebras)
-/

import FdrsFormal.FunctionSpaces.Measure.ProductMeasure
import FdrsFormal.FunctionSpaces.Measure.LpNorm
