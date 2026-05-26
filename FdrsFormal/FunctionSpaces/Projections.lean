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

# FunctionSpaces Projections Module

This module provides block projection operators and their properties.

## Contents

1. **Definition**: Block projection P_L (conditional expectation onto ℱ_L)
2. **Properties**: Idempotence, tower property, contraction
3. **Details**: Detail operators Δ_L and telescoping decomposition

## Mathematical References

- fdrs.md, Sections 3-4 (lines 628-696)
- THEOREM_MAPPING.md, FunctionSpaces/Projections section

## Dependencies

- FunctionSpaces/Measure (uniform product measure)
- FunctionSpaces/Basic (TensorSpace, BlockConstantSpace)
-/

import FdrsFormal.FunctionSpaces.Projections.Definition
import FdrsFormal.FunctionSpaces.Projections.Properties
import FdrsFormal.FunctionSpaces.Projections.Details
import FdrsFormal.FunctionSpaces.Projections.CoordinateSplit
