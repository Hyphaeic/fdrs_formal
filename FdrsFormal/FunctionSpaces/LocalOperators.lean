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

# FunctionSpaces LocalOperators Module

This module provides prefix-local operators and the gating algebra.

## Contents

1. **Definition**: L-local (prefix-local) operators
2. **Examples**: P_L, cylinder indicators, kernel operators
3. **GatingAlgebra**: The algebra G_L of phase-locked activation patterns

## Mathematical References

- fdrs.md, Section 5 (lines 705-737)
- THEOREM_MAPPING.md, FunctionSpaces/LocalOperators section

## Dependencies

- FunctionSpaces/Projections (block projections P_L)
- FunctionSpaces/Basic (TensorSpace)
-/

import FdrsFormal.FunctionSpaces.LocalOperators.Definition
import FdrsFormal.FunctionSpaces.LocalOperators.DigitPermutation
