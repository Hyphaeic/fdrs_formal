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

# Integration Module

This module aggregates all integration components that connect
FDRS modes with analytic number theory primitives.

## Contents

- **BlockMemory**: Cylinder-local state spaces and lift/restrict operators
- **Primitives**: ANT primitives (residue projection, Möbius inversion)
- **Programs**: Integer semantics (integers as programs)
- **RuntimeAlgebra**: Runtime operator algebra ℜ_N
- **DualFiltrations**: Additive and multiplicative filtration structures
- **Complexity**: Complexity bounds for operations

## References

- fdrs.md, Phase 4 (Integration)
-/

import FdrsFormal.Integration.BlockMemory.Definition
import FdrsFormal.Integration.Primitives.ResidueProjection
import FdrsFormal.Integration.Primitives.MobiusInversion
import FdrsFormal.Integration.Programs.IntegerSemantics
import FdrsFormal.Integration.RuntimeAlgebra.Definition
import FdrsFormal.Integration.DualFiltrations.Definition
import FdrsFormal.Integration.Complexity.Definition
