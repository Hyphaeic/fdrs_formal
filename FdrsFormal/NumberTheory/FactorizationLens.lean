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

# Factorization Lens Module

Dual filtration structure: additive (cylinders) vs multiplicative (valuations).

## Contents

1. **Definition**: Factorization n = u_P(n) · s_P(n) into P-free × P-smooth parts
2. Fiberwise locality of Dirichlet transforms
3. Markov property on factorization lens coordinates

## Mathematical References

- fdrs.md, Phase 3 Fragment 4 (lines 2228-2476)
- Paper §8.1-8.2, Definition 8.2
- DEPENDENCY_BASED_STRUCTURE.md, Tier 13

## Status

🔵 **STUB** - Axioms created (2026-01-21)
- Factorization decomposition: ✅ Defined
- Fiberwise locality: ✅ Axiomatized
- Ready for: Multiplicative structure proofs or accept as foundations
-/

import FdrsFormal.NumberTheory.FactorizationLens.Definition
import FdrsFormal.NumberTheory.FactorizationLens.ValuationAlgebra
import FdrsFormal.NumberTheory.FactorizationLens.Periodicity
import FdrsFormal.NumberTheory.FactorizationLens.ExponentConvolution
import FdrsFormal.NumberTheory.FactorizationLens.FiberDecomposition
import FdrsFormal.NumberTheory.FactorizationLens.AugmentedState
import FdrsFormal.NumberTheory.FactorizationLens.MarkovProperty
import FdrsFormal.NumberTheory.FactorizationLens.SquarefreeOnLattice
import FdrsFormal.NumberTheory.FactorizationLens.PowerKernel
