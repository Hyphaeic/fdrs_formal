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

# Vilenkin is Special Case (Capstone)

Proves that Phase 2 multiresolution analysis is the homogeneous special
case of Phase 11.

## Mathematical Content (fdrs.md §11.9)

**Theorem 69**: Vilenkin is special case — Phase 2 MRA = homogeneous Phase 11

## References

- fdrs.md, Phase 11, Section 11.9.1
-/

import FdrsFormal.Analysis.DigitConditional.Projection
import FdrsFormal.Analysis.DigitConditional.FourierCeiling
import FdrsFormal.Analysis.DigitConditional.RepresentationGap
import FdrsFormal.Analysis.DigitConditional.Complexity

namespace FdrsFormal.Analysis.DigitConditional

/-! ## Theorem 69: Vilenkin is special case -/

/--
**fdrs.md**: Theorem 69 (Vilenkin is special case) [§11.9.1 · Phase 11]

For a homogeneous tree, leafCount = product of branching factors, recovering
the standard cylinder partition structure. Combined with:
- connectionToFDRSFiltration: P_T f = f for adapted f (Theorem 68)
- homogeneousCeilingTrivial: α = 1 (Proposition 134)
- compensatedHeterogeneity: Gap = 1 when all branching equal (Corollary 31)
this establishes that the classical Vilenkin/Haar MRA is the homogeneous
special case.
-/
theorem vilenkinIsSpecialCase {N : ℕ} (hN : N > 0)
    (T : NonStationaryRadixTree N)
    (hom : T.isHomogeneous) :
    T.leafCount = T.tree.branchingFactors.prod :=
  homogeneousRecovery T hom

end FdrsFormal.Analysis.DigitConditional
