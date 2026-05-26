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

# Digit-Conditional Signal Analysis (Phase 11)

Non-stationary radix trees and digit-conditional signal structure:
- heterogeneous branching captures signals invisible to Vilenkin/Fourier analysis,
- orthogonal layer decomposition generalizes the MRA detail operators,
- Phase 2 multiresolution analysis is recovered as the homogeneous special case.

## Contents

- **Tree.lean**: Definitions 164-165, Propositions 131-132 (radix trees, leaf count, homogeneous recovery)
- **Decomposition.lean**: Definitions 166-167, Lemma 5, Theorem 65, Corollary 30 (adapted signals, layers, orthogonal decomp)
- **SignalClass.lean**: Definition 168, Proposition 133 (signal taxonomy, strict hierarchy)
- **FourierCeiling.lean**: Definition 169, Theorem 66, Proposition 134 (energy fraction, Fourier ceiling)
- **RepresentationGap.lean**: Definitions 170-171, Proposition 135, Theorem 67, Corollary 31 (gap formula)
- **Projection.lean**: Definition 172, Proposition 136, Theorem 68 (tree projection, FDRS connection)
- **Detection.lean**: Definition 173, Proposition 137 (F-statistic, detection power)
- **Complexity.lean**: Definition 174, Proposition 138 (DCC, taxonomy characterization)
- **SpecialCase.lean**: Theorem 69 (Vilenkin is special case — capstone)

## References

- fdrs.md, Phase 11, Sections 11.1-11.9
-/

import FdrsFormal.Analysis.DigitConditional.Tree
import FdrsFormal.Analysis.DigitConditional.Decomposition
import FdrsFormal.Analysis.DigitConditional.SignalClass
import FdrsFormal.Analysis.DigitConditional.FourierCeiling
import FdrsFormal.Analysis.DigitConditional.RepresentationGap
import FdrsFormal.Analysis.DigitConditional.Projection
import FdrsFormal.Analysis.DigitConditional.Detection
import FdrsFormal.Analysis.DigitConditional.Complexity
import FdrsFormal.Analysis.DigitConditional.SpecialCase
