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

# Variable Radix Ultrametric Module

Aggregator for the ultrametric structure on variable-radix spaces.

## Contents

- `Definition`: The ultrametric δ_ω(x,y) = β_ω(lcp)^{-1}
- `Axioms`: Proof that δ_ω is an ultrametric (strong triangle inequality)
- `CylinderBalls`: Cylinders C_ω(s) = metric balls

## References

- fdrs.md, Phase 5-6, Section 2 (lines 4010-4041)
-/

import FdrsFormal.Modes.VariableRadix.InducedUltrametric.Definition
import FdrsFormal.Modes.VariableRadix.InducedUltrametric.Axioms
import FdrsFormal.Modes.VariableRadix.InducedUltrametric.CylinderBalls
