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

# Prefix Weights Module

Aggregator for prefix weight construction.

## Contents

- `Definition`: Definition 58 - β_ω prefix weights
- `OdometerDecode`: Definition 59 - Odometer decoding
- `ArithmeticCylinders`: Theorem 36 - SU ⟹ cylinders = congruence

## References

- fdrs.md, Phase 5-6, Section 2-3 (lines 5144-5147, 4733-4740, 4870-4900)
- DEPENDENCY_BASED_STRUCTURE.md, Modes/VariableRadix/PrefixWeights
- Paper: Fragment 5.4
-/

import FdrsFormal.Modes.VariableRadix.PrefixWeights.Definition
import FdrsFormal.Modes.VariableRadix.PrefixWeights.OdometerDecode
import FdrsFormal.Modes.VariableRadix.PrefixWeights.ArithmeticCylinders
