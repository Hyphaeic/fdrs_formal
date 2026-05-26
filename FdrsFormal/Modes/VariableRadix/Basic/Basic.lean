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

# Variable Radix Basic Module

Aggregator for the basic definitions of variable-radix systems.

## Contents

- `RadixLaw`: The branching function ω: Σ* → ℕ≥2
- `DigitAlphabet`: Digit sets D_ω(s) at each prefix
- `TreeStructure`: The rooted tree T_ω
- `VariableSpace`: Finite and infinite variable-radix spaces

## References

- fdrs.md, Phase 5-6, Section 1 (lines 3956-3992)
-/

import FdrsFormal.Modes.VariableRadix.Basic.RadixLaw
import FdrsFormal.Modes.VariableRadix.Basic.DigitAlphabet
import FdrsFormal.Modes.VariableRadix.Basic.TreeStructure
import FdrsFormal.Modes.VariableRadix.Basic.VariableSpace
