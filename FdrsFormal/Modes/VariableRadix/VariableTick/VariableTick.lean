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

# Variable Radix Tick Module

Aggregator for the variable radix Tick operator.

## Contents

- `Definition`: Tick via encode/decode and lexicographic successor
- `Correctness`: Theorem 31 - Tick = +1 in rank
- `CarryAlgorithm`: Direct digit-level carry computation
- `Termination`: Proposition 81 - Carry always terminates

## References

- fdrs.md, Phase 5-6, Section 4-5 (lines 4099-4160)
- DEPENDENCY_BASED_STRUCTURE.md, Modes/VariableRadix/VariableTick
-/

import FdrsFormal.Modes.VariableRadix.VariableTick.Definition
import FdrsFormal.Modes.VariableRadix.VariableTick.Correctness
import FdrsFormal.Modes.VariableRadix.VariableTick.CarryAlgorithm
import FdrsFormal.Modes.VariableRadix.VariableTick.Termination
