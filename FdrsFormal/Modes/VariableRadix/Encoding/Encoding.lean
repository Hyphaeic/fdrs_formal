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

# Variable Radix Encoding Module (THEOREM A)

Aggregator for the encoding/bijection construction.

## Contents

- `SubtreeCards`: Subtree sizes W^{(k)}_ω(s) for counting
- `Ranking`: The decode function (counting lex-smaller elements)
- `OrderPreserving`: Proof that decode preserves order
- `Bijection`: **THEOREM A** - the canonical bijection φ_ω: R_ω ≅ ℕ

## References

- fdrs.md, Phase 5-6, Section 3 (lines 4044-4091)
- Paper: THEOREM A (§6.3)
-/

import FdrsFormal.Modes.VariableRadix.Encoding.SubtreeCards
import FdrsFormal.Modes.VariableRadix.Encoding.Ranking
import FdrsFormal.Modes.VariableRadix.Encoding.OrderPreserving
import FdrsFormal.Modes.VariableRadix.Encoding.Bijection
import FdrsFormal.Modes.VariableRadix.Encoding.LexOrder
