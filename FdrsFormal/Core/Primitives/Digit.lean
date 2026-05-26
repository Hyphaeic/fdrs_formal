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

# Digit Types

Defines the digit alphabet at each position as Fin (b i).

## References

- fdrs.md, Phase 1 Fragment 1, Section 1 (lines 6-8)
- Paper §2.1
-/

import FdrsFormal.Core.Primitives.RadixSeq
import Mathlib.Data.Fin.Basic

namespace FdrsFormal.Core.Primitives

/-! ## Digit Type -/

/-- The digit alphabet at position `i` for radix sequence `b`.
    This is `Fin (b i)`, representing digits {0, 1, ..., b_i - 1}. -/
abbrev Digit (b : RadixSeq) (i : ℕ) := Fin (b i)

end FdrsFormal.Core.Primitives
