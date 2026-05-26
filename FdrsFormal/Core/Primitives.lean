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

# Core Primitives

Re-exports all primitive definitions for mixed-radix systems:
- RadixSeq: Sequence of radices with b_i ≥ 2
- Digit: Finite digit types
- placeValue: Cumulative radix products B_m

## References

- fdrs.md, Phase 1 Fragment 1, Section 1
- Paper §2.1
-/

import FdrsFormal.Core.Primitives.RadixSeq
import FdrsFormal.Core.Primitives.Digit
import FdrsFormal.Core.Primitives.PlaceValue
