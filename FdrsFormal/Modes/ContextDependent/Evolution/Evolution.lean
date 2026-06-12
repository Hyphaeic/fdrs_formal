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

# Evolution Module

Aggregator for context evolution definitions.

## Contents

- `ContextDynamics`: Definition 88 - Γ: 𝒞 × ℰ → 𝒞
- `StatefulSystem`: Definition 89 - (Ω, 𝒞, c₀, Γ, ℰ)
- `Trace`: Definition 90 - Event sequences and context traces
- `Preservation`: Theorem 45 - CSU preserved under context switching

## References

- fdrs.md, Phase 7, Section 7.2 (lines 5540-5599)
-/

import FdrsFormal.Modes.ContextDependent.Evolution.ContextDynamics
import FdrsFormal.Modes.ContextDependent.Evolution.StatefulSystem
import FdrsFormal.Modes.ContextDependent.Evolution.Trace
import FdrsFormal.Modes.ContextDependent.Evolution.Preservation
