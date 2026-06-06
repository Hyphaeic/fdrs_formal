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

# Base-Zero Sea Dynamics (Phase 10)

Deterministic substrate dynamics where:
- base-0 is representational potential,
- base-1 is instantiated occupancy,
- arithmetic structure emerges from controlled creation and reversion events.

## Contents

- **Basic.lean**: Definitions 151-153 (Sea, ObservationProfile, LegacyThread)
- **Dynamics.lean**: Definitions 154-157 (CreateSelector, ConsumeTargetRule, ConsumeSchedule, SeaTick)
- **Properties.lean**: Propositions 126-128, Theorem 62 (determinism, validity, balance law, transition system)
- **Projection.lean**: Definitions 158-159, Theorem 63 (window-to-digit projection, Phase 9 special case)
- **Modules.lean**: Definitions 160-163, Propositions 129-130, Theorem 64 (digit modules, resistance, coupled networks)
- **LinearChain.lean**: `LinearChain`, `linearChainStep`, `chainToCylinder`; Theorem 64 strengthened — the chain step projects to the Phase 9 odometer (`linearChain_projectsTo_odometer`), **fully proven (0 sorries)**, superseding the vacuous `classicalMixedRadixLine`

## References

- fdrs.md, Phase 10, Sections 10.1-10.9 (lines 7181-7477)
-/

import FdrsFormal.Modes.BaseZeroSea.Basic
import FdrsFormal.Modes.BaseZeroSea.Dynamics
import FdrsFormal.Modes.BaseZeroSea.Properties
import FdrsFormal.Modes.BaseZeroSea.Projection
import FdrsFormal.Modes.BaseZeroSea.Modules
import FdrsFormal.Modes.BaseZeroSea.LinearChain
