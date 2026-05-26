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

# Realization Module (THEOREM E)

Aggregator for realization strategies and equivalence.

## Contents

- `Strategies`: Definition 92 - Lazy vs eager realization
- `EquivalenceThm`: Theorem 46 - THEOREM E: Lazy-eager equivalence

## Main Result

**THEOREM E (Lazy-Eager Semantic Equivalence)**:
For any finite trace and deterministic access pattern, lazy and eager realization
produce identical observable behavior (same values at accessed locations).

## References

- fdrs.md, Phase 7, Section 7.3 (lines 5601-5636)
- DEPENDENCY_BASED_STRUCTURE.md, Modes/ContextDependent/Realization
- Paper: THEOREM E
-/

import FdrsFormal.Modes.ContextDependent.Realization.Strategies
import FdrsFormal.Modes.ContextDependent.Realization.EquivalenceThm
import FdrsFormal.Modes.ContextDependent.Realization.SemanticModes
