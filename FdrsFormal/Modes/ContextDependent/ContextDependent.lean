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

# Context-Dependent Module (MODE II)

Main aggregator for context-dependent radix systems.

## Overview

This module formalizes **context-dependent radix systems** where the radix
function depends on both the prefix AND external context:

  Ω : Σ* × 𝒞 → ℕ≥2

This generalizes variable radix (MODE I) by allowing the radix to be
determined by external state that evolves over time.

## Contents

### Basic Definitions
- `Basic/`: Context space, extended oracle, CSU

### Evolution
- `Evolution/`: Context dynamics, stateful systems, traces, CSU preservation

### Realization (THEOREM E)
- `Realization/`: Lazy vs eager strategies, semantic equivalence

### Preservation (THEOREM F)
- `Preservation/`: Structure-preserving transitions, operator preservation

### Variations
- `Variations/`: Stochastic contexts, multi-agent systems

## Main Theorems

**THEOREM E** (Lazy-Eager Equivalence): For any finite trace and deterministic
access pattern, lazy and eager realization produce identical observable behavior.
See: `Realization/EquivalenceThm.lean`

**THEOREM F** (Depth-L Operators Preserved): If transition c → c' is
structure-preserving at depth L, then all L-local gates, projections, and
metric structure are invariant.
See: `Preservation/OperatorPreserved.lean`

## Key Properties

- **CSU**: Contextual sibling uniformity - SU holds at each context snapshot
- **Representation Independence**: Lazy/eager choice doesn't affect semantics
- **Safe Context Changes**: Can modify radix at depth > L without affecting depth-L ops

## References

- fdrs.md, Phase 7 (Context-Dependent Radix Systems)
- Paper (external draft): §7, Theorems E and F
-/

-- Basic definitions
import FdrsFormal.Modes.ContextDependent.Basic.Basic

-- Evolution
import FdrsFormal.Modes.ContextDependent.Evolution.Evolution

-- Realization (THEOREM E)
import FdrsFormal.Modes.ContextDependent.Realization.Realization

-- Preservation (THEOREM F)
import FdrsFormal.Modes.ContextDependent.Preservation.Preservation

-- Variations
import FdrsFormal.Modes.ContextDependent.Variations.Variations
