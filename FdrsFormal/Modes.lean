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

# Modes Module

This module aggregates the three generalization modes of FDRS.

## Contents

- **VariableRadix/** (Mode I): Prefix-pure radix laws ω: Σ* → ℕ≥2
  - Theorems A-B (Canonical bijection, Realizability)

- **ContextDependent/** (Mode II): Context-dependent radix laws Ω: Σ* × C → ℕ≥2
  - Theorems E-F (Lazy-eager, Structure preservation)

- **ExtendedBase/** (Mode III): Extended bases with distinguished 0, 1

- **BaseZeroSea/** (Phase 10): Deterministic base-zero sea dynamics

- **Analysis/DigitConditional/** (Phase 11): Digit-conditional signal analysis

## References

- fdrs.md, Phases 5-6 (Modes), Phase 10 (Base-Zero Sea), Phase 11 (Digit-Conditional)
-/

import FdrsFormal.Modes.VariableRadix.VariableRadix
import FdrsFormal.Modes.ContextDependent.ContextDependent
import FdrsFormal.Modes.ExtendedBase
import FdrsFormal.Modes.BaseZeroSea
import FdrsFormal.Analysis.DigitConditional
