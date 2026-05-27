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

# Valuations Module

p-adic valuations, divisibility projectors, and squarefree filtering.

## Contents

1. **Definition**: p-adic valuation v_p(n), divisibility and exact valuation projectors
2. **Squarefree**: Squarefree indicator and product factorization

## Mathematical References

- fdrs.md, Phase 3 Fragment 3 (lines 2044-2142)

## Status

Built and machine-checked against Mathlib; the early "axiomatized/STUB" labels are
obsolete (this module has no axioms). Run `python3 scripts/fdrs-summary` for the live,
authoritative status — axioms, sorries, and any remaining scaffold declarations —
rather than relying on counts written here.
-/

import FdrsFormal.NumberTheory.Valuations.Definition
import FdrsFormal.NumberTheory.Valuations.Squarefree
