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

# Characters Module

Additive and multiplicative (Dirichlet) characters with orthogonality and CRT.

## Contents

1. **AdditiveCharacters**: Characters on ℤ/Nℤ, orthogonality, residue projectors
2. **DirichletCharacters**: Multiplicative characters, dual orthogonality
3. **CRT**: Factorization of characters and projectors under Chinese Remainder Theorem

## Mathematical References

- fdrs.md, Phase 3 Fragment 2 (lines 1769-1942)

## Status

Built and machine-checked against Mathlib; the early "axiomatized/STUB" labels are
obsolete (this module has no axioms). Run `python3 scripts/fdrs-summary` for the live,
authoritative status — axioms, sorries, and any remaining scaffold declarations —
rather than relying on counts written here.
-/

import FdrsFormal.NumberTheory.Characters.AdditiveCharacters
import FdrsFormal.NumberTheory.Characters.DirichletCharacters
import FdrsFormal.NumberTheory.Characters.CRT
import FdrsFormal.NumberTheory.Characters.TwistTransform
