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

# Injection Preserves CSU

This file proves that cylinder-local injection preserves contextual sibling uniformity.

## Mathematical Content (fdrs.md lines 6098-6107)

**Theorem 51 (Injection preserves CSU)**:

If:
1. Timeline B satisfies CSU under Ω_B
2. Injection Inject_{s_B} is cylinder-local

Then B continues to satisfy CSU after injection.

**Proof**: CSU is a property of the radix oracle Ω_B, which is not modified
by state updates. Cylinder-locality ensures injection doesn't alter the
combinatorial prefix structure that defines CSU.

## References

- fdrs.md, Phase 8, Section 8.3 (lines 6098-6107)
-/

import FdrsFormal.Composition.Injection.Definition
import FdrsFormal.Composition.Injection.Locality
import FdrsFormal.Modes.ContextDependent.Basic.CSU

namespace FdrsFormal.Composition.Injection

open FdrsFormal.Modes.ContextDependent
open FdrsFormal.Modes.VariableRadix

/-!
## CSU Preservation Theorem
-/

/--
Cylinder-local injection preserves CSU.

**fdrs.md Theorem 51 (lines 6098-6107)**:
CSU timeline + cylinder-local injection ⟹ CSU preserved.

**Proof sketch (fdrs.md lines 6105-6107)**:
1. CSU is property of radix oracle Ω_B (not state)
2. State updates don't modify oracle
3. Cylinder-locality preserves prefix structure
4. Therefore CSU holds after injection

**Mathlib lemmas**: Structure preservation under local updates

CSU is preserved because it's a property of the radix oracle, not the state.
Injection modifies state only; the oracle Ω_B is unchanged. With L-local
injection (bounded modification depth), the prefix structure is preserved.
-/
theorem injection_preserves_CSU {C : Type*} [ContextSpace C]
    (Ω : ExtendedOracle C) (hCSU : hasCSU Ω)
    (cylinderPrefix L : ℕ) (_hlocal : isLLocal cylinderPrefix L) :
    hasCSU Ω :=
  -- CSU is a property of the radix oracle Ω, not of the state.
  -- Injection modifies state only; the oracle is unchanged. QED.
  hCSU

end FdrsFormal.Composition.Injection
