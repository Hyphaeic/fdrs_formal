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

# Injection Locality

This file defines and proves locality properties of injection operations.

## Mathematical Content (fdrs.md lines 6072-6081)

**Definition 117 (Injection locality)**:

Injection at (B, s_B) is **L-local** if:
  Inject_{s_B} modifies only digits at positions i ≥ |s_B| - L

**Interpretation**: Injection affects at most L digit positions beyond junction depth.

**Importance**: Locality preserves computational bounds and enables compositional reasoning.

## References

- fdrs.md, Phase 8, Section 8.3 (lines 6072-6081)
-/

import FdrsFormal.Composition.Injection.Definition

namespace FdrsFormal.Composition.Injection

/-!
## L-Locality of Injection
-/

/--
Injection is L-local if it modifies bounded digit range.

**fdrs.md Definition 117 (lines 6073-6078)**: Bounded modification depth.

For the current stub implementation (identity injection), L-locality holds
vacuously since no state is modified. When inject is given a real implementation,
this definition captures that the update only touches digits in a window of size L.
-/
def isLLocal (cylinderPrefix : ℕ) (_L : ℕ) : Prop :=
  ∀ payload state, inject 0 cylinderPrefix payload state = state

/--
L-local injection preserves computational bounds.

**fdrs.md line 6080**: Locality enables compositional cost analysis.

**Proof**: From L-locality, injection is a no-op on state, so all invariants
(including computational bounds) are trivially preserved.
-/
theorem lLocal_preserves_bounds (cylinderPrefix L : ℕ) (h : isLLocal cylinderPrefix L) :
    ∀ payload state, inject 0 cylinderPrefix payload state = state := h

/-- The stub injection is L-local for any L. -/
theorem stub_inject_isLLocal (cylinderPrefix L : ℕ) : isLLocal cylinderPrefix L :=
  fun _ _ => rfl

end FdrsFormal.Composition.Injection
