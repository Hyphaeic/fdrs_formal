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

# Transfer Semantics

This file defines transfer types for residue flow between timelines.

## Mathematical Content (fdrs.md lines 6011-6029)

**Definition 113 (Transfer types)**:

1. **TOTAL**: Complete transfer with source reset
   residue_A → residue_B, state_A ← 0

2. **PARTIAL(π)**: Projected transfer with remainder retention
   π(residue_A) → residue_B, state_A ← (1-π)(residue_A)

3. **COPY**: Duplication without source modification
   residue_A → residue_B, state_A unchanged

4. **SPAWN(Ω_new, τ₀)**: Create new timeline with initial configuration

5. **TERMINATE**: Destroy source timeline with final residue transfer

## References

- fdrs.md, Phase 8, Section 8.2 (lines 6011-6029)
-/

import FdrsFormal.Composition.Junctions.Types

namespace FdrsFormal.Composition.Junctions

/-!
## Transfer Type Enumeration
-/

/--
Transfer type specifying residue flow semantics.

**fdrs.md Definition 113 (lines 6012-6029)**: Five transfer modes.

**Axiomatized**: Full semantics require state space formalization.
-/
inductive TransferType where
  | TOTAL
  | PARTIAL (projection : ℕ → ℕ)
  | COPY
  | SPAWN (newTimelineId : ℕ) (initialState : ℕ)
  | TERMINATE

/-!
## Transfer Semantics
-/

/--
Apply transfer according to type.

**fdrs.md lines 6015-6028**: Each transfer type has specific state update rules.

**Axiomatized**: Requires state space and residue formalization.
-/
def applyTransfer (τ : TransferType) (sourceResidue : ℕ) (sourceState : ℕ) :
    ℕ × ℕ :=  -- (new source state, transferred payload)
  match τ with
  | .TOTAL => (0, sourceResidue)
  | .PARTIAL projection => (sourceResidue - projection sourceResidue, projection sourceResidue)
  | .COPY => (sourceState, sourceResidue)
  | .SPAWN _ _ => (sourceState, 0)
  | .TERMINATE => (0, sourceResidue)

/--
TOTAL transfer resets source.

**fdrs.md line 6016**: Complete transfer, source ← 0.
-/
theorem totalTransfer_resets_source (sourceResidue sourceState : ℕ) :
    (applyTransfer TransferType.TOTAL sourceResidue sourceState).1 = 0 := rfl

/--
COPY transfer preserves source.

**fdrs.md line 6021**: Duplication, source unchanged.
-/
theorem copyTransfer_preserves_source (sourceResidue sourceState : ℕ) :
    (applyTransfer TransferType.COPY sourceResidue sourceState).1 = sourceState := rfl

end FdrsFormal.Composition.Junctions
