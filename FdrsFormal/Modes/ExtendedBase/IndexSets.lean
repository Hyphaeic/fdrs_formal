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

# Extended Base Index Sets

Active index set, capacity index set, and effective base for generalized radix sequences.

## Mathematical Content (fdrs.md lines 6894-6907)

**Definition 137**: Active and capacity index sets
**Definition 138**: Effective base b̃_i = max(b_i, 1)

## References

- fdrs.md, Phase 9, Section 9.1 (lines 6894-6907)
- DEPENDENCY_BASED_STRUCTURE.md, Tier 20
-/

import FdrsFormal.Modes.ExtendedBase.Definition

namespace FdrsFormal.Modes.ExtendedBase

/-! ## Definition 137: Active and capacity index sets -/

/--
**fdrs.md**: Definition 137 (Active and capacity index sets) [§9.1.3 · Phase 9] (lines 6894-6898)

For a generalized radix sequence b:
- Active index set: I_active := {i ≥ 0 : b_i ≥ 1}
- Capacity index set: I_capacity := {i ≥ 0 : b_i ≥ 2}
-/
def activeIndices (b : ℕ → ℕ) : Set ℕ := {i | b i ≥ 1}

def capacityIndices (b : ℕ → ℕ) : Set ℕ := {i | b i ≥ 2}

/-! ## Definition 138: Effective base -/

/--
**fdrs.md**: Definition 138 (Effective base) [§9.1.4 · Phase 9] (lines 6900-6907)

Define the effective base function:
  b̃_i := max(b_i, 1)

This ensures place value products remain well-defined and monotone.
-/
def effectiveBase (b : ℕ → ℕ) (i : ℕ) : ℕ := max (b i) 1

theorem effectiveBase_ge_one (b : ℕ → ℕ) (i : ℕ) : effectiveBase b i ≥ 1 := by
  unfold effectiveBase
  omega

end FdrsFormal.Modes.ExtendedBase
