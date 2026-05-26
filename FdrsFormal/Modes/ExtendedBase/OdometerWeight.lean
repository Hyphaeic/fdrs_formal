import FdrsFormal.Modes.ExtendedBase.ArithmeticCylinder

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

# Extended Odometer Weight

Defines the extended odometer weight β_ω(s) and proves that base-0 and
base-1 positions contribute factor 1.

## Mathematical Content (fdrs.md lines 7007-7014)

**Proposition 124 (Extended β_ω(s))**:
For prefix s of length |s| = L:
  β_ω(s) := ∏_{i=0}^{L-1} b̃_ω(s_{<i})
Base-1 and base-0 positions contribute factor 1.

## References

-- fdrs.md lines 7007-7015, Proposition 124
- fdrs.md, Phase 9, Section 9.5.2 (lines 7007-7014)
-/

namespace FdrsFormal.Modes.ExtendedBase

/-! ## Proposition 124: Extended odometer weight -/

/--
**fdrs.md**: Proposition 124 (Extended β_ω(s)) [§9.5.2 · Phase 9] (lines 7007-7014)

The extended odometer weight for a prefix of length L:
  β_ω(s) := ∏_{i=0}^{L-1} b̃_ω(s_{<i}) = generalizedPlaceValue b L

This is exactly the generalized cumulative radix product (Definition 139)
applied to the extended base sequence.
-/
def extendedOdometerWeight (b : ℕ → ℕ) (L : ℕ) : ℕ :=
  generalizedPlaceValue b L

/-- The extended odometer weight is at least 1. -/
theorem extendedOdometerWeight_ge_one (b : ℕ → ℕ) (L : ℕ) :
    extendedOdometerWeight b L ≥ 1 := by
  exact placeValue_ge_one b L

/-- The extended odometer weight is monotone in the prefix length. -/
theorem extendedOdometerWeight_monotone (b : ℕ → ℕ) (L : ℕ) :
    extendedOdometerWeight b L ≤ extendedOdometerWeight b (L + 1) := by
  exact placeValue_monotone b L

/--
Base-0 positions contribute factor 1 to the odometer weight.
Since effectiveBase(0) = max(0, 1) = 1.
-/
theorem extendedOdometerWeight_base0_factor (b : ℕ → ℕ) (i : ℕ) (h : b i = 0) :
    effectiveBase b i = 1 := by
  exact effectiveBase_eq_one_of_lt_two (by omega)

/--
Base-1 positions contribute factor 1 to the odometer weight.
Since effectiveBase(1) = max(1, 1) = 1.
-/
theorem extendedOdometerWeight_base1_factor (b : ℕ → ℕ) (i : ℕ) (h : b i = 1) :
    effectiveBase b i = 1 := by
  exact effectiveBase_eq_one_of_lt_two (by omega)

/--
The extended odometer weight equals the product over capacity positions only
(positions with base ≥ 2). This follows directly from Proposition 125.
-/
theorem extendedOdometerWeight_eq_capacity_prod (b : ℕ → ℕ) (L : ℕ) :
    extendedOdometerWeight b L =
    ((Finset.range L).filter (fun i => 2 ≤ b i)).prod b := by
  exact generalizedPlaceValue_eq_capacity_prod b L

end FdrsFormal.Modes.ExtendedBase
