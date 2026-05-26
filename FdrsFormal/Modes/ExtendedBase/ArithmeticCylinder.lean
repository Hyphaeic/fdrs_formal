import FdrsFormal.Modes.ExtendedBase.PlaceValues

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

# Arithmetic-Cylinder Property Extension

Proves that divisibility conditions on generalized place values reduce
to products over capacity positions only (base ≥ 2).

## Mathematical Content (fdrs.md lines 7016-7023)

**Proposition 125 (Arithmetic-cylinder property extension)**:
The condition "q | β_ω(s)" reduces to:
  q divides ∏_{i<L, b_ω(s_{<i}) ≥ 2} b_ω(s_{<i})
Only capacity positions contribute to divisibility conditions.

## References

-- fdrs.md lines 7016-7028, Proposition 125
- fdrs.md, Phase 9, Section 9.5.3 (lines 7016-7023)
-/

namespace FdrsFormal.Modes.ExtendedBase

/-! ## Helper lemmas for effectiveBase -/

/-- When base ≥ 2, the effective base equals the actual base. -/
theorem effectiveBase_eq_of_ge_two {b : ℕ → ℕ} {i : ℕ} (h : 2 ≤ b i) :
    effectiveBase b i = b i := by
  unfold effectiveBase; omega

/-- When base < 2, the effective base is 1 (contributes nothing to products). -/
theorem effectiveBase_eq_one_of_lt_two {b : ℕ → ℕ} {i : ℕ} (h : b i < 2) :
    effectiveBase b i = 1 := by
  unfold effectiveBase; omega

/-! ## Generalized place value as Finset product -/

/-- Generalized place value equals the product of effective bases over range. -/
theorem generalizedPlaceValue_eq_prod (b : ℕ → ℕ) (n : ℕ) :
    generalizedPlaceValue b n = (Finset.range n).prod (effectiveBase b) := by
  induction n with
  | zero => simp [generalizedPlaceValue]
  | succ n ih =>
    simp [generalizedPlaceValue, Finset.prod_range_succ, ih]

/-! ## Proposition 125: Arithmetic-cylinder property extension -/

/--
**fdrs.md**: Proposition 125 (Arithmetic-cylinder property extension) [§9.5.3 · Phase 9] (lines 7016-7023)

The generalized place value equals the product over capacity positions only:
  B_L = ∏_{i < L, b_i ≥ 2} b_i

since positions with b_i < 2 have effectiveBase = 1 and contribute
nothing to the product.

**Proof**: Induction on L. At each step, if b_n ≥ 2 (capacity position),
the factor equals b_n and appears in the filtered product. If b_n < 2,
the factor is 1 and the filtered product is unchanged.
-/
theorem generalizedPlaceValue_eq_capacity_prod (b : ℕ → ℕ) (L : ℕ) :
    generalizedPlaceValue b L =
    ((Finset.range L).filter (fun i => 2 ≤ b i)).prod b := by
  induction L with
  | zero => simp [generalizedPlaceValue]
  | succ n ih =>
    rw [generalizedPlaceValue, ih, Finset.range_add_one, Finset.filter_insert]
    by_cases h : 2 ≤ b n
    · simp only [h, ↓reduceIte]
      rw [Finset.prod_insert]
      · rw [effectiveBase_eq_of_ge_two h, mul_comm]
      · simp [Finset.mem_filter, Finset.mem_range]
    · simp only [h, ↓reduceIte]
      rw [effectiveBase_eq_one_of_lt_two (by omega), mul_one]

/--
Corollary: divisibility conditions on β_ω(s) reduce to capacity positions.

q | B_L ↔ q | ∏_{i < L, b_i ≥ 2} b_i
-/
theorem arithmeticCylinderExtension (b : ℕ → ℕ) (L : ℕ) (q : ℕ) :
    q ∣ generalizedPlaceValue b L ↔
    q ∣ ((Finset.range L).filter (fun i => 2 ≤ b i)).prod b := by
  rw [generalizedPlaceValue_eq_capacity_prod]

end FdrsFormal.Modes.ExtendedBase
