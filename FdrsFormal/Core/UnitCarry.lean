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

# Unit Carry Decomposition (Irrational Case)

Defines the carry structure induced by repeated addition of a part inside
the unit interval. For irrational a ∈ (0,1):
- fitCount N(a) = ⌊1/a⌋ — how many copies fit before overflow
- completionResidue ρ(a) = 1 - N(a)·a — the gap to unity
- overflowCarry ω(a) = (N(a)+1)·a - 1 — the spill past unity

The last copy of a splits into ρ(a) (completing the unit) and ω(a) (carrying
forward), satisfying ρ(a) + ω(a) = a.

## Mathematical Content (fdrs.md §12.2)

**Definition 177**: fitCount, completionResidue, overflowCarry
**Proposition 141**: Basic carry arithmetic
**Proposition 142**: Irrational sharpening
**Proposition 143**: Greater/lesser part specialization

## References

- fdrs.md, Phase 12, Section 12.2
-/

import FdrsFormal.Core.UnitComplement
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace FdrsFormal.Core

/-! ## Definition 177: Fit count, completion residue, overflow carry -/

/--
**fdrs.md**: Definition 177 (fit count) [§12.2.1 · Phase 12]

The fit count of a ∈ (0,1): how many full copies of a fit in the unit.
N(a) = ⌊1/a⌋.
-/
noncomputable def fitCount (a : ℝ) : ℕ := ⌊1 / a⌋₊

/--
**fdrs.md**: Definition 177 (completion residue) [§12.2.1 · Phase 12]

The gap between N(a) copies and the unit: ρ(a) = 1 - N(a) · a.
-/
noncomputable def completionResidue (a : ℝ) : ℝ := 1 - (fitCount a : ℝ) * a

/--
**fdrs.md**: Definition 177 (overflow carry) [§12.2.1 · Phase 12]

The spill past the unit from one additional copy: ω(a) = (N(a)+1) · a - 1.
-/
noncomputable def overflowCarry (a : ℝ) : ℝ := ((fitCount a : ℝ) + 1) * a - 1

/-! ## Proposition 141: Basic carry arithmetic -/

namespace UnitCarry

variable {x a : ℝ}

/--
**fdrs.md**: Proposition 141(1) [§12.2.2 · Phase 12]

The maximal non-overflowing stack fits: N(a) · a ≤ 1.
-/
theorem fitCount_mul_le (ha : 0 < a) : (fitCount a : ℝ) * a ≤ 1 := by
  have hle := Nat.floor_le (show (0 : ℝ) ≤ 1 / a by positivity)
  calc (fitCount a : ℝ) * a ≤ 1 / a * a :=
        mul_le_mul_of_nonneg_right hle (le_of_lt ha)
    _ = 1 := div_mul_cancel₀ 1 ha.ne'

/--
**fdrs.md**: Proposition 141(2) [§12.2.2 · Phase 12]

One more copy overflows: (N(a)+1) · a > 1.
-/
theorem fitCount_succ_mul_gt (ha : 0 < a) : 1 < ((fitCount a : ℝ) + 1) * a := by
  have hlt : 1 / a < (↑⌊1 / a⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (1 / a)
  calc 1 = 1 / a * a := (div_mul_cancel₀ 1 ha.ne').symm
    _ < ((fitCount a : ℝ) + 1) * a := by
        apply mul_lt_mul_of_pos_right _ ha
        exact_mod_cast hlt

/--
For a ∈ (0,1), at least one copy fits: N(a) ≥ 1.
-/
theorem fitCount_ge_one (ha0 : 0 < a) (ha1 : a < 1) : 1 ≤ fitCount a := by
  apply Nat.le_floor
  rw [Nat.cast_one, le_div_iff₀ ha0]
  linarith

/--
**fdrs.md**: Proposition 141(3) [§12.2.2 · Phase 12]

The carry sum law: ω(a) = a - ρ(a).
-/
@[simp]
theorem overflowCarry_eq_sub (a : ℝ) :
    overflowCarry a = a - completionResidue a := by
  simp only [overflowCarry, completionResidue]; ring

/--
The last copy splits: ρ(a) + ω(a) = a.
-/
theorem completionResidue_add_overflowCarry (a : ℝ) :
    completionResidue a + overflowCarry a = a := by
  simp only [completionResidue, overflowCarry]; ring

/--
The stack equation: N(a) · a + ρ(a) = 1.
-/
theorem fitCount_mul_add_residue (a : ℝ) :
    (fitCount a : ℝ) * a + completionResidue a = 1 := by
  simp only [completionResidue]; ring

/--
The overflow equation: (N(a)+1) · a = 1 + ω(a).
-/
theorem fitCount_succ_mul_eq (a : ℝ) :
    ((fitCount a : ℝ) + 1) * a = 1 + overflowCarry a := by
  simp only [overflowCarry]; ring

/-! ## Proposition 142: Irrational sharpening -/

/--
**fdrs.md**: Proposition 142(1) [§12.2.3 · Phase 12]

For irrational a, the stack never exactly hits 1: N(a) · a < 1.
(If it did, a = 1/N would be rational.)
-/
theorem fitCount_mul_lt (ha : 0 < a) (hirr : Irrational a) :
    (fitCount a : ℝ) * a < 1 := by
  refine lt_of_le_of_ne (fitCount_mul_le ha) fun h => ?_
  have hN : fitCount a ≠ 0 := by
    intro hN0; rw [hN0] at h; simp at h
  have hNr : (fitCount a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have ha_eq : a = 1 / (fitCount a : ℝ) := by
    field_simp at h ⊢; linarith
  exact hirr ⟨1 / (fitCount a : ℚ), by push_cast [hNr]; linarith⟩

/--
**fdrs.md**: Proposition 142(2) [§12.2.3 · Phase 12]

The completion residue is positive for irrational a: 0 < ρ(a).
-/
theorem completionResidue_pos (ha : 0 < a) (hirr : Irrational a) :
    0 < completionResidue a := by
  simp only [completionResidue]; linarith [fitCount_mul_lt ha hirr]

/--
The completion residue is strictly less than a: ρ(a) < a.
-/
theorem completionResidue_lt (ha : 0 < a) : completionResidue a < a := by
  simp only [completionResidue]; linarith [fitCount_succ_mul_gt ha]

/--
The overflow carry is positive: 0 < ω(a).
-/
theorem overflowCarry_pos (ha : 0 < a) : 0 < overflowCarry a := by
  simp only [overflowCarry]; linarith [fitCount_succ_mul_gt ha]

/--
**fdrs.md**: Proposition 142(3) [§12.2.3 · Phase 12]

For irrational a, the carry is strictly less than a: ω(a) < a.
-/
theorem overflowCarry_lt (ha : 0 < a) (hirr : Irrational a) :
    overflowCarry a < a := by
  rw [overflowCarry_eq_sub]; linarith [completionResidue_pos ha hirr]

/-! ## Proposition 143: Greater/lesser part specialization -/

/-- Irrational x ≠ 1/2 (since 1/2 is rational). -/
theorem irrational_ne_half (hirr : Irrational x) : x ≠ 1 / 2 := by
  intro h; exact hirr ⟨1 / 2, by push_cast; linarith⟩

/-- The lesser part of an irrational x ∈ (0,1) is irrational. -/
theorem irrational_lesserPart (_hx0 : 0 < x) (_hx1 : x < 1)
    (hirr : Irrational x) : Irrational (lesserPart x) := by
  simp only [lesserPart]
  by_cases h : x ≤ 1 - x
  · rw [min_eq_left h]; exact hirr
  · push_neg at h; rw [min_eq_right (le_of_lt h)]
    intro ⟨q, hq⟩; exact hirr ⟨1 - q, by push_cast; linarith⟩

/-- The greater part of an irrational x ∈ (0,1) is irrational. -/
theorem irrational_greaterPart (_hx0 : 0 < x) (_hx1 : x < 1)
    (hirr : Irrational x) : Irrational (greaterPart x) := by
  simp only [greaterPart]
  by_cases h : 1 - x ≤ x
  · rw [max_eq_left h]; exact hirr
  · push_neg at h; rw [max_eq_right (le_of_lt h)]
    intro ⟨q, hq⟩; exact hirr ⟨1 - q, by push_cast; linarith⟩

/-- The lesser part of x ∈ (0,1) is positive. -/
theorem lesserPart_pos' (hx0 : 0 < x) (hx1 : x < 1) :
    0 < lesserPart x := by
  simp only [lesserPart]; exact lt_min hx0 (by linarith)

/-- The lesser part of an irrational x ∈ (0,1) is strictly below 1/2. -/
theorem lesserPart_lt_half (_hx0 : 0 < x) (_hx1 : x < 1)
    (hirr : Irrational x) : lesserPart x < 1 / 2 := by
  simp only [lesserPart]
  have hne := irrational_ne_half hirr
  rcases lt_or_gt_of_ne hne with h | h
  · rw [min_eq_left (by linarith : x ≤ 1 - x)]; linarith
  · rw [min_eq_right (by linarith : 1 - x ≤ x)]; linarith

/-- The greater part of an irrational x ∈ (0,1) is strictly above 1/2. -/
theorem greaterPart_gt_half (_hx0 : 0 < x) (_hx1 : x < 1)
    (hirr : Irrational x) : 1 / 2 < greaterPart x := by
  simp only [greaterPart]
  have hne := irrational_ne_half hirr
  rcases lt_or_gt_of_ne hne with h | h
  · rw [max_eq_right (by linarith : x ≤ 1 - x)]; linarith
  · rw [max_eq_left (by linarith : 1 - x ≤ x)]; linarith

/-- The greater part of x ∈ (0,1) is strictly below 1. -/
theorem greaterPart_lt_one' (hx0 : 0 < x) (hx1 : x < 1) :
    greaterPart x < 1 := by
  simp only [greaterPart]; exact max_lt hx1 (by linarith)

/--
**fdrs.md**: Proposition 143(1) [§12.2.4 · Phase 12]

The fit count of the greater part is exactly 1: N(g) = 1.
Since 1/2 < g < 1, we have 1 < 1/g < 2, so ⌊1/g⌋ = 1.
-/
theorem fitCount_greaterPart (hx0 : 0 < x) (hx1 : x < 1)
    (hirr : Irrational x) : fitCount (greaterPart x) = 1 := by
  have hg_gt := greaterPart_gt_half hx0 hx1 hirr
  have hg_lt := greaterPart_lt_one' hx0 hx1
  have hg_pos : (0 : ℝ) < greaterPart x := by linarith
  apply le_antisymm
  · -- upper: fitCount ≤ 1 because 1/g < 2
    by_contra h; push_neg at h
    -- h : 2 ≤ fitCount (greaterPart x)
    have h2 : (2 : ℝ) ≤ (fitCount (greaterPart x) : ℝ) := by exact_mod_cast h
    have h3 : (fitCount (greaterPart x) : ℝ) ≤ 1 / greaterPart x :=
      Nat.floor_le (by positivity)
    have h4 : (2 : ℝ) ≤ 1 / greaterPart x := le_trans h2 h3
    have h5 : 2 * greaterPart x ≤ 1 := by
      rwa [le_div_iff₀ hg_pos] at h4
    linarith
  · -- lower: 1 ≤ fitCount because g < 1
    exact fitCount_ge_one hg_pos hg_lt

/--
**fdrs.md**: Proposition 143(2) [§12.2.4 · Phase 12]

The completion residue of the greater part equals the lesser part: ρ(g) = ℓ.
-/
theorem completionResidue_greaterPart (hx0 : 0 < x) (hx1 : x < 1)
    (hirr : Irrational x) :
    completionResidue (greaterPart x) = lesserPart x := by
  simp only [completionResidue, fitCount_greaterPart hx0 hx1 hirr, Nat.cast_one, one_mul]
  linarith [UnitComplement.lesserPart_add_greaterPart x]

/--
**fdrs.md**: Proposition 143(3) [§12.2.4 · Phase 12]

The overflow carry of the greater part: ω(g) = 2g - 1.
-/
theorem overflowCarry_greaterPart (hx0 : 0 < x) (hx1 : x < 1)
    (hirr : Irrational x) :
    overflowCarry (greaterPart x) = 2 * greaterPart x - 1 := by
  simp only [overflowCarry, fitCount_greaterPart hx0 hx1 hirr]; push_cast; ring

/--
**fdrs.md**: Proposition 143(4) [§12.2.4 · Phase 12]

The fit count of the lesser part is at least 2: N(ℓ) ≥ 2.
Since 0 < ℓ < 1/2, we have 1/ℓ > 2, so ⌊1/ℓ⌋ ≥ 2.
-/
theorem fitCount_lesserPart_ge (hx0 : 0 < x) (hx1 : x < 1)
    (hirr : Irrational x) : 2 ≤ fitCount (lesserPart x) := by
  have hl_pos := lesserPart_pos' hx0 hx1
  have hl_half := lesserPart_lt_half hx0 hx1 hirr
  apply Nat.le_floor
  rw [Nat.cast_ofNat, le_div_iff₀ hl_pos]
  linarith

end UnitCarry

end FdrsFormal.Core
