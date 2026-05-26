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

# Unit Complement

Defines the additive complement-to-unity structure on the closed unit
interval [0,1]. For x ∈ [0,1], the unit complement is 1 - x,
satisfying the complement sum law x + (1 - x) = 1.

## Mathematical Content (fdrs.md §12.1)

**Definition 175 (unit complement)**: comp(x) = 1 - x
**Definition 176 (unit pair and parts)**: pair(x) = (x, 1 - x),
  lesser(x) = min(x, 1 - x), greater(x) = max(x, 1 - x)
**Proposition 139 (complement properties)**: closure, involution, fixed point
**Proposition 140 (ordering split)**: lesser/greater part dichotomy

## References

- fdrs.md, Phase 12, Section 12.1
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace FdrsFormal.Core

/-! ## Definition 175: Unit complement -/

/--
**fdrs.md**: Definition 175 (unit complement) [§12.1.1 · Phase 12]

For x ∈ ℝ, define comp(x) = 1 - x.
The defining law is the complement sum: x + comp(x) = 1.
-/
noncomputable def unitComplement (x : ℝ) : ℝ := 1 - x

/-! ## Definition 176: Unit pair and parts -/

/--
**fdrs.md**: Definition 176 (unit pair) [§12.1.2 · Phase 12]

For x ∈ ℝ, define pair(x) = (x, 1 - x).
-/
noncomputable def unitPair (x : ℝ) : ℝ × ℝ := (x, 1 - x)

/--
The lesser part of a unit decomposition: min(x, 1 - x).
-/
noncomputable def lesserPart (x : ℝ) : ℝ := min x (1 - x)

/--
The greater part of a unit decomposition: max(x, 1 - x).
-/
noncomputable def greaterPart (x : ℝ) : ℝ := max x (1 - x)

/-! ## Proposition 139: Complement properties -/

namespace UnitComplement

variable {x : ℝ}

/--
**fdrs.md**: Proposition 139(1) (closure) [§12.1.3 · Phase 12]

The unit complement preserves membership in [0,1].
-/
theorem mem_Icc (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    unitComplement x ∈ Set.Icc (0 : ℝ) 1 := by
  simp only [unitComplement, Set.mem_Icc]
  constructor <;> linarith [hx.1, hx.2]

/--
**fdrs.md**: Proposition 139(1) (complement sum) [§12.1.3 · Phase 12]

The complement sum law: x + (1 - x) = 1.
-/
@[simp]
theorem add_comp (x : ℝ) : x + unitComplement x = 1 := by
  simp [unitComplement]

/--
The complement sum law (reversed): (1 - x) + x = 1.
-/
@[simp]
theorem comp_add (x : ℝ) : unitComplement x + x = 1 := by
  simp [unitComplement]

/--
**fdrs.md**: Proposition 139(2) (involution) [§12.1.3 · Phase 12]

The unit complement is an involution: comp(comp(x)) = x.
-/
@[simp]
theorem involutive (x : ℝ) : unitComplement (unitComplement x) = x := by
  simp [unitComplement]

/--
The unit complement function is involutive.
-/
theorem function_involutive : Function.Involutive unitComplement := fun x => involutive x

/--
**fdrs.md**: Proposition 139(3) (fixed point) [§12.1.3 · Phase 12]

The unique fixed point of the unit complement is 1/2:
comp(x) = x ↔ x = 1/2.
-/
theorem fixedPoint_iff (x : ℝ) : unitComplement x = x ↔ x = 1 / 2 := by
  simp only [unitComplement]
  constructor <;> intro h <;> linarith

/-! ## Proposition 140: Ordering split -/

/--
**fdrs.md**: Proposition 140(1) [§12.1.4 · Phase 12]

If x < 1/2, then x < comp(x).
-/
theorem lt_comp_of_lt_half (h : x < 1 / 2) : x < unitComplement x := by
  simp only [unitComplement]; linarith

/--
**fdrs.md**: Proposition 140(2) [§12.1.4 · Phase 12]

If x = 1/2, then x = comp(x).
-/
theorem eq_comp_of_eq_half (h : x = 1 / 2) : x = unitComplement x := by
  simp only [unitComplement]; linarith

/--
**fdrs.md**: Proposition 140(3) [§12.1.4 · Phase 12]

If x > 1/2, then x > comp(x).
-/
theorem gt_comp_of_gt_half (h : x > 1 / 2) : x > unitComplement x := by
  simp only [unitComplement]; linarith

/-! ## Lesser/Greater part properties -/

/--
**fdrs.md**: Proposition 140(4) [§12.1.4 · Phase 12]

The lesser and greater parts sum to 1.
-/
theorem lesserPart_add_greaterPart (x : ℝ) : lesserPart x + greaterPart x = 1 := by
  simp only [lesserPart, greaterPart]
  by_cases h : x ≤ 1 - x
  · rw [min_eq_left h, max_eq_right h]; ring
  · push_neg at h
    rw [min_eq_right (le_of_lt h), max_eq_left (le_of_lt h)]; ring

/--
The lesser part is at most the greater part.
-/
theorem lesserPart_le_greaterPart (x : ℝ) : lesserPart x ≤ greaterPart x := by
  simp only [lesserPart, greaterPart]
  exact min_le_max

/--
For x ∈ [0,1], the lesser part is non-negative.
-/
theorem lesserPart_nonneg (hx : x ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ lesserPart x := by
  simp only [lesserPart]
  exact le_min hx.1 (by linarith [hx.2])

/--
For x ∈ [0,1], the greater part is at most 1.
-/
theorem greaterPart_le_one (hx : x ∈ Set.Icc (0 : ℝ) 1) : greaterPart x ≤ 1 := by
  simp only [greaterPart]
  exact max_le hx.2 (by linarith [hx.1])

/-! ## Unit pair properties -/

/--
The components of the unit pair sum to 1.
-/
theorem unitPair_sum (x : ℝ) : (unitPair x).1 + (unitPair x).2 = 1 := by
  simp [unitPair]

/--
The unit pair under complement swaps components.
-/
theorem unitPair_comp (x : ℝ) :
    unitPair (unitComplement x) = (unitComplement x, x) := by
  simp [unitPair, unitComplement]

end UnitComplement

end FdrsFormal.Core
