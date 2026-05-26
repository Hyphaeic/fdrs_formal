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

# Place Values

Defines place values B_m = ∏_{i=0}^{m-1} b_i (cumulative radix products).

## References

- fdrs.md, Phase 1 Fragment 1, Section 1 (lines 9-15)
- Paper §2.1
-/

import FdrsFormal.Core.Primitives.RadixSeq
import FdrsFormal.Core.Primitives.Digit
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace FdrsFormal.Core.Primitives

/-! ## Place Values -/

/-- Place value at position `m`: B_m = ∏_{i=0}^{m-1} b_i
    - B_0 = 1
    - B_{m+1} = B_m * b_m

    This is the "weight" of digit position m in the mixed-radix representation. -/
def placeValue (b : RadixSeq) : ℕ → ℕ
  | 0 => 1
  | m + 1 => placeValue b m * b m

namespace placeValue

variable {b : RadixSeq}

@[simp]
theorem zero : placeValue b 0 = 1 := rfl

@[simp]
theorem succ (m : ℕ) : placeValue b (m + 1) = placeValue b m * b m := rfl

/-- Place value is always positive -/
theorem pos (m : ℕ) : 0 < placeValue b m := by
  induction m with
  | zero => simp
  | succ m ih => simp [Nat.mul_pos ih (b.pos m)]

/-- Place value is at least 1 -/
theorem one_le (m : ℕ) : 1 ≤ placeValue b m :=
  Nat.one_le_of_lt (pos m)

/-- Place value is never zero -/
theorem ne_zero (m : ℕ) : placeValue b m ≠ 0 :=
  Nat.pos_iff_ne_zero.mp (pos m)

/-- Place value is strictly monotone: B_m < B_{m+1} -/
theorem strictMono : StrictMono (placeValue b) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [succ]
  have h : placeValue b n * 1 < placeValue b n * b n :=
    Nat.mul_lt_mul_of_pos_left (b.ge_two n) (pos n)
  simp at h
  exact h

/-- Place value is monotone: m ≤ n → B_m ≤ B_n -/
theorem mono : Monotone (placeValue b) :=
  strictMono.monotone

/-- B_m divides B_n when m ≤ n -/
theorem dvd_of_le {m n : ℕ} (h : m ≤ n) : placeValue b m ∣ placeValue b n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ, succ]
    exact Dvd.dvd.mul_right ih _

/-- Sum of maximum digits equals B_{k+1} - 1.
    This is the key lemma for proving bounds on decoded values.
    When all digits are at their maximum (b_i - 1), the represented value is B_{k+1} - 1. -/
theorem sum_max_digits (k : ℕ) :
    ∑ i : Fin (k + 1), (b i - 1) * placeValue b i = placeValue b (k + 1) - 1 := by
  induction k with
  | zero =>
    rw [Fin.sum_univ_one]
    simp only [Fin.val_zero, zero, Nat.mul_one, succ, Nat.one_mul]
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, succ]
    -- Prove: (B_{k+1} - 1) + (b_{k+1} - 1) * B_{k+1} = B_{k+1} * b_{k+1} - 1
    have hb_ge_2 : 2 ≤ b (k + 1) := b.ge_two (k + 1)
    have hB_pos : 0 < placeValue b (k + 1) := pos (k + 1)
    have hB_ge_1 : 1 ≤ placeValue b (k + 1) := hB_pos
    have hbB_ge_B : placeValue b (k + 1) ≤ b (k + 1) * placeValue b (k + 1) :=
      Nat.le_mul_of_pos_left _ (Nat.zero_lt_of_lt hb_ge_2)
    -- First, show that (b - 1) * B + B = b * B
    have h1 : (b (k + 1) - 1) * placeValue b (k + 1) + placeValue b (k + 1) =
              b (k + 1) * placeValue b (k + 1) := by
      have : b (k + 1) = b (k + 1) - 1 + 1 := (Nat.sub_add_cancel (Nat.one_le_of_lt hb_ge_2)).symm
      rw [this, Nat.add_mul]
      simp
    -- Now combine: (B - 1) + (b - 1) * B = (B - 1) + (b * B - B) = b * B - 1
    calc placeValue b (k + 1) - 1 + (b (k + 1) - 1) * placeValue b (k + 1)
        = (placeValue b (k + 1) - 1) + ((b (k + 1) - 1) * placeValue b (k + 1)) := rfl
      _ = ((b (k + 1) - 1) * placeValue b (k + 1) + placeValue b (k + 1)) - 1 := by
            rw [Nat.add_comm, Nat.add_sub_assoc hB_ge_1]
      _ = b (k + 1) * placeValue b (k + 1) - 1 := by rw [h1]
      _ = placeValue b (k + 1 + 1) - 1 := by
            simp only [succ, Nat.mul_comm (b (k + 1)), Nat.mul_assoc]

/-- Bound on values below B_{k+1}: any digit sequence of length k+1 decodes to less than B_{k+1} -/
theorem sum_digits_lt (k : ℕ) (d : (i : Fin (k + 1)) → Digit b i) :
    ∑ i : Fin (k + 1), (d i : ℕ) * placeValue b i < placeValue b (k + 1) := by
  calc ∑ i : Fin (k + 1), (d i : ℕ) * placeValue b i
      ≤ ∑ i : Fin (k + 1), (b i - 1) * placeValue b i := by
        apply Finset.sum_le_sum
        intro i _
        apply Nat.mul_le_mul_right
        exact Nat.le_sub_one_of_lt (d i).isLt
    _ = placeValue b (k + 1) - 1 := sum_max_digits k
    _ < placeValue b (k + 1) := Nat.sub_lt (pos (k + 1)) Nat.one_pos

end placeValue

end FdrsFormal.Core.Primitives
