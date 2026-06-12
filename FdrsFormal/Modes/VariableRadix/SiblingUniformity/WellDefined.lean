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

# Sibling Uniformity: Well-Definedness

This file proves that sibling uniformity implies well-defined block sizes.

## Mathematical Content (fdrs.md lines 4698-4720)

**Proposition 87 (Constant block sizes)**:
If ω is SU at depth k, then for each prefix s, the block size
B_ω(s) := W^{(k)}_ω(s∥d) is well-defined (independent of d).

This allows us to define a uniform block size function.

## References

- fdrs.md, Phase 5-6, Section 1 (lines 4698-4720)
-/

import FdrsFormal.Modes.VariableRadix.SiblingUniformity.Definition

namespace FdrsFormal.Modes.VariableRadix

/-!
## Block Size Function
-/

/--
The block size at prefix s under sibling uniformity.

This is well-defined because SU ensures all children have the same completion count.
-/
noncomputable def blockSize (ω : RadixLaw) (k : ℕ) (s : PrefixWord) : ℕ :=
  if h : s.length < k ∧ 0 < ω.radix s then
    completionCount ω k (s ++ [0])
  else
    1

/--
**Proposition 87**: Under SU, the block size equals the completion count of any child.
-/
theorem blockSize_eq_completionCount (ω : RadixLaw) (k : ℕ)
    (hsu : isSiblingUniform ω k) (s : PrefixWord) (hs : s.length < k)
    (d : ℕ) (hd : d < ω.radix s) :
    blockSize ω k s = completionCount ω k (s ++ [d]) := by
  -- blockSize = completionCount(s ++ [0]) by definition
  unfold blockSize
  have hradix_pos : 0 < ω.radix s := ω.radix_pos s
  simp only [hs, hradix_pos, and_self, ↓reduceDIte]
  -- By SU, completionCount(s ++ [0]) = completionCount(s ++ [d])
  have hsu_s := hsu s (Nat.le_of_lt hs)
  exact hsu_s (Nat.le_of_lt hs) 0 d hradix_pos hd

/-!
## Block Size Properties
-/

/-- Block size is positive -/
theorem blockSize_pos (ω : RadixLaw) (k : ℕ) (s : PrefixWord) :
    0 < blockSize ω k s := by
  unfold blockSize
  split_ifs with h
  · -- Case: s.length < k ∧ 0 < radix s
    exact completionCount_pos ω k (s ++ [0]) (by simp; omega)
  · -- Case: otherwise, blockSize = 1
    exact Nat.one_pos

/-- Completion count factors through block size -/
theorem completionCount_eq_radix_mul_blockSize (ω : RadixLaw) (k : ℕ)
    (hsu : isSiblingUniform ω k) (s : PrefixWord) (hs : s.length < k) :
    completionCount ω k s = ω.radix s * blockSize ω k s := by
  -- completionCount s = ∑_{d < radix s} completionCount(s ++ [d])
  rw [completionCount_rec ω k s (Nat.lt_add_one_of_lt hs)]
  -- Under SU, all terms are equal to blockSize
  have heq : ∀ d ∈ Finset.range (ω.radix s), completionCount ω k (s ++ [d]) = blockSize ω k s := by
    intro d hd
    rw [Finset.mem_range] at hd
    exact (blockSize_eq_completionCount ω k hsu s hs d hd).symm
  rw [Finset.sum_congr rfl heq]
  simp [Finset.sum_const, Finset.card_range]

/-- Block size divides completion count -/
theorem blockSize_dvd_completionCount (ω : RadixLaw) (k : ℕ)
    (hsu : isSiblingUniform ω k) (s : PrefixWord) (hs : s.length ≤ k) :
    blockSize ω k s ∣ completionCount ω k s := by
  by_cases hlt : s.length < k
  · -- Case: s.length < k, use the factorization
    rw [completionCount_eq_radix_mul_blockSize ω k hsu s hlt]
    exact Dvd.intro (ω.radix s) (mul_comm _ _)
  · -- Case: s.length = k (since s.length ≤ k and ¬(s.length < k))
    have heq : s.length = k := Nat.le_antisymm hs (Nat.not_lt.mp hlt)
    -- At length k, completionCount uses the recursive formula with s.length < k+1
    -- But blockSize will be 1 since ¬(s.length < k)
    unfold blockSize
    simp only [hlt, false_and, ↓reduceDIte]
    exact one_dvd _

/-!
## Block Size Monotonicity
-/

/-- Block size decreases with longer prefixes -/
theorem blockSize_mono (ω : RadixLaw) (k : ℕ)
    (hsu : isSiblingUniform ω k) (s : PrefixWord) (d : ℕ)
    (hs : s.length < k) (hd : d < ω.radix s) :
    blockSize ω k (s ++ [d]) ≤ blockSize ω k s := by
  -- Under SU: blockSize(s) = completionCount(s ++ [d])
  have hbs_s : blockSize ω k s = completionCount ω k (s ++ [d]) :=
    blockSize_eq_completionCount ω k hsu s hs d hd
  rw [hbs_s]
  -- Now show: blockSize ω k (s ++ [d]) ≤ completionCount ω k (s ++ [d])
  have hlen_ext : (s ++ [d]).length = s.length + 1 := by simp
  by_cases h : (s ++ [d]).length < k
  · -- Case: s ++ [d] is short enough
    have hradix_pos : 0 < ω.radix (s ++ [d]) := ω.radix_pos _
    -- blockSize(s ++ [d]) = completionCount((s ++ [d]) ++ [0])
    unfold blockSize
    simp only [h, hradix_pos, and_self, ↓reduceDIte]
    -- This is a child of completionCount(s ++ [d]), so ≤
    have hlen_sd : (s ++ [d]).length < k + 1 := Nat.lt_add_one_of_lt h
    rw [completionCount_rec ω k (s ++ [d]) hlen_sd]
    have h0_mem : 0 ∈ Finset.range (ω.radix (s ++ [d])) := by
      simp only [Finset.mem_range]; exact hradix_pos
    exact Finset.single_le_sum (f := fun d' => completionCount ω k ((s ++ [d]) ++ [d']))
      (fun _ _ => Nat.zero_le _) h0_mem
  · -- Case: s ++ [d] is at boundary (length = k), blockSize = 1
    unfold blockSize
    simp only [h, false_and, ↓reduceDIte]
    exact completionCount_pos ω k (s ++ [d]) (by simp; omega)

/-- Block size at depth k is 1 -/
theorem blockSize_at_depth (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k) :
    blockSize ω k τ.digits = 1 := by
  unfold blockSize
  -- τ.digits has length k + 1, so τ.digits.length < k is false
  have hlen : τ.digits.length = k + 1 := τ.length_eq
  have hnotlt : ¬(τ.digits.length < k) := by omega
  simp only [hnotlt, false_and, ↓reduceDIte]

end FdrsFormal.Modes.VariableRadix
