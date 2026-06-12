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

# Subtree Cardinalities

This file defines the subtree sizes W^{(k)}_ω(s) used for encoding.

## Mathematical Content (fdrs.md lines 4056-4069)

**Definition 61 (subtree/completion counts)**:
For a finite depth k and prefix s with |s| ≤ k+1, define
  W^{(k)}_ω(s) := |{τ ∈ R^{(k)}_ω : τ starts with s}|

This counts the number of valid completions of prefix s to depth k.

**Recursive formula**:
  W^{(k)}_ω(s) = ∑_{d ∈ D_ω(s)} W^{(k)}_ω(s ++ [d])  if |s| < k+1
  W^{(k)}_ω(s) = 1                                    if |s| = k+1

## References

- fdrs.md, Phase 5-6, Section 3 (lines 4056-4069)
-/

import FdrsFormal.Modes.VariableRadix.Basic.Basic

namespace FdrsFormal.Modes.VariableRadix

/-!
## Subtree Cardinality (Completion Count)
-/

/--
The number of completions of prefix s to depth k.

**fdrs.md Definition 61**: W^{(k)}_ω(s) = |{τ ∈ R^{(k)}_ω : τ starts with s}|

This is computed recursively:
- If |s| = k+1, then W = 1 (s is already a complete path)
- Otherwise, W = ∑_{d ∈ D_ω(s)} W^{(k)}_ω(s ++ [d])
-/
def completionCount (ω : RadixLaw) (k : ℕ) (s : PrefixWord) : ℕ :=
  if h : s.length = k + 1 then 1
  else if hgt : s.length > k + 1 then 0  -- Invalid: prefix too long
  else
    -- Sum over all valid next digits
    have hlt : s.length < k + 1 := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hgt) h
    (Finset.range (ω.radix s)).sum fun d =>
      have : k + 1 - (s ++ [d]).length < k + 1 - s.length := by simp; omega
      completionCount ω k (s ++ [d])
termination_by k + 1 - s.length

/-- A complete prefix has exactly one completion -/
theorem completionCount_of_length_eq (ω : RadixLaw) (k : ℕ) (s : PrefixWord)
    (hs : s.length = k + 1) : completionCount ω k s = 1 := by
  unfold completionCount
  simp only [hs, ↓reduceDIte]

/-- An overlong prefix has no completions -/
theorem completionCount_of_length_gt (ω : RadixLaw) (k : ℕ) (s : PrefixWord)
    (hs : s.length > k + 1) : completionCount ω k s = 0 := by
  unfold completionCount
  simp only [show s.length ≠ k + 1 from Nat.ne_of_gt hs, ↓reduceDIte, hs]

/-- The recursive formula for completion count -/
theorem completionCount_rec (ω : RadixLaw) (k : ℕ) (s : PrefixWord)
    (hs : s.length < k + 1) :
    completionCount ω k s =
      (Finset.range (ω.radix s)).sum fun d => completionCount ω k (s ++ [d]) := by
  conv_lhs => unfold completionCount
  simp only [show s.length ≠ k + 1 from Nat.ne_of_lt hs, ↓reduceDIte,
             show ¬(s.length > k + 1) from Nat.not_lt.mpr (Nat.le_of_lt hs)]

/-- Completion count is positive for valid prefixes -/
theorem completionCount_pos (ω : RadixLaw) (k : ℕ) (s : PrefixWord)
    (hs : s.length ≤ k + 1) : 0 < completionCount ω k s := by
  -- Induction on the "remaining depth" k + 1 - s.length
  obtain ⟨n, hn⟩ : ∃ n, n = k + 1 - s.length := ⟨_, rfl⟩
  induction n using Nat.strongRecOn generalizing s with
  | _ n ih =>
    by_cases heq : s.length = k + 1
    · -- Base case: s is already complete
      rw [completionCount_of_length_eq ω k s heq]
      exact Nat.one_pos
    · -- Recursive case: s.length < k + 1
      have hlt : s.length < k + 1 := Nat.lt_of_le_of_ne hs heq
      rw [completionCount_rec ω k s hlt]
      -- Sum is positive because radix ≥ 2 and each term is positive
      apply Finset.sum_pos
      · intro d _
        have hle : (s ++ [d]).length ≤ k + 1 := by simp; omega
        have hdec : k + 1 - (s ++ [d]).length < n := by simp at hn ⊢; omega
        exact ih (k + 1 - (s ++ [d]).length) hdec (s ++ [d]) hle rfl
      · -- Finset.range (ω.radix s) is nonempty because radix > 0
        simp only [Finset.nonempty_range_iff]
        exact Nat.ne_of_gt (ω.radix_pos s)

/-- General shift lemma: completion count of d :: s under ω equals completion count of s under ω.shift d -/
theorem completionCount_shift_general (ω : RadixLaw) (k : ℕ) (d : ℕ) (s : PrefixWord)
    (hs : s.length ≤ k + 1) :
    completionCount ω (k + 1) (d :: s) = completionCount (ω.shift d) k s := by
  -- Induction on remaining depth k + 1 - s.length
  obtain ⟨n, hn⟩ : ∃ n, n = k + 1 - s.length := ⟨_, rfl⟩
  induction n using Nat.strongRecOn generalizing s with
  | _ n ih =>
    by_cases heq : s.length = k + 1
    · -- Base case: s has full length
      -- LHS: (d :: s).length = k + 2 = (k+1) + 1, so completionCount = 1
      have hlen_lhs : (d :: s).length = (k + 1) + 1 := by simp [heq]
      rw [completionCount_of_length_eq ω (k + 1) (d :: s) hlen_lhs]
      -- RHS: s.length = k + 1, so completionCount = 1
      rw [completionCount_of_length_eq (ω.shift d) k s heq]
    · -- Recursive case: s.length < k + 1
      have hlt : s.length < k + 1 := Nat.lt_of_le_of_ne hs heq
      have hlt_lhs : (d :: s).length < (k + 1) + 1 := by simp; omega
      -- Unfold both sides using the recursive formula
      rw [completionCount_rec ω (k + 1) (d :: s) hlt_lhs]
      rw [completionCount_rec (ω.shift d) k s hlt]
      -- The sums have the same range: ω.radix (d :: s) = (ω.shift d).radix s
      have h_radix : ω.radix (d :: s) = (ω.shift d).radix s := rfl
      -- Show the terms match
      apply Finset.sum_congr
      · rw [h_radix]
      · intro j _
        -- Need: completionCount ω (k+1) ((d :: s) ++ [j]) = completionCount (ω.shift d) k (s ++ [j])
        -- Note: (d :: s) ++ [j] = d :: (s ++ [j])
        have h_append : (d :: s) ++ [j] = d :: (s ++ [j]) := by simp
        rw [h_append]
        -- Apply IH
        have hle_ext : (s ++ [j]).length ≤ k + 1 := by simp; omega
        have hdec : k + 1 - (s ++ [j]).length < n := by simp at hn ⊢; omega
        exact ih (k + 1 - (s ++ [j]).length) hdec (s ++ [j]) hle_ext rfl

/-- Completion count shifts with the radix law -/
theorem completionCount_shift (ω : RadixLaw) (k : ℕ) (d : ℕ) :
    completionCount ω (k + 1) [d] = completionCount (ω.shift d) k [] := by
  -- Special case of completionCount_shift_general with s = []
  have h := completionCount_shift_general ω k d [] (by simp)
  simp at h
  exact h

/-- The completion count at the root is the total space size -/
theorem completionCount_nil (ω : RadixLaw) (k : ℕ) :
    completionCount ω k [] = FiniteVariableSpace.card ω k := by
  -- Proof by induction on k
  induction k generalizing ω with
  | zero =>
    -- Base case: k = 0
    -- completionCount ω 0 [] = ∑_{d < ω.radix []} completionCount ω 0 [d]
    --                        = ∑_{d < ω.radix []} 1  (since [d].length = 1 = 0 + 1)
    --                        = ω.radix []
    -- FiniteVariableSpace.card ω 0 = ω.radix []
    rw [completionCount_rec ω 0 [] (by simp)]
    simp only [FiniteVariableSpace.card, List.nil_append]
    -- Sum of 1's over range n = n
    have h : ∀ d ∈ Finset.range (ω.radix []), completionCount ω 0 [d] = 1 := by
      intro d _
      exact completionCount_of_length_eq ω 0 [d] (by simp)
    rw [Finset.sum_congr rfl h]
    simp [Finset.sum_const, Finset.card_range]
  | succ k ih =>
    -- Inductive case: k + 1
    rw [completionCount_rec ω (k + 1) [] (by simp)]
    simp only [FiniteVariableSpace.card, List.nil_append]
    apply Finset.sum_congr rfl
    intro d _
    rw [completionCount_shift]
    exact ih (ω.shift d)

/-!
## Cumulative Subtree Sizes
-/

/--
The cumulative count of completions for prefixes less than s in lex order at position i.

For a prefix s = (d₀, d₁, ..., dₙ₋₁) at position i, this computes:
∑_{j=0}^{d_i - 1} W^{(k)}_ω(s[0..i-1] ++ [j])

This is the contribution to the rank from position i.
-/
def cumulativeAtPosition (ω : RadixLaw) (k : ℕ) (s : PrefixWord) (i : ℕ) (hi : i < s.length) : ℕ :=
  let pfx := s.take i  -- "pfx" instead of "prefix" which is reserved
  let d := s.get ⟨i, hi⟩
  (Finset.range d).sum fun j => completionCount ω k (pfx ++ [j])

/--
The cumulative count (rank) of a prefix s.

This sums the contributions from each position in s.
-/
def cumulativeCount (ω : RadixLaw) (k : ℕ) (s : PrefixWord) : ℕ :=
  (Finset.range s.length).sum fun i =>
    if hi : i < s.length then cumulativeAtPosition ω k s i hi else 0

/-- The rank of a finite sequence is its position in lex order -/
def finiteRank (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k) : ℕ :=
  cumulativeCount ω k τ.digits

end FdrsFormal.Modes.VariableRadix
