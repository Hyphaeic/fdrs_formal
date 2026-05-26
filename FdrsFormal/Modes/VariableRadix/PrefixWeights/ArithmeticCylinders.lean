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

# Arithmetic Cylinders under Sibling Uniformity

This file proves that cylinders correspond to contiguous rank intervals.

## Mathematical Content (fdrs.md lines 4870-4900)

**Corrected Theorem**: Cylinders are rank intervals, not congruence classes.
The set of elements in cylinder(s) is exactly the interval
[minRank(s), minRank(s) + completionCount(s)).

## References

- fdrs.md, Phase 5-6, Section 3 (lines 4870-4900)
- DEPENDENCY_BASED_STRUCTURE.md, Modes/VariableRadix/PrefixWeights
-/

import FdrsFormal.Modes.VariableRadix.PrefixWeights.OdometerDecode
import FdrsFormal.Modes.VariableRadix.SiblingUniformity.SiblingUniformity
import Mathlib.Data.Int.Lemmas

namespace FdrsFormal.Modes.VariableRadix

/-!
## Cylinder Definition
-/

/-- The set of sequences extending a prefix -/
def cylinderSet (ω : RadixLaw) (k : ℕ) (s : PrefixWord) : Set (FiniteVariableSpace ω k) :=
  {τ | s <+: τ.digits}

/-!
## Cylinder Minimum Element

We define the lexicographically smallest element in each cylinder.
-/

/-- Helper: Appending zeros to a valid prefix preserves validity -/
private theorem isValidPrefix'_append_zeros (ω : RadixLaw) (s : PrefixWord) (n : ℕ)
    (hv : isValidPrefix' ω s) :
    isValidPrefix' ω (s ++ List.replicate n 0) := by
  induction n generalizing s with
  | zero => simp [hv]
  | succ n ih =>
    have h1 : s ++ List.replicate (n + 1) 0 = (s ++ [0]) ++ List.replicate n 0 := by
      simp only [List.replicate_succ, List.append_assoc, List.singleton_append]
    rw [h1]
    apply ih
    apply isValidPrefix'_append_singleton hv
    exact ω.radix_pos _

/-- The first element of a cylinder -/
def cylinderMin (ω : RadixLaw) (k : ℕ) (s : PrefixWord) (hs : s.length ≤ k + 1)
    (hv : isValidPrefix' ω s) : FiniteVariableSpace ω k where
  digits := s ++ List.replicate (k + 1 - s.length) 0
  length_eq := by simp [Nat.add_sub_cancel' hs]
  valid := isValidPrefix'_append_zeros ω s (k + 1 - s.length) hv

/-- Helper: cylinderMin is in the cylinder -/
theorem cylinderMin_mem (ω : RadixLaw) (k : ℕ) (s : PrefixWord)
    (hs : s.length ≤ k + 1) (hv : isValidPrefix' ω s) :
    cylinderMin ω k s hs hv ∈ cylinderSet ω k s := by
  simp only [cylinderSet, Set.mem_setOf_eq, cylinderMin]
  exact List.prefix_append s _

/-- Helper: If τ is in the cylinder, then s is a valid prefix -/
theorem cylinderSet_valid (ω : RadixLaw) (k : ℕ) (s : PrefixWord)
    (τ : FiniteVariableSpace ω k) (hτ : τ ∈ cylinderSet ω k s) :
    isValidPrefix' ω s := by
  simp only [cylinderSet, Set.mem_setOf_eq] at hτ
  intro i hi
  obtain ⟨t, ht_eq⟩ := hτ
  have hi' : i < (s ++ t).length := by simp; omega
  have hi_τ : i < τ.digits.length := by rw [← ht_eq]; exact hi'
  have h_valid := τ.valid i hi_τ
  have h1 : τ.digits.get ⟨i, hi_τ⟩ = s.get ⟨i, hi⟩ := by
    simp only [← ht_eq, List.get_eq_getElem, List.getElem_append_left hi]
  have h2 : τ.digits.take i = s.take i := by
    simp only [← ht_eq, List.take_append_of_le_length (Nat.le_of_lt hi)]
  rw [h1, h2] at h_valid
  exact h_valid

/-- Helper: zeros < t when t ≠ zeros (for same length lists) -/
private theorem replicate_zero_lt_of_ne {n : ℕ} {t : List ℕ}
    (hlen : t.length = n) (hne : List.replicate n 0 ≠ t) :
    List.replicate n 0 < t := by
  induction n generalizing t with
  | zero =>
    simp at hlen
    subst hlen
    simp at hne
  | succ n ih =>
    cases t with
    | nil => simp at hlen
    | cons h tl =>
      simp at hlen
      by_cases h_head : h = 0
      · subst h_head
        simp only [List.replicate]
        apply List.Lex.cons
        apply ih hlen
        intro h_eq
        apply hne
        simp only [List.replicate_succ]
        rw [h_eq]
      · simp only [List.replicate]
        apply List.Lex.rel
        exact Nat.pos_of_ne_zero h_head

/-- The minimum element has the smallest rank in its cylinder -/
theorem cylinderMin_is_min (ω : RadixLaw) (k : ℕ) (s : PrefixWord)
    (hs : s.length ≤ k + 1) (hv : isValidPrefix' ω s)
    (τ : FiniteVariableSpace ω k) (hτ : τ ∈ cylinderSet ω k s) :
    variableRadixDecode ω k (cylinderMin ω k s hs hv) ≤ variableRadixDecode ω k τ := by
  by_cases heq : cylinderMin ω k s hs hv = τ
  · rw [heq]
  · have hlt : (cylinderMin ω k s hs hv).digits < τ.digits := by
      simp only [cylinderSet, Set.mem_setOf_eq] at hτ
      simp only [cylinderMin]
      obtain ⟨t, ht_eq⟩ := hτ
      rw [← ht_eq]
      have hlen_τ : (s ++ t).length = k + 1 := by rw [ht_eq]; exact τ.length_eq
      have hlen_t : t.length = k + 1 - s.length := by simp at hlen_τ; omega
      have ht_ne : List.replicate (k + 1 - s.length) 0 ≠ t := by
        intro h_eq
        apply heq
        apply FiniteVariableSpace.ext
        simp only [cylinderMin, h_eq, ht_eq]
      have h_suffix_lt := replicate_zero_lt_of_ne hlen_t ht_ne
      exact List.Lex.append_left (· < ·) h_suffix_lt s
    have h_decode_lt := (decode_lt_iff ω k (cylinderMin ω k s hs hv) τ).mpr hlt
    exact Nat.le_of_lt h_decode_lt

/-!
## Helper Lemmas for Lex Order
-/

/-- If s < t (same length), then s ++ a < t ++ b for any extensions -/
theorem lex_lt_of_prefix_lt {α : Type*} [LT α] (s t : List α) (a b : List α)
    (hlen : s.length = t.length) (hlt : s < t) :
    (s ++ a) < (t ++ b) := by
  induction hlt with
  | nil =>
    -- Impossible: nil says s = [], t = y :: ys, but hlen says 0 = 1 + ys.length
    simp at hlen
  | @rel x xs y ys hr =>
    simp only [List.cons_append]
    exact List.Lex.rel hr
  | @cons x xs ys _ ih =>
    simp only [List.cons_append]
    have hlen' : xs.length = ys.length := by simp at hlen; exact hlen
    exact List.Lex.cons (ih hlen')

/-!
## Helper: cylinderMin decode extension

This key lemma shows how the rank of cylinderMin changes when extending the prefix.
-/

/-- Helper: The decode of cylinderMin(s ++ [d]) relates to cylinderMin(s) by the cumulative sum -/
private theorem cylinderMin_decode_ext (ω : RadixLaw) (k : ℕ) (s : PrefixWord)
    (hs : s.length < k + 1) (hv : isValidPrefix' ω s)
    (d : ℕ) (hd : d < ω.radix s) :
    let hs' : s.length ≤ k + 1 := Nat.le_of_lt hs
    let hs_ext : (s ++ [d]).length ≤ k + 1 := by simp; omega
    let hv_ext : isValidPrefix' ω (s ++ [d]) := by
      intro i hi
      simp only [List.length_append, List.length_singleton] at hi
      by_cases hi' : i < s.length
      · simp only [List.get_eq_getElem, List.getElem_append_left hi',
                   List.take_append_of_le_length (Nat.le_of_lt hi')]
        exact hv i hi'
      · have hi'' : i = s.length := by omega
        subst hi''
        simp only [List.get_eq_getElem, List.getElem_append_right (Nat.le_refl _),
                   Nat.sub_self, List.getElem_singleton,
                   List.take_append_of_le_length (Nat.le_refl _)]
        simp only [List.take_length]
        exact hd
    variableRadixDecode ω k (cylinderMin ω k (s ++ [d]) hs_ext hv_ext) =
      variableRadixDecode ω k (cylinderMin ω k s hs' hv) +
        (Finset.range d).sum (fun d' => completionCount ω k (s ++ [d'])) := by
  -- Introduce the let bindings
  let hs' : s.length ≤ k + 1 := Nat.le_of_lt hs
  let hs_ext : (s ++ [d]).length ≤ k + 1 := by simp; omega
  let hv_ext : isValidPrefix' ω (s ++ [d]) := by
    intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hi' : i < s.length
    · simp only [List.get_eq_getElem, List.getElem_append_left hi',
                 List.take_append_of_le_length (Nat.le_of_lt hi')]
      exact hv i hi'
    · have hi'' : i = s.length := by omega
      subst hi''
      simp only [List.get_eq_getElem, List.getElem_append_right (Nat.le_refl _),
                 Nat.sub_self, List.getElem_singleton,
                 List.take_append_of_le_length (Nat.le_refl _)]
      simp only [List.take_length]
      exact hd
  -- Define the digit sequences
  let A := s ++ List.replicate (k + 1 - s.length) 0  -- cylinderMin(s).digits
  let B := (s ++ [d]) ++ List.replicate (k + 1 - (s ++ [d]).length) 0  -- cylinderMin(s++[d]).digits

  -- Basic length facts
  have hlenA : A.length = k + 1 := by simp [A]; omega
  have hlenB : B.length = k + 1 := by simp [B]; omega

  -- The digits are as claimed
  have hA_digits : (cylinderMin ω k s hs' hv).digits = A := rfl
  have hB_digits : (cylinderMin ω k (s ++ [d]) hs_ext hv_ext).digits = B := rfl

  simp only [variableRadixDecode, finiteRank, hA_digits, hB_digits]

  -- Key fact 1: For i < s.length, A[i] = B[i] = s[i]
  have h_prefix_eq : ∀ i (hi_A : i < A.length) (hi_B : i < B.length),
      i < s.length → A.get ⟨i, hi_A⟩ = B.get ⟨i, hi_B⟩ := by
    intro i hi_A hi_B hi
    simp only [A, B, List.get_eq_getElem]
    rw [List.getElem_append_left hi]
    have hi' : i < (s ++ [d]).length := by simp; omega
    rw [List.getElem_append_left hi']
    rw [List.getElem_append_left hi]

  -- Helper: s.length < A.length and s.length < B.length
  have hs_lt_A : s.length < A.length := by simp only [hlenA]; omega
  have hs_lt_B : s.length < B.length := by simp only [hlenB]; omega

  -- Key fact 2: A[s.length] = 0
  have hA_at_slen : A.get ⟨s.length, hs_lt_A⟩ = 0 := by
    simp only [A, List.get_eq_getElem]
    rw [List.getElem_append_right (Nat.le_refl _)]
    simp [List.getElem_replicate]

  -- Key fact 3: B[s.length] = d
  have hB_at_slen : B.get ⟨s.length, hs_lt_B⟩ = d := by
    simp only [B, List.get_eq_getElem]
    have h1 : s.length < (s ++ [d]).length := by simp
    rw [List.getElem_append_left h1]
    rw [List.getElem_append_right (Nat.le_refl _)]
    simp

  -- Key fact 4: For i > s.length, A[i] = B[i] = 0
  have h_suffix_eq : ∀ i (hi_A : i < A.length) (hi_B : i < B.length), s.length < i → i < k + 1 →
      A.get ⟨i, hi_A⟩ = 0 ∧ B.get ⟨i, hi_B⟩ = 0 := by
    intro i hi_A hi_B hi_lo hi_hi
    constructor
    · simp only [A, List.get_eq_getElem]
      rw [List.getElem_append_right (Nat.le_of_lt hi_lo)]
      simp [List.getElem_replicate]
    · simp only [B, List.get_eq_getElem]
      rw [List.getElem_append_right (by simp; omega : (s ++ [d]).length ≤ i)]
      simp [List.getElem_replicate]

  -- Key fact 5: A.take i = B.take i for i ≤ s.length
  have h_take_eq : ∀ i, i ≤ s.length → A.take i = B.take i := by
    intro i hi
    apply List.ext_getElem
    · simp [hlenA, hlenB, Nat.min_eq_left (by omega : i ≤ k + 1)]
    · intro j hj _
      simp only [List.getElem_take]
      have hj_lt_s : j < s.length := by
        simp only [List.length_take, hlenA, Nat.min_eq_left (by omega : i ≤ k + 1)] at hj
        omega
      -- For A = s ++ replicate..., we have A[j] = s[j] since j < s.length
      have hA_j : A[j]'(by simp only [hlenA]; omega) = s[j] := by
        simp only [A]
        rw [List.getElem_append_left hj_lt_s]
      -- For B = s ++ [d] ++ replicate..., we have B[j] = s[j] since j < s.length
      have hB_j : B[j]'(by simp only [hlenB]; omega) = s[j] := by
        simp only [B]
        have hj_lt_sd : j < (s ++ [d]).length := by simp; omega
        rw [List.getElem_append_left hj_lt_sd, List.getElem_append_left hj_lt_s]
      rw [hA_j, hB_j]

  -- Key fact 6: A.take s.length = s and B.take s.length = s
  have hA_take_s : A.take s.length = s := by
    simp only [A]
    rw [List.take_append_of_le_length (Nat.le_refl _)]
    simp

  have hB_take_s : B.take s.length = s := by
    simp only [B]
    have h1 : s.length ≤ (s ++ [d]).length := by simp
    rw [List.take_append_of_le_length h1]
    rw [List.take_append_of_le_length (Nat.le_refl _)]
    simp

  -- Now compute cumulativeCount for both
  simp only [cumulativeCount, hlenA, hlenB]

  -- Helper: cumulativeAtPosition for A at position i < s.length
  have hA_cumAt_prefix : ∀ i (hi_A : i < A.length) (hi_B : i < B.length) (hi : i < s.length),
      cumulativeAtPosition ω k A i hi_A =
      cumulativeAtPosition ω k B i hi_B := by
    intro i hi_A hi_B hi
    simp only [cumulativeAtPosition]
    have h_take : A.take i = B.take i := h_take_eq i (Nat.le_of_lt hi)
    have h_get : A.get ⟨i, hi_A⟩ = B.get ⟨i, hi_B⟩ := h_prefix_eq i hi_A hi_B hi
    simp only [h_take, h_get]

  -- Helper: cumulativeAtPosition for A at s.length is 0 (since A[s.length] = 0)
  have hA_cumAt_slen : cumulativeAtPosition ω k A s.length hs_lt_A = 0 := by
    simp only [cumulativeAtPosition, hA_at_slen]
    simp [Finset.range_zero]

  -- Helper: cumulativeAtPosition for B at s.length is sum_{j<d} completionCount(s ++ [j])
  have hB_cumAt_slen : cumulativeAtPosition ω k B s.length hs_lt_B =
      (Finset.range d).sum (fun d' => completionCount ω k (s ++ [d'])) := by
    simp only [cumulativeAtPosition, hB_at_slen, hB_take_s]

  -- Helper: cumulativeAtPosition for both at positions > s.length is 0
  have h_cumAt_suffix : ∀ i (hi_A : i < A.length) (hi_B : i < B.length),
      s.length < i → i < k + 1 →
      cumulativeAtPosition ω k A i hi_A = 0 ∧
      cumulativeAtPosition ω k B i hi_B = 0 := by
    intro i hi_A hi_B hi_lo hi_hi
    obtain ⟨hA_zero, hB_zero⟩ := h_suffix_eq i hi_A hi_B hi_lo hi_hi
    constructor
    · simp only [cumulativeAtPosition, hA_zero, Finset.range_zero, Finset.sum_empty]
    · simp only [cumulativeAtPosition, hB_zero, Finset.range_zero, Finset.sum_empty]

  -- Split the range [0, k+1) at s.length
  -- First, establish the disjointness properties we'll need
  have h_disj1 : Disjoint (Finset.range s.length) {s.length} := by
    simp only [Finset.disjoint_singleton_right, Finset.mem_range]
    omega
  have h_disj2 : Disjoint (Finset.range s.length ∪ {s.length}) (Finset.Ico (s.length + 1) (k + 1)) := by
    rw [Finset.disjoint_union_left]
    constructor
    · simp only [Finset.disjoint_left, Finset.mem_range, Finset.mem_Ico]
      intro x hx1 hx2
      omega
    · simp only [Finset.disjoint_singleton_left, Finset.mem_Ico]
      omega

  have h_split_A : (Finset.range (k + 1)).sum (fun i =>
      if hi : i < A.length then cumulativeAtPosition ω k A i hi else 0) =
      (Finset.range s.length).sum (fun i =>
        if hi : i < A.length then cumulativeAtPosition ω k A i hi else 0) +
      (if hi : s.length < A.length then cumulativeAtPosition ω k A s.length hi else 0) +
      (Finset.Ico (s.length + 1) (k + 1)).sum (fun i =>
        if hi : i < A.length then cumulativeAtPosition ω k A i hi else 0) := by
    simp only [hlenA]
    have hsplit : Finset.range (k + 1) = Finset.range s.length ∪ {s.length} ∪ Finset.Ico (s.length + 1) (k + 1) := by
      ext x
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton, Finset.mem_Ico]
      omega
    rw [hsplit, Finset.sum_union h_disj2, Finset.sum_union h_disj1, Finset.sum_singleton]

  have h_split_B : (Finset.range (k + 1)).sum (fun i =>
      if hi : i < B.length then cumulativeAtPosition ω k B i hi else 0) =
      (Finset.range s.length).sum (fun i =>
        if hi : i < B.length then cumulativeAtPosition ω k B i hi else 0) +
      (if hi : s.length < B.length then cumulativeAtPosition ω k B s.length hi else 0) +
      (Finset.Ico (s.length + 1) (k + 1)).sum (fun i =>
        if hi : i < B.length then cumulativeAtPosition ω k B i hi else 0) := by
    simp only [hlenB]
    have hsplit : Finset.range (k + 1) = Finset.range s.length ∪ {s.length} ∪ Finset.Ico (s.length + 1) (k + 1) := by
      ext x
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton, Finset.mem_Ico]
      omega
    rw [hsplit, Finset.sum_union h_disj2, Finset.sum_union h_disj1, Finset.sum_singleton]

  -- Simplify the sums
  have h_prefix_sums_eq : (Finset.range s.length).sum (fun i =>
      if hi : i < A.length then cumulativeAtPosition ω k A i hi else 0) =
      (Finset.range s.length).sum (fun i =>
        if hi : i < B.length then cumulativeAtPosition ω k B i hi else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    have hi_A : i < A.length := by simp only [hlenA]; omega
    have hi_B : i < B.length := by simp only [hlenB]; omega
    simp only [hi_A, hi_B, dite_true]
    exact hA_cumAt_prefix i hi_A hi_B hi

  have h_A_at_slen : (if hi : s.length < A.length then cumulativeAtPosition ω k A s.length hi else 0) = 0 := by
    simp only [hlenA, (by omega : s.length < k + 1), dite_true]
    exact hA_cumAt_slen

  have h_B_at_slen : (if hi : s.length < B.length then cumulativeAtPosition ω k B s.length hi else 0) =
      (Finset.range d).sum (fun d' => completionCount ω k (s ++ [d'])) := by
    simp only [hlenB, (by omega : s.length < k + 1), dite_true]
    exact hB_cumAt_slen

  have h_suffix_A_zero : (Finset.Ico (s.length + 1) (k + 1)).sum (fun i =>
      if hi : i < A.length then cumulativeAtPosition ω k A i hi else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_Ico] at hi
    simp only [hlenA, hi.2, dite_true]
    have hi_A : i < A.length := hlenA ▸ hi.2
    have hi_B : i < B.length := hlenB ▸ hi.2
    exact (h_cumAt_suffix i hi_A hi_B hi.1 hi.2).1

  have h_suffix_B_zero : (Finset.Ico (s.length + 1) (k + 1)).sum (fun i =>
      if hi : i < B.length then cumulativeAtPosition ω k B i hi else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_Ico] at hi
    simp only [hlenB, hi.2, dite_true]
    have hi_A : i < A.length := hlenA ▸ hi.2
    have hi_B : i < B.length := hlenB ▸ hi.2
    exact (h_cumAt_suffix i hi_A hi_B hi.1 hi.2).2

  -- Transform the goal to use our helper format
  suffices h_goal :
      (Finset.range (k + 1)).sum (fun i => if hi : i < B.length then cumulativeAtPosition ω k B i hi else 0) =
      (Finset.range (k + 1)).sum (fun i => if hi : i < A.length then cumulativeAtPosition ω k A i hi else 0) +
        (Finset.range d).sum (fun d' => completionCount ω k (s ++ [d'])) by
    -- Convert between the two forms
    have h_conv_A : (Finset.range (k + 1)).sum (fun x => if _ : x < k + 1 then cumulativeAtPosition ω k A x (hlenA ▸ ‹_›) else 0) =
        (Finset.range (k + 1)).sum (fun i => if hi : i < A.length then cumulativeAtPosition ω k A i hi else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [Finset.mem_range] at hx
      simp only [hlenA, hx, dite_true]
    have h_conv_B : (Finset.range (k + 1)).sum (fun x => if _ : x < k + 1 then cumulativeAtPosition ω k B x (hlenB ▸ ‹_›) else 0) =
        (Finset.range (k + 1)).sum (fun i => if hi : i < B.length then cumulativeAtPosition ω k B i hi else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [Finset.mem_range] at hx
      simp only [hlenB, hx, dite_true]
    rw [h_conv_A, h_conv_B]
    exact h_goal

  -- Now prove h_goal using calc
  calc (Finset.range (k + 1)).sum (fun i => if hi : i < B.length then cumulativeAtPosition ω k B i hi else 0)
      = (Finset.range s.length).sum (fun i => if hi : i < B.length then cumulativeAtPosition ω k B i hi else 0) +
        (if hi : s.length < B.length then cumulativeAtPosition ω k B s.length hi else 0) +
        (Finset.Ico (s.length + 1) (k + 1)).sum (fun i => if hi : i < B.length then cumulativeAtPosition ω k B i hi else 0) := h_split_B
    _ = (Finset.range s.length).sum (fun i => if hi : i < A.length then cumulativeAtPosition ω k A i hi else 0) +
        (if hi : s.length < B.length then cumulativeAtPosition ω k B s.length hi else 0) +
        (Finset.Ico (s.length + 1) (k + 1)).sum (fun i => if hi : i < B.length then cumulativeAtPosition ω k B i hi else 0) := by
        rw [h_prefix_sums_eq]
    _ = (Finset.range s.length).sum (fun i => if hi : i < A.length then cumulativeAtPosition ω k A i hi else 0) +
        (Finset.range d).sum (fun d' => completionCount ω k (s ++ [d'])) +
        (Finset.Ico (s.length + 1) (k + 1)).sum (fun i => if hi : i < B.length then cumulativeAtPosition ω k B i hi else 0) := by
        rw [h_B_at_slen]
    _ = (Finset.range s.length).sum (fun i => if hi : i < A.length then cumulativeAtPosition ω k A i hi else 0) +
        (Finset.range d).sum (fun d' => completionCount ω k (s ++ [d'])) + 0 := by
        rw [h_suffix_B_zero]
    _ = (Finset.range s.length).sum (fun i => if hi : i < A.length then cumulativeAtPosition ω k A i hi else 0) +
        0 + 0 +
        (Finset.range d).sum (fun d' => completionCount ω k (s ++ [d'])) := by ring
    _ = (Finset.range s.length).sum (fun i => if hi : i < A.length then cumulativeAtPosition ω k A i hi else 0) +
        (if hi : s.length < A.length then cumulativeAtPosition ω k A s.length hi else 0) +
        (Finset.Ico (s.length + 1) (k + 1)).sum (fun i => if hi : i < A.length then cumulativeAtPosition ω k A i hi else 0) +
        (Finset.range d).sum (fun d' => completionCount ω k (s ++ [d'])) := by
        rw [h_A_at_slen, h_suffix_A_zero]
    _ = (Finset.range (k + 1)).sum (fun i => if hi : i < A.length then cumulativeAtPosition ω k A i hi else 0) +
        (Finset.range d).sum (fun d' => completionCount ω k (s ++ [d'])) := by
        rw [← h_split_A]

/-!
## Cylinder Rank Bounds
-/

/--
Elements in a cylinder have rank bounded above by min_rank + completionCount - 1.
-/
theorem cylinder_rank_upper_bound (ω : RadixLaw) (k : ℕ) (s : PrefixWord)
    (hs : s.length ≤ k + 1) (hv : isValidPrefix' ω s)
    (τ : FiniteVariableSpace ω k) (hτ : τ ∈ cylinderSet ω k s) :
    variableRadixDecode ω k τ <
      variableRadixDecode ω k (cylinderMin ω k s hs hv) + completionCount ω k s := by
  simp only [cylinderSet, Set.mem_setOf_eq] at hτ
  -- Induction on remaining depth n = k + 1 - s.length
  obtain ⟨n, hn⟩ : ∃ n, n = k + 1 - s.length := ⟨_, rfl⟩
  induction n using Nat.strongRecOn generalizing s with
  | _ n ih =>
    by_cases heq : s.length = k + 1
    · -- Base case: s is a complete sequence
      have h_comp : completionCount ω k s = 1 := completionCount_of_length_eq ω k s heq
      have h_τ_eq : τ.digits = s := by
        obtain ⟨t, ht⟩ := hτ
        have hlen_τ : τ.digits.length = k + 1 := τ.length_eq
        have hlen_st : (s ++ t).length = k + 1 := by rw [ht]; exact hlen_τ
        simp only [List.length_append] at hlen_st
        have ht_len : t.length = 0 := by omega
        have ht_nil : t = [] := List.eq_nil_of_length_eq_zero ht_len
        simp only [ht_nil, List.append_nil] at ht
        exact ht.symm
      have h_min_eq : (cylinderMin ω k s hs hv).digits = s := by
        simp only [cylinderMin, heq, Nat.sub_self, List.replicate_zero, List.append_nil]
      have h_τ_min : τ = cylinderMin ω k s hs hv := by
        apply FiniteVariableSpace.ext
        rw [h_τ_eq, h_min_eq]
      rw [h_τ_min, h_comp]
      exact Nat.lt_add_one _
    · -- Inductive case: s.length < k + 1
      have hs_lt : s.length < k + 1 := Nat.lt_of_le_of_ne hs heq
      obtain ⟨t, ht⟩ := hτ
      cases t with
      | nil =>
        simp only [List.append_nil] at ht
        have hlen_τ : τ.digits.length = k + 1 := τ.length_eq
        rw [← ht] at hlen_τ
        omega
      | cons d ds =>
        have ht' : τ.digits = (s ++ [d]) ++ ds := by simp only [ht, List.append_assoc, List.singleton_append]
        have h_in_ext : (s ++ [d]) <+: τ.digits := ⟨ds, ht'.symm⟩
        have hv_ext : isValidPrefix' ω (s ++ [d]) := by
          intro i hi
          simp only [List.length_append, List.length_singleton] at hi
          by_cases hi' : i < s.length
          · have h1 : (s ++ [d]).get ⟨i, by simp; omega⟩ = s.get ⟨i, hi'⟩ := by
              simp only [List.get_eq_getElem, List.getElem_append_left hi']
            have h2 : (s ++ [d]).take i = s.take i := by
              simp only [List.take_append_of_le_length (Nat.le_of_lt hi')]
            rw [h1, h2]
            exact hv i hi'
          · have hi'' : i = s.length := by omega
            subst hi''
            simp only [List.get_eq_getElem, List.getElem_append_right (Nat.le_refl _),
                       Nat.sub_self, List.getElem_singleton]
            simp only [List.take_append_of_le_length (Nat.le_refl _)]
            have hlen_τ : τ.digits.length = k + 1 := τ.length_eq
            have h_d_pos : s.length < τ.digits.length := by rw [hlen_τ]; exact hs_lt
            have h_valid_d := τ.valid s.length h_d_pos
            simp only [← ht, List.get_eq_getElem] at h_valid_d
            simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
                       List.getElem_cons_zero] at h_valid_d
            simp only [List.take_append_of_le_length (Nat.le_refl _)] at h_valid_d
            exact h_valid_d
        have hs_ext : (s ++ [d]).length ≤ k + 1 := by simp; omega
        have hdec : k + 1 - (s ++ [d]).length < n := by simp at hn ⊢; omega
        have ih_applied := ih (k + 1 - (s ++ [d]).length) hdec (s ++ [d]) hs_ext hv_ext h_in_ext rfl

        have h_min_le_ext : (cylinderMin ω k s hs hv).digits ≤ (cylinderMin ω k (s ++ [d]) hs_ext hv_ext).digits := by
          simp only [cylinderMin]
          by_cases hd : d = 0
          · subst hd
            have h_eq : s ++ List.replicate (k + 1 - s.length) 0 =
                (s ++ [0]) ++ List.replicate (k + 1 - (s ++ [0]).length) 0 := by
              simp only [List.length_append, List.length_singleton]
              have h1 : k + 1 - (s.length + 1) = k - s.length := by omega
              rw [h1]
              simp only [List.append_assoc, List.singleton_append]
              congr 1
              have h2 : k + 1 - s.length = (k - s.length) + 1 := by omega
              rw [h2, List.replicate_succ]
            rw [h_eq]
          · have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
            apply le_of_lt
            have h_rhs : (s ++ [d]) ++ List.replicate (k + 1 - (s ++ [d]).length) 0 =
                s ++ ([d] ++ List.replicate (k + 1 - (s ++ [d]).length) 0) := by
              simp only [List.append_assoc]
            rw [h_rhs]
            apply List.Lex.append_left
            simp only [List.length_append, List.length_singleton]
            have h_len : k + 1 - (s.length + 1) = k - s.length := by omega
            rw [h_len]
            have h_rep : List.replicate (k + 1 - s.length) 0 = 0 :: List.replicate (k - s.length) 0 := by
              have h : k + 1 - s.length = (k - s.length) + 1 := by omega
              rw [h, List.replicate_succ]
            rw [h_rep]
            apply List.Lex.rel
            exact hd_pos

        have h_decode_min_le : variableRadixDecode ω k (cylinderMin ω k s hs hv) ≤
            variableRadixDecode ω k (cylinderMin ω k (s ++ [d]) hs_ext hv_ext) := by
          rcases Nat.lt_trichotomy
            (variableRadixDecode ω k (cylinderMin ω k s hs hv))
            (variableRadixDecode ω k (cylinderMin ω k (s ++ [d]) hs_ext hv_ext)) with hlt | heq' | hgt
          · exact Nat.le_of_lt hlt
          · exact Nat.le_of_eq heq'
          · exfalso
            have h_lex := (decode_lt_iff ω k _ _).mp hgt
            exact (not_lt.mpr h_min_le_ext) h_lex

        have hd_valid : d < ω.radix s := by
          have hlen_τ : τ.digits.length = k + 1 := τ.length_eq
          have h_d_pos : s.length < τ.digits.length := by rw [hlen_τ]; exact hs_lt
          have h_valid_d := τ.valid s.length h_d_pos
          simp only [← ht, List.get_eq_getElem] at h_valid_d
          simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
                     List.getElem_cons_zero] at h_valid_d
          simp only [List.take_append_of_le_length (Nat.le_refl _)] at h_valid_d
          simp only [List.take_length] at h_valid_d
          exact h_valid_d

        have hs' : s.length ≤ k + 1 := Nat.le_of_lt hs_lt
        have h_ext_decode := cylinderMin_decode_ext ω k s hs_lt hv d hd_valid
        simp only at h_ext_decode

        have h_min_eq : cylinderMin ω k s hs hv = cylinderMin ω k s hs' hv := by
          apply FiniteVariableSpace.ext
          simp only [cylinderMin]

        calc variableRadixDecode ω k τ
            < variableRadixDecode ω k (cylinderMin ω k (s ++ [d]) hs_ext hv_ext) +
              completionCount ω k (s ++ [d]) := ih_applied
          _ = variableRadixDecode ω k (cylinderMin ω k s hs' hv) +
              (Finset.range d).sum (fun d' => completionCount ω k (s ++ [d'])) +
              completionCount ω k (s ++ [d]) := by rw [h_ext_decode]
          _ = variableRadixDecode ω k (cylinderMin ω k s hs hv) +
              (Finset.range d).sum (fun d' => completionCount ω k (s ++ [d'])) +
              completionCount ω k (s ++ [d]) := by rw [h_min_eq]
          _ = variableRadixDecode ω k (cylinderMin ω k s hs hv) +
              ((Finset.range d).sum (fun d' => completionCount ω k (s ++ [d'])) +
               completionCount ω k (s ++ [d])) := by ring
          _ = variableRadixDecode ω k (cylinderMin ω k s hs hv) +
              (Finset.range (d + 1)).sum (fun d' => completionCount ω k (s ++ [d'])) := by
              rw [Finset.sum_range_succ]
          _ ≤ variableRadixDecode ω k (cylinderMin ω k s hs hv) +
              (Finset.range (ω.radix s)).sum (fun d' => completionCount ω k (s ++ [d'])) := by
              apply Nat.add_le_add_left
              apply Finset.sum_le_sum_of_subset
              intro x hx
              simp only [Finset.mem_range] at hx ⊢
              omega
          _ = variableRadixDecode ω k (cylinderMin ω k s hs hv) + completionCount ω k s := by
              rw [← completionCount_rec ω k s hs_lt]

/-!
## Helper: Elements outside cylinder have ranks outside interval
-/

/-!
Cylinder intervals are ordered by prefix lexicographic order.

**Mathematical argument**: For same-length prefixes s < s' in lex order:
- All elements in cylinder(s) have rank < minRank(s') (by lex ordering)
- The cylinder contains completionCount(s) consecutive ranks starting at minRank(s)
- Therefore minRank(s) + completionCount(s) ≤ minRank(s')

**Proof**: Construct the "cylinder maximum" element τ ∈ cylinder(s) with
decode(τ) + 1 = minRank(s) + completionCount(s), using the largest valid digit
(radix - 1) at each position. Then τ.digits < cylinderMin(s').digits by
lex_lt_of_prefix_lt, so decode(τ) < decode(cylinderMin(s')), giving the result.
-/

/-- There exists a maximum-rank element in each cylinder:
    decode(τ) + 1 = minRank(s) + completionCount(s) -/
private theorem cylinder_max_rank (ω : RadixLaw) (k : ℕ) (s : PrefixWord)
    (hs : s.length ≤ k + 1) (hv : isValidPrefix' ω s) :
    ∃ τ : FiniteVariableSpace ω k, τ ∈ cylinderSet ω k s ∧
      variableRadixDecode ω k τ + 1 =
        variableRadixDecode ω k (cylinderMin ω k s hs hv) + completionCount ω k s := by
  obtain ⟨n, hn⟩ : ∃ n, n = k + 1 - s.length := ⟨_, rfl⟩
  induction n using Nat.strongRecOn generalizing s with
  | _ n ih =>
    by_cases heq : s.length = k + 1
    · -- Base: comp(s) = 1, take cylinderMin itself
      exact ⟨cylinderMin ω k s hs hv, cylinderMin_mem ω k s hs hv,
        by rw [completionCount_of_length_eq ω k s heq]⟩
    · -- Step: use max digit d = radix(s) - 1, apply IH to s ++ [d]
      have hs_lt : s.length < k + 1 := Nat.lt_of_le_of_ne hs heq
      set d := ω.radix s - 1 with hd_def
      have hd_lt : d < ω.radix s := by have := ω.radix_ge_two s; omega
      have hd_succ : d + 1 = ω.radix s := by have := ω.radix_ge_two s; omega
      have hv_ext : isValidPrefix' ω (s ++ [d]) := isValidPrefix'_append_singleton hv hd_lt
      have hs_ext : (s ++ [d]).length ≤ k + 1 := by simp; omega
      have hdec : k + 1 - (s ++ [d]).length < n := by simp at hn ⊢; omega
      obtain ⟨τ, hτ_mem, hτ_rank⟩ := ih _ hdec (s ++ [d]) hs_ext hv_ext rfl
      refine ⟨τ, ?_, ?_⟩
      · -- τ ∈ cylinder(s ++ [d]) ⊆ cylinder(s)
        simp only [cylinderSet, Set.mem_setOf_eq] at hτ_mem ⊢
        exact (List.prefix_append s [d]).trans hτ_mem
      · -- decode(τ) + 1 = decode(cylinderMin(s++[d])) + comp(s++[d])
        --                = (decode(cylinderMin(s)) + Σ_{d'<d} comp(s++[d'])) + comp(s++[d])
        --                = decode(cylinderMin(s)) + comp(s)
        have h_ext := cylinderMin_decode_ext ω k s hs_lt hv d hd_lt
        simp only at h_ext
        have h_comp := (completionCount_rec ω k s hs_lt).symm
        have h_split := Finset.sum_range_succ (fun d' => completionCount ω k (s ++ [d'])) d
        rw [hd_succ] at h_split
        omega

theorem cylinder_interval_le (ω : RadixLaw) (k : ℕ) (s s' : PrefixWord)
    (hs : s.length ≤ k + 1) (hs' : s'.length ≤ k + 1)
    (hv : isValidPrefix' ω s) (hv' : isValidPrefix' ω s')
    (hlen : s.length = s'.length) (hlt : s < s') :
    variableRadixDecode ω k (cylinderMin ω k s hs hv) + completionCount ω k s ≤
      variableRadixDecode ω k (cylinderMin ω k s' hs' hv') := by
  obtain ⟨τ, hτ_mem, hτ_rank⟩ := cylinder_max_rank ω k s hs hv
  have hτ_prefix : s <+: τ.digits := by
    simp only [cylinderSet, Set.mem_setOf_eq] at hτ_mem; exact hτ_mem
  obtain ⟨suffix_τ, h_τ_eq⟩ := hτ_prefix
  have h_lex : τ.digits < (cylinderMin ω k s' hs' hv').digits := by
    simp only [cylinderMin]
    rw [← h_τ_eq]
    exact lex_lt_of_prefix_lt s s' suffix_τ _ hlen hlt
  have h_decode_lt := (decode_lt_iff ω k τ (cylinderMin ω k s' hs' hv')).mpr h_lex
  omega

/--
Helper: elements NOT in a cylinder have ranks outside its interval.
-/
private theorem rank_not_in_interval_of_not_in_cylinder (ω : RadixLaw) (k : ℕ) (s : PrefixWord)
    (hs : s.length ≤ k + 1) (hv : isValidPrefix' ω s)
    (τ : FiniteVariableSpace ω k) (hτ : τ ∉ cylinderSet ω k s) :
    variableRadixDecode ω k τ < variableRadixDecode ω k (cylinderMin ω k s hs hv) ∨
    variableRadixDecode ω k τ ≥
      variableRadixDecode ω k (cylinderMin ω k s hs hv) + completionCount ω k s := by
  simp only [cylinderSet, Set.mem_setOf_eq] at hτ
  let s' := τ.digits.take s.length
  have hs'_ne : s' ≠ s := by
    intro heq
    apply hτ
    rw [← heq]
    exact List.take_prefix s.length τ.digits
  have hs'_valid : isValidPrefix' ω s' := by
    intro i hi
    simp only [s', List.length_take, τ.length_eq, Nat.min_eq_left hs] at hi
    have hi_τ : i < τ.digits.length := by rw [τ.length_eq]; omega
    have hi_s' : i < s'.length := by simp only [s', List.length_take, τ.length_eq, Nat.min_eq_left hs]; exact hi
    have hget : s'[i] = τ.digits[i] := by
      simp only [s', List.getElem_take]
    have htake : s'.take i = τ.digits.take i := by
      simp only [s']
      rw [List.take_take]
      congr 1
      exact Nat.min_eq_left (Nat.le_of_lt hi)
    simp only [List.get_eq_getElem]
    rw [hget, htake]
    exact τ.valid i hi_τ
  have hs'_len : s'.length = s.length := by
    simp only [s', List.length_take, τ.length_eq]
    exact Nat.min_eq_left hs
  have hτ_in_s' : τ ∈ cylinderSet ω k s' := by
    simp only [cylinderSet, Set.mem_setOf_eq, s']
    exact List.take_prefix s.length τ.digits
  have hs'_bound : s'.length ≤ k + 1 := hs'_len ▸ hs
  rcases lt_trichotomy s s' with h_lt | h_eq | h_gt
  · -- Case s < s': cylinder(s) comes before cylinder(s')
    right
    have h_all_lt : ∀ σ : FiniteVariableSpace ω k, σ ∈ cylinderSet ω k s →
        σ.digits < (cylinderMin ω k s' hs'_bound hs'_valid).digits := by
      intro σ hσ
      simp only [cylinderSet, Set.mem_setOf_eq] at hσ
      obtain ⟨suffix_σ, h_σ_eq⟩ := hσ
      simp only [cylinderMin]
      rw [← h_σ_eq]
      exact lex_lt_of_prefix_lt s s' suffix_σ _ hs'_len.symm h_lt
    have h_ranks_lt : ∀ σ : FiniteVariableSpace ω k, σ ∈ cylinderSet ω k s →
        variableRadixDecode ω k σ <
          variableRadixDecode ω k (cylinderMin ω k s' hs'_bound hs'_valid) := by
      intro σ hσ
      exact (decode_lt_iff ω k σ _).mpr (h_all_lt σ hσ)
    have h_min_in : cylinderMin ω k s hs hv ∈ cylinderSet ω k s := cylinderMin_mem ω k s hs hv
    -- Key: minRank(s) + comp(s) ≤ minRank(s') because s < s' means cylinder(s) comes before cylinder(s')
    -- This follows from the partition structure of cylinders at the same depth
    -- The ranks in cylinder(s) form [minRank(s), minRank(s) + comp(s)) and all are < minRank(s')
    -- By surjectivity of encoding, there's an element with rank minRank(s) + comp(s) - 1
    -- which is also < minRank(s'), hence minRank(s) + comp(s) ≤ minRank(s')
    have h_interval_le : variableRadixDecode ω k (cylinderMin ω k s hs hv) + completionCount ω k s ≤
        variableRadixDecode ω k (cylinderMin ω k s' hs'_bound hs'_valid) := by
      -- Use the axiom for cylinder interval ordering
      exact cylinder_interval_le ω k s s' hs hs'_bound hv hs'_valid hs'_len.symm h_lt
    have h_τ_ge_min_s' := cylinderMin_is_min ω k s' hs'_bound hs'_valid τ hτ_in_s'
    exact Nat.le_trans h_interval_le h_τ_ge_min_s'
  · exact absurd h_eq.symm hs'_ne
  · -- Case s > s': cylinder(s') comes before cylinder(s)
    left
    have h_τ_lt_min : τ.digits < (cylinderMin ω k s hs hv).digits := by
      simp only [cylinderMin]
      have h_s'_prefix_τ : s' <+: τ.digits := List.take_prefix s.length τ.digits
      obtain ⟨suffix_τ, h_τ_eq⟩ := h_s'_prefix_τ
      rw [← h_τ_eq]
      exact lex_lt_of_prefix_lt s' s suffix_τ _ hs'_len h_gt
    exact (decode_lt_iff ω k τ (cylinderMin ω k s hs hv)).mpr h_τ_lt_min

/-!
## Main Theorem: Cylinders are Rank Intervals
-/

/-- Cylinders are exactly rank intervals -/
theorem cylinder_eq_rank_interval (ω : RadixLaw) (k : ℕ) (s : PrefixWord)
    (hs : s.length ≤ k + 1) (hv : isValidPrefix' ω s) :
    cylinderSet ω k s = {τ |
      let minRank := variableRadixDecode ω k (cylinderMin ω k s hs hv)
      minRank ≤ variableRadixDecode ω k τ ∧
      variableRadixDecode ω k τ < minRank + completionCount ω k s} := by
  ext τ
  constructor
  · intro hτ
    simp only [Set.mem_setOf_eq]
    constructor
    · exact cylinderMin_is_min ω k s hs hv τ hτ
    · exact cylinder_rank_upper_bound ω k s hs hv τ hτ
  · intro ⟨hlo, hhi⟩
    by_contra h_not_in
    have h_outside := rank_not_in_interval_of_not_in_cylinder ω k s hs hv τ h_not_in
    rcases h_outside with h_below | h_above
    · exact Nat.not_le.mpr h_below hlo
    · exact Nat.not_lt.mpr h_above hhi

/-!
## Additional Properties
-/

/-- Cylinders partition the space -/
theorem cylinders_partition_by_congruence (ω : RadixLaw) (k : ℕ) (j : ℕ)
    (hj : j ≤ k) (_hsu : isSiblingUniform ω k) :
    ∀ τ : FiniteVariableSpace ω k,
      ∃! s : PrefixWord, s.length = j + 1 ∧ τ ∈ cylinderSet ω k s := by
  intro τ
  use τ.digits.take (j + 1)
  constructor
  · constructor
    · simp only [List.length_take, τ.length_eq, Nat.min_eq_left (by omega : j + 1 ≤ k + 1)]
    · simp only [cylinderSet, Set.mem_setOf_eq]
      exact List.take_prefix (j + 1) τ.digits
  · intro s ⟨hlen, hmem⟩
    simp only [cylinderSet, Set.mem_setOf_eq] at hmem
    obtain ⟨t, ht⟩ := hmem
    have h : s = τ.digits.take s.length := by
      rw [← ht]
      simp only [List.take_append_of_le_length (Nat.le_refl s.length), List.take_length]
    rw [h, hlen]

/-- Distance from minRank is bounded by completionCount -/
theorem rank_distance_from_min (ω : RadixLaw) (k : ℕ) (s : PrefixWord)
    (hs : s.length ≤ k + 1) (hv : isValidPrefix' ω s)
    (τ : FiniteVariableSpace ω k) (hτ : τ ∈ cylinderSet ω k s) :
    variableRadixDecode ω k τ - variableRadixDecode ω k (cylinderMin ω k s hs hv) <
      completionCount ω k s := by
  have h_upper := cylinder_rank_upper_bound ω k s hs hv τ hτ
  have h_lower := cylinderMin_is_min ω k s hs hv τ hτ
  omega

/-- Rank difference in same cylinder is bounded -/
theorem cylinder_rank_diff_bounded (ω : RadixLaw) (k : ℕ) (s : PrefixWord)
    (hs : s.length ≤ k + 1) (hv : isValidPrefix' ω s)
    (τ σ : FiniteVariableSpace ω k)
    (hτ : τ ∈ cylinderSet ω k s) (hσ : σ ∈ cylinderSet ω k s) :
    Int.natAbs ((variableRadixDecode ω k τ : ℤ) - variableRadixDecode ω k σ) <
      completionCount ω k s := by
  let minRank := variableRadixDecode ω k (cylinderMin ω k s hs hv)
  have hτ_lo := cylinderMin_is_min ω k s hs hv τ hτ
  have hτ_hi := cylinder_rank_upper_bound ω k s hs hv τ hτ
  have hσ_lo := cylinderMin_is_min ω k s hs hv σ hσ
  have hσ_hi := cylinder_rank_upper_bound ω k s hs hv σ hσ
  -- Both ranks are in [minRank, minRank + completionCount)
  -- The absolute difference is bounded by the interval width
  -- Shift to relative values: τ - minRank and σ - minRank
  let τ_rel := variableRadixDecode ω k τ - minRank
  let σ_rel := variableRadixDecode ω k σ - minRank
  have hτ_rel_lt : τ_rel < completionCount ω k s := by
    simp only [τ_rel]
    omega
  have hσ_rel_lt : σ_rel < completionCount ω k s := by
    simp only [σ_rel]
    omega
  -- Key observation: (τ - σ : ℤ) = (τ_rel - σ_rel : ℤ)
  have h_diff_eq : (variableRadixDecode ω k τ : ℤ) - variableRadixDecode ω k σ =
      (τ_rel : ℤ) - (σ_rel : ℤ) := by
    simp only [τ_rel, σ_rel]
    omega
  rw [h_diff_eq]
  -- Use the lemma from Mathlib: natAbs_coe_sub_coe_lt_of_lt
  exact Int.natAbs_coe_sub_coe_lt_of_lt hτ_rel_lt hσ_rel_lt

end FdrsFormal.Modes.VariableRadix
