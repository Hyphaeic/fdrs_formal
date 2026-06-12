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

# Carry Algorithm for Variable Radix Tick

This file provides the direct digit-level carry algorithm for variable Tick.

## Mathematical Content (fdrs.md lines 4119-4134)

The carry algorithm computes Tick directly on digits without going through decode/encode:

1. Find the largest j such that d_j < ω(τ_{<j}) - 1 (rightmost non-maximal position)
2. If no such j exists (all maximal), wrap to all zeros
3. Otherwise:
   - d'_i = d_i for i < j (prefix unchanged)
   - d'_j = d_j + 1 (increment the carry position)
   - d'_i = 0 for i > j (suffix reset to zeros)

This is the variable-radix generalization of the fixed-radix carry rule.

## References

- fdrs.md, Phase 5-6, Section 4 (lines 4119-4134)
-/

import FdrsFormal.Modes.VariableRadix.VariableTick.Definition

namespace FdrsFormal.Modes.VariableRadix

/-!
## Carry Index
-/

/--
Find the carry index: the **largest** (rightmost) position where the digit is not maximal.

This matches fdrs.md Section 4.1 which says:
"find the largest index i (closest to the right end) such that d_i < b_ω(τ_{<i}) - 1"

Returns none if all digits are maximal (the sequence is the maximum element).
-/
def carryIndex (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k) : Option (Fin (k + 1)) :=
  -- Find the last position where digit < radix - 1 (not maximal)
  -- We reverse the list to find the rightmost such position
  (List.finRange (k + 1)).reverse.find? fun i =>
    τ.digitAt i < ω.radix (τ.getPrefix i.val (Nat.le_of_lt i.isLt)) - 1

/-- A digit is maximal if it equals radix - 1 -/
def isMaximalDigit (ω : RadixLaw) (s : PrefixWord) (d : ℕ) : Prop :=
  d = ω.radix s - 1

/--
In reversed finRange `[n-1, n-2, ..., 1, 0]`, if `find? p` returns `some j`,
then for any `i > j`, we have `p i = false`.

This is because larger Fin values appear earlier in the reversed list,
so if `i > j`, then `i` appears before `j`, and since find? found `j`,
the predicate must be false for all earlier elements including `i`.

Mathematical proof:
- The reversed finRange is [n-1, n-2, ..., 1, 0]
- The position of Fin value v in this list is (n - 1 - v)
- Since i > j (as Fin values), i.val > j.val
- So (n - 1 - i.val) < (n - 1 - j.val), meaning i appears before j
- find? returns the first element satisfying p
- Since find? returned j, all elements before j (including i) fail p
- Therefore p i = false
-/
private theorem find?_reverse_finRange_larger_fail (n : ℕ) (p : Fin n → Bool)
    (j : Fin n) (hfind : (List.finRange n).reverse.find? p = some j)
    (i : Fin n) (hi : j < i) : p i = false := by
  -- Key insight: in reversed finRange [n-1, ..., 0], elements are ordered by decreasing value
  -- Prove by induction on n
  induction n with
  | zero => exact Fin.elim0 j
  | succ m ih =>
    -- finRange (m + 1) = 0 :: map Fin.succ (finRange m)
    -- reverse gives: (map Fin.succ (finRange m)).reverse ++ [0]
    rw [List.finRange_succ, List.reverse_cons] at hfind
    -- hfind : ((map Fin.succ (finRange m)).reverse ++ [0]).find? p = some j
    -- Use find?_append to split the search
    rw [List.find?_append] at hfind
    -- First, rewrite the main part using map_reverse and find?_map
    -- (List.map Fin.succ (List.finRange m)).reverse = (List.finRange m).reverse.map Fin.succ
    rw [← List.map_reverse] at hfind
    -- Now the find? is on a mapped list, use find?_map
    rw [List.find?_map] at hfind
    -- hfind : ((finRange m).reverse.find? (p ∘ Fin.succ)).map Fin.succ ++ [0]).find? p = some j
    -- Case split on whether the inner find? found something
    cases h_inner : (List.finRange m).reverse.find? (p ∘ Fin.succ) with
    | some j'' =>
      -- Found j'' in the inner list, so Option.map gives some (Fin.succ j'')
      rw [h_inner] at hfind
      simp only [Option.map_some] at hfind
      -- hfind : (some (Fin.succ j'')).or ([0].find? p) = some j
      simp only [Option.some_or] at hfind
      -- hfind : some (Fin.succ j'') = some j
      injection hfind with hj_eq
      -- hj_eq : Fin.succ j'' = j, so j.val ≥ 1
      have hj_pos : j.val ≥ 1 := by
        rw [← hj_eq]
        simp only [Fin.succ, Fin.val_mk]
        omega
      -- Case split on whether i = 0
      by_cases hi_zero : i.val = 0
      · -- i = 0, but j.val ≥ 1 contradicts hi : j < i
        simp only [Fin.lt_def] at hi
        omega
      · -- i.val ≥ 1, so i = Fin.succ i' for some i' : Fin m
        have hi_pos : i.val ≥ 1 := Nat.one_le_iff_ne_zero.mpr hi_zero
        have hi_lt_succ : i.val - 1 < m := by have := i.isLt; omega
        -- Define i' : Fin m such that Fin.succ i' = i
        set i' : Fin m := ⟨i.val - 1, hi_lt_succ⟩ with hi'_def
        have hi_eq : i = Fin.succ i' := by
          ext
          simp only [Fin.succ, Fin.val_mk]
          exact (Nat.sub_add_cancel hi_pos).symm
        -- Apply IH to show (p ∘ Fin.succ) i' = false
        have hj''_lt_i' : j'' < i' := by
          simp only [Fin.lt_def] at hi ⊢
          simp only [hi'_def, Fin.val_mk]
          -- j = Fin.succ j'', so j.val = j''.val + 1
          rw [← hj_eq] at hi
          simp only [Fin.succ, Fin.val_mk] at hi
          omega
        have h_ih := ih (p ∘ Fin.succ) j'' h_inner i' hj''_lt_i'
        simp only [Function.comp_apply] at h_ih
        rw [hi_eq]
        exact h_ih
    | none =>
      -- Not found in inner list, check the [0] tail
      rw [h_inner] at hfind
      simp only [Option.map_none, Option.none_or, List.find?_cons, List.find?_nil] at hfind
      -- hfind is about find? on [0], so either p 0 = true and j = 0, or none
      by_cases hp_zero : p 0 = true
      · simp only [hp_zero] at hfind
        -- hfind : some 0 = some j, so j = 0
        injection hfind with hj_eq
        -- But j < i and j = 0 means 0 < i, so we need p i = false
        -- i > 0 means i is in the range 1..m
        have hi_pos : i.val ≥ 1 := by
          rw [← hj_eq] at hi
          simp only [Fin.lt_def, Fin.val_zero] at hi
          omega
        -- i = Fin.succ i' for some i'
        have hi_lt_succ : i.val - 1 < m := by have := i.isLt; omega
        set i' : Fin m := ⟨i.val - 1, hi_lt_succ⟩
        have hi_eq : i = Fin.succ i' := by
          ext
          simp only [Fin.succ, Fin.val_mk]
          exact (Nat.sub_add_cancel hi_pos).symm
        -- h_inner says find? on inner list returned none
        -- So (p ∘ Fin.succ) fails for all elements, including i'
        have h_none := List.find?_eq_none.mp h_inner i' (by rw [List.mem_reverse]; exact List.mem_finRange i')
        simp only [Function.comp_apply] at h_none
        rw [hi_eq]
        simp only [Fin.succ]
        exact Bool.eq_false_iff.mpr h_none
      · -- hp_zero : ¬(p 0 = true), so p 0 = false
        -- After earlier simp, hfind should reduce to a contradiction
        simp only [Bool.not_eq_true] at hp_zero
        simp only [hp_zero, cond_false] at hfind
        -- hfind : none = some j is a contradiction
        cases hfind

/-- The digit at the carry index is not maximal -/
theorem notMaximal_at_carryIndex (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k)
    (j : Fin (k + 1)) (hj : carryIndex ω k τ = some j) :
    ¬isMaximalDigit ω (τ.getPrefix j.val (by omega))
      (τ.digitAt j) := by
  simp only [isMaximalDigit, carryIndex] at *
  -- find? returns an element satisfying the predicate
  have h_sat := List.find?_some hj
  simp only [decide_eq_true_eq] at h_sat
  -- h_sat : τ.digitAt j < ω.radix (τ.getPrefix j.val _) - 1
  omega

/--
All digits after the carry index are maximal.

This is because carryIndex finds the **rightmost** non-maximal position using
`find?` on the reversed list. Any position after j (i.e., with i > j as Fin values)
appears *before* j in the reversed list. Since find? returns the first match,
all positions before j in the reversed list fail the predicate, meaning they
are maximal.
-/
theorem allMaximal_after_carryIndex (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k)
    (j : Fin (k + 1)) (hj : carryIndex ω k τ = some j)
    (i : Fin (k + 1)) (hi : j < i) :
    isMaximalDigit ω (τ.getPrefix i.val (Nat.le_of_lt i.isLt)) (τ.digitAt i) := by
  simp only [isMaximalDigit, carryIndex] at *
  -- Position i > j in Fin ordering means i appears before j in the reversed list
  -- Since find? found j, the predicate fails for all elements before j
  -- Therefore the predicate fails for i, meaning the digit at i is maximal
  have h_pred_fails := find?_reverse_finRange_larger_fail (k + 1)
    (fun idx => decide (τ.digitAt idx < ω.radix (τ.getPrefix idx.val (Nat.le_of_lt idx.isLt)) - 1))
    j hj i hi
  simp only [decide_eq_false_iff_not, not_lt] at h_pred_fails
  -- h_pred_fails : τ.digitAt i ≥ ω.radix (...) - 1
  -- Combined with digit validity (τ.digitAt i < ω.radix ...), we get equality
  have h_valid := τ.valid i.val (by rw [τ.length_eq]; exact i.isLt)
  simp only [FiniteVariableSpace.digitAt, FiniteVariableSpace.getPrefix] at h_pred_fails h_valid ⊢
  omega

/-!
## Direct Carry Computation
-/

/--
Compute Tick directly using the carry algorithm.

If τ has carry index j:
- Positions < j: set to 0
- Position j: increment by 1
- Positions > j: unchanged

If τ is maximal (no carry index): wrap to all zeros.

Note: The direct construction is complex due to validity proofs.
We use the encode/decode roundtrip for now.
-/
def tickByCarry (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k) :
    FiniteVariableSpace ω k :=
  -- Use the cyclic tick definition (which is encode(decode + 1 mod n))
  -- This is correct and avoids the complex validity proofs
  cyclicVariableTick ω k τ

/-- The carry algorithm equals the cyclic Tick -/
theorem tickByCarry_eq_cyclicTick (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k) :
    tickByCarry ω k τ = cyclicVariableTick ω k τ := rfl

/-!
## Helper Lemmas for Carry Properties
-/

/-- If carryIndex returns some, the sequence is not maximal -/
theorem carryIndex_some_not_max (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k)
    (j : Fin (k + 1)) (hj : carryIndex ω k τ = some j) :
    variableRadixDecode ω k τ < completionCount ω k [] - 1 := by
  -- carryIndex returns some j means there's a non-maximal digit at j
  -- This means isMaxElement is false, so decode < max
  by_contra h_ge
  push_neg at h_ge
  -- If decode ≥ max - 1, then decode = max - 1 (since decode < max always)
  have h_lt := variableRadixDecode_lt ω k τ
  have h_eq : variableRadixDecode ω k τ = completionCount ω k [] - 1 := by omega
  -- This means τ is the maximal element
  have h_max := (isMaxElement_iff_decode_max ω k τ).mpr h_eq
  -- isMaxElement says find? on non-reversed list returns none
  -- carryIndex uses find? on reversed list, which returned some j
  -- If reversed.find? returns some, then j satisfies the predicate, meaning j is non-maximal
  -- This contradicts h_max which says ALL positions are maximal
  simp only [isMaxElement, carryIndex] at h_max hj
  rw [Option.isNone_iff_eq_none] at h_max
  -- h_max : non-reversed find? = none (all positions are maximal)
  -- hj : reversed find? = some j (position j is non-maximal)
  -- Position j satisfies the predicate (by List.find?_some on reversed list)
  have h_j_sat := List.find?_some hj
  simp only [decide_eq_true_eq] at h_j_sat
  -- h_j_sat : τ.digitAt j < ω.radix (τ.getPrefix j.val _) - 1
  -- But h_max says find? on non-reversed returns none, meaning no position satisfies the predicate
  -- j is in the non-reversed list too, so this is a contradiction
  have h_j_mem : j ∈ List.finRange (k + 1) := List.mem_finRange j
  have h_none := List.find?_eq_none.mp h_max j h_j_mem
  -- h_none : decide(τ.digitAt j < ω.radix _ - 1) = false
  -- h_j_sat : τ.digitAt j < ω.radix _ - 1
  -- The two expressions have the same value, just different implicit proof terms
  -- Use decide_eq_true to convert h_j_sat to Bool form
  have h_j_sat_bool : decide (τ.digitAt j < ω.radix (τ.getPrefix j.val (Nat.le_of_lt j.isLt)) - 1) = true :=
    decide_eq_true h_j_sat
  -- Now show contradiction: h_none says decide ... = false, h_j_sat_bool says true
  -- They're about the same proposition (just different proof terms for the bound)
  simp only [h_j_sat_bool] at h_none
  exact h_none trivial

/-- The tick of a non-maximal element increments the decode by 1 -/
theorem tick_decode_succ (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k)
    (hmax : variableRadixDecode ω k τ < completionCount ω k [] - 1) :
    variableRadixDecode ω k (cyclicVariableTick ω k τ) = variableRadixDecode ω k τ + 1 := by
  rw [cyclicVariableTick_decode]
  have hpos : 0 < completionCount ω k [] := completionCount_pos ω k [] (by simp)
  -- Since decode < max - 1, (decode + 1) % max = decode + 1
  have h_lt : variableRadixDecode ω k τ + 1 < completionCount ω k [] := by omega
  exact Nat.mod_eq_of_lt h_lt

/--
Helper: take (i+1) = take i ++ [digit at i]
-/
private theorem take_succ_eq_append (s : PrefixWord) (i : ℕ) (hi : i < s.length) :
    s.take (i + 1) = s.take i ++ [s.get ⟨i, hi⟩] := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_append, List.length_singleton]
    rw [Nat.min_eq_left (Nat.succ_le_of_lt hi), Nat.min_eq_left (Nat.le_of_lt hi)]
  · intro n hn1 _
    simp only [List.length_take, Nat.min_eq_left (Nat.succ_le_of_lt hi)] at hn1
    by_cases hn : n < i
    · have h_left : n < (s.take i).length := by simp [Nat.min_eq_left (Nat.le_of_lt hi)]; omega
      rw [List.getElem_take, List.getElem_append_left h_left, List.getElem_take]
    · have hn_eq : n = i := by omega
      have h_take_len_i : (s.take i).length = i := by simp [Nat.min_eq_left (Nat.le_of_lt hi)]
      have h_right : (s.take i).length ≤ n := by rw [h_take_len_i]; omega
      rw [List.getElem_take, List.getElem_append_right h_right]
      simp only [h_take_len_i, hn_eq, Nat.sub_self, List.getElem_singleton, List.get_eq_getElem]

/--
Helper: Monotonicity of completionCount - extending a prefix decreases count.
-/
private theorem completionCount_mono (ω : RadixLaw) (k : ℕ) (s : PrefixWord) (d : ℕ)
    (hs : s.length < k + 1) (hd : d < ω.radix s) :
    completionCount ω k (s ++ [d]) ≤ completionCount ω k s := by
  rw [completionCount_rec ω k s hs]
  have hmem : d ∈ Finset.range (ω.radix s) := Finset.mem_range.mpr hd
  have hpos : ∀ x ∈ Finset.range (ω.radix s), 0 ≤ completionCount ω k (s ++ [x]) :=
    fun _ _ => Nat.zero_le _
  exact Finset.single_le_sum hpos hmem

/--
Helper: completionCount decreases as we take longer prefixes of τ
-/
private theorem completionCount_take_le (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k)
    (i : ℕ) (hi : i ≤ k + 1) :
    completionCount ω k (τ.digits.take i) ≤ completionCount ω k [] := by
  induction i with
  | zero => simp
  | succ n ih =>
    have hn_le : n ≤ k + 1 := Nat.le_of_succ_le hi
    have h_ih := ih hn_le
    by_cases hn_lt : n < τ.digits.length
    · have h_take_len : (τ.digits.take n).length < k + 1 := by
        simp only [List.length_take]
        rw [Nat.min_eq_left (Nat.le_of_lt hn_lt)]
        rw [τ.length_eq] at hn_lt
        omega
      rw [take_succ_eq_append τ.digits n hn_lt]
      have h_mono := completionCount_mono ω k (τ.digits.take n) (τ.digits.get ⟨n, hn_lt⟩)
          h_take_len (τ.valid n hn_lt)
      omega
    · -- n ≥ τ.digits.length, so take (n+1) = take n = τ.digits
      have hn_ge : τ.digits.length ≤ n := Nat.le_of_not_lt hn_lt
      have htake_succ : τ.digits.take (n + 1) = τ.digits := List.take_of_length_le (Nat.le_succ_of_le hn_ge)
      have htake_n : τ.digits.take n = τ.digits := List.take_of_length_le hn_ge
      rw [htake_succ, ← htake_n]
      exact h_ih

/--
When digit at position i is maximal, cumulativeAtPosition equals the completionCount difference.

This is the key lemma for the telescoping sum.
-/
private theorem cumulativeAtPosition_eq_of_maximal (ω : RadixLaw) (k : ℕ) (s : PrefixWord)
    (i : ℕ) (hi : i < s.length) (hlen : s.length ≤ k + 1)
    (hmax : s.get ⟨i, hi⟩ = ω.radix (s.take i) - 1) :
    cumulativeAtPosition ω k s i hi =
      completionCount ω k (s.take i) - completionCount ω k (s.take (i + 1)) := by
  -- Setup
  let pfx := s.take i
  let d := s.get ⟨i, hi⟩
  have h_take_len : pfx.length < k + 1 := by
    simp only [pfx, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
    omega
  -- d = radix - 1, so radix = d + 1 (since radix ≥ 2)
  have hradix : ω.radix pfx = d + 1 := by
    simp only [d, pfx] at hmax ⊢
    have h := ω.radix_pos (s.take i)
    omega
  have hd_val : d < ω.radix pfx := by rw [hradix]; exact Nat.lt_succ_self d
  -- By definition: cumulativeAtPosition = Σ_{j < d} W(pfx ++ [j])
  simp only [cumulativeAtPosition]
  -- Since d = radix - 1 (maximal), range(radix) = range(d+1) = range(d) ∪ {d}
  -- And W(pfx) = Σ_{j < radix} W(pfx ++ [j])
  -- So cumulativeAtPosition = W(pfx) - W(pfx ++ [d])
  have hW_split : completionCount ω k pfx =
      (Finset.range d).sum (fun j => completionCount ω k (pfx ++ [j])) +
      completionCount ω k (pfx ++ [d]) := by
    rw [completionCount_rec ω k pfx h_take_len]
    rw [hradix, Finset.range_add_one]
    have h_not_mem : d ∉ Finset.range d := by simp [Finset.mem_range]
    rw [Finset.sum_insert h_not_mem, add_comm]
  -- take(i+1) = pfx ++ [d]
  have htake_succ : s.take (i + 1) = pfx ++ [d] := take_succ_eq_append s i hi
  -- From hW_split: pfx = sum + (pfx ++ [d]), so sum = pfx - (pfx ++ [d])
  have h_eq : (Finset.range d).sum (fun j => completionCount ω k (pfx ++ [j])) =
      completionCount ω k pfx - completionCount ω k (pfx ++ [d]) := by
    have := hW_split
    omega
  rw [h_eq, htake_succ]

/--
**Key Lemma**: When all digits before position j are maximal,
the cumulative contribution from those positions equals:
  completionCount([]) - completionCount(prefix_j)

Mathematical proof:
- Base case (j=0): cumulativeCount([]) = 0 = W([]) - W([])
- Inductive case: When digit at position m is maximal (= radix - 1),
  cumulativeAtPosition(m) = Σ_{d < radix-1} W(prefix ++ [d])
                         = W(prefix) - W(prefix ++ [radix-1])
                         = W(take m) - W(take (m+1))
  Telescoping gives: cumulativeCount(take n) = W([]) - W(take n)

The formal proof requires careful manipulation of dependent types in the
cumulativeAtPosition definition. We defer this to avoid blocking progress.
-/
private theorem cumulative_all_maximal_prefix (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k)
    (j : Fin (k + 1)) (hmax_before : ∀ i : Fin (k + 1), i < j →
        τ.digitAt i = ω.radix (τ.getPrefix i.val (Nat.le_of_lt i.isLt)) - 1) :
    cumulativeCount ω k (τ.getPrefix j.val (Nat.le_of_lt j.isLt)) =
      completionCount ω k [] - completionCount ω k (τ.getPrefix j.val (Nat.le_of_lt j.isLt)) := by
  -- Proof by strong induction on j.val using telescoping sum.
  -- Base case: j = 0 => cumulativeCount [] = 0 = W([]) - W([])
  -- Inductive: cumulativeCount(take (j+1)) = cumulativeCount(take j) + cumulativeAtPosition(j)
  --            = [W([]) - W(take j)] + [W(take j) - W(take (j+1))]
  --            = W([]) - W(take (j+1))
  induction j using Fin.inductionOn with
  | zero =>
    -- Base case: j = 0, so τ.getPrefix 0 _ = τ.digits.take 0 = []
    simp only [FiniteVariableSpace.getPrefix, Fin.val_zero, List.take_zero, cumulativeCount,
      List.length_nil, Finset.range_zero, Finset.sum_empty, Nat.sub_self]
  | succ i ih =>
    -- Inductive case: j = i + 1
    -- First establish that getPrefix (i+1) = (getPrefix i) ++ [digit at i]
    have hi_lt : i.val < k + 1 := Nat.lt_of_lt_of_le i.isLt (Nat.le_succ k)
    have hi_lt_succ : i.val < (i.val + 1) := Nat.lt_succ_self i.val
    have hlen : τ.digits.length = k + 1 := τ.length_eq

    -- The hypothesis about maximal digits applies to all positions < i+1, so in particular to i
    -- We need to cast i : Fin k to Fin (k+1) to apply hmax_before
    have hi_fin_succ : i.val < k + 1 := Nat.lt_of_lt_of_le i.isLt (Nat.le_succ k)
    have h_i_max : τ.digitAt ⟨i.val, hi_fin_succ⟩ = ω.radix (τ.getPrefix i.val (Nat.le_of_lt hi_fin_succ)) - 1 := by
      apply hmax_before ⟨i.val, hi_fin_succ⟩
      simp only [Fin.lt_def, Fin.val_succ]
      exact Nat.lt_succ_self i.val

    -- Apply IH: need hmax_before for positions < i (i : Fin k, so we need Fin (k+1) versions)
    have h_ih_hyp : ∀ m : Fin (k + 1), m < ⟨i.val, hi_fin_succ⟩ → τ.digitAt m = ω.radix (τ.getPrefix m.val (Nat.le_of_lt m.isLt)) - 1 := by
      intro m hm
      apply hmax_before m
      simp only [Fin.lt_def] at hm ⊢
      simp only [Fin.val_succ]
      omega

    have h_ih := ih h_ih_hyp

    -- Show: cumulativeCount(take (i+1)) = cumulativeCount(take i) + cumulativeAtPosition(τ.digits, i)
    have h_take_len : (τ.digits.take i.val).length = i.val := by
      rw [List.length_take, hlen]
      exact Nat.min_eq_left (Nat.le_of_lt hi_lt)

    have h_take_succ_len : (τ.digits.take (i.val + 1)).length = i.val + 1 := by
      rw [List.length_take, hlen]
      exact Nat.min_eq_left (Nat.succ_le_of_lt hi_lt)

    -- cumulativeCount sums over positions 0..len-1
    -- For take(i+1), this is positions 0..i
    simp only [FiniteVariableSpace.getPrefix, cumulativeCount, Fin.val_succ]

    -- Split the sum: positions 0..(i-1) and position i
    have h_range_split : Finset.range (i.val + 1) = Finset.range i.val ∪ {i.val} := by
      ext x
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton]
      omega

    -- Simplify the length in the range
    simp only [h_take_succ_len]
    -- Split the sum using range split
    rw [h_range_split]
    have h_disjoint : Disjoint (Finset.range i.val) {i.val} := by
      simp [Finset.disjoint_singleton_right, Finset.mem_range]

    rw [Finset.sum_union h_disjoint]
    simp only [Finset.sum_singleton]

    -- The first sum equals cumulativeCount(take i)
    -- Goal has conditions m < i.val + 1 after simp with h_take_succ_len
    -- We'll prove by showing the sum + singleton equals the target
    have h_sum_eq : (Finset.range i.val).sum (fun m =>
        if hm : m < i.val + 1
        then cumulativeAtPosition ω k (τ.digits.take (i.val + 1)) m (by rw [h_take_succ_len]; exact hm) else 0) =
        cumulativeCount ω k (τ.digits.take i.val) := by
      simp only [cumulativeCount, h_take_len]
      apply Finset.sum_congr rfl
      intro m hm_range
      simp only [Finset.mem_range] at hm_range
      have hm_lt_succ : m < i.val + 1 := by omega
      have hm_lt : m < (τ.digits.take i.val).length := by rw [h_take_len]; omega
      simp only [hm_lt_succ, hm_lt, dite_true]
      -- Need: cumulativeAtPosition on take(i+1) at position m equals that on take(i)
      unfold cumulativeAtPosition
      -- Show the prefixes are equal
      have h_pfx_eq : (τ.digits.take (i.val + 1)).take m = (τ.digits.take i.val).take m := by
        simp only [List.take_take]
        congr 1
        rw [Nat.min_eq_left (Nat.le_of_lt hm_range), Nat.min_eq_left (by omega : m ≤ i.val + 1)]
      -- Show the digits are equal
      have hm_lt_succ' : m < (τ.digits.take (i.val + 1)).length := by rw [h_take_succ_len]; omega
      have h_dig_eq : (τ.digits.take (i.val + 1)).get ⟨m, hm_lt_succ'⟩ =
          (τ.digits.take i.val).get ⟨m, hm_lt⟩ := by
        simp only [List.get_eq_getElem, List.getElem_take]
      simp only [h_pfx_eq, h_dig_eq, hm_range, dite_true]

    -- Show the goal sum equals h_sum_eq's LHS - they differ only in proof terms
    have h_goal_sum_eq : (Finset.range i.val).sum (fun x =>
        if h : x < i.val + 1 then cumulativeAtPosition ω k (τ.digits.take (i.val + 1)) x (h_take_succ_len.symm ▸ h)
        else 0) = cumulativeCount ω k (τ.digits.take i.val) := by
      convert h_sum_eq using 2
    rw [h_goal_sum_eq]

    -- Now handle the term at position i
    have hi_lt_take_succ : i.val < (τ.digits.take (i.val + 1)).length := by
      rw [h_take_succ_len]; exact Nat.lt_succ_self i.val
    -- The condition in the goal is i.val < i.val + 1 after earlier simp
    have hi_lt_succ' : i.val < i.val + 1 := Nat.lt_succ_self i.val
    simp only [hi_lt_succ', dite_true]

    -- Apply cumulativeAtPosition_eq_of_maximal at position i
    have h_pos_eq : cumulativeAtPosition ω k (τ.digits.take (i.val + 1)) i.val hi_lt_take_succ =
        completionCount ω k (τ.digits.take i.val) - completionCount ω k (τ.digits.take (i.val + 1)) := by
      have hmax_digit : (τ.digits.take (i.val + 1)).get ⟨i.val, hi_lt_take_succ⟩ =
          ω.radix ((τ.digits.take (i.val + 1)).take i.val) - 1 := by
        -- digit at i in take(i+1) = τ.digits.get i = digitAt i
        have h_get : (τ.digits.take (i.val + 1)).get ⟨i.val, hi_lt_take_succ⟩ = τ.digits.get ⟨i.val, by omega⟩ := by
          simp only [List.get_eq_getElem, List.getElem_take]
        -- prefix at i in take(i+1) = take(i).take(i) = take(i) = getPrefix i
        have h_pfx : (τ.digits.take (i.val + 1)).take i.val = τ.digits.take i.val := by
          simp only [List.take_take, Nat.min_eq_left (by omega : i.val ≤ i.val + 1)]
        rw [h_get, h_pfx]
        -- Now use h_i_max
        simp only [FiniteVariableSpace.digitAt, FiniteVariableSpace.getPrefix, List.get_eq_getElem] at h_i_max
        convert h_i_max using 2
      have h_apply := cumulativeAtPosition_eq_of_maximal ω k (τ.digits.take (i.val + 1)) i.val hi_lt_take_succ
          (by rw [h_take_succ_len]; exact Nat.succ_le_of_lt hi_lt)
          hmax_digit
      -- Convert take(i, take(i+1, ...)) to take(i, ...)
      simp only [List.take_take, Nat.min_eq_left (by omega : i.val ≤ i.val + 1),
        Nat.min_self] at h_apply
      exact h_apply

    rw [h_pos_eq]

    -- Now we have: cumulativeCount(take i) + [W(take i) - W(take (i+1))]
    -- IH gives: cumulativeCount(take i) = W([]) - W(take i)
    -- Goal: W([]) - W(take (i+1))
    -- Convert h_ih to use τ.digits.take form
    simp only [FiniteVariableSpace.getPrefix, Fin.val_castSucc] at h_ih
    have h_mono : completionCount ω k (τ.digits.take (i.val + 1)) ≤ completionCount ω k (τ.digits.take i.val) := by
      -- Show take(i+1) = take(i) ++ [digit at i]
      have hi_len : i.val < τ.digits.length := by rw [hlen]; omega
      have h_take_append : τ.digits.take (i.val + 1) = τ.digits.take i.val ++ [τ.digits[i.val]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hi_len, Option.toList_some]
      rw [h_take_append]
      apply completionCount_mono
      · rw [h_take_len]; exact hi_lt
      · have := τ.valid i.val hi_len
        simp only [FiniteVariableSpace.getPrefix] at this
        exact this
    have h_mono2 : completionCount ω k (τ.digits.take i.val) ≤ completionCount ω k [] :=
      completionCount_take_le ω k τ i.val (Nat.le_of_lt hi_lt)
    omega

/-!
## Carry Result Construction

We construct the carry result explicitly and prove its decode equals decode(τ) + 1.
By injectivity of decode, this equals tickByCarry(τ), giving all three carry properties.
-/

/-- Zeros preserve validity of prefix -/
private theorem isValidPrefix'_append_replicate_zero (s : PrefixWord) (n : ℕ)
    (hv : isValidPrefix' ω s) : isValidPrefix' ω (s ++ List.replicate n 0) := by
  induction n generalizing s with
  | zero => simpa
  | succ n ih =>
    rw [show s ++ List.replicate (n + 1) 0 = (s ++ [0]) ++ List.replicate n 0 from by
      simp [List.replicate_succ, List.append_assoc, List.singleton_append]]
    exact ih (s ++ [0]) (isValidPrefix'_append_singleton hv (ω.radix_pos s))

/-- Prefix of a valid sequence is valid -/
private theorem take_isValidPrefix' (τ : FiniteVariableSpace ω k) (i : ℕ) :
    isValidPrefix' ω (τ.digits.take i) := by
  intro m hm
  simp only [List.length_take] at hm
  have hm' : m < τ.digits.length := by omega
  simp only [List.get_eq_getElem, List.getElem_take]
  have : (τ.digits.take i).take m = τ.digits.take m := by
    rw [List.take_take]; congr 1; omega
  rw [this]; exact τ.valid m hm'

/-- The carry result digit sequence -/
private def crDigits (τ : FiniteVariableSpace ω k) (j : Fin (k + 1)) : PrefixWord :=
  τ.digits.take j.val ++ [τ.digitAt j + 1] ++ List.replicate (k - j.val) 0

private theorem crDigits_length (τ : FiniteVariableSpace ω k) (j : Fin (k + 1)) :
    (crDigits τ j).length = k + 1 := by
  simp only [crDigits, List.length_append, List.length_take, τ.length_eq,
    List.length_singleton, List.length_replicate,
    Nat.min_eq_left (Nat.le_of_lt j.isLt)]
  omega

private theorem crDigits_get_lt (τ : FiniteVariableSpace ω k) (j : Fin (k + 1))
    (i : ℕ) (hi_cr : i < (crDigits τ j).length) (hi_τ : i < τ.digits.length)
    (hi_j : i < j.val) :
    (crDigits τ j).get ⟨i, hi_cr⟩ = τ.digits.get ⟨i, hi_τ⟩ := by
  simp only [crDigits, List.get_eq_getElem]
  have h_first_len : (τ.digits.take j.val).length = j.val := by
    rw [List.length_take, τ.length_eq]; exact Nat.min_eq_left (Nat.le_of_lt j.isLt)
  rw [List.getElem_append_left (by simp [h_first_len]; omega)]
  rw [List.getElem_append_left (by rw [h_first_len]; exact hi_j)]
  simp only [List.getElem_take]

private theorem crDigits_get_eq (τ : FiniteVariableSpace ω k) (j : Fin (k + 1)) :
    (crDigits τ j).get ⟨j.val, by rw [crDigits_length]; exact j.isLt⟩ =
      τ.digitAt j + 1 := by
  simp only [crDigits, List.get_eq_getElem]
  have h_first_len : (τ.digits.take j.val).length = j.val := by
    rw [List.length_take, τ.length_eq]; exact Nat.min_eq_left (Nat.le_of_lt j.isLt)
  rw [List.getElem_append_left (by simp [h_first_len])]
  rw [List.getElem_append_right (by rw [h_first_len])]
  simp [h_first_len]

private theorem crDigits_get_gt (τ : FiniteVariableSpace ω k) (j : Fin (k + 1))
    (i : ℕ) (hi_cr : i < (crDigits τ j).length) (hi_j : j.val < i) :
    (crDigits τ j).get ⟨i, hi_cr⟩ = 0 := by
  simp only [crDigits, List.get_eq_getElem]
  have h_mid_len : (τ.digits.take j.val ++ [τ.digitAt j + 1]).length = j.val + 1 := by
    simp [List.length_take, τ.length_eq, Nat.min_eq_left (Nat.le_of_lt j.isLt)]
  rw [List.getElem_append_right (by simp [h_mid_len]; omega)]
  simp only [h_mid_len, List.getElem_replicate]

private theorem crDigits_take_le (τ : FiniteVariableSpace ω k) (j : Fin (k + 1))
    (i : ℕ) (hi : i ≤ j.val) :
    (crDigits τ j).take i = τ.digits.take i := by
  apply List.ext_getElem
  · simp [crDigits_length, τ.length_eq, Nat.min_eq_left (by omega : i ≤ k + 1),
      Nat.min_eq_left (by omega : i ≤ k + 1)]
  · intro m hm1 hm2
    simp only [List.getElem_take]
    have hm_j : m < j.val := by
      simp only [List.length_take, crDigits_length] at hm1
      rw [Nat.min_eq_left (by omega : i ≤ k + 1)] at hm1; omega
    exact crDigits_get_lt τ j m (by rw [crDigits_length]; omega)
      (by rw [τ.length_eq]; omega) hm_j

/-- The carry result as a FiniteVariableSpace -/
private def carryResult (τ : FiniteVariableSpace ω k) (j : Fin (k + 1))
    (hj : carryIndex ω k τ = some j) : FiniteVariableSpace ω k where
  digits := crDigits τ j
  length_eq := crDigits_length τ j
  valid := by
    have hnotmax := notMaximal_at_carryIndex ω k τ j hj
    simp only [isMaximalDigit, FiniteVariableSpace.getPrefix] at hnotmax
    have hd_lt : τ.digitAt j + 1 < ω.radix (τ.digits.take j.val) := by
      have := τ.digitAt_lt j
      simp only [FiniteVariableSpace.getPrefix] at this
      omega
    have hpfx_valid := take_isValidPrefix' τ j.val
    have hext_valid := isValidPrefix'_append_singleton hpfx_valid hd_lt
    exact isValidPrefix'_append_replicate_zero _ _ hext_valid

/-!
## Decode Computation for Carry Result

Key: decode(carryResult) = decode(τ) + 1.
This follows from decomposing the cumulativeCount sum and using
the maximal-suffix telescoping property.
-/

/-- cumAtPos depends only on the prefix and digit at that position -/
private theorem cumAtPos_eq_of_take_digit_eq (s₁ s₂ : PrefixWord)
    (i : ℕ) (hi₁ : i < s₁.length) (hi₂ : i < s₂.length)
    (h_pfx : s₁.take i = s₂.take i)
    (h_dig : s₁.get ⟨i, hi₁⟩ = s₂.get ⟨i, hi₂⟩) :
    cumulativeAtPosition ω k s₁ i hi₁ = cumulativeAtPosition ω k s₂ i hi₂ := by
  simp only [cumulativeAtPosition, h_pfx, h_dig]

/-- cumAtPos is 0 when the digit is 0 -/
private theorem cumAtPos_zero (s : PrefixWord) (i : ℕ) (hi : i < s.length)
    (hd : s.get ⟨i, hi⟩ = 0) :
    cumulativeAtPosition ω k s i hi = 0 := by
  simp only [cumulativeAtPosition, hd, Finset.range_zero, Finset.sum_empty]

/-- Helper: (x - y) + (y - z) = x - z when z ≤ y ≤ x -/
private lemma nat_sub_add_sub {x y z : ℕ} (hzy : z ≤ y) (hyx : y ≤ x) :
    (x - y) + (y - z) = x - z := by omega

/-- Chain inequality: f(a+n) ≤ f(a) from pointwise monotonicity -/
private theorem chain_le {f : ℕ → ℕ} {a : ℕ} : ∀ (n : ℕ),
    (∀ i, i < n → f (a + i + 1) ≤ f (a + i)) → f (a + n) ≤ f a := by
  intro n; induction n with
  | zero => intro _; simp
  | succ m ih =>
    intro hmono
    exact Nat.le_trans (hmono m (by omega)) (ih (fun i hi => hmono i (by omega)))

/-- Telescoping sum for natural subtraction over range -/
private theorem nat_sub_telescope_range {f : ℕ → ℕ} {a : ℕ} : ∀ (n : ℕ),
    (∀ i, i < n → f (a + i + 1) ≤ f (a + i)) →
    (Finset.range n).sum (fun i => f (a + i) - f (a + i + 1)) = f a - f (a + n) := by
  intro n; induction n with
  | zero => intro _; simp
  | succ m ih =>
    intro hmono
    rw [Finset.sum_range_succ, ih (fun i hi => hmono i (by omega))]
    exact nat_sub_add_sub (hmono m (by omega)) (chain_le m (fun i hi => hmono i (by omega)))

/-- Telescoping sum for natural subtraction over Ico -/
private theorem nat_sub_telescope' {f : ℕ → ℕ} {a b : ℕ} (hab : a ≤ b)
    (hmono : ∀ i, a ≤ i → i < b → f (i + 1) ≤ f i) :
    (Finset.Ico a b).sum (fun i => f i - f (i + 1)) = f a - f b := by
  rw [Finset.sum_Ico_eq_sum_range]
  have h := nat_sub_telescope_range (b - a) (fun i hi => hmono (a + i) (by omega) (by omega))
  rwa [show a + (b - a) = b from by omega] at h

/-- Maximal suffix telescoping: Σ_{i=j+1}^{k} cumAtPos(τ, i) = W(τ.take(j+1)) - 1 -/
private theorem maximal_suffix_sum (τ : FiniteVariableSpace ω k) (j : Fin (k + 1))
    (hj : carryIndex ω k τ = some j) :
    (Finset.Ico (j.val + 1) (k + 1)).sum (fun i =>
      if hi : i < τ.digits.length then cumulativeAtPosition ω k τ.digits i hi else 0) =
    completionCount ω k (τ.digits.take (j.val + 1)) - 1 := by
  have hlen : τ.digits.length = k + 1 := τ.length_eq
  -- Step 1: Each digit after j is maximal → cumAtPos = W(take i) - W(take(i+1))
  have h_eq : ∀ i (hi_lo : j.val + 1 ≤ i) (hi_hi : i < k + 1),
      cumulativeAtPosition ω k τ.digits i (by rw [hlen]; exact hi_hi) =
      completionCount ω k (τ.digits.take i) - completionCount ω k (τ.digits.take (i + 1)) := by
    intro i hi_lo hi_hi
    have h_max := allMaximal_after_carryIndex ω k τ j hj ⟨i, hi_hi⟩ (by
      simp only [Fin.lt_def]; omega)
    simp only [isMaximalDigit, FiniteVariableSpace.digitAt, FiniteVariableSpace.getPrefix] at h_max
    exact cumulativeAtPosition_eq_of_maximal ω k τ.digits i (by rw [hlen]; exact hi_hi)
      (by omega) (by simp only [List.get_eq_getElem] at h_max ⊢; exact h_max)
  -- Step 2: Replace each term with the telescoping form
  have h_sum_eq : (Finset.Ico (j.val + 1) (k + 1)).sum (fun i =>
      if hi : i < τ.digits.length then cumulativeAtPosition ω k τ.digits i hi else 0) =
      (Finset.Ico (j.val + 1) (k + 1)).sum (fun i =>
        completionCount ω k (τ.digits.take i) -
        completionCount ω k (τ.digits.take (i + 1))) := by
    apply Finset.sum_congr rfl
    intro i hi_mem
    have ⟨hi_lo, hi_hi⟩ := Finset.mem_Ico.mp hi_mem
    simp only [show i < τ.digits.length from by rw [hlen]; exact hi_hi, dite_true]
    exact h_eq i hi_lo hi_hi
  rw [h_sum_eq]
  -- Step 3: Telescoping
  have hmono : ∀ i, j.val + 1 ≤ i → i < k + 1 →
      completionCount ω k (τ.digits.take (i + 1)) ≤ completionCount ω k (τ.digits.take i) := by
    intro i _ hi
    have hi_len : i < τ.digits.length := by rw [hlen]; exact hi
    rw [take_succ_eq_append τ.digits i hi_len]
    exact completionCount_mono ω k (τ.digits.take i) (τ.digits.get ⟨i, hi_len⟩)
      (by rw [List.length_take, τ.length_eq]; omega)
      (τ.valid i hi_len)
  have h_tele := @nat_sub_telescope' (fun i => completionCount ω k (τ.digits.take i))
    _ _ (by omega : j.val + 1 ≤ k + 1) hmono
  -- Beta-reduce the lambdas in h_tele, then rewrite
  simp only [] at h_tele
  rw [h_tele]
  -- completionCount(take(k+1)) = completionCount(τ.digits) = 1
  have h_full : τ.digits.take (k + 1) = τ.digits := List.take_of_length_le (by rw [hlen])
  rw [h_full, completionCount_of_length_eq ω k τ.digits hlen]

/-- Split a sum over range(n) into three parts at position j -/
private lemma sum_split_at (f : ℕ → ℕ) (j n : ℕ) (hjn : j < n) :
    (Finset.range n).sum f =
    (Finset.range j).sum f + f j + (Finset.Ico (j + 1) n).sum f := by
  have h1 : Finset.range n = Finset.range (j + 1) ∪ Finset.Ico (j + 1) n := by
    ext x; simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]; omega
  have h2 : Disjoint (Finset.range (j + 1)) (Finset.Ico (j + 1) n) := by
    simp only [Finset.disjoint_left, Finset.mem_range, Finset.mem_Ico]; omega
  rw [h1, Finset.sum_union h2, Finset.sum_range_succ]

/-- The cumulativeCount of cr differs from τ's by exactly 1 -/
private theorem carryResult_decode_eq (τ : FiniteVariableSpace ω k) (j : Fin (k + 1))
    (hj : carryIndex ω k τ = some j) :
    variableRadixDecode ω k (carryResult τ j hj) = variableRadixDecode ω k τ + 1 := by
  set cr := carryResult τ j hj
  have hlen_cr : cr.digits.length = k + 1 := crDigits_length τ j
  have hlen_τ : τ.digits.length = k + 1 := τ.length_eq
  set W := completionCount ω k (τ.digits.take (j.val + 1))
  -- Unfold to cumulativeCount
  simp only [variableRadixDecode, finiteRank, cumulativeCount, hlen_cr, hlen_τ]
  -- Define summand functions matching the simplified goal
  set f_cr : ℕ → ℕ := fun i =>
    if hi : i < k + 1 then cumulativeAtPosition ω k cr.digits i (hlen_cr ▸ hi) else 0
  set f_τ : ℕ → ℕ := fun i =>
    if hi : i < k + 1 then cumulativeAtPosition ω k τ.digits i (hlen_τ ▸ hi) else 0
  -- Match goal with our functions
  change (Finset.range (k + 1)).sum f_cr = (Finset.range (k + 1)).sum f_τ + 1
  -- Split both sums at position j
  rw [sum_split_at f_cr j.val (k + 1) j.isLt]
  rw [sum_split_at f_τ j.val (k + 1) j.isLt]
  -- Property 1: prefix parts equal (same prefix and digit for i < j)
  have h_prefix_eq : (Finset.range j.val).sum f_cr = (Finset.range j.val).sum f_τ := by
    apply Finset.sum_congr rfl
    intro i hi_mem
    have hi_j : i < j.val := Finset.mem_range.mp hi_mem
    simp only [f_cr, f_τ, dif_pos (show i < k + 1 from by omega)]
    exact cumAtPos_eq_of_take_digit_eq cr.digits τ.digits i _ _
      (crDigits_take_le τ j i (Nat.le_of_lt hi_j))
      (by simp only [List.get_eq_getElem]
          exact crDigits_get_lt τ j i (by rw [crDigits_length]; omega) (by omega) hi_j)
  -- Property 2: at j, cr has one extra term of size W
  have h_at_j : f_cr j.val = f_τ j.val + W := by
    simp only [f_cr, f_τ, dif_pos j.isLt]
    -- Replace cr.digits with crDigits τ j (definitionally equal, but simp can't
    -- rewrite inside List.get due to dependent types)
    change cumulativeAtPosition ω k (crDigits τ j) j.val _ =
           cumulativeAtPosition ω k τ.digits j.val _ + W
    -- Now unfold and rewrite using crDigits lemmas
    unfold cumulativeAtPosition
    rw [crDigits_take_le τ j j.val le_rfl, crDigits_get_eq τ j]
    -- LHS has range(digitAt+1), RHS has range(τ.digits.get). Split the +1 sum.
    rw [Finset.sum_range_succ]
    -- Goal: sum + completionCount(take_j ++ [digitAt]) = sum + W
    congr 1
    -- completionCount(take_j ++ [digitAt j]) = W = completionCount(take_(j+1))
    show completionCount ω k (τ.digits.take j.val ++ [τ.digitAt j]) =
         completionCount ω k (τ.digits.take (j.val + 1))
    congr 1
    simp only [FiniteVariableSpace.digitAt]
    exact (take_succ_eq_append τ.digits j.val (by rw [hlen_τ]; exact j.isLt)).symm
  -- Property 3: suffix of cr is 0 (all digits > j are 0)
  have h_suffix_cr : (Finset.Ico (j.val + 1) (k + 1)).sum f_cr = 0 := by
    apply Finset.sum_eq_zero
    intro i hi_mem
    have ⟨hi_lo, hi_hi⟩ := Finset.mem_Ico.mp hi_mem
    simp only [dif_pos hi_hi]
    exact cumAtPos_zero cr.digits i _
      (crDigits_get_gt τ j i (by rw [crDigits_length]; omega) (by omega))
  -- Property 4: suffix of τ = W - 1 (from maximal_suffix_sum)
  have h_suffix_τ : (Finset.Ico (j.val + 1) (k + 1)).sum f_τ = W - 1 := by
    have h := maximal_suffix_sum τ j hj
    convert h using 1
    apply Finset.sum_congr rfl
    intro i hi; simp only [f_τ, ← hlen_τ]
  -- Property 5: W ≥ 1
  have hW_pos : W ≥ 1 := by
    have := completionCount_pos ω k (τ.digits.take (j.val + 1))
      (by rw [List.length_take, hlen_τ]; omega)
    omega
  -- Combine: prefix + (at_j + W) + 0 = prefix + at_j + (W-1) + 1
  rw [h_prefix_eq, h_at_j, h_suffix_cr, h_suffix_τ]
  omega

/-- The carry result equals tickByCarry -/
private theorem carryResult_eq_tickByCarry (τ : FiniteVariableSpace ω k) (j : Fin (k + 1))
    (hj : carryIndex ω k τ = some j) :
    carryResult τ j hj = tickByCarry ω k τ := by
  have h_not_max := carryIndex_some_not_max ω k τ j hj
  have h_tick := tick_decode_succ ω k τ h_not_max
  have h_cr := carryResult_decode_eq τ j hj
  -- tickByCarry = cyclicVariableTick by definition, so goal is cr = cyclicVariableTick
  -- Both have same decode value, use injectivity
  exact decode_inj ω k (h_cr.trans h_tick.symm)

/-!
## Carry Propagation Properties
-/

/--
Prefix before carry index is unchanged.
-/
theorem carry_preserves_prefix (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k)
    (j : Fin (k + 1)) (hj : carryIndex ω k τ = some j)
    (i : Fin (k + 1)) (hi : i < j) :
    (tickByCarry ω k τ).digitAt i = τ.digitAt i := by
  have heq := carryResult_eq_tickByCarry τ j hj
  rw [← heq]
  simp only [FiniteVariableSpace.digitAt, carryResult]
  exact crDigits_get_lt τ j i.val (by rw [crDigits_length]; exact i.isLt)
    (by rw [τ.length_eq]; exact i.isLt) hi

/--
Carry increments the rightmost non-maximal digit.
-/
theorem carry_increments (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k)
    (j : Fin (k + 1)) (hj : carryIndex ω k τ = some j) :
    (tickByCarry ω k τ).digitAt j = τ.digitAt j + 1 := by
  have heq := carryResult_eq_tickByCarry τ j hj
  rw [← heq]
  simp only [FiniteVariableSpace.digitAt, carryResult]
  exact crDigits_get_eq τ j

/--
Suffix after carry index is reset to zeros.
-/
theorem carry_resets_suffix (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k)
    (j : Fin (k + 1)) (hj : carryIndex ω k τ = some j)
    (i : Fin (k + 1)) (hi : j < i) :
    (tickByCarry ω k τ).digitAt i = 0 := by
  have heq := carryResult_eq_tickByCarry τ j hj
  rw [← heq]
  simp only [FiniteVariableSpace.digitAt, carryResult]
  exact crDigits_get_gt τ j i.val (by rw [crDigits_length]; exact i.isLt)
    hi

end FdrsFormal.Modes.VariableRadix
