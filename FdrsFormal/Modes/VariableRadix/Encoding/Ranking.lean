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

# Variable Radix Ranking (Decode)

This file constructs the ranking function φ_ω that maps sequences to natural numbers.

## Mathematical Content (fdrs.md lines 4071-4078)

**Definition 62 (variable-radix decode)**:
Define dec^{(k)}_ω: R^{(k)}_ω → {0, ..., |R^{(k)}_ω| - 1} by:
  dec^{(k)}_ω(τ) = #{σ ∈ R^{(k)}_ω : σ <_lex τ}

This counts sequences lexicographically smaller than τ.

**Recursive computation**:
  dec^{(k)}_ω(d_0, ..., d_k) = ∑_{d < d_0} W^{(k)}_ω([d]) + dec^{(k)}_ω'(d_1, ..., d_k)

where the second decode is relative to the subtree rooted at d_0.

## References

- fdrs.md, Phase 5-6, Section 3 (lines 4071-4078)
- DEPENDENCY_BASED_STRUCTURE.md, Modes/VariableRadix/Encoding
-/

import FdrsFormal.Modes.VariableRadix.Encoding.SubtreeCards

namespace FdrsFormal.Modes.VariableRadix

/-!
## Lexicographic Order
-/

/-- Lexicographic comparison of prefix words (uses List.Lex from Mathlib) -/
def lexLt (s t : PrefixWord) : Prop := List.Lex (· < ·) s t

/-- Lexicographic order is a strict total order on same-length prefixes -/
instance : LT PrefixWord where
  lt := lexLt

/-!
## Variable Radix Decode (Ranking)

We use the `finiteRank` function defined in SubtreeCards.lean, which computes:
  rank(τ) = ∑_{i=0}^{k} ∑_{d < τ[i]} W^{(k)}_ω(τ[<i] ++ [d])

This counts all completions that are lexicographically smaller than τ.
-/

/--
The decode (ranking) function for variable radix spaces.

**fdrs.md Definition 62**: dec^{(k)}_ω(τ) = #{σ : σ <_lex τ}

This is computed by summing, for each position i, the completion counts
of all prefixes with the same initial segment but smaller digit at position i.
-/
def variableRadixDecode (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k) : ℕ :=
  finiteRank ω k τ

/-!
## Properties of Decode
-/

/-- Helper: completionCount recursive split for shorter prefixes -/
private theorem completionCount_sum_children (ω : RadixLaw) (k : ℕ) (s : PrefixWord)
    (hs : s.length < k + 1) :
    completionCount ω k s = (Finset.range (ω.radix s)).sum fun d => completionCount ω k (s ++ [d]) :=
  completionCount_rec ω k s hs

/-- The i-th digit is valid (bounded by radix at that prefix) -/
private theorem digit_valid (τ : FiniteVariableSpace ω k) (i : ℕ) (hi : i < τ.digits.length) :
    τ.digits.get ⟨i, hi⟩ < ω.radix (τ.digits.take i) :=
  τ.valid i hi

/-- Taking i+1 elements equals taking i and appending the i-th element -/
private theorem take_succ_eq (s : PrefixWord) (i : ℕ) (hi : i < s.length) :
    s.take (i + 1) = s.take i ++ [s.get ⟨i, hi⟩] := by
  induction s generalizing i with
  | nil => exact absurd hi (Nat.not_lt_zero i)
  | cons x xs ih =>
    cases i with
    | zero => simp [List.get]
    | succ i' =>
      simp only [List.take, List.cons_append, List.cons.injEq, true_and]
      have hi' : i' < xs.length := Nat.lt_of_succ_lt_succ hi
      exact ih i' hi'

/-- Helper: cumulative at position i is bounded by completionCount difference -/
private theorem cumulativeAtPosition_le (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k)
    (i : ℕ) (hi : i < τ.digits.length) (hi' : i < k + 1) :
    cumulativeAtPosition ω k τ.digits i hi ≤
      completionCount ω k (τ.digits.take i) - completionCount ω k (τ.digits.take (i + 1)) := by
  -- Set up notation
  let pfx := τ.digits.take i
  let d_i := τ.digits.get ⟨i, hi⟩
  -- The prefix at position i has length < k+1
  have h_take_len : pfx.length < k + 1 := by
    simp only [pfx, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
    omega
  -- The digit is valid
  have hdig : d_i < ω.radix pfx := digit_valid τ i hi
  -- Unfold cumulativeAtPosition: it equals sum over d < d_i
  have hcum : cumulativeAtPosition ω k τ.digits i hi =
      (Finset.range d_i).sum fun d => completionCount ω k (pfx ++ [d]) := rfl
  -- completionCount(pfx) = sum over all children
  have hW_pfx : completionCount ω k pfx =
      (Finset.range (ω.radix pfx)).sum fun d => completionCount ω k (pfx ++ [d]) :=
    completionCount_sum_children ω k pfx h_take_len
  -- take (i+1) = pfx ++ [d_i]
  have htake_succ : τ.digits.take (i + 1) = pfx ++ [d_i] :=
    take_succ_eq τ.digits i hi
  -- Abbreviate the sums
  let sum_small := (Finset.range d_i).sum fun d => completionCount ω k (pfx ++ [d])
  let sum_large := (Finset.Ico d_i (ω.radix pfx)).sum fun d => completionCount ω k (pfx ++ [d])
  let W_di := completionCount ω k (pfx ++ [d_i])
  -- Split the full sum
  have hsplit : (Finset.range (ω.radix pfx)).sum (fun d => completionCount ω k (pfx ++ [d])) =
      sum_small + sum_large := by
    rw [← Finset.sum_union]
    · congr 1; ext d; simp [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]; omega
    · simp [Finset.disjoint_left, Finset.mem_range, Finset.mem_Ico]; intro x hx; omega
  -- The Ico sum contains W(pfx++[d_i])
  have hIco_ge : W_di ≤ sum_large := by
    have hmem : d_i ∈ Finset.Ico d_i (ω.radix pfx) := by simp [Finset.mem_Ico, hdig]
    have hpos : ∀ d ∈ Finset.Ico d_i (ω.radix pfx), 0 ≤ completionCount ω k (pfx ++ [d]) :=
      fun d _ => Nat.zero_le _
    exact Finset.single_le_sum hpos hmem
  -- Rewrite the goal
  calc cumulativeAtPosition ω k τ.digits i hi
      = sum_small := hcum
    _ ≤ sum_small + sum_large - W_di := by omega
    _ = completionCount ω k pfx - W_di := by rw [← hsplit, ← hW_pfx]
    _ = completionCount ω k (τ.digits.take i) - completionCount ω k (τ.digits.take (i + 1)) := by
        rw [htake_succ]

/-- Monotonicity of completionCount: extending a prefix decreases count -/
private theorem completionCount_take_mono (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k)
    (i : ℕ) (hi : i < τ.digits.length) :
    completionCount ω k (τ.digits.take (i + 1)) ≤ completionCount ω k (τ.digits.take i) := by
  have hi' : i < k + 1 := by rw [← τ.length_eq]; exact hi
  have h_take_len : (τ.digits.take i).length < k + 1 := by
    simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]; omega
  rw [completionCount_sum_children ω k (τ.digits.take i) h_take_len]
  rw [take_succ_eq τ.digits i hi]
  have hmem : τ.digits.get ⟨i, hi⟩ ∈ Finset.range (ω.radix (τ.digits.take i)) := by
    simp only [Finset.mem_range]; exact digit_valid τ i hi
  have hpos : ∀ d ∈ Finset.range (ω.radix (τ.digits.take i)),
      0 ≤ completionCount ω k (τ.digits.take i ++ [d]) := fun d _ => Nat.zero_le _
  exact Finset.single_le_sum hpos hmem

/-- For a decreasing sequence, f(n) ≤ f(0) -/
private theorem decreasing_le_initial {f : ℕ → ℕ} {n : ℕ}
    (hmono : ∀ i, i < n → f (i + 1) ≤ f i) : f n ≤ f 0 := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ m ih =>
    have h1 : f (m + 1) ≤ f m := hmono m (Nat.lt_succ_self m)
    have h2 : f m ≤ f 0 := ih (fun i hi => hmono i (Nat.lt_succ_of_lt hi))
    exact Nat.le_trans h1 h2

/-- Telescoping sum for natural subtraction with decreasing sequence -/
private theorem nat_sub_telescope {f : ℕ → ℕ} {n : ℕ}
    (hmono : ∀ i, i < n → f (i + 1) ≤ f i) :
    (Finset.range n).sum (fun i => f i - f (i + 1)) = f 0 - f n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hmono' : ∀ j, j < n → f (j + 1) ≤ f j := fun j hj => hmono j (Nat.lt_succ_of_lt hj)
    rw [ih hmono']
    -- Goal: (f 0 - f n) + (f n - f (n + 1)) = f 0 - f (n + 1)
    have hfn_le : f (n + 1) ≤ f n := hmono n (Nat.lt_succ_self n)
    have hfn_le_f0 : f n ≤ f 0 := decreasing_le_initial hmono'
    omega

/-- The decode value is bounded by the space cardinality -/
theorem variableRadixDecode_lt (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k) :
    variableRadixDecode ω k τ < completionCount ω k [] := by
  unfold variableRadixDecode finiteRank cumulativeCount
  have hlen : τ.digits.length = k + 1 := τ.length_eq
  -- The full sequence has count 1
  have hW_full : completionCount ω k τ.digits = 1 :=
    completionCount_of_length_eq ω k τ.digits hlen
  -- Abbreviate the sum
  set S := (Finset.range τ.digits.length).sum
      (fun i => if hi : i < τ.digits.length then cumulativeAtPosition ω k τ.digits i hi else 0) with hS
  -- Each cumulativeAtPosition ≤ W(take i) - W(take (i+1))
  have hstep1 : S ≤ (Finset.range τ.digits.length).sum
      (fun i => if hi : i < τ.digits.length then
        completionCount ω k (τ.digits.take i) - completionCount ω k (τ.digits.take (i + 1))
      else 0) := by
    apply Finset.sum_le_sum
    intro i hi_mem
    simp only [Finset.mem_range] at hi_mem
    simp only [hi_mem, dite_true]
    have hi' : i < k + 1 := by rw [← hlen]; exact hi_mem
    exact cumulativeAtPosition_le ω k τ i hi_mem hi'
  -- The RHS sums to at most W([]) - W(τ.digits) = W([]) - 1
  have hstep2 : (Finset.range τ.digits.length).sum
      (fun i => if hi : i < τ.digits.length then
        completionCount ω k (τ.digits.take i) - completionCount ω k (τ.digits.take (i + 1))
      else 0) ≤ completionCount ω k [] - 1 := by
    -- Simplify the dite
    have hsimpl : (Finset.range τ.digits.length).sum
        (fun i => if hi : i < τ.digits.length then
          completionCount ω k (τ.digits.take i) - completionCount ω k (τ.digits.take (i + 1))
        else 0) =
        (Finset.range τ.digits.length).sum
          (fun i => completionCount ω k (τ.digits.take i) -
            completionCount ω k (τ.digits.take (i + 1))) := by
      apply Finset.sum_congr rfl
      intro i hi_mem
      simp [Finset.mem_range.mp hi_mem]
    rw [hsimpl]
    -- Telescoping for nat subtraction with decreasing sequence
    have hmono : ∀ i, i < τ.digits.length →
        completionCount ω k (τ.digits.take (i + 1)) ≤ completionCount ω k (τ.digits.take i) :=
      fun i hi => completionCount_take_mono ω k τ i hi
    -- Apply the telescoping lemma
    let f := fun i => completionCount ω k (τ.digits.take i)
    have htelescope := nat_sub_telescope (f := f) (n := τ.digits.length) hmono
    -- f 0 = completionCount ω k [] and f (length) = completionCount ω k τ.digits
    have hf0 : f 0 = completionCount ω k [] := by simp [f]
    have hfn : f τ.digits.length = completionCount ω k τ.digits := by simp [f]
    -- The sum equals f 0 - f n by telescoping
    have heq : (Finset.range τ.digits.length).sum (fun i =>
        completionCount ω k (τ.digits.take i) - completionCount ω k (τ.digits.take (i + 1))) =
        f 0 - f τ.digits.length := htelescope
    rw [heq, hf0, hfn, hW_full]
  -- Combine: S ≤ W([]) - 1 < W([])
  have hpos : 0 < completionCount ω k [] := completionCount_pos ω k [] (by simp)
  omega

/-- The remaining contribution from position i onwards is bounded by W(take i) - 1 -/
private theorem remaining_contrib_bound (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k) (i : ℕ)
    (hi : i < k + 1) :
    (Finset.Ico i (k + 1)).sum (fun j =>
      if hj : j < τ.digits.length then cumulativeAtPosition ω k τ.digits j hj else 0) ≤
    completionCount ω k (τ.digits.take i) - 1 := by
  have hlen : τ.digits.length = k + 1 := τ.length_eq
  -- Use the bound from cumulativeAtPosition_le and telescope
  have hbound : (Finset.Ico i (k + 1)).sum (fun j =>
      if hj : j < τ.digits.length then cumulativeAtPosition ω k τ.digits j hj else 0) ≤
      (Finset.Ico i (k + 1)).sum (fun j =>
        completionCount ω k (τ.digits.take j) - completionCount ω k (τ.digits.take (j + 1))) := by
    apply Finset.sum_le_sum
    intro j hj_mem
    simp only [Finset.mem_Ico] at hj_mem
    have hj' : j < τ.digits.length := by rw [hlen]; exact hj_mem.2
    simp only [hj', dite_true]
    exact cumulativeAtPosition_le ω k τ j hj' hj_mem.2
  -- The RHS telescopes - use the Finset.sum_Ico_eq_sum_range conversion and nat_sub_telescope
  have htelescope : (Finset.Ico i (k + 1)).sum (fun j =>
      completionCount ω k (τ.digits.take j) - completionCount ω k (τ.digits.take (j + 1))) =
      completionCount ω k (τ.digits.take i) - completionCount ω k (τ.digits.take (k + 1)) := by
    -- Helper: monotonicity
    have hmono : ∀ j, j < k + 1 →
        completionCount ω k (τ.digits.take (j + 1)) ≤ completionCount ω k (τ.digits.take j) := by
      intro j hj
      have hj' : j < τ.digits.length := by rw [hlen]; exact hj
      exact completionCount_take_mono ω k τ j hj'
    -- Convert Ico to range
    rw [Finset.sum_Ico_eq_sum_range]
    -- Define f(j) = W(take (i + j)) so f(0) = W(take i) and f(k+1-i) = W(take(k+1))
    let n := k + 1 - i
    let f := fun j => completionCount ω k (τ.digits.take (i + j))
    -- The sum becomes ∑_{j < n} (f(j) - f(j+1))
    have hsum_eq : (Finset.range n).sum (fun j => completionCount ω k (τ.digits.take (i + j)) -
        completionCount ω k (τ.digits.take (i + j + 1))) =
        (Finset.range n).sum (fun j => f j - f (j + 1)) := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [f]
      ring_nf
    rw [hsum_eq]
    -- Apply telescoping
    have hmono_f : ∀ j, j < n → f (j + 1) ≤ f j := by
      intro j hj
      simp only [f]
      have hbound : i + j < k + 1 := by omega
      exact hmono (i + j) hbound
    rw [nat_sub_telescope hmono_f]
    simp only [f, Nat.add_zero, n]
    congr 1
    have h_add : i + (k + 1 - i) = k + 1 := Nat.add_sub_cancel' (Nat.le_of_lt hi)
    rw [h_add]
  calc (Finset.Ico i (k + 1)).sum (fun j =>
        if hj : j < τ.digits.length then cumulativeAtPosition ω k τ.digits j hj else 0)
      ≤ (Finset.Ico i (k + 1)).sum (fun j =>
          completionCount ω k (τ.digits.take j) - completionCount ω k (τ.digits.take (j + 1))) := hbound
    _ = completionCount ω k (τ.digits.take i) - completionCount ω k (τ.digits.take (k + 1)) := htelescope
    _ = completionCount ω k (τ.digits.take i) - completionCount ω k τ.digits := by
        congr 1
        have h : k + 1 ≥ τ.digits.length := by rw [hlen]
        rw [List.take_of_length_le h]
    _ = completionCount ω k (τ.digits.take i) - 1 := by
        rw [completionCount_of_length_eq ω k τ.digits hlen]

/-- Cumulative contribution before position i -/
private def sumBefore (ω : RadixLaw) (k : ℕ) (s : PrefixWord) (i : ℕ) : ℕ :=
  (Finset.range i).sum fun j =>
    if hj : j < s.length then cumulativeAtPosition ω k s j hj else 0

/-- Cumulative contribution from position i onwards -/
private def sumFrom (ω : RadixLaw) (k : ℕ) (s : PrefixWord) (i : ℕ) : ℕ :=
  (Finset.Ico i s.length).sum fun j =>
    if hj : j < s.length then cumulativeAtPosition ω k s j hj else 0

/-- The cumulativeAtPosition depends only on the prefix up to position i -/
private theorem cumulativeAtPosition_eq_of_prefix_eq (ω : RadixLaw) (k : ℕ)
    (τ σ : FiniteVariableSpace ω k) (j : ℕ)
    (hjτ : j < τ.digits.length) (hjσ : j < σ.digits.length)
    (hprefix : τ.digits.take (j + 1) = σ.digits.take (j + 1)) :
    cumulativeAtPosition ω k τ.digits j hjτ = cumulativeAtPosition ω k σ.digits j hjσ := by
  -- cumulativeAtPosition depends on τ.digits.take j and τ.digits.get ⟨j, hjτ⟩
  simp only [cumulativeAtPosition]
  -- Need: τ.digits.take j = σ.digits.take j and τ.digits[j] = σ.digits[j]
  have h_take : τ.digits.take j = σ.digits.take j := by
    have h1 : τ.digits.take j = (τ.digits.take (j + 1)).take j := by
      rw [List.take_take]; congr 1; omega
    have h2 : σ.digits.take j = (σ.digits.take (j + 1)).take j := by
      rw [List.take_take]; congr 1; omega
    rw [h1, h2, hprefix]
  have h_digit : τ.digits.get ⟨j, hjτ⟩ = σ.digits.get ⟨j, hjσ⟩ := by
    -- Use the fact that take (j+1) = take j ++ [get j]
    have hτ : τ.digits.take (j + 1) = τ.digits.take j ++ [τ.digits.get ⟨j, hjτ⟩] :=
      take_succ_eq τ.digits j hjτ
    have hσ : σ.digits.take (j + 1) = σ.digits.take j ++ [σ.digits.get ⟨j, hjσ⟩] :=
      take_succ_eq σ.digits j hjσ
    rw [hτ, hσ, h_take] at hprefix
    have h_lists_eq : [τ.digits.get ⟨j, hjτ⟩] = [σ.digits.get ⟨j, hjσ⟩] :=
      List.append_cancel_left hprefix
    exact List.singleton_injective h_lists_eq
  rw [h_take, h_digit]

/-- Sum before position i is equal when prefixes agree up to i -/
private theorem sumBefore_eq_of_prefix_eq (ω : RadixLaw) (k : ℕ)
    (τ σ : FiniteVariableSpace ω k) (i : ℕ)
    (hi : i ≤ k + 1)
    (hprefix : τ.digits.take i = σ.digits.take i) :
    sumBefore ω k τ.digits i = sumBefore ω k σ.digits i := by
  simp only [sumBefore]
  apply Finset.sum_congr rfl
  intro j hj_mem
  simp only [Finset.mem_range] at hj_mem
  have hjτ : j < τ.digits.length := by rw [τ.length_eq]; omega
  have hjσ : j < σ.digits.length := by rw [σ.length_eq]; omega
  simp only [hjτ, hjσ, dite_true]
  apply cumulativeAtPosition_eq_of_prefix_eq
  -- Need: τ.digits.take (j + 1) = σ.digits.take (j + 1)
  have h1 : τ.digits.take (j + 1) = (τ.digits.take i).take (j + 1) := by
    rw [List.take_take]; congr 1; omega
  have h2 : σ.digits.take (j + 1) = (σ.digits.take i).take (j + 1) := by
    rw [List.take_take]; congr 1; omega
  rw [h1, h2, hprefix]

/-- At position i, cumulative at σ ≥ cumulative at τ + W(τ.take(i+1)) when τ[i] < σ[i] -/
private theorem cumulativeAtPosition_gap (ω : RadixLaw) (k : ℕ)
    (τ σ : FiniteVariableSpace ω k) (i : ℕ)
    (hi : i < k + 1)
    (hprefix : τ.digits.take i = σ.digits.take i)
    (hlt : τ.digitAt ⟨i, hi⟩ < σ.digitAt ⟨i, hi⟩) :
    let hiτ := by rw [τ.length_eq]; exact hi
    let hiσ := by rw [σ.length_eq]; exact hi
    cumulativeAtPosition ω k τ.digits i hiτ + completionCount ω k (τ.digits.take (i + 1)) ≤
      cumulativeAtPosition ω k σ.digits i hiσ := by
  intro hiτ hiσ
  simp only [cumulativeAtPosition, FiniteVariableSpace.digitAt, FiniteVariableSpace.getPrefix] at hlt ⊢
  -- τ.digits.get ⟨i, hiτ⟩ < σ.digits.get ⟨i, hiσ⟩
  set d_τ := τ.digits.get ⟨i, hiτ⟩
  set d_σ := σ.digits.get ⟨i, hiσ⟩
  set pfx_τ := τ.digits.take i
  set pfx_σ := σ.digits.take i
  -- pfx_τ = pfx_σ
  have h_pfx : pfx_τ = pfx_σ := hprefix
  -- τ's contribution: ∑_{d < d_τ} W(pfx_τ ++ [d])
  -- σ's contribution: ∑_{d < d_σ} W(pfx_σ ++ [d])
  -- Since d_τ < d_σ, σ's sum includes τ's sum plus terms for d_τ ≤ d < d_σ
  -- In particular, it includes W(pfx_τ ++ [d_τ]) = W(τ.take(i+1))
  have hsplit : (Finset.range d_σ) = (Finset.range d_τ) ∪ (Finset.Ico d_τ d_σ) := by
    ext d; simp [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
  have hdisjoint : Disjoint (Finset.range d_τ) (Finset.Ico d_τ d_σ) := by
    simp [Finset.disjoint_left, Finset.mem_range, Finset.mem_Ico]; intro x hx; omega
  rw [hsplit, Finset.sum_union hdisjoint]
  -- The sum over range d_τ with pfx_σ equals the sum over range d_τ with pfx_τ
  have h_sum_eq : (Finset.range d_τ).sum (fun d => completionCount ω k (pfx_σ ++ [d])) =
      (Finset.range d_τ).sum (fun d => completionCount ω k (pfx_τ ++ [d])) := by
    apply Finset.sum_congr rfl
    intro d _
    rw [h_pfx]
  rw [h_sum_eq]
  -- The Ico sum contains the term for d_τ
  have h_mem : d_τ ∈ Finset.Ico d_τ d_σ := by simp [Finset.mem_Ico, hlt]
  -- τ.take(i+1) = pfx_τ ++ [d_τ]
  have h_take_succ : τ.digits.take (i + 1) = pfx_τ ++ [d_τ] := take_succ_eq τ.digits i hiτ
  rw [h_take_succ]
  -- Goal: sum_small + W(pfx_τ ++ [d_τ]) ≤ sum_small + sum_large
  -- The Ico sum contains W(pfx_σ ++ [d_τ]) = W(pfx_τ ++ [d_τ])
  have h_Ico_eq : (Finset.Ico d_τ d_σ).sum (fun d => completionCount ω k (pfx_σ ++ [d])) =
      (Finset.Ico d_τ d_σ).sum (fun d => completionCount ω k (pfx_τ ++ [d])) := by
    apply Finset.sum_congr rfl
    intro d _
    rw [h_pfx]
  have h_single_le : completionCount ω k (pfx_τ ++ [d_τ]) ≤
      (Finset.Ico d_τ d_σ).sum (fun d => completionCount ω k (pfx_τ ++ [d])) :=
    Finset.single_le_sum (f := fun d => completionCount ω k (pfx_τ ++ [d]))
        (fun d _ => Nat.zero_le _) h_mem
  calc (Finset.range d_τ).sum (fun d => completionCount ω k (pfx_τ ++ [d])) +
          completionCount ω k (pfx_τ ++ [d_τ])
      ≤ (Finset.range d_τ).sum (fun d => completionCount ω k (pfx_τ ++ [d])) +
          (Finset.Ico d_τ d_σ).sum (fun d => completionCount ω k (pfx_τ ++ [d])) := by
        apply Nat.add_le_add_left h_single_le
    _ = (Finset.range d_τ).sum (fun d => completionCount ω k (pfx_τ ++ [d])) +
          (Finset.Ico d_τ d_σ).sum (fun d => completionCount ω k (pfx_σ ++ [d])) := by
        rw [← h_Ico_eq]

/-- Helper: if τ < σ at position i with same prefix, the contribution differs -/
private theorem decode_lt_of_digit_lt (ω : RadixLaw) (k : ℕ)
    (τ σ : FiniteVariableSpace ω k) (i : ℕ) (hi : i < k + 1)
    (hprefix : τ.digits.take i = σ.digits.take i)
    (hlt : τ.digitAt ⟨i, hi⟩ < σ.digitAt ⟨i, hi⟩) :
    variableRadixDecode ω k τ < variableRadixDecode ω k σ := by
  -- Length facts
  have hlenτ : τ.digits.length = k + 1 := τ.length_eq
  have hlenσ : σ.digits.length = k + 1 := σ.length_eq
  have hiτ : i < τ.digits.length := by rw [hlenτ]; exact hi
  have hiσ : i < σ.digits.length := by rw [hlenσ]; exact hi
  -- Decompose the decode sums
  unfold variableRadixDecode finiteRank cumulativeCount
  -- Split the sum at position i: sum = sumBefore + cumAt_i + sumAfter
  -- For τ: decode(τ) = sumBefore(τ, i) + cumAt(τ, i) + sumAfter(τ, i+1)
  -- For σ: decode(σ) = sumBefore(σ, i) + cumAt(σ, i) + sumAfter(σ, i+1)
  -- sumBefore(τ, i) = sumBefore(σ, i) by hprefix
  have h_before_eq : sumBefore ω k τ.digits i = sumBefore ω k σ.digits i :=
    sumBefore_eq_of_prefix_eq ω k τ σ i (Nat.le_of_lt hi) hprefix
  -- The decomposition of the full sum
  have h_decomp_τ : (Finset.range τ.digits.length).sum (fun j =>
      if hj : j < τ.digits.length then cumulativeAtPosition ω k τ.digits j hj else 0) =
      sumBefore ω k τ.digits i + cumulativeAtPosition ω k τ.digits i hiτ + sumFrom ω k τ.digits (i + 1) := by
    simp only [sumBefore, sumFrom, hlenτ]
    -- range (k+1) = range i ∪ {i} ∪ Ico (i+1) (k+1)
    have hsplit : Finset.range (k + 1) = Finset.range i ∪ {i} ∪ Finset.Ico (i + 1) (k + 1) := by
      ext j; simp [Finset.mem_range, Finset.mem_union, Finset.mem_singleton, Finset.mem_Ico]; omega
    have hdisj1 : Disjoint (Finset.range i) {i} := by
      rw [Finset.disjoint_left]; intro a ha_range ha_sing
      simp only [Finset.mem_range] at ha_range
      simp only [Finset.mem_singleton] at ha_sing
      omega
    have hdisj2 : Disjoint (Finset.range i ∪ {i}) (Finset.Ico (i + 1) (k + 1)) := by
      rw [Finset.disjoint_left]; intro a ha_left ha_right
      simp only [Finset.mem_union, Finset.mem_range, Finset.mem_singleton] at ha_left
      simp only [Finset.mem_Ico] at ha_right
      omega
    rw [hsplit, Finset.sum_union hdisj2, Finset.sum_union hdisj1]
    simp only [Finset.sum_singleton, hi, dite_true, Nat.add_comm]
  have h_decomp_σ : (Finset.range σ.digits.length).sum (fun j =>
      if hj : j < σ.digits.length then cumulativeAtPosition ω k σ.digits j hj else 0) =
      sumBefore ω k σ.digits i + cumulativeAtPosition ω k σ.digits i hiσ + sumFrom ω k σ.digits (i + 1) := by
    simp only [sumBefore, sumFrom, hlenσ]
    have hsplit : Finset.range (k + 1) = Finset.range i ∪ {i} ∪ Finset.Ico (i + 1) (k + 1) := by
      ext j; simp [Finset.mem_range, Finset.mem_union, Finset.mem_singleton, Finset.mem_Ico]; omega
    have hdisj1 : Disjoint (Finset.range i) {i} := by
      rw [Finset.disjoint_left]; intro a ha_range ha_sing
      simp only [Finset.mem_range] at ha_range
      simp only [Finset.mem_singleton] at ha_sing
      omega
    have hdisj2 : Disjoint (Finset.range i ∪ {i}) (Finset.Ico (i + 1) (k + 1)) := by
      rw [Finset.disjoint_left]; intro a ha_left ha_right
      simp only [Finset.mem_union, Finset.mem_range, Finset.mem_singleton] at ha_left
      simp only [Finset.mem_Ico] at ha_right
      omega
    rw [hsplit, Finset.sum_union hdisj2, Finset.sum_union hdisj1]
    simp only [Finset.sum_singleton, hi, dite_true, Nat.add_comm]
  rw [h_decomp_τ, h_decomp_σ, h_before_eq]
  -- Need: cumAt(τ,i) + sumFrom(τ,i+1) < cumAt(σ,i) + sumFrom(σ,i+1)
  -- From cumulativeAtPosition_gap: cumAt(τ,i) + W(τ.take(i+1)) ≤ cumAt(σ,i)
  -- From remaining_contrib_bound: sumFrom(τ,i+1) ≤ W(τ.take(i+1)) - 1
  -- So: cumAt(τ,i) + sumFrom(τ,i+1) ≤ cumAt(τ,i) + W(τ.take(i+1)) - 1 < cumAt(σ,i) ≤ cumAt(σ,i) + sumFrom(σ,i+1)
  have h_gap := cumulativeAtPosition_gap ω k τ σ i hi hprefix hlt
  simp only at h_gap
  -- Need to convert sumFrom to the form used in remaining_contrib_bound
  have h_sumFrom_eq : sumFrom ω k τ.digits (i + 1) =
      (Finset.Ico (i + 1) (k + 1)).sum (fun j =>
        if hj : j < τ.digits.length then cumulativeAtPosition ω k τ.digits j hj else 0) := by
    simp only [sumFrom, hlenτ]
  have hi1 : i + 1 ≤ k + 1 := Nat.succ_le_of_lt hi
  -- W(τ.take(i+1)) > 0
  have h_W_pos : 0 < completionCount ω k (τ.digits.take (i + 1)) := by
    apply completionCount_pos
    rw [List.length_take, hlenτ]
    exact Nat.min_le_right _ _
  -- Combine
  have h_sumFrom_bound : sumFrom ω k τ.digits (i + 1) ≤ completionCount ω k (τ.digits.take (i + 1)) - 1 := by
    by_cases h_eq : i + 1 = k + 1
    · -- Edge case: i = k, so sumFrom is empty
      simp only [sumFrom, hlenτ, h_eq, Finset.Ico_self, Finset.sum_empty]
      omega
    · -- General case
      have hi1' : i + 1 < k + 1 := Nat.lt_of_le_of_ne hi1 h_eq
      rw [h_sumFrom_eq]
      exact remaining_contrib_bound ω k τ (i + 1) hi1'
  omega

/-- Helper: List.Lex for same-length lists implies a first differing position -/
private theorem lex_same_length_first_diff {α : Type*} {r : α → α → Prop} {l₁ l₂ : List α}
    (h : List.Lex r l₁ l₂) (hlen : l₁.length = l₂.length) :
    ∃ i, ∃ hi₁ : i < l₁.length, ∃ hi₂ : i < l₂.length,
      l₁.take i = l₂.take i ∧ r (l₁.get ⟨i, hi₁⟩) (l₂.get ⟨i, hi₂⟩) := by
  induction h with
  | nil => simp at hlen
  | @rel a₁ l₁' a₂ l₂' hr =>
    -- Heads differ: r a₁ a₂
    refine ⟨0, by simp, by simp, rfl, hr⟩
  | @cons a l₁' l₂' htail ih =>
    -- Heads are equal, recurse on tails
    simp only [List.length_cons] at hlen
    obtain ⟨i, hi₁, hi₂, htake, hrel⟩ := ih (Nat.succ_injective hlen)
    refine ⟨i + 1, by simp [hi₁], by simp [hi₂], ?_, ?_⟩
    · simp only [List.take_succ_cons]
      exact congr_arg (a :: ·) htake
    · simp only [List.get_cons_succ]
      exact hrel

/-- Decode respects lexicographic order -/
theorem variableRadixDecode_strictMono (ω : RadixLaw) (k : ℕ)
    (τ σ : FiniteVariableSpace ω k) (h : τ.digits < σ.digits) :
    variableRadixDecode ω k τ < variableRadixDecode ω k σ := by
  -- τ.digits < σ.digits means List.Lex (· < ·) τ.digits σ.digits
  -- Extract the first position where they differ
  have hlen : τ.digits.length = σ.digits.length := by rw [τ.length_eq, σ.length_eq]
  obtain ⟨i, hi_τ, hi_σ, htake, hlt_digits⟩ := lex_same_length_first_diff h hlen
  -- Convert to the form needed by decode_lt_of_digit_lt
  have hi : i < k + 1 := by rw [← τ.length_eq]; exact hi_τ
  have hprefix : τ.digits.take i = σ.digits.take i := htake
  have hlt : τ.digitAt ⟨i, hi⟩ < σ.digitAt ⟨i, hi⟩ := by
    simp only [FiniteVariableSpace.digitAt]
    convert hlt_digits using 1 <;> rfl
  exact decode_lt_of_digit_lt ω k τ σ i hi hprefix hlt

/-!
## Variable Radix Encode (Inverse Ranking)
-/

/--
Auxiliary function to find the digit at position i given remaining count.

Given that we need to place a digit d such that after accounting for all
completions with smaller digits, we have exactly `remaining` elements left,
this finds the appropriate digit.

Returns (d, remaining - ∑_{j<d} completionCount(pfx++[j])) where d is the
unique digit such that:
- ∑_{j<d} completionCount(pfx++[j]) ≤ remaining
- ∑_{j≤d} completionCount(pfx++[j]) > remaining (or d is the last valid digit)
-/
private def findDigit (ω : RadixLaw) (k : ℕ) (pfx : PrefixWord) (remaining : ℕ) : ℕ × ℕ :=
  go 0 remaining 0
where
  /-- Inner loop: d is current digit, rem is remaining count, cumSum is ∑_{j<d} W(pfx++[j]) -/
  go (d : ℕ) (rem : ℕ) (cumSum : ℕ) : ℕ × ℕ :=
    if hd : d < ω.radix pfx then
      let cnt := completionCount ω k (pfx ++ [d])
      if cnt ≤ rem then
        go (d + 1) (rem - cnt) (cumSum + cnt)
      else
        (d, rem)
    else
      -- d = ω.radix pfx, return last valid digit
      (d - 1, rem)
  termination_by (ω.radix pfx - d)

/-- Helper: cumulative sum of completion counts up to digit d -/
private def cumSumTo (ω : RadixLaw) (k : ℕ) (pfx : PrefixWord) (d : ℕ) : ℕ :=
  (Finset.range d).sum fun j => completionCount ω k (pfx ++ [j])

/-- The cumulative sum increases by one term -/
private theorem cumSumTo_succ (ω : RadixLaw) (k : ℕ) (pfx : PrefixWord) (d : ℕ) :
    cumSumTo ω k pfx (d + 1) = cumSumTo ω k pfx d + completionCount ω k (pfx ++ [d]) := by
  simp only [cumSumTo, Finset.sum_range_succ]

/-- The cumulative sum at radix equals the completion count -/
private theorem cumSumTo_radix (ω : RadixLaw) (k : ℕ) (pfx : PrefixWord) (hpfx_len : pfx.length < k + 1) :
    cumSumTo ω k pfx (ω.radix pfx) = completionCount ω k pfx := by
  simp only [cumSumTo]
  exact (completionCount_rec ω k pfx hpfx_len).symm

/-- The go function finds a digit d where cumSumTo d ≤ n < cumSumTo (d+1) -/
private theorem findDigit_go_spec (ω : RadixLaw) (k : ℕ) (pfx : PrefixWord) (d₀ rem₀ cumSum₀ : ℕ)
    (hpfx_len : pfx.length < k + 1)
    (hcum : cumSum₀ = cumSumTo ω k pfx d₀)
    (hrem : rem₀ + cumSum₀ < completionCount ω k pfx) :
    (findDigit.go ω k pfx d₀ rem₀ cumSum₀).1 < ω.radix pfx := by
  -- Get the measure for well-founded recursion
  obtain ⟨m, hm⟩ : ∃ m, m = ω.radix pfx - d₀ := ⟨_, rfl⟩
  -- Induction on remaining digits to check
  induction m using Nat.strongRecOn generalizing d₀ rem₀ cumSum₀ with
  | _ n ih =>
    unfold findDigit.go
    by_cases hd : d₀ < ω.radix pfx
    · -- d₀ < radix: check if completionCount > rem
      simp only [hd, dite_true]
      set cnt := completionCount ω k (pfx ++ [d₀])
      by_cases hcnt : cnt ≤ rem₀
      · -- cnt ≤ rem₀: recurse to next digit
        simp only [hcnt, ite_true]
        -- Apply IH
        have hdec : ω.radix pfx - (d₀ + 1) < n := by omega
        have hcum' : cumSum₀ + cnt = cumSumTo ω k pfx (d₀ + 1) := by
          rw [cumSumTo_succ, hcum]
        have hrem' : (rem₀ - cnt) + (cumSum₀ + cnt) < completionCount ω k pfx := by
          -- Since cnt ≤ rem₀, we have (rem₀ - cnt) + (cumSum₀ + cnt) = rem₀ + cumSum₀
          have heq : (rem₀ - cnt) + (cumSum₀ + cnt) = rem₀ + cumSum₀ := by
            have h1 : (rem₀ - cnt) + (cumSum₀ + cnt) = (rem₀ - cnt) + cnt + cumSum₀ := by ring
            have h2 : (rem₀ - cnt) + cnt = rem₀ := Nat.sub_add_cancel hcnt
            omega
          rw [heq]; exact hrem
        exact ih (ω.radix pfx - (d₀ + 1)) hdec (d₀ + 1) (rem₀ - cnt) (cumSum₀ + cnt) hcum' hrem' rfl
      · -- cnt > rem₀: return d₀
        simp only [hcnt, ite_false]
        exact hd
    · -- d₀ ≥ radix: this case is impossible given preconditions
      simp only [hd, dite_false]
      -- We have cumSum₀ = cumSumTo ω k pfx d₀ ≥ cumSumTo ω k pfx (ω.radix pfx) = completionCount
      have hge : d₀ ≥ ω.radix pfx := Nat.le_of_not_lt hd
      have hcum_ge : cumSum₀ ≥ completionCount ω k pfx := by
        rw [hcum]
        -- cumSumTo increases monotonically
        have hmono : cumSumTo ω k pfx (ω.radix pfx) ≤ cumSumTo ω k pfx d₀ := by
          simp only [cumSumTo]
          apply Finset.sum_le_sum_of_subset
          intro x hx
          simp only [Finset.mem_range] at hx ⊢
          omega
        calc completionCount ω k pfx
            = cumSumTo ω k pfx (ω.radix pfx) := (cumSumTo_radix ω k pfx hpfx_len).symm
          _ ≤ cumSumTo ω k pfx d₀ := hmono
      -- But rem₀ + cumSum₀ < completionCount, so rem₀ < 0, contradiction
      omega

/-- The digit returned by findDigit is valid -/
private theorem findDigit_lt_radix (ω : RadixLaw) (k : ℕ) (pfx : PrefixWord) (n : ℕ)
    (hpfx_len : pfx.length < k + 1) (hn : n < completionCount ω k pfx) :
    (findDigit ω k pfx n).1 < ω.radix pfx := by
  unfold findDigit
  apply findDigit_go_spec ω k pfx 0 n 0 hpfx_len
  · simp [cumSumTo]
  · simp; exact hn

/-- The go function returns (d, rem) where rem < W(pfx++[d]) -/
private theorem findDigit_go_rem_spec (ω : RadixLaw) (k : ℕ) (pfx : PrefixWord)
    (d₀ rem₀ cumSum₀ : ℕ)
    (hpfx_len : pfx.length < k + 1)
    (hcum : cumSum₀ = cumSumTo ω k pfx d₀)
    (hrem : rem₀ + cumSum₀ < completionCount ω k pfx) :
    let result := findDigit.go ω k pfx d₀ rem₀ cumSum₀
    result.2 < completionCount ω k (pfx ++ [result.1]) := by
  -- Get the measure for well-founded recursion
  obtain ⟨m, hm⟩ : ∃ m, m = ω.radix pfx - d₀ := ⟨_, rfl⟩
  -- Induction on remaining digits to check
  induction m using Nat.strongRecOn generalizing d₀ rem₀ cumSum₀ with
  | _ n ih =>
    unfold findDigit.go
    by_cases hd : d₀ < ω.radix pfx
    · -- d₀ < radix: check if completionCount > rem
      simp only [hd, dite_true]
      set cnt := completionCount ω k (pfx ++ [d₀])
      by_cases hcnt : cnt ≤ rem₀
      · -- cnt ≤ rem₀: recurse to next digit
        simp only [hcnt, ite_true]
        -- Apply IH
        have hdec : ω.radix pfx - (d₀ + 1) < n := by omega
        have hcum' : cumSum₀ + cnt = cumSumTo ω k pfx (d₀ + 1) := by
          rw [cumSumTo_succ, hcum]
        have hrem' : (rem₀ - cnt) + (cumSum₀ + cnt) < completionCount ω k pfx := by
          have heq : (rem₀ - cnt) + (cumSum₀ + cnt) = rem₀ + cumSum₀ := by
            have h1 : (rem₀ - cnt) + (cumSum₀ + cnt) = (rem₀ - cnt) + cnt + cumSum₀ := by ring
            have h2 : (rem₀ - cnt) + cnt = rem₀ := Nat.sub_add_cancel hcnt
            omega
          rw [heq]; exact hrem
        exact ih (ω.radix pfx - (d₀ + 1)) hdec (d₀ + 1) (rem₀ - cnt) (cumSum₀ + cnt) hcum' hrem' rfl
      · -- cnt > rem₀: return (d₀, rem₀) where rem₀ < cnt = W(pfx++[d₀])
        simp only [hcnt, ite_false]
        exact Nat.lt_of_not_le hcnt
    · -- d₀ ≥ radix: this case is impossible given preconditions
      simp only [hd, dite_false]
      have hge : d₀ ≥ ω.radix pfx := Nat.le_of_not_lt hd
      have hcum_ge : cumSum₀ ≥ completionCount ω k pfx := by
        rw [hcum]
        have hmono : cumSumTo ω k pfx (ω.radix pfx) ≤ cumSumTo ω k pfx d₀ := by
          simp only [cumSumTo]
          apply Finset.sum_le_sum_of_subset
          intro x hx
          simp only [Finset.mem_range] at hx ⊢
          omega
        calc completionCount ω k pfx
            = cumSumTo ω k pfx (ω.radix pfx) := (cumSumTo_radix ω k pfx hpfx_len).symm
          _ ≤ cumSumTo ω k pfx d₀ := hmono
      omega

/-- The remaining value from findDigit is bounded by the completion count of the extended prefix -/
private theorem findDigit_rem_lt (ω : RadixLaw) (k : ℕ) (pfx : PrefixWord) (n : ℕ)
    (hpfx_len : pfx.length < k + 1) (hn : n < completionCount ω k pfx) :
    (findDigit ω k pfx n).2 < completionCount ω k (pfx ++ [(findDigit ω k pfx n).1]) := by
  unfold findDigit
  apply findDigit_go_rem_spec ω k pfx 0 n 0 hpfx_len
  · simp [cumSumTo]
  · simp; exact hn

/-- The go function returns (d, rem) where cumSumTo d + rem = n -/
private theorem findDigit_go_sum_spec (ω : RadixLaw) (k : ℕ) (pfx : PrefixWord)
    (d₀ rem₀ cumSum₀ : ℕ)
    (hpfx_len : pfx.length < k + 1)
    (hcum : cumSum₀ = cumSumTo ω k pfx d₀)
    (hrem : rem₀ + cumSum₀ < completionCount ω k pfx) :
    let result := findDigit.go ω k pfx d₀ rem₀ cumSum₀
    cumSumTo ω k pfx result.1 + result.2 = rem₀ + cumSum₀ := by
  -- Get the measure for well-founded recursion
  obtain ⟨m, hm⟩ : ∃ m, m = ω.radix pfx - d₀ := ⟨_, rfl⟩
  -- Induction on remaining digits to check
  induction m using Nat.strongRecOn generalizing d₀ rem₀ cumSum₀ with
  | _ n ih =>
    unfold findDigit.go
    by_cases hd : d₀ < ω.radix pfx
    · -- d₀ < radix: check if completionCount > rem
      simp only [hd, dite_true]
      set cnt := completionCount ω k (pfx ++ [d₀])
      by_cases hcnt : cnt ≤ rem₀
      · -- cnt ≤ rem₀: recurse to next digit
        simp only [hcnt, ite_true]
        -- Apply IH
        have hdec : ω.radix pfx - (d₀ + 1) < n := by omega
        have hcum' : cumSum₀ + cnt = cumSumTo ω k pfx (d₀ + 1) := by
          rw [cumSumTo_succ, hcum]
        have hrem' : (rem₀ - cnt) + (cumSum₀ + cnt) < completionCount ω k pfx := by
          have heq : (rem₀ - cnt) + (cumSum₀ + cnt) = rem₀ + cumSum₀ := by
            have h1 : (rem₀ - cnt) + (cumSum₀ + cnt) = (rem₀ - cnt) + cnt + cumSum₀ := by ring
            have h2 : (rem₀ - cnt) + cnt = rem₀ := Nat.sub_add_cancel hcnt
            omega
          rw [heq]; exact hrem
        have ih_result := ih (ω.radix pfx - (d₀ + 1)) hdec (d₀ + 1) (rem₀ - cnt) (cumSum₀ + cnt)
          hcum' hrem' rfl
        -- ih_result: cumSumTo result.1 + result.2 = (rem₀ - cnt) + (cumSum₀ + cnt)
        calc cumSumTo ω k pfx (findDigit.go ω k pfx (d₀ + 1) (rem₀ - cnt) (cumSum₀ + cnt)).1 +
              (findDigit.go ω k pfx (d₀ + 1) (rem₀ - cnt) (cumSum₀ + cnt)).2
            = (rem₀ - cnt) + (cumSum₀ + cnt) := ih_result
          _ = rem₀ + cumSum₀ := by omega
      · -- cnt > rem₀: return (d₀, rem₀)
        simp only [hcnt, ite_false]
        rw [hcum]; ring
    · -- d₀ ≥ radix: this case is impossible given preconditions
      simp only [hd, dite_false]
      have hge : d₀ ≥ ω.radix pfx := Nat.le_of_not_lt hd
      have hcum_ge : cumSum₀ ≥ completionCount ω k pfx := by
        rw [hcum]
        have hmono : cumSumTo ω k pfx (ω.radix pfx) ≤ cumSumTo ω k pfx d₀ := by
          simp only [cumSumTo]
          apply Finset.sum_le_sum_of_subset
          intro x hx
          simp only [Finset.mem_range] at hx ⊢
          omega
        calc completionCount ω k pfx
            = cumSumTo ω k pfx (ω.radix pfx) := (cumSumTo_radix ω k pfx hpfx_len).symm
          _ ≤ cumSumTo ω k pfx d₀ := hmono
      omega

/-- findDigit satisfies: cumSumTo d + rem = n -/
private theorem findDigit_sum_spec (ω : RadixLaw) (k : ℕ) (pfx : PrefixWord) (n : ℕ)
    (hpfx_len : pfx.length < k + 1) (hn : n < completionCount ω k pfx) :
    cumSumTo ω k pfx (findDigit ω k pfx n).1 + (findDigit ω k pfx n).2 = n := by
  unfold findDigit
  have h := findDigit_go_sum_spec ω k pfx 0 n 0 hpfx_len (by simp [cumSumTo]) (by simp; exact hn)
  simp at h
  exact h

/--
Build a valid sequence digit by digit from a rank.

Invariants maintained:
- pfx.length + depth = k + 1
- n < completionCount ω k pfx
- isValidPrefix' ω pfx
-/
private def encodeAux (ω : RadixLaw) (k : ℕ) (n : ℕ) (depth : ℕ) (pfx : PrefixWord)
    (hlen : pfx.length + depth = k + 1)
    (hn : n < completionCount ω k pfx)
    (hvalid : isValidPrefix' ω pfx) : PrefixWord :=
  if hdepth : depth = 0 then
    pfx
  else
    have hpfx_len : pfx.length < k + 1 := by omega
    let result := findDigit ω k pfx n
    let d := result.1
    let rem := result.2
    have hd_lt : d < ω.radix pfx := findDigit_lt_radix ω k pfx n hpfx_len hn
    have hvalid' : isValidPrefix' ω (pfx ++ [d]) := isValidPrefix'_append_singleton hvalid hd_lt
    have hlen' : (pfx ++ [d]).length + (depth - 1) = k + 1 := by simp; omega
    have hn' : rem < completionCount ω k (pfx ++ [d]) := findDigit_rem_lt ω k pfx n hpfx_len hn
    have hdec : depth - 1 < depth := Nat.sub_lt (Nat.pos_of_ne_zero hdepth) Nat.one_pos
    encodeAux ω k rem (depth - 1) (pfx ++ [d]) hlen' hn' hvalid'
termination_by depth

/-- encodeAux produces a prefix of the correct length -/
private theorem encodeAux_length (ω : RadixLaw) (k : ℕ) (n : ℕ) (depth : ℕ) (pfx : PrefixWord)
    (hlen : pfx.length + depth = k + 1)
    (hn : n < completionCount ω k pfx)
    (hvalid : isValidPrefix' ω pfx) :
    (encodeAux ω k n depth pfx hlen hn hvalid).length = k + 1 := by
  induction depth generalizing pfx n with
  | zero =>
    unfold encodeAux
    simp only [↓reduceDIte]
    omega
  | succ d ih =>
    unfold encodeAux
    simp only [Nat.succ_ne_zero, ↓reduceDIte]
    -- The recursive call produces the result
    apply ih

/-- encodeAux produces a valid prefix -/
private theorem encodeAux_valid (ω : RadixLaw) (k : ℕ) (n : ℕ) (depth : ℕ) (pfx : PrefixWord)
    (hlen : pfx.length + depth = k + 1)
    (hn : n < completionCount ω k pfx)
    (hvalid : isValidPrefix' ω pfx) :
    isValidPrefix' ω (encodeAux ω k n depth pfx hlen hn hvalid) := by
  induction depth generalizing pfx n with
  | zero =>
    unfold encodeAux
    simp only [↓reduceDIte]
    exact hvalid
  | succ d ih =>
    unfold encodeAux
    simp only [Nat.succ_ne_zero, ↓reduceDIte]
    apply ih

/--
The encode function: given a natural number, produce the τ at that rank.

**fdrs.md**: enc^{(k)}_ω = (dec^{(k)}_ω)^{-1}
-/
def variableRadixEncode (ω : RadixLaw) (k : ℕ) (n : ℕ)
    (hn : n < completionCount ω k []) : FiniteVariableSpace ω k :=
  let hlen : ([] : PrefixWord).length + (k + 1) = k + 1 := by simp
  let digits := encodeAux ω k n (k + 1) [] hlen hn (isValidPrefix'_nil ω)
  { digits := digits
    length_eq := encodeAux_length ω k n (k + 1) [] hlen hn (isValidPrefix'_nil ω)
    valid := encodeAux_valid ω k n (k + 1) [] hlen hn (isValidPrefix'_nil ω) }

/-- cumulativeAtPosition in terms of cumSumTo -/
private theorem cumulativeAtPosition_eq_cumSumTo (ω : RadixLaw) (k : ℕ) (s : PrefixWord)
    (i : ℕ) (hi : i < s.length) :
    cumulativeAtPosition ω k s i hi = cumSumTo ω k (s.take i) (s.get ⟨i, hi⟩) := by
  simp only [cumulativeAtPosition, cumSumTo]

/-- Helper: cumulativeAtPosition matches for positions within the original prefix -/
private theorem cumulativeAtPosition_append_eq (ω : RadixLaw) (k : ℕ) (pfx : PrefixWord) (d : ℕ)
    (i : ℕ) (hi_pfx : i < pfx.length) :
    let hi_ext : i < (pfx ++ [d]).length := by simp; omega
    cumulativeAtPosition ω k (pfx ++ [d]) i hi_ext = cumulativeAtPosition ω k pfx i hi_pfx := by
  intro hi_ext
  simp only [cumulativeAtPosition]
  -- Need: (pfx ++ [d]).take i = pfx.take i and (pfx ++ [d])[i] = pfx[i]
  have h_take : (pfx ++ [d]).take i = pfx.take i := by
    apply List.ext_getElem
    · simp only [List.length_take, List.length_append, List.length_singleton]
      rw [Nat.min_eq_left (by omega : i ≤ pfx.length + 1)]
      rw [Nat.min_eq_left (Nat.le_of_lt hi_pfx)]
    · intro n h1 h2
      simp only [List.getElem_take]
      simp only [List.length_take, List.length_append, List.length_singleton] at h1
      rw [Nat.min_eq_left (by omega : i ≤ pfx.length + 1)] at h1
      have hn : n < pfx.length := by omega
      simp only [List.getElem_append_left hn]
  have h_get : (pfx ++ [d]).get ⟨i, hi_ext⟩ = pfx.get ⟨i, hi_pfx⟩ := by
    simp only [List.get_eq_getElem, List.getElem_append_left hi_pfx]
  rw [h_take, h_get]

/-- Helper: cumulativeAtPosition at pfx.length equals cumSumTo -/
private theorem cumulativeAtPosition_at_length (ω : RadixLaw) (k : ℕ) (pfx : PrefixWord) (d : ℕ) :
    let hi : pfx.length < (pfx ++ [d]).length := by simp
    cumulativeAtPosition ω k (pfx ++ [d]) pfx.length hi = cumSumTo ω k pfx d := by
  intro hi
  simp only [cumulativeAtPosition, cumSumTo]
  -- Need: (pfx ++ [d]).take pfx.length = pfx and (pfx ++ [d])[pfx.length] = d
  have h_take : (pfx ++ [d]).take pfx.length = pfx := by simp
  have h_get : (pfx ++ [d]).get ⟨pfx.length, hi⟩ = d := by
    simp only [List.get_eq_getElem, List.getElem_append_right (Nat.le_refl _)]
    simp
  rw [h_take, h_get]

/-- The cumulative count decomposes at a prefix -/
private theorem cumulativeCount_append_digit (ω : RadixLaw) (k : ℕ) (pfx : PrefixWord) (d : ℕ)
    (_hlen : pfx.length < k + 1) :
    cumulativeCount ω k (pfx ++ [d]) =
      cumulativeCount ω k pfx + cumSumTo ω k pfx d := by
  -- The extended list has length pfx.length + 1
  have hlen_ext : (pfx ++ [d]).length = pfx.length + 1 := by simp

  simp only [cumulativeCount]

  -- We need to show:
  -- ∑ i in range (pfx.length + 1), (if hi : i < pfx.length + 1 then cumAt(pfx++[d], i, hi) else 0) =
  -- ∑ i in range pfx.length, (if hi : i < pfx.length then cumAt(pfx, i, hi) else 0) + cumSumTo pfx d

  -- Simplify the dites since they're always true in their respective ranges
  have h_lhs : (Finset.range (pfx ++ [d]).length).sum
      (fun i => if hi : i < (pfx ++ [d]).length then cumulativeAtPosition ω k (pfx ++ [d]) i hi else 0) =
      (Finset.range (pfx.length + 1)).sum (fun i =>
        if hi : i < pfx.length + 1 then cumulativeAtPosition ω k (pfx ++ [d]) i (hlen_ext ▸ hi) else 0) := by
    simp only [hlen_ext]

  have h_rhs : (Finset.range pfx.length).sum
      (fun i => if hi : i < pfx.length then cumulativeAtPosition ω k pfx i hi else 0) =
      (Finset.range pfx.length).sum (fun i =>
        if hi : i < pfx.length + 1 then cumulativeAtPosition ω k (pfx ++ [d]) i (hlen_ext ▸ hi) else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    have hi' : i < pfx.length + 1 := Nat.lt_succ_of_lt hi
    simp only [hi, hi', dite_true]
    exact (cumulativeAtPosition_append_eq ω k pfx d i hi).symm

  rw [h_lhs, h_rhs]

  -- Now split the LHS sum using sum_range_succ
  rw [Finset.sum_range_succ]
  simp only [Nat.lt_succ_self, dite_true]

  -- The term at pfx.length equals cumSumTo
  have h_last : cumulativeAtPosition ω k (pfx ++ [d]) pfx.length (by simp) = cumSumTo ω k pfx d :=
    cumulativeAtPosition_at_length ω k pfx d
  rw [h_last, Nat.add_comm]

/-- Key lemma: encodeAux produces a sequence whose cumulativeCount equals pfx's plus n -/
private theorem encodeAux_cumulativeCount (ω : RadixLaw) (k : ℕ) (n : ℕ) (depth : ℕ)
    (pfx : PrefixWord)
    (hlen : pfx.length + depth = k + 1)
    (hn : n < completionCount ω k pfx)
    (hvalid : isValidPrefix' ω pfx) :
    cumulativeCount ω k (encodeAux ω k n depth pfx hlen hn hvalid) =
      cumulativeCount ω k pfx + n := by
  induction depth generalizing pfx n hn hvalid with
  | zero =>
    -- depth = 0 means pfx.length = k + 1, so completionCount pfx = 1
    unfold encodeAux
    simp only [↓reduceDIte]
    -- n < 1 implies n = 0
    have hW : completionCount ω k pfx = 1 := completionCount_of_length_eq ω k pfx (by omega)
    have hn0 : n = 0 := Nat.lt_one_iff.mp (hW ▸ hn)
    simp [hn0]
  | succ d ih =>
    unfold encodeAux
    simp only [Nat.succ_ne_zero, ↓reduceDIte]
    -- The result is encodeAux with (pfx ++ [digit], rem)
    have hpfx_len : pfx.length < k + 1 := by omega
    -- Get digit and remaining from findDigit
    set result := findDigit ω k pfx n with hresult_def
    set digit := result.1 with hdigit_def
    set rem := result.2 with hrem_def
    -- Key properties
    have hd_valid : digit < ω.radix pfx := findDigit_lt_radix ω k pfx n hpfx_len hn
    have hrem_bound : rem < completionCount ω k (pfx ++ [digit]) :=
      findDigit_rem_lt ω k pfx n hpfx_len hn
    have hvalid' : isValidPrefix' ω (pfx ++ [digit]) :=
      isValidPrefix'_append_singleton hvalid hd_valid
    have hlen' : (pfx ++ [digit]).length + d = k + 1 := by simp; omega
    -- Apply IH (note: generalizing creates vars in order: n, pfx, hn, hvalid)
    have ih_result := ih rem (pfx ++ [digit]) hlen' hrem_bound hvalid'
    -- cumulativeCount (pfx ++ [digit]) = cumulativeCount pfx + cumSumTo pfx digit
    have h_cum_ext := cumulativeCount_append_digit ω k pfx digit hpfx_len
    -- findDigit_sum_spec: cumSumTo pfx digit + rem = n
    have h_sum := findDigit_sum_spec ω k pfx n hpfx_len hn
    -- The goal is about the unfolded encodeAux which matches ih_result
    -- digit = (findDigit ω k pfx n).1 and rem = (findDigit ω k pfx n).2
    simp only [hdigit_def, hrem_def, hresult_def] at ih_result h_cum_ext ⊢
    -- Now combine
    calc cumulativeCount ω k (encodeAux ω k (findDigit ω k pfx n).2 d
            (pfx ++ [(findDigit ω k pfx n).1]) hlen' hrem_bound hvalid')
        = cumulativeCount ω k (pfx ++ [(findDigit ω k pfx n).1]) + (findDigit ω k pfx n).2 := ih_result
      _ = (cumulativeCount ω k pfx + cumSumTo ω k pfx (findDigit ω k pfx n).1) +
            (findDigit ω k pfx n).2 := by rw [h_cum_ext]
      _ = cumulativeCount ω k pfx + (cumSumTo ω k pfx (findDigit ω k pfx n).1 +
            (findDigit ω k pfx n).2) := by ring
      _ = cumulativeCount ω k pfx + n := by rw [h_sum]

/-- For any valid sequence, its cumulative count minus prefix's count is bounded by completion count -/
private theorem cumulativeCount_sub_lt_completionCount (ω : RadixLaw) (k : ℕ)
    (τ : FiniteVariableSpace ω k) (i : ℕ) (hi : i ≤ k + 1) :
    cumulativeCount ω k τ.digits - cumulativeCount ω k (τ.digits.take i) <
      completionCount ω k (τ.digits.take i) := by
  have hlen : τ.digits.length = k + 1 := τ.length_eq
  by_cases heq : i = k + 1
  · -- If i = k+1, the prefix is the full sequence
    subst heq
    simp only [List.take_of_length_le (by rw [hlen] : τ.digits.length ≤ k + 1)]
    simp only [Nat.sub_self, completionCount_of_length_eq ω k τ.digits hlen]
    exact Nat.one_pos
  · -- Otherwise, i < k+1
    have hi' : i < k + 1 := Nat.lt_of_le_of_ne hi heq
    -- The contribution from positions i onwards is bounded by completionCount(take i) - 1
    have hbound := remaining_contrib_bound ω k τ i hi'
    have htake_len : (τ.digits.take i).length = i := by
      simp only [List.length_take, hlen]
      exact Nat.min_eq_left (by omega : i ≤ k + 1)
    -- Use sumBefore and sumFrom
    have h_split : cumulativeCount ω k τ.digits = sumBefore ω k τ.digits i + sumFrom ω k τ.digits i := by
      simp only [cumulativeCount, sumBefore, sumFrom, hlen]
      have hsplit : Finset.range (k + 1) = Finset.range i ∪ Finset.Ico i (k + 1) := by
        ext j; simp [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
      have hdisjoint : Disjoint (Finset.range i) (Finset.Ico i (k + 1)) := by
        simp [Finset.disjoint_left, Finset.mem_range, Finset.mem_Ico]; omega
      rw [hsplit, Finset.sum_union hdisjoint]
    -- sumBefore τ i = cumulativeCount (τ.take i) when i < τ.length
    have h_before : sumBefore ω k τ.digits i = cumulativeCount ω k (τ.digits.take i) := by
      simp only [sumBefore, cumulativeCount, htake_len]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_range] at hj
      have hj_lt : j < τ.digits.length := by rw [hlen]; omega
      have hj_lt' : j < (τ.digits.take i).length := by rw [htake_len]; exact hj
      -- LHS condition is j < k+1 (= τ.digits.length), RHS condition is j < i
      simp only [dif_pos hj_lt, dif_pos hj, cumulativeAtPosition]
      have h_take_eq : τ.digits.take j = (τ.digits.take i).take j := by
        rw [List.take_take]; congr 1; omega
      have h_get_eq : τ.digits.get ⟨j, hj_lt⟩ = (τ.digits.take i).get ⟨j, hj_lt'⟩ := by
        simp only [List.get_eq_getElem, htake_len]
        exact List.getElem_take' hj_lt hj
      rw [h_take_eq, h_get_eq]
    -- sumFrom τ i ≤ completionCount(τ.take i) - 1 from hbound
    have h_from_bound : sumFrom ω k τ.digits i ≤ completionCount ω k (τ.digits.take i) - 1 := by
      simp only [sumFrom, hlen]
      convert hbound using 3 with j
      simp only [hlen]
    -- Combine
    rw [h_split, h_before]
    -- After rewrites: goal is (cumulativeCount(take i) + sumFrom) - cumulativeCount(take i) < completionCount(take i)
    calc cumulativeCount ω k (τ.digits.take i) + sumFrom ω k τ.digits i - cumulativeCount ω k (τ.digits.take i)
        = sumFrom ω k τ.digits i := by omega
      _ ≤ completionCount ω k (τ.digits.take i) - 1 := h_from_bound
      _ < completionCount ω k (τ.digits.take i) := by
          have hpos : 0 < completionCount ω k (τ.digits.take i) := by
            apply completionCount_pos; rw [htake_len]; exact Nat.le_of_lt hi'
          omega

/-- cumulativeCount is monotone: prefix has smaller cumulative count -/
private theorem cumulativeCount_prefix_le (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k)
    (i : ℕ) (hi : i ≤ k + 1) :
    cumulativeCount ω k (τ.digits.take i) ≤ cumulativeCount ω k τ.digits := by
  have hlen : τ.digits.length = k + 1 := τ.length_eq
  have htake_len : (τ.digits.take i).length = min i (k + 1) := by
    rw [List.length_take, hlen]
  have htake_len' : (τ.digits.take i).length = i := by
    rw [htake_len, Nat.min_eq_left hi]
  -- Use sumBefore and sumFrom to split
  have h_split : cumulativeCount ω k τ.digits = sumBefore ω k τ.digits i + sumFrom ω k τ.digits i := by
    simp only [cumulativeCount, sumBefore, sumFrom, hlen]
    have hsplit : Finset.range (k + 1) = Finset.range i ∪ Finset.Ico i (k + 1) := by
      ext j; simp [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
    have hdisjoint : Disjoint (Finset.range i) (Finset.Ico i (k + 1)) := by
      simp [Finset.disjoint_left, Finset.mem_range, Finset.mem_Ico]; omega
    rw [hsplit, Finset.sum_union hdisjoint]
  -- sumBefore τ i = cumulativeCount (τ.take i)
  have h_before : sumBefore ω k τ.digits i = cumulativeCount ω k (τ.digits.take i) := by
    simp only [sumBefore, cumulativeCount, htake_len']
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    have hj_lt : j < τ.digits.length := by rw [hlen]; omega
    have hj_lt' : j < (τ.digits.take i).length := by rw [htake_len']; exact hj
    simp only [dif_pos hj_lt, dif_pos hj, cumulativeAtPosition]
    have h_take_eq : τ.digits.take j = (τ.digits.take i).take j := by
      rw [List.take_take]; congr 1; omega
    have h_get_eq : τ.digits.get ⟨j, hj_lt⟩ = (τ.digits.take i).get ⟨j, hj_lt'⟩ := by
      simp only [List.get_eq_getElem]
      exact List.getElem_take' hj_lt hj
    rw [h_take_eq, h_get_eq]
  rw [h_split, h_before]
  exact Nat.le_add_right _ _

/-- findDigit recovers the next digit when given the correct remaining rank -/
private theorem findDigit_recovers_digit (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k)
    (i : ℕ) (hi : i < k + 1) :
    let pfx := τ.digits.take i
    let rank := cumulativeCount ω k τ.digits
    let rem := rank - cumulativeCount ω k pfx
    (findDigit ω k pfx rem).1 = τ.digits.get ⟨i, by rw [τ.length_eq]; exact hi⟩ := by
  intro pfx rank rem
  have hlen : τ.digits.length = k + 1 := τ.length_eq
  have hi_lt : i < τ.digits.length := by rw [hlen]; exact hi
  have hpfx_len : pfx.length < k + 1 := by simp [pfx, Nat.min_eq_left (Nat.le_of_lt hi)]; omega
  -- rem < completionCount(pfx) by cumulativeCount_sub_lt_completionCount
  have hrem : rem < completionCount ω k pfx :=
    cumulativeCount_sub_lt_completionCount ω k τ i (Nat.le_of_lt hi)
  -- By findDigit_sum_spec: cumSumTo pfx d + findDigit.2 = rem where d = findDigit.1
  have h_sum := findDigit_sum_spec ω k pfx rem hpfx_len hrem
  -- We need to show d = τ.digits[i]
  -- Key: d is the unique digit such that cumSumTo pfx d ≤ rem < cumSumTo pfx (d+1)
  -- We'll show τ.digits[i] satisfies this property
  set d := (findDigit ω k pfx rem).1
  set d_τ := τ.digits.get ⟨i, hi_lt⟩
  -- Property 1: cumSumTo pfx d_τ ≤ rem
  have hle : cumSumTo ω k pfx d_τ ≤ rem := by
    -- cumSumTo pfx d_τ = cumulativeCount(pfx ++ [d_τ]) - cumulativeCount(pfx)
    --                  = cumulativeCount(τ.take(i+1)) - cumulativeCount(pfx)
    have h_ext : pfx ++ [d_τ] = τ.digits.take (i + 1) := by
      simp only [pfx]
      rw [← take_succ_eq τ.digits i hi_lt]
    have h_cum := cumulativeCount_append_digit ω k pfx d_τ hpfx_len
    -- rem = rank - cumulativeCount(pfx)
    -- cumSumTo pfx d_τ = cumulativeCount(τ.take(i+1)) - cumulativeCount(pfx)
    rw [h_ext] at h_cum
    have hle' : cumulativeCount ω k (τ.digits.take (i + 1)) ≤ cumulativeCount ω k τ.digits :=
      cumulativeCount_prefix_le ω k τ (i + 1) (by omega)
    simp only [rem, rank]
    -- cumSumTo pfx d_τ = cumulativeCount(τ.take(i+1)) - cumulativeCount(pfx) by h_cum
    have h_cumsum_eq : cumSumTo ω k pfx d_τ = cumulativeCount ω k (τ.digits.take (i + 1)) -
        cumulativeCount ω k pfx := by omega
    omega
  -- Property 2: rem < cumSumTo pfx (d_τ + 1) = cumSumTo pfx d_τ + completionCount(pfx ++ [d_τ])
  have hlt : rem < cumSumTo ω k pfx (d_τ + 1) := by
    rw [cumSumTo_succ]
    have h_ext : pfx ++ [d_τ] = τ.digits.take (i + 1) := by
      simp only [pfx]
      rw [← take_succ_eq τ.digits i hi_lt]
    rw [h_ext]
    -- Need: rem < cumSumTo pfx d_τ + completionCount(τ.take(i+1))
    -- rem = rank - cumulativeCount(pfx)
    -- cumSumTo pfx d_τ = cumulativeCount(τ.take(i+1)) - cumulativeCount(pfx)
    -- So: rank - cumulativeCount(pfx) < cumulativeCount(τ.take(i+1)) - cumulativeCount(pfx) +
    --       completionCount(τ.take(i+1))
    -- Simplifies to: rank < cumulativeCount(τ.take(i+1)) + completionCount(τ.take(i+1))
    -- This is exactly: cumulativeCount(τ) < cumulativeCount(τ.take(i+1)) + completionCount(τ.take(i+1))
    -- Which follows from cumulativeCount_sub_lt_completionCount
    simp only [rem, rank]
    have h_bound := cumulativeCount_sub_lt_completionCount ω k τ (i + 1) (by omega : i + 1 ≤ k + 1)
    have h_cumsum_eq : cumSumTo ω k pfx d_τ = cumulativeCount ω k (τ.digits.take (i + 1)) -
        cumulativeCount ω k pfx := by
      have h_cum := cumulativeCount_append_digit ω k pfx d_τ hpfx_len
      rw [h_ext] at h_cum
      omega
    omega
  -- Now we can conclude d = d_τ
  -- From findDigit properties: cumSumTo pfx d ≤ rem and rem < cumSumTo pfx d + completionCount(pfx++[d])
  -- Combined with our properties of d_τ: cumSumTo pfx d_τ ≤ rem < cumSumTo pfx (d_τ + 1)
  -- These uniquely determine d = d_τ
  by_contra hne
  cases Nat.lt_or_gt_of_ne hne with
  | inl hlt_d =>
    -- d < d_τ: then cumSumTo pfx (d+1) ≤ cumSumTo pfx d_τ ≤ rem
    -- But findDigit ensures rem < completionCount(pfx++[d]), so
    -- cumSumTo pfx d + findDigit.2 = rem and findDigit.2 < completionCount(pfx++[d])
    -- So rem < cumSumTo pfx d + completionCount(pfx++[d]) = cumSumTo pfx (d+1)
    -- Contradiction with cumSumTo pfx (d+1) ≤ rem
    have h1 : cumSumTo ω k pfx (d + 1) ≤ cumSumTo ω k pfx d_τ := by
      simp only [cumSumTo]
      apply Finset.sum_le_sum_of_subset
      intro j hj
      simp only [Finset.mem_range] at hj ⊢
      omega
    -- Use the findDigit properties without unfolding d
    have h_rem_lt := findDigit_go_rem_spec ω k pfx 0 rem 0 hpfx_len (by simp [cumSumTo]) (by simp; exact hrem)
    -- h_rem_lt: (findDigit_go ...).2 < completionCount(pfx ++ [(findDigit_go ...).1])
    -- Since findDigit = findDigit_go ... 0 ..., we have d = (findDigit_go ...).1
    have h2 : (findDigit ω k pfx rem).2 < completionCount ω k (pfx ++ [d]) := by
      simp only [findDigit, d] at h_rem_lt ⊢; exact h_rem_lt
    have h3 : cumSumTo ω k pfx (d + 1) = cumSumTo ω k pfx d + completionCount ω k (pfx ++ [d]) :=
      cumSumTo_succ _ _ _ _
    have h4 := findDigit_sum_spec ω k pfx rem hpfx_len hrem
    -- h4: cumSumTo pfx d + (findDigit rem).2 = rem
    -- So rem = cumSumTo pfx d + (findDigit rem).2
    -- From h2: (findDigit rem).2 < completionCount(pfx ++ [d])
    -- Thus: rem < cumSumTo pfx d + completionCount(pfx ++ [d]) = cumSumTo pfx (d+1) [by h3]
    have h5 : rem < cumSumTo ω k pfx (d + 1) := by
      rw [h3]; omega
    -- From h1: cumSumTo pfx (d+1) ≤ cumSumTo pfx d_τ
    -- From hle: cumSumTo pfx d_τ ≤ rem
    -- So: rem < cumSumTo pfx (d+1) ≤ cumSumTo pfx d_τ ≤ rem
    -- Contradiction
    omega
  | inr hgt_d =>
    -- d > d_τ: then cumSumTo pfx d ≥ cumSumTo pfx (d_τ + 1) > rem
    -- But findDigit_sum_spec says cumSumTo pfx d + findDigit.2 = rem, so cumSumTo pfx d ≤ rem
    -- Contradiction
    have h1 : cumSumTo ω k pfx d ≥ cumSumTo ω k pfx (d_τ + 1) := by
      simp only [cumSumTo]
      apply Finset.sum_le_sum_of_subset
      intro j hj
      simp only [Finset.mem_range] at hj ⊢
      omega
    have h2 := findDigit_sum_spec ω k pfx rem hpfx_len hrem
    -- h2: cumSumTo pfx d + (findDigit rem).2 = rem
    -- So cumSumTo pfx d ≤ rem
    -- But h1 and hlt: cumSumTo pfx d ≥ cumSumTo pfx (d_τ + 1) > rem
    -- Contradiction
    omega

/-- encodeAux recovers the suffix of τ when given the correct remaining rank -/
private theorem encodeAux_recovers (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k)
    (i : ℕ) (hi : i ≤ k + 1) :
    let pfx := τ.digits.take i
    let rank := cumulativeCount ω k τ.digits
    let rem := rank - cumulativeCount ω k pfx
    let depth := k + 1 - i
    ∀ (hlen : pfx.length + depth = k + 1)
      (hn : rem < completionCount ω k pfx)
      (hvalid : isValidPrefix' ω pfx),
    encodeAux ω k rem depth pfx hlen hn hvalid = τ.digits := by
  have hτlen : τ.digits.length = k + 1 := τ.length_eq
  -- Strong induction on k + 1 - i (the depth remaining)
  obtain ⟨n, hn_eq⟩ : ∃ n, n = k + 1 - i := ⟨_, rfl⟩
  induction n using Nat.strongRecOn generalizing i with
  | _ n ih =>
    intro pfx rank rem depth hlen hn_lt hvalid
    by_cases hdepth : depth = 0
    · -- depth = 0 means i = k + 1
      have hi_eq : i = k + 1 := by simp only [depth] at hdepth; omega
      unfold encodeAux
      simp only [hdepth, ↓reduceDIte]
      -- pfx = τ.digits.take (k+1) = τ.digits
      simp only [pfx, hi_eq, List.take_of_length_le (by rw [hτlen])]
    · -- depth > 0
      have hi_lt : i < k + 1 := by simp only [depth] at hdepth; omega
      have hi_τ : i < τ.digits.length := by rw [hτlen]; exact hi_lt
      unfold encodeAux
      simp only [hdepth, ↓reduceDIte]
      -- findDigit recovers the i-th digit
      have hpfx_len : pfx.length < k + 1 := by
        simp only [pfx, List.length_take, hτlen]
        rw [Nat.min_eq_left (by omega : i ≤ k + 1)]
        exact hi_lt
      have h_digit := findDigit_recovers_digit ω k τ i hi_lt
      -- The next prefix is τ.take(i+1)
      have h_ext : pfx ++ [(findDigit ω k pfx rem).1] = τ.digits.take (i + 1) := by
        have h_digit := findDigit_recovers_digit ω k τ i hi_lt
        simp only [pfx, rem, rank] at h_digit ⊢
        rw [take_succ_eq τ.digits i hi_τ, h_digit]
      -- The remaining rank after position i
      have h_rem_next : (findDigit ω k pfx rem).2 =
          rank - cumulativeCount ω k (τ.digits.take (i + 1)) := by
        have h_sum := findDigit_sum_spec ω k pfx rem hpfx_len hn_lt
        -- From cumulativeCount_append_digit: cumulativeCount(pfx++[d]) = cumulativeCount(pfx) + cumSumTo pfx d
        have h_cum := cumulativeCount_append_digit ω k pfx (findDigit ω k pfx rem).1 hpfx_len
        rw [h_ext] at h_cum
        -- h_cum: cumulativeCount(take (i+1)) = cumulativeCount(pfx) + cumSumTo pfx d
        -- h_sum: cumSumTo pfx d + (findDigit rem).2 = rem
        -- rem = rank - cumulativeCount(pfx)
        -- We want: (findDigit rem).2 = rank - cumulativeCount(take (i+1))
        --
        -- Derivation:
        -- (findDigit rem).2 = rem - cumSumTo pfx d  [from h_sum]
        --                   = (rank - cumulativeCount pfx) - cumSumTo pfx d
        --                   = (rank - cumulativeCount pfx) - (cumulativeCount(take (i+1)) - cumulativeCount pfx) [from h_cum]
        --                   = rank - cumulativeCount(take (i+1))
        simp only [rem, rank, pfx] at h_sum h_cum ⊢
        -- Need explicit bounds for natural number subtraction
        have hmono : cumulativeCount ω k (τ.digits.take (i + 1)) ≤ cumulativeCount ω k τ.digits :=
          cumulativeCount_prefix_le ω k τ (i + 1) (by omega)
        omega
      -- Apply IH with i+1
      have hdec : k + 1 - (i + 1) < n := by omega
      have hi' : i + 1 ≤ k + 1 := by omega
      have ih' := ih (k + 1 - (i + 1)) hdec (i + 1) hi' rfl
      -- Compute the arguments for ih' which expects τ.digits.take (i + 1)
      have hlen_next : (τ.digits.take (i + 1)).length + (k + 1 - (i + 1)) = k + 1 := by
        simp only [List.length_take, hτlen]
        rw [Nat.min_eq_left (by omega : i + 1 ≤ k + 1)]
        omega
      have hvalid_next : isValidPrefix' ω (τ.digits.take (i + 1)) := by
        rw [← h_ext]
        exact isValidPrefix'_append_singleton hvalid (findDigit_lt_radix ω k pfx rem hpfx_len hn_lt)
      have hn_next : rank - cumulativeCount ω k (τ.digits.take (i + 1)) <
          completionCount ω k (τ.digits.take (i + 1)) := by
        exact cumulativeCount_sub_lt_completionCount ω k τ (i + 1) hi'
      -- Apply IH
      have hrec := ih' hlen_next hn_next hvalid_next
      -- Show LHS equals RHS using hrec
      have heq1 : depth - 1 = k + 1 - (i + 1) := by simp only [depth]; omega
      have heq2 : (findDigit ω k pfx rem).2 = rank - cumulativeCount ω k (τ.digits.take (i + 1)) := h_rem_next
      -- The goal's encodeAux call equals τ.digits
      -- Rewrite using the equalities then apply hrec
      simp_rw [heq2, heq1, h_ext]
      simp only [pfx, rem, rank] at hrec ⊢
      exact hrec

/-- Encode is left inverse of decode -/
theorem variableRadixEncode_decode (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k) :
    variableRadixEncode ω k (variableRadixDecode ω k τ)
      (variableRadixDecode_lt ω k τ) = τ := by
  -- Use encodeAux_recovers with i = 0
  unfold variableRadixEncode variableRadixDecode finiteRank
  simp only
  have hlen : ([] : PrefixWord).length + (k + 1) = k + 1 := by simp
  have h := encodeAux_recovers ω k τ 0 (by omega)
  simp only [List.take_zero, cumulativeCount, List.length_nil, Finset.range_zero,
    Finset.sum_empty, Nat.sub_zero] at h
  have hvalid := isValidPrefix'_nil ω
  have hn : cumulativeCount ω k τ.digits < completionCount ω k [] :=
    variableRadixDecode_lt ω k τ
  have result := h hlen hn hvalid
  apply FiniteVariableSpace.ext
  exact result

/-- Decode is left inverse of encode -/
theorem variableRadixDecode_encode (ω : RadixLaw) (k : ℕ) (n : ℕ)
    (hn : n < completionCount ω k []) :
    variableRadixDecode ω k (variableRadixEncode ω k n hn) = n := by
  -- Use encodeAux_cumulativeCount with pfx = []
  unfold variableRadixDecode variableRadixEncode finiteRank
  simp only
  have hlen : ([] : PrefixWord).length + (k + 1) = k + 1 := by simp
  have h := encodeAux_cumulativeCount ω k n (k + 1) [] hlen hn (isValidPrefix'_nil ω)
  simp only [cumulativeCount, List.length_nil, Finset.range_zero, Finset.sum_empty, zero_add] at h
  exact h

end FdrsFormal.Modes.VariableRadix
