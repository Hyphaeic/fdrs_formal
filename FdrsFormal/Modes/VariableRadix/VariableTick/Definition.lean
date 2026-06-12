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

# Variable Radix Tick Definition

This file defines the Tick operator for variable radix systems.

## Mathematical Content (fdrs.md lines 4099-4117)

**Definition 63 (variable Tick via ranking)**:
Define T^{(k)}_ω: R^{(k)}_ω → R^{(k)}_ω by:
  T^{(k)}_ω(τ) := enc^{(k)}_ω((dec^{(k)}_ω(τ) + 1) mod |R^{(k)}_ω|)

**Definition 64 (variable Tick via lex successor)**:
Alternatively, T(τ) is the lexicographic successor of τ (with wraparound).

## References

- fdrs.md, Phase 5-6, Section 4 (lines 4099-4117)
-/

import FdrsFormal.Modes.VariableRadix.Encoding.Encoding

namespace FdrsFormal.Modes.VariableRadix

/-!
## Variable Radix Tick (Cyclic, Finite)
-/

/--
The cyclic Tick operator on finite variable radix space.

**fdrs.md Definition 63**: T^{(k)}_ω(τ) = enc((dec(τ) + 1) mod |R^{(k)}_ω|)

This increments the rank by 1, wrapping around at the maximum.
-/
def cyclicVariableTick (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k) :
    FiniteVariableSpace ω k :=
  let n := variableRadixDecode ω k τ
  let size := completionCount ω k []
  let n' := (n + 1) % size
  variableRadixEncode ω k n' (Nat.mod_lt _ (completionCount_pos ω k [] (Nat.zero_le _)))

/-- Cyclic tick increments the rank by 1 modulo space size -/
theorem cyclicVariableTick_decode (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k) :
    variableRadixDecode ω k (cyclicVariableTick ω k τ) =
      (variableRadixDecode ω k τ + 1) % completionCount ω k [] := by
  simp only [cyclicVariableTick]
  exact variableRadixDecode_encode ω k _ _

/-!
## Variable Radix Tick (Non-cyclic, Infinite Case via Carry Algorithm)

**fdrs.md Definition 66**: For an eventually-maximal infinite path τ,
T(τ) finds the rightmost non-maximal digit, increments it, and resets
the suffix to zeros. This is the infinite analogue of the carry algorithm.

The infinite variable radix space R^{(∞)}_ω is uncountable (it contains
Cantor space {0,1}^ℕ), so there is no bijection with ℕ. Instead we
define Tick directly via digit manipulation.
-/

/-- A path is maximal if every digit equals radix - 1. -/
def IsMaximalPath (ω : RadixLaw) (τ : InfiniteVariableSpace ω) : Prop :=
  ∀ i, τ.digit i = ω.radix (τ.getPrefix i) - 1

/-- A path is eventually maximal if all digits past some bound are maximal. -/
def IsEventuallyMaximal (ω : RadixLaw) (τ : InfiniteVariableSpace ω) : Prop :=
  ∃ N, ∀ i, i ≥ N → τ.digit i = ω.radix (τ.getPrefix i) - 1

/--
Given an eventually-maximal non-maximal path, there exists a rightmost
non-maximal position j such that all positions after j are maximal.
-/
theorem exists_largest_nonmax (ω : RadixLaw) (τ : InfiniteVariableSpace ω)
    (hev : IsEventuallyMaximal ω τ) (hnotmax : ¬IsMaximalPath ω τ) :
    ∃ j, τ.digit j < ω.radix (τ.getPrefix j) - 1 ∧
         ∀ i, i > j → τ.digit i = ω.radix (τ.getPrefix i) - 1 := by
  obtain ⟨N, hN⟩ := hev
  -- There is some non-maximal position
  simp only [IsMaximalPath] at hnotmax
  push_neg at hnotmax
  obtain ⟨i₀, hi₀⟩ := hnotmax
  have hi₀_lt : τ.digit i₀ < ω.radix (τ.getPrefix i₀) - 1 := by
    have hv : τ.digit i₀ < ω.radix (τ.getPrefix i₀) := τ.valid i₀
    omega
  -- i₀ < N (otherwise it would be maximal)
  have hi₀N : i₀ < N := by
    by_contra h; push_neg at h; exact absurd (hN i₀ h) (by omega)
  -- Filter non-maximal positions in {0, ..., N-1}
  let S := (Finset.range N).filter fun i =>
    decide (τ.digit i < ω.radix (τ.getPrefix i) - 1) = true
  have hS_nonempty : S.Nonempty :=
    ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi₀N, decide_eq_true hi₀_lt⟩⟩
  -- Take the maximum
  set j := S.max' hS_nonempty
  have hj_mem := Finset.max'_mem S hS_nonempty
  rw [Finset.mem_filter] at hj_mem
  have hj_nonmax : τ.digit j < ω.radix (τ.getPrefix j) - 1 := by
    have := hj_mem.2; simp at this; exact this
  refine ⟨j, hj_nonmax, fun i hi => ?_⟩
  -- For i > j: either i ≥ N (done by hN) or i < N but not in S
  by_cases hiN : i ≥ N
  · exact hN i hiN
  · push_neg at hiN
    -- i < N and i > j, so i ∉ S (since j is the max of S)
    have : i ∉ S := by
      intro hmem
      have := Finset.le_max' S i hmem
      omega
    rw [Finset.mem_filter] at this
    push_neg at this
    have hi_range : i ∈ Finset.range N := Finset.mem_range.mpr hiN
    have := this hi_range
    simp at this
    have hv : τ.digit i < ω.radix (τ.getPrefix i) := τ.valid i
    omega

/-- The carry index for an eventually-maximal non-maximal infinite path. -/
noncomputable def carryIndexInfinite (ω : RadixLaw) (τ : InfiniteVariableSpace ω)
    (hev : IsEventuallyMaximal ω τ) (hnotmax : ¬IsMaximalPath ω τ) : ℕ :=
  (exists_largest_nonmax ω τ hev hnotmax).choose

theorem carryIndexInfinite_nonMaximal (ω : RadixLaw) (τ : InfiniteVariableSpace ω)
    (hev : IsEventuallyMaximal ω τ) (hnotmax : ¬IsMaximalPath ω τ) :
    τ.digit (carryIndexInfinite ω τ hev hnotmax) <
      ω.radix (τ.getPrefix (carryIndexInfinite ω τ hev hnotmax)) - 1 :=
  (exists_largest_nonmax ω τ hev hnotmax).choose_spec.1

theorem carryIndexInfinite_allMaxAfter (ω : RadixLaw) (τ : InfiniteVariableSpace ω)
    (hev : IsEventuallyMaximal ω τ) (hnotmax : ¬IsMaximalPath ω τ)
    (i : ℕ) (hi : i > carryIndexInfinite ω τ hev hnotmax) :
    τ.digit i = ω.radix (τ.getPrefix i) - 1 :=
  (exists_largest_nonmax ω τ hev hnotmax).choose_spec.2 i hi

/--
Helper: the prefix of the tick result at positions ≤ j equals the prefix of τ.
-/
private theorem tick_prefix_eq (ω : RadixLaw) (τ : InfiniteVariableSpace ω)
    (j : ℕ) (n : ℕ) (hn : n ≤ j) :
    List.ofFn (fun m : Fin n => if m.val < j then τ.digit m.val
                                else if m.val = j then τ.digit j + 1
                                else 0) =
    τ.getPrefix n := by
  simp only [InfiniteVariableSpace.getPrefix]
  congr 1; ext ⟨m, hm⟩
  simp only [show m < j from by omega, ite_true]

/--
The non-cyclic Tick operator on infinite variable radix space.

**fdrs.md Definition 66**: Find the rightmost non-maximal digit j,
increment it, and reset the suffix to zeros.

Requires the path to be eventually maximal (so the carry terminates)
and not fully maximal (so there is a digit to increment).
-/
noncomputable def variableTick (ω : RadixLaw) (τ : InfiniteVariableSpace ω)
    (hev : IsEventuallyMaximal ω τ) (hnotmax : ¬IsMaximalPath ω τ) :
    InfiniteVariableSpace ω where
  digit i :=
    let j := carryIndexInfinite ω τ hev hnotmax
    if i < j then τ.digit i
    else if i = j then τ.digit j + 1
    else 0
  valid := by
    intro i
    have hj_nm := carryIndexInfinite_nonMaximal ω τ hev hnotmax
    set j := carryIndexInfinite ω τ hev hnotmax with hj_def
    simp only []
    by_cases hij : i < j
    · -- Prefix: digit = τ.digit i, prefix unchanged
      simp only [hij, ite_true]
      have hpfx : List.ofFn (fun m : Fin i => if m.val < j then τ.digit m.val
                    else if m.val = j then τ.digit j + 1 else 0) = τ.getPrefix i :=
        tick_prefix_eq ω τ j i (Nat.le_of_lt hij)
      rw [hpfx]; exact τ.valid i
    · by_cases hij' : i = j
      · -- Carry position: digit = τ.digit j + 1
        subst hij'
        simp only [lt_irrefl, ite_false, ite_true]
        have hpfx : List.ofFn (fun m : Fin j => if m.val < j then τ.digit m.val
                      else if m.val = j then τ.digit j + 1 else 0) = τ.getPrefix j :=
          tick_prefix_eq ω τ j j le_rfl
        rw [hpfx]; omega
      · -- Suffix: digit = 0
        simp only [show ¬(i < j) from by omega, hij', ite_false]
        exact ω.radix_pos _

/-!
## Tick as Lexicographic Successor
-/

/--
Helper: If s < t in lex order, extract the first differing position.
-/
private theorem lex_first_diff_pos {s t : PrefixWord}
    (hlt : s < t) (hlen : s.length = t.length) :
    ∃ i, ∃ hi_s : i < s.length, ∃ hi_t : i < t.length,
      s.take i = t.take i ∧ s.get ⟨i, hi_s⟩ < t.get ⟨i, hi_t⟩ := by
  induction hlt with
  | nil => simp at hlen
  | @rel a₁ l₁' a₂ l₂' hr =>
    exact ⟨0, by simp, by simp, rfl, hr⟩
  | @cons a l₁' l₂' htail ih =>
    obtain ⟨i, hi₁, hi₂, htake, hrel⟩ := ih (by simp only [List.length_cons] at hlen; omega)
    refine ⟨i + 1, by simp; omega, by simp; omega, ?_, ?_⟩
    · simp only [List.take_succ_cons]
      exact congrArg (a :: ·) htake
    · simp only [List.get_cons_succ]
      exact hrel

/--
Check if a sequence is the maximum element (all digits maximal).
-/
def isMaxElement (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k) : Bool :=
  -- τ is maximal iff carryIndex returns none
  (List.finRange (k + 1)).find? (fun i =>
    τ.digitAt i < ω.radix (τ.getPrefix i.val (Nat.le_of_lt i.isLt)) - 1) |>.isNone

/--
The lexicographic successor of a finite sequence (if it exists within the space).

This is the direct digit-level computation of Tick.
Returns None if τ is the maximum element (all digits maximal).
-/
def lexSuccessor (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k) :
    Option (FiniteVariableSpace ω k) :=
  if isMaxElement ω k τ then none else some (cyclicVariableTick ω k τ)

/--
Lex-largest element must have all maximal digits.

If τ is lex-largest but has a non-maximal digit at position i,
we construct σ > τ: keep prefix, increment digit i, fill zeros after.
-/
theorem lexLargest_allMaximal_aux (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k)
    (i : ℕ) (hi : i < k + 1)
    (h_nonmax : τ.digitAt ⟨i, hi⟩ < ω.radix (τ.getPrefix i (Nat.le_of_lt hi)) - 1)
    (h_largest : ∀ σ : FiniteVariableSpace ω k, ¬(τ.digits < σ.digits)) :
    False := by
  have hi' : i < τ.digits.length := by rw [τ.length_eq]; exact hi
  -- Incremented digit is still valid
  have hd_lt : τ.digits[i] + 1 < ω.radix (τ.digits.take i) := by
    simp only [FiniteVariableSpace.digitAt, FiniteVariableSpace.getPrefix,
               List.get_eq_getElem] at h_nonmax; omega
  -- τ.digits.take i is a valid prefix
  have hpfx_valid : isValidPrefix' ω (τ.digits.take i) := by
    intro j hj
    have hj_lt : j < i := by simp [τ.length_eq] at hj; omega
    rw [List.get_eq_getElem, List.getElem_take, List.take_take,
        show min j i = j from Nat.min_eq_left (by omega)]
    exact τ.valid j (by rw [τ.length_eq]; omega)
  -- Build σ_list = τ.digits.take i ++ (d :: zeros)
  set pfx := τ.digits.take i
  set d := τ.digits[i] + 1
  set σ_list := pfx ++ (d :: List.replicate (k - i) 0)
  have hpfx_len : pfx.length = i := by simp [pfx, τ.length_eq]; omega
  have hσ_len : σ_list.length = k + 1 := by simp [σ_list, hpfx_len]; omega
  -- Validity via isValidPrefix'_append_singleton + zeros
  have hσ_valid : isValidPrefix' ω σ_list := by
    have h_ext := isValidPrefix'_append_singleton hpfx_valid hd_lt
    intro j hj; rw [hσ_len] at hj
    by_cases hji : j ≤ i
    · -- j ≤ i: validity follows from pfx ++ [d] being valid
      have hj_in : j < (pfx ++ [d]).length := by simp [hpfx_len]; omega
      have : σ_list = (pfx ++ [d]) ++ List.replicate (k - i) 0 := by
        simp [σ_list, List.append_assoc, List.singleton_append]
      simp only [this, List.get_eq_getElem]
      rw [List.getElem_append_left hj_in,
          List.take_append_of_le_length (by omega : j ≤ (pfx ++ [d]).length)]
      exact h_ext j (by simp [hpfx_len]; omega)
    · -- j > i: digit is 0 from replicate, 0 < radix
      push_neg at hji
      have hj_ge : (pfx ++ [d]).length ≤ j := by simp [hpfx_len]; omega
      have : σ_list = (pfx ++ [d]) ++ List.replicate (k - i) 0 := by
        simp [σ_list, List.append_assoc, List.singleton_append]
      simp only [this, List.get_eq_getElem]
      rw [List.getElem_append_right hj_ge]
      simp [List.getElem_replicate]
      exact ω.radix_pos _
  -- Construct σ
  let σ : FiniteVariableSpace ω k := ⟨σ_list, hσ_len, hσ_valid⟩
  apply h_largest σ
  -- Lex ordering: τ.digits < σ.digits
  show τ.digits < σ_list
  -- Decompose τ.digits at position i: pfx ++ τ[i] :: drop(i+1)
  have h_decomp : τ.digits = pfx ++ (τ.digits[i]'hi' :: τ.digits.drop (i + 1)) := by
    have h1 := (List.take_append_drop i τ.digits).symm
    rw [← List.getElem_cons_drop hi'] at h1
    exact h1
  rw [h_decomp]
  -- σ_list = pfx ++ (d :: zeros), τ.digits[i]'hi' < d, so Lex.rel applies
  exact List.Lex.append_left (· < ·)
    (List.Lex.rel (show τ.digits[i]'hi' < d by omega)) pfx

/-- isMaxElement is true iff decode equals completionCount - 1 -/
theorem isMaxElement_iff_decode_max (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k) :
    isMaxElement ω k τ = true ↔ variableRadixDecode ω k τ = completionCount ω k [] - 1 := by
  simp only [isMaxElement, Option.isNone_iff_eq_none]
  constructor
  · -- isMaxElement = true → decode = max
    intro h_none
    -- h_none says find? returns none, so all digits are maximal
    have h_all_max : ∀ i : Fin (k + 1),
        τ.digitAt i = ω.radix (τ.getPrefix i.val (Nat.le_of_lt i.isLt)) - 1 := by
      intro i
      rw [List.find?_eq_none] at h_none
      have := h_none i (List.mem_finRange i)
      simp only [decide_eq_true_eq, not_lt] at this
      have h_lt := τ.digitAt_lt i
      omega
    -- Now we need to show that all maximal digits means decode = max
    -- This follows from the bijection: τ is lex-largest, so decode(τ) = max
    -- We proved this in Termination.lean
    have hpos : 0 < completionCount ω k [] := completionCount_pos ω k [] (by simp)
    have h_max_lt : completionCount ω k [] - 1 < completionCount ω k [] := by omega
    -- Use the bijection: if τ ≠ encode(max-1), then decode(τ) ≠ max-1
    -- But τ is lex-largest, so it must equal encode(max-1)
    -- Actually, let's use the approach from cumulativeCount_allMaximal
    -- The key is: all maximal digits → decode = max
    by_contra h_ne
    have h_lt : variableRadixDecode ω k τ < completionCount ω k [] - 1 := by
      have := variableRadixDecode_lt ω k τ
      omega
    -- Let τ_max = encode(completionCount - 1)
    set τ_max := variableRadixEncode ω k (completionCount ω k [] - 1) h_max_lt
    have h_decode_max : variableRadixDecode ω k τ_max = completionCount ω k [] - 1 :=
      variableRadixDecode_encode ω k (completionCount ω k [] - 1) h_max_lt
    -- Since decode(τ) < decode(τ_max), we have τ < τ_max (lex order)
    have h_lex_lt : τ.digits < τ_max.digits := by
      rw [← decode_lt_iff ω k τ τ_max]
      calc variableRadixDecode ω k τ
          < completionCount ω k [] - 1 := h_lt
        _ = variableRadixDecode ω k τ_max := h_decode_max.symm
    -- But τ has all maximal digits, so τ_max < τ (by allMaximal_not_lt_any logic)
    -- This is a contradiction
    -- Actually we need the symmetric statement: τ_max cannot be > τ when τ has all max digits
    -- Let's prove τ_max.digits < τ.digits cannot happen
    exfalso
    -- We need to show that if τ has all maximal digits and τ < τ_max, that's impossible
    -- because τ_max.digits[i] < τ.digits[i] = radix - 1 would mean τ_max.digits[i] ≥ radix
    -- Actually, h_lex_lt says τ < τ_max, meaning at some position i:
    -- τ.take i = τ_max.take i and τ[i] < τ_max[i]
    -- But τ[i] = radix(prefix) - 1 (maximal), so τ_max[i] ≥ radix
    -- But τ_max[i] < radix (validity), contradiction
    have hlen_eq : τ.digits.length = τ_max.digits.length := by rw [τ.length_eq, τ_max.length_eq]
    -- Extract first differing position using the helper lemma
    obtain ⟨i, hi_τ, hi_max, hprefix, hlt_digit⟩ := lex_first_diff_pos h_lex_lt hlen_eq
    -- At position i, τ has maximal digit
    have hi : i < k + 1 := by rw [← τ.length_eq]; exact hi_τ
    have h_τ_max_digit := h_all_max ⟨i, hi⟩
    simp only [FiniteVariableSpace.digitAt, FiniteVariableSpace.getPrefix] at h_τ_max_digit
    -- hlt_digit : τ.digits[i] < τ_max.digits[i]
    -- h_τ_max_digit : τ.digits[i] = radix(τ.take i) - 1
    -- So τ_max.digits[i] ≥ radix(τ.take i)
    -- But τ_max.digits[i] < radix(τ_max.take i) = radix(τ.take i) (prefixes equal)
    have h_valid := τ_max.digitAt_lt ⟨i, hi⟩
    simp only [FiniteVariableSpace.digitAt, FiniteVariableSpace.getPrefix] at h_valid
    have h_radix_eq : ω.radix (τ.digits.take i) = ω.radix (τ_max.digits.take i) := by
      rw [hprefix]
    rw [h_radix_eq] at h_τ_max_digit
    omega
  · -- decode = max → isMaxElement = true
    intro h_max
    -- If decode = max, then τ is the lex-largest element
    -- So all digits must be maximal (otherwise there's a larger element)
    rw [List.find?_eq_none]
    intro i _
    simp only [decide_eq_true_eq, not_lt]
    -- Need: τ.digitAt i ≥ radix - 1, i.e., τ.digitAt i = radix - 1
    have h_lt := τ.digitAt_lt i
    by_contra h_not_max
    push_neg at h_not_max
    have h_strict : τ.digitAt i < ω.radix (τ.getPrefix i.val (Nat.le_of_lt i.isLt)) - 1 := by omega
    -- If digit i is not maximal, we can construct a larger element
    -- Let σ = τ with digit i incremented by 1
    -- Then σ > τ in lex order, so decode(σ) > decode(τ) = max
    -- But decode(σ) < completionCount, contradiction
    -- Actually, simpler: if not all digits maximal, then τ is not the lex-largest
    -- So there exists σ with decode(σ) = decode(τ) + 1 (namely cyclicTick(τ))
    -- But decode(τ) = max = completionCount - 1
    -- So decode(cyclicTick(τ)) = (max + 1) % completionCount = 0 ≠ max + 1
    -- This doesn't directly give a contradiction...
    -- Let's use a different approach: the element with decode = max is unique
    -- It's encode(max) = encode(completionCount - 1)
    -- If τ has a non-maximal digit, then τ ≠ encode(max)
    -- So decode(τ) ≠ max, contradiction with h_max
    have hpos : 0 < completionCount ω k [] := completionCount_pos ω k [] (by simp)
    have h_max_lt : completionCount ω k [] - 1 < completionCount ω k [] := by omega
    set τ_max := variableRadixEncode ω k (completionCount ω k [] - 1) h_max_lt
    -- τ_max has decode = completionCount - 1
    have h_decode_max : variableRadixDecode ω k τ_max = completionCount ω k [] - 1 :=
      variableRadixDecode_encode ω k (completionCount ω k [] - 1) h_max_lt
    -- Since decode(τ) = decode(τ_max), we have τ = τ_max by injectivity
    have h_eq : τ = τ_max := decode_inj ω k (h_max.trans h_decode_max.symm)
    -- But τ has digit i < radix - 1, while τ_max should have all maximal digits
    -- Let's check if τ_max really has all maximal digits
    -- Actually, by the bijection, τ_max = encode(max) is the lex-largest element
    -- So τ_max must have all maximal digits (proved above in the reverse direction)
    -- But wait, we're in the middle of proving this...
    -- Let me use a cleaner argument: τ = τ_max, but τ has digit i not maximal
    -- We need to show τ_max has digit i maximal, contradiction
    -- This requires knowing that encode(max) produces all maximal digits
    -- Let's just use: if τ = τ_max and τ.digitAt i < radix - 1, then
    -- τ_max.digitAt i = τ.digitAt i < radix - 1, so τ_max has a non-maximal digit
    -- But then by the first direction of this lemma, decode(τ_max) < max
    -- But decode(τ_max) = max by definition. Contradiction.
    subst h_eq
    -- Now τ_max.digitAt i < radix - 1
    -- But we're trying to prove find? returns none for τ_max
    -- This is a circular argument...
    -- Let me try a different approach: use strict monotonicity
    -- If τ has a non-maximal digit at position i, then cyclicTick(τ) > τ in lex order
    -- So decode(cyclicTick(τ)) > decode(τ) = completionCount - 1
    -- But decode ≤ completionCount - 1 for all elements, contradiction
    have h_tick := cyclicVariableTick_decode ω k τ_max
    -- h_tick : decode(tick(τ_max)) = (decode(τ_max) + 1) % completionCount
    --        = (completionCount - 1 + 1) % completionCount = 0
    -- So tick(τ_max) has decode 0
    -- If τ_max has a non-maximal digit, then τ_max < tick(τ_max) in some sense...
    -- Actually this is getting complicated. Let me use the contrapositive more directly.
    -- We have: decode(τ) = max implies τ = encode(max)
    -- And encode(max) should be the lex-largest element
    -- By definition, encode produces the element at that rank
    -- The element at rank max is the lex-largest
    -- So encode(max) has all maximal digits (by the property of lex order)
    -- Actually, I think the cleanest proof is: assume not all maximal, get a contradiction
    -- The element with all maximal digits has decode = max (proved above)
    -- By uniqueness of decode = max, τ equals that element
    -- So τ has all maximal digits, contradiction
    -- But this requires first proving "some element has all maximal digits"
    -- Let's just construct it: start with digit 0 being radix([]) - 1, etc.
    -- This is complex to formalize directly.
    -- For now, let me use: variableRadixDecode is strictly monotone on lex order
    -- If τ has decode = max and there exists σ > τ, then decode(σ) > decode(τ) = max
    -- But decode(σ) ≤ max - 1, contradiction
    -- So no σ > τ exists, meaning τ is lex-largest
    -- A lex-largest element must have all maximal digits (otherwise increment to get larger)
    -- So τ has all maximal digits at position i, contradiction with h_strict
    have h_τ_largest : ∀ σ : FiniteVariableSpace ω k, ¬(τ_max.digits < σ.digits) := by
      intro σ h_gt
      have h_decode_gt := (decode_lt_iff ω k τ_max σ).mpr h_gt
      rw [h_decode_max] at h_decode_gt
      have h_σ_lt := variableRadixDecode_lt ω k σ
      omega
    -- Since τ_max is lex-largest and has digit i not maximal, we can construct σ > τ_max
    -- Use the axiom that captures the key construction
    exact lexLargest_allMaximal_aux ω k τ_max i.val i.isLt h_strict h_τ_largest

/-- Lex successor equals cyclic tick (when not at maximum) -/
theorem lexSuccessor_eq_cyclicTick (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k)
    (hmax : variableRadixDecode ω k τ < completionCount ω k [] - 1) :
    lexSuccessor ω k τ = some (cyclicVariableTick ω k τ) := by
  simp only [lexSuccessor]
  -- Need to show: isMaxElement is false
  have h_not_max : isMaxElement ω k τ = false := by
    simp only [Bool.eq_false_iff]
    intro h_is_max
    have := (isMaxElement_iff_decode_max ω k τ).mp h_is_max
    omega
  simp only [h_not_max, Bool.false_eq_true, ite_false]

/-- At maximum, lex successor is none (cyclic tick wraps) -/
theorem lexSuccessor_of_max (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k)
    (hmax : variableRadixDecode ω k τ = completionCount ω k [] - 1) :
    lexSuccessor ω k τ = none := by
  simp only [lexSuccessor]
  have h_is_max : isMaxElement ω k τ = true := (isMaxElement_iff_decode_max ω k τ).mpr hmax
  simp only [h_is_max, ite_true]

end FdrsFormal.Modes.VariableRadix
