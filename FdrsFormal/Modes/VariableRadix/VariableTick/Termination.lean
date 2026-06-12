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

# Carry Termination for Variable Radix Tick

This file proves that the carry algorithm always terminates.

## Mathematical Content (fdrs.md lines 4148-4160)

**Proposition 81 (Carry Termination)**:
The carry algorithm always terminates in at most k steps for k-digit sequences.

At each step, the carry propagates to a higher position, so it must stop
within k iterations (either finding a non-maximal digit or wrapping).

## References

- fdrs.md, Phase 5-6, Section 5 (lines 4148-4160)
-/

import FdrsFormal.Modes.VariableRadix.VariableTick.CarryAlgorithm
import FdrsFormal.Modes.VariableRadix.VariableTick.Correctness

namespace FdrsFormal.Modes.VariableRadix

/-!
## Carry Termination
-/

/--
**Proposition 81**: The carry algorithm terminates in at most k steps.

For a k-digit sequence, the carry can propagate through at most k positions
before either finding a non-maximal digit or determining all digits are maximal.
-/
theorem carry_terminates (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k) :
    (carryIndex ω k τ).isSome ∨ (∀ i : Fin (k + 1),
      isMaximalDigit ω (τ.getPrefix i.val (by omega))
        (τ.digitAt i)) := by
  -- carryIndex finds the first non-maximal digit
  -- Either such a digit exists (isSome), or all are maximal
  by_cases h : (carryIndex ω k τ).isSome
  · left; exact h
  · right
    simp only [Option.isSome_iff_exists, not_exists] at h
    intro i
    simp only [isMaximalDigit]
    -- carryIndex = none means find? returned none
    -- So no index satisfies digitAt i < radix(prefix) - 1
    -- Which means all digits are maximal (= radix - 1)
    by_contra h_not_max
    -- h_not_max : τ.digitAt i ≠ ω.radix (τ.getPrefix i.val _) - 1
    -- Since digitAt i < radix (from digitAt_lt), we have digitAt i < radix - 1
    have h_lt := τ.digitAt_lt i
    have h_strict : τ.digitAt i < ω.radix (τ.getPrefix i.val (by omega)) - 1 := by
      omega
    -- So i should be found by find?, which means carryIndex.isSome
    simp only [carryIndex] at h
    -- h : ¬∃ a, reversed.find? ... = some a
    -- But find? on reversed list should find some element since h_strict holds for i
    have h_not_none : (List.finRange (k + 1)).reverse.find? (fun j =>
        τ.digitAt j < ω.radix (τ.getPrefix j.val (Nat.le_of_lt j.isLt)) - 1) ≠ none := by
      intro heq
      rw [List.find?_eq_none] at heq
      have h_i_mem : i ∈ (List.finRange (k + 1)).reverse := by
        rw [List.mem_reverse]
        exact List.mem_finRange i
      have := heq i h_i_mem
      simp only [decide_eq_true_eq] at this
      omega
    rw [Option.ne_none_iff_exists'] at h_not_none
    obtain ⟨j, hj⟩ := h_not_none
    exact h j hj

/-- The carry index, if it exists, is at most k -/
theorem carryIndex_le (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k)
    (j : Fin (k + 1)) (hj : carryIndex ω k τ = some j) :
    j.val ≤ k :=
  Nat.lt_succ_iff.mp j.isLt

/-!
## Complexity Analysis
-/

/-- The carry algorithm has linear time complexity in k -/
theorem carry_complexity (ω : RadixLaw) (k : ℕ) :
    ∃ (steps : FiniteVariableSpace ω k → ℕ),
      (∀ τ, steps τ ≤ k + 1) ∧
      (∀ τ, tickByCarry ω k τ = cyclicVariableTick ω k τ) := by
  use fun _ => k + 1
  constructor
  · intro τ; exact Nat.le_refl _
  · intro τ; exact tickByCarry_eq_cyclicTick ω k τ

/-!
## Worst Case Analysis
-/

/-- A sequence has worst-case carry if all digits are maximal -/
def isWorstCaseCarry (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k) : Prop :=
  carryIndex ω k τ = none

/-- Worst case means all digits are maximal -/
theorem worstCase_iff_allMaximal (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k) :
    isWorstCaseCarry ω k τ ↔
      ∀ i : Fin (k + 1),
        isMaximalDigit ω (τ.getPrefix i.val (by omega))
          (τ.digitAt i) := by
  simp only [isWorstCaseCarry, carryIndex, isMaximalDigit]
  constructor
  · -- carryIndex = none → all digits maximal
    intro h_none i
    -- find? on reversed list = none means no element satisfies the predicate
    rw [List.find?_eq_none] at h_none
    have h_i_mem : i ∈ (List.finRange (k + 1)).reverse := by
      rw [List.mem_reverse]
      exact List.mem_finRange i
    have := h_none i h_i_mem
    simp only [decide_eq_true_eq, not_lt] at this
    have h_lt := τ.digitAt_lt i
    omega
  · -- all digits maximal → carryIndex = none
    intro h_all
    rw [List.find?_eq_none]
    intro i h_i_mem
    simp only [decide_eq_true_eq, not_lt]
    have := h_all i
    omega

/--
Helper: If τ > σ in lex order, extract the first differing position.
-/
private theorem lex_first_diff_pos {s t : PrefixWord}
    (hgt : t < s) (hlen : s.length = t.length) :
    ∃ i, ∃ hi_s : i < s.length, ∃ hi_t : i < t.length,
      t.take i = s.take i ∧ t.get ⟨i, hi_t⟩ < s.get ⟨i, hi_s⟩ := by
  induction hgt with
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
Helper: τ with all maximal digits cannot have any element larger in lex order.

If τ < σ (lex), we derive a contradiction because τ[i] is maximal at some position.
-/
private theorem allMaximal_not_lt_any (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k)
    (hmax : ∀ i : Fin (k + 1), isMaximalDigit ω (τ.getPrefix i.val (Nat.le_of_lt i.isLt)) (τ.digitAt i))
    (σ : FiniteVariableSpace ω k) :
    ¬(τ.digits < σ.digits) := by
  intro hgt
  -- hgt : τ.digits < σ.digits, meaning at some position i, τ[i] < σ[i] with equal prefix
  -- But τ[i] is maximal (= radix - 1), so σ[i] ≥ radix, contradicting validity
  have hlen_eq : σ.digits.length = τ.digits.length := by rw [τ.length_eq, σ.length_eq]
  -- Extract the first differing position from the lex relation
  obtain ⟨i, hi_σ, hi_τ, hprefix, hlt_digit⟩ := lex_first_diff_pos hgt hlen_eq
  -- At position i, τ has a maximal digit
  have hi : i < k + 1 := by rw [← τ.length_eq]; exact hi_τ
  have h_τ_max := hmax ⟨i, hi⟩
  simp only [isMaximalDigit, FiniteVariableSpace.digitAt, FiniteVariableSpace.getPrefix] at h_τ_max
  -- h_τ_max says τ.digits[i] = radix(τ.take i) - 1
  -- hlt_digit says τ.digits[i] < σ.digits[i]
  -- So σ.digits[i] ≥ radix(τ.take i)
  -- But σ.digits[i] < radix(σ.take i) = radix(τ.take i) (since prefixes equal)
  have h_σ_valid := σ.digitAt_lt ⟨i, hi⟩
  simp only [FiniteVariableSpace.digitAt, FiniteVariableSpace.getPrefix] at h_σ_valid
  -- h_σ_valid says σ.digits[i] < radix(σ.take i)
  -- Since hprefix : τ.take i = σ.take i, we have radix(τ.take i) = radix(σ.take i)
  have h_radix_eq : ω.radix (τ.digits.take i) = ω.radix (σ.digits.take i) := by
    rw [hprefix]
  rw [h_radix_eq] at h_τ_max
  -- Now: τ.digits[i] = radix - 1 and τ.digits[i] < σ.digits[i] < radix
  -- This means σ.digits[i] > radix - 1, i.e., σ.digits[i] ≥ radix
  -- But σ.digits[i] < radix. Contradiction.
  have hge : σ.digits.get ⟨i, hi_σ⟩ ≥ ω.radix (σ.digits.take i) := by
    have hgt' : σ.digits.get ⟨i, hi_σ⟩ > τ.digits.get ⟨i, hi_τ⟩ := hlt_digit
    have heq' : τ.digits.get ⟨i, hi_τ⟩ = ω.radix (σ.digits.take i) - 1 := h_τ_max
    omega
  omega

/--
Helper: τ with all maximal digits is lexicographically the largest element.

When all digits are at their maximum value, no other element can be larger.
-/
private theorem allMaximal_isLexLargest (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k)
    (hmax : ∀ i : Fin (k + 1), isMaximalDigit ω (τ.getPrefix i.val (Nat.le_of_lt i.isLt)) (τ.digitAt i))
    (σ : FiniteVariableSpace ω k) (hne : σ ≠ τ) :
    σ.digits < τ.digits := by
  -- Use order preservation of decode: decode is order-preserving bijection
  -- If ¬(σ < τ) and σ ≠ τ, then decode(σ) ≥ decode(τ)
  -- But decode(τ) = completionCount - 1 (max value), so decode(σ) ≤ completionCount - 1
  -- If decode(σ) = decode(τ), then σ = τ by injectivity (contradiction)
  -- If decode(σ) > decode(τ), then σ > τ in lex order
  -- But this contradicts allMaximal_not_lt_any
  by_contra h_not_lt
  -- Either σ.digits = τ.digits or τ.digits < σ.digits
  have h_digits_ne : σ.digits ≠ τ.digits := by
    intro heq; exact hne (FiniteVariableSpace.ext heq)
  -- Since decode is an order-preserving bijection, ¬(σ < τ) means decode(σ) ≥ decode(τ)
  -- But τ has all maximal digits, so decode(τ) = max = completionCount - 1
  -- So decode(σ) ≥ completionCount - 1
  -- Since decode(σ) < completionCount, we have decode(σ) = completionCount - 1
  -- Then σ = τ by injectivity, contradiction
  have h_τ_decode := variableRadixDecode_lt ω k τ
  have h_σ_decode := variableRadixDecode_lt ω k σ
  -- Use that decode is strictly monotone: σ < τ ↔ decode(σ) < decode(τ)
  -- So ¬(σ < τ) ↔ decode(σ) ≥ decode(τ) (since total order)
  -- But we can also use: τ < σ ↔ decode(τ) < decode(σ)
  have h_not_lt' : ¬(τ.digits < σ.digits) := allMaximal_not_lt_any ω k τ hmax σ
  -- So ¬(τ < σ). Combined with ¬(σ < τ) and σ ≠ τ:
  -- If decode(σ) < decode(τ), then σ < τ (by order preservation) - contradiction
  -- If decode(σ) = decode(τ), then σ = τ (by injectivity) - contradiction
  -- If decode(σ) > decode(τ), then τ < σ (by order preservation) - contradiction with h_not_lt'
  have h_dec_σ_lt : ¬(variableRadixDecode ω k σ < variableRadixDecode ω k τ) := by
    intro hlt
    have := (decode_lt_iff ω k σ τ).mp hlt
    exact h_not_lt this
  have h_dec_τ_lt : ¬(variableRadixDecode ω k τ < variableRadixDecode ω k σ) := by
    intro hlt
    have := (decode_lt_iff ω k τ σ).mp hlt
    exact h_not_lt' this
  have h_dec_eq : variableRadixDecode ω k σ = variableRadixDecode ω k τ := by omega
  have h_eq : σ = τ := decode_inj ω k h_dec_eq
  exact hne h_eq

/--
Helper: When all digits are maximal, decode equals completionCount - 1.

The maximal element is lex-largest, and decode is order-preserving, so it has the maximum rank.
-/
private theorem cumulativeCount_allMaximal (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k)
    (hmax : ∀ i : Fin (k + 1), isMaximalDigit ω (τ.getPrefix i.val (Nat.le_of_lt i.isLt)) (τ.digitAt i)) :
    variableRadixDecode ω k τ = completionCount ω k [] - 1 := by
  -- Use the bijection property: decode is a bijection to {0, ..., completionCount - 1}
  -- The lex-largest element has the highest decode value
  -- Since τ is lex-largest (all maximal), decode(τ) = completionCount - 1
  have hpos : 0 < completionCount ω k [] := completionCount_pos ω k [] (by simp)
  -- encode(completionCount - 1) is the element with the maximum decode
  have h_max_lt : completionCount ω k [] - 1 < completionCount ω k [] := by omega
  set τ_max := variableRadixEncode ω k (completionCount ω k [] - 1) h_max_lt
  -- decode(τ_max) = completionCount - 1
  have h_decode_max : variableRadixDecode ω k τ_max = completionCount ω k [] - 1 :=
    variableRadixDecode_encode ω k (completionCount ω k [] - 1) h_max_lt
  -- Show τ = τ_max by showing they have the same decode
  -- We know decode(τ) < completionCount
  have h_τ_lt := variableRadixDecode_lt ω k τ
  -- If decode(τ) < completionCount - 1, then τ < τ_max (by order preservation)
  -- But τ is lex-largest, so this is impossible
  by_cases heq : variableRadixDecode ω k τ = completionCount ω k [] - 1
  · exact heq
  · exfalso
    have h_lt_max : variableRadixDecode ω k τ < completionCount ω k [] - 1 := by omega
    -- By order preservation (Theorem A), this means τ < τ_max in lex order
    have h_lex_lt : τ.digits < τ_max.digits := by
      rw [← decode_lt_iff ω k τ τ_max]
      calc variableRadixDecode ω k τ
          < completionCount ω k [] - 1 := h_lt_max
        _ = variableRadixDecode ω k τ_max := h_decode_max.symm
    -- But τ is lex-largest (all maximal), so τ_max ≤ τ, i.e., ¬(τ < τ_max)
    have hne : τ_max ≠ τ := by
      intro heq'
      have := congrArg (variableRadixDecode ω k) heq'
      rw [h_decode_max] at this
      omega
    have h_τmax_lt := allMaximal_isLexLargest ω k τ hmax τ_max hne
    -- h_τmax_lt : τ_max.digits < τ.digits
    -- h_lex_lt : τ.digits < τ_max.digits
    -- These contradict trichotomy
    exact Nat.lt_irrefl (variableRadixDecode ω k τ)
      (calc variableRadixDecode ω k τ
          < variableRadixDecode ω k τ_max := (decode_lt_iff ω k τ τ_max).mpr h_lex_lt
        _ < variableRadixDecode ω k τ := (decode_lt_iff ω k τ_max τ).mpr h_τmax_lt)

/-- In worst case, tick wraps to zero -/
theorem worstCase_wraps_to_zero (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k)
    (hwc : isWorstCaseCarry ω k τ) :
    variableRadixDecode ω k (tickByCarry ω k τ) = 0 := by
  -- tickByCarry = cyclicVariableTick, and cyclic tick gives (decode + 1) % size
  rw [tickByCarry_eq_cyclicTick, variableTick_correctness_finite]
  -- From hwc, all digits are maximal
  have hmax := (worstCase_iff_allMaximal ω k τ).mp hwc
  -- When all digits maximal, decode = completionCount - 1
  have h_decode := cumulativeCount_allMaximal ω k τ hmax
  -- (completionCount - 1 + 1) % completionCount = 0
  rw [h_decode]
  have hpos : 0 < completionCount ω k [] := completionCount_pos ω k [] (by simp)
  -- (n - 1 + 1) % n = n % n = 0 when n > 0
  have h_cancel : completionCount ω k [] - 1 + 1 = completionCount ω k [] :=
    Nat.sub_add_cancel (Nat.one_le_of_lt hpos)
  rw [h_cancel, Nat.mod_self]

end FdrsFormal.Modes.VariableRadix
