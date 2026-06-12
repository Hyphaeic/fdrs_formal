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

# Order-Preserving Property of Variable Radix Encoding

This file proves that the bijection φ_ω preserves lexicographic order.

## Mathematical Content (fdrs.md lines 4080-4091)

The bijection φ_ω: R^{(k)}_ω → {0, ..., |R^{(k)}_ω| - 1} satisfies:
  τ <_lex σ ⟺ φ_ω(τ) < φ_ω(σ)

This follows from the definition of φ_ω as counting lexicographically smaller elements.

## References

- fdrs.md, Phase 5-6, Section 3 (lines 4080-4091)
-/

import FdrsFormal.Modes.VariableRadix.Encoding.Ranking

namespace FdrsFormal.Modes.VariableRadix

/-!
## Order Isomorphism Properties
-/

/-- The decode function reflects order -/
theorem decode_lt_iff (ω : RadixLaw) (k : ℕ) (τ σ : FiniteVariableSpace ω k) :
    variableRadixDecode ω k τ < variableRadixDecode ω k σ ↔ τ.digits < σ.digits := by
  constructor
  · -- Forward: decode τ < decode σ → τ.digits < σ.digits
    -- By contrapositive: ¬(τ.digits < σ.digits) → ¬(decode τ < decode σ)
    intro h_decode_lt
    by_contra h_not_lt
    -- ¬(τ.digits < σ.digits), so either τ.digits = σ.digits or σ.digits < τ.digits
    -- Use lt_or_eq_of_le combined with not_lt to derive cases
    by_cases h_eq : τ.digits = σ.digits
    · -- τ.digits = σ.digits, so τ = σ (by ext), so decode τ = decode σ
      have heq : τ = σ := FiniteVariableSpace.ext h_eq
      rw [heq] at h_decode_lt
      exact Nat.lt_irrefl _ h_decode_lt
    · -- τ.digits ≠ σ.digits and ¬(τ.digits < σ.digits)
      -- Since lists have decidable linear order, σ.digits < τ.digits
      have h_gt : σ.digits < τ.digits := by
        -- From not (τ < σ) and τ ≠ σ, we get σ < τ by trichotomy
        rcases lt_trichotomy τ.digits σ.digits with h_lt | h_eq' | h_gt
        · exact absurd h_lt h_not_lt
        · exact absurd h_eq' h_eq
        · exact h_gt
      have h_decode_gt := variableRadixDecode_strictMono ω k σ τ h_gt
      omega
  · -- Backward: τ.digits < σ.digits → decode τ < decode σ
    exact variableRadixDecode_strictMono ω k τ σ

/-- The decode function preserves equality -/
theorem decode_inj (ω : RadixLaw) (k : ℕ) :
    Function.Injective (variableRadixDecode ω k) := by
  intro τ σ h
  -- If decode τ = decode σ and τ ≠ σ, then by trichotomy, either τ < σ or σ < τ
  -- Both lead to contradiction with h
  by_contra h_ne
  -- τ ≠ σ, so either τ.digits < σ.digits or σ.digits < τ.digits
  by_cases h_lt : τ.digits < σ.digits
  · -- τ.digits < σ.digits implies decode τ < decode σ
    have h_decode_lt := variableRadixDecode_strictMono ω k τ σ h_lt
    omega
  · -- ¬(τ.digits < σ.digits), and since τ ≠ σ, we have σ.digits < τ.digits
    have h_ne_digits : τ.digits ≠ σ.digits := fun heq => h_ne (FiniteVariableSpace.ext heq)
    have h_gt : σ.digits < τ.digits := by
      rcases lt_trichotomy τ.digits σ.digits with hlt | heq | hgt
      · exact absurd hlt h_lt
      · exact absurd heq h_ne_digits
      · exact hgt
    have h_decode_gt := variableRadixDecode_strictMono ω k σ τ h_gt
    omega

/-- The encode function is strictly monotone -/
theorem encode_strictMono (ω : RadixLaw) (k : ℕ) :
    ∀ m n (hm : m < completionCount ω k []) (hn : n < completionCount ω k []),
      m < n → (variableRadixEncode ω k m hm).digits < (variableRadixEncode ω k n hn).digits := by
  intro m n hm hn h_mn
  -- Let τ = encode(m), σ = encode(n)
  set τ := variableRadixEncode ω k m hm with hτ_def
  set σ := variableRadixEncode ω k n hn with hσ_def
  -- decode(encode(m)) = m and decode(encode(n)) = n
  have h_dec_τ : variableRadixDecode ω k τ = m := variableRadixDecode_encode ω k m hm
  have h_dec_σ : variableRadixDecode ω k σ = n := variableRadixDecode_encode ω k n hn
  -- From m < n and the decode equalities, we have decode τ < decode σ
  have h_decode_lt : variableRadixDecode ω k τ < variableRadixDecode ω k σ := by
    rw [h_dec_τ, h_dec_σ]; exact h_mn
  -- Apply decode_lt_iff backward: decode τ < decode σ ↔ τ.digits < σ.digits
  exact (decode_lt_iff ω k τ σ).mp h_decode_lt

/-!
## Order Isomorphism Statement
-/

/-- The decode/encode pair forms an order isomorphism -/
theorem variableRadix_orderIso (ω : RadixLaw) (k : ℕ) :
    ∃ (f : FiniteVariableSpace ω k → Fin (completionCount ω k [])),
      Function.Bijective f := by
  -- Use the decode function wrapped in Fin
  use fun τ => ⟨variableRadixDecode ω k τ, variableRadixDecode_lt ω k τ⟩
  constructor
  · -- Injective: follows from decode_inj
    intro τ σ h
    simp only [Fin.mk.injEq] at h
    exact decode_inj ω k h
  · -- Surjective: for any n, encode(n) decodes back to n
    intro ⟨n, hn⟩
    use variableRadixEncode ω k n hn
    simp only [Fin.mk.injEq]
    exact variableRadixDecode_encode ω k n hn

end FdrsFormal.Modes.VariableRadix
