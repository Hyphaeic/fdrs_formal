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

# Variable Tick Correctness

This file proves that variable Tick equals +1 in rank.

## Mathematical Content (fdrs.md lines 4136-4146)

**Theorem 31 (Tick = +1 in rank)**:
For all τ ∈ R^{(k)}_ω (not at maximum):
  dec(T(τ)) = dec(τ) + 1

This is the fundamental correctness theorem for variable radix Tick.

## References

- fdrs.md, Phase 5-6, Section 4 (lines 4136-4146)
-/

import FdrsFormal.Modes.VariableRadix.VariableTick.Definition

namespace FdrsFormal.Modes.VariableRadix

/-!
## Tick Correctness (Finite Case)
-/

/--
**Theorem 31**: Variable Tick increments the rank by 1 (mod space size).

dec(T^{(k)}_ω(τ)) = (dec(τ) + 1) mod |R^{(k)}_ω|
-/
theorem variableTick_correctness_finite (ω : RadixLaw) (k : ℕ)
    (τ : FiniteVariableSpace ω k) :
    variableRadixDecode ω k (cyclicVariableTick ω k τ) =
      (variableRadixDecode ω k τ + 1) % completionCount ω k [] :=
  cyclicVariableTick_decode ω k τ

/-- Non-cyclic version: when not at max, Tick increments rank by 1 -/
theorem variableTick_correctness_noncyclic (ω : RadixLaw) (k : ℕ)
    (τ : FiniteVariableSpace ω k)
    (hnotmax : variableRadixDecode ω k τ < completionCount ω k [] - 1) :
    variableRadixDecode ω k (cyclicVariableTick ω k τ) =
      variableRadixDecode ω k τ + 1 := by
  rw [variableTick_correctness_finite]
  -- Need: (decode τ + 1) % size = decode τ + 1 when decode τ < size - 1
  have h_lt_size : variableRadixDecode ω k τ + 1 < completionCount ω k [] := by omega
  exact Nat.mod_eq_of_lt h_lt_size

/-!
## Tick Correctness (Infinite Case)

The infinite Tick (carry-based) preserves the prefix, increments the carry
digit, and resets the suffix to zeros.
-/

/-- Prefix before carry index is unchanged by infinite Tick. -/
theorem variableTick_preserves_prefix (ω : RadixLaw) (τ : InfiniteVariableSpace ω)
    (hev : IsEventuallyMaximal ω τ) (hnotmax : ¬IsMaximalPath ω τ)
    (i : ℕ) (hi : i < carryIndexInfinite ω τ hev hnotmax) :
    (variableTick ω τ hev hnotmax).digit i = τ.digit i := by
  simp only [variableTick, hi, ite_true]

/-- The carry digit is incremented by 1 by infinite Tick. -/
theorem variableTick_increments (ω : RadixLaw) (τ : InfiniteVariableSpace ω)
    (hev : IsEventuallyMaximal ω τ) (hnotmax : ¬IsMaximalPath ω τ) :
    (variableTick ω τ hev hnotmax).digit (carryIndexInfinite ω τ hev hnotmax) =
      τ.digit (carryIndexInfinite ω τ hev hnotmax) + 1 := by
  simp only [variableTick, lt_irrefl, ite_false, ite_true]

/-- Suffix after carry index is reset to zero by infinite Tick. -/
theorem variableTick_resets_suffix (ω : RadixLaw) (τ : InfiniteVariableSpace ω)
    (hev : IsEventuallyMaximal ω τ) (hnotmax : ¬IsMaximalPath ω τ)
    (i : ℕ) (hi : carryIndexInfinite ω τ hev hnotmax < i) :
    (variableTick ω τ hev hnotmax).digit i = 0 := by
  simp only [variableTick, show ¬(i < carryIndexInfinite ω τ hev hnotmax) from by omega,
    show ¬(i = carryIndexInfinite ω τ hev hnotmax) from by omega, ite_false]

/-!
## Tick Properties
-/

/-- Tick is injective -/
theorem variableTick_injective (ω : RadixLaw) (k : ℕ) :
    Function.Injective (cyclicVariableTick ω k) := by
  intro τ σ h
  have h1 := variableTick_correctness_finite ω k τ
  have h2 := variableTick_correctness_finite ω k σ
  have heq := congrArg (variableRadixDecode ω k) h
  rw [h1, h2] at heq
  -- heq: (decode τ + 1) % n = (decode σ + 1) % n
  -- Since decode is a bijection, τ = σ iff decode τ = decode σ
  have hτ_lt := variableRadixDecode_lt ω k τ
  have hσ_lt := variableRadixDecode_lt ω k σ
  -- From (a + 1) % n = (b + 1) % n where a, b < n:
  -- Case 1: a + 1 < n and b + 1 < n → a + 1 = b + 1 → a = b
  -- Case 2: a + 1 = n (i.e., a = n - 1) → (a + 1) % n = 0
  --         b + 1 = n (i.e., b = n - 1) → same
  -- Case 3: mixed - can't happen since 0 ≠ non-zero
  have h_decode_eq : variableRadixDecode ω k τ = variableRadixDecode ω k σ := by
    have hn := completionCount_pos ω k [] (Nat.zero_le _)
    -- From modular arithmetic: if (a + 1) % n = (b + 1) % n and a, b < n, then a = b
    -- The map x ↦ (x + 1) % n is a bijection on Fin n
    let f : Fin (completionCount ω k []) → Fin (completionCount ω k []) :=
      fun x => ⟨(x.val + 1) % completionCount ω k [], Nat.mod_lt _ hn⟩
    have h_inj : Function.Injective f := by
      intro ⟨a, ha⟩ ⟨b, hb⟩ hab
      simp only [f, Fin.mk.injEq] at hab ⊢
      -- (a + 1) % n = (b + 1) % n with a, b < n implies a = b
      by_cases ha' : a + 1 < completionCount ω k []
      · by_cases hb' : b + 1 < completionCount ω k []
        · rw [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at hab; omega
        · have hb_eq : b = completionCount ω k [] - 1 := by omega
          rw [Nat.mod_eq_of_lt ha', hb_eq, Nat.sub_add_cancel (Nat.one_le_of_lt hn), Nat.mod_self] at hab
          omega
      · have ha_eq : a = completionCount ω k [] - 1 := by omega
        by_cases hb' : b + 1 < completionCount ω k []
        · rw [ha_eq, Nat.sub_add_cancel (Nat.one_le_of_lt hn), Nat.mod_self, Nat.mod_eq_of_lt hb'] at hab
          omega
        · have hb_eq : b = completionCount ω k [] - 1 := by omega
          omega
    have h := @h_inj ⟨variableRadixDecode ω k τ, hτ_lt⟩ ⟨variableRadixDecode ω k σ, hσ_lt⟩
    simp only [f, Fin.mk.injEq] at h
    exact h heq
  exact decode_inj ω k h_decode_eq

/-- Tick is surjective (cyclic) -/
theorem cyclicVariableTick_surjective (ω : RadixLaw) (k : ℕ) :
    Function.Surjective (cyclicVariableTick ω k) := by
  intro σ
  -- For any σ, find τ such that tick(τ) = σ
  -- σ has decode value d. We want τ with decode (d - 1) mod n
  let n := completionCount ω k []
  let d := variableRadixDecode ω k σ
  have hn := completionCount_pos ω k [] (Nat.zero_le _)
  have hd : d < n := variableRadixDecode_lt ω k σ
  -- Preimage: (d + n - 1) % n
  let d' := (d + n - 1) % n
  have hd' : d' < n := Nat.mod_lt _ hn
  use variableRadixEncode ω k d' hd'
  -- Show: tick(encode(d')) = σ
  have h1 : variableRadixDecode ω k (cyclicVariableTick ω k (variableRadixEncode ω k d' hd')) =
      (variableRadixDecode ω k (variableRadixEncode ω k d' hd') + 1) % n :=
    variableTick_correctness_finite ω k _
  rw [variableRadixDecode_encode] at h1
  -- h1: decode(tick(encode(d'))) = (d' + 1) % n
  -- Show: (d' + 1) % n = d
  have h2 : (d' + 1) % n = d := by
    -- ((d + n - 1) % n + 1) % n = d when d < n
    -- Use: (a % n + b) % n = (a + b) % n
    have h_mod_add : ((d + n - 1) % n + 1) % n = (d + n - 1 + 1) % n := by
      conv_lhs => rw [Nat.add_mod, Nat.mod_mod]
      conv_rhs => rw [Nat.add_mod]
    have h_eq : d + n - 1 + 1 = d + n := by omega
    calc (d' + 1) % n
        = ((d + n - 1) % n + 1) % n := rfl
      _ = (d + n - 1 + 1) % n := h_mod_add
      _ = (d + n) % n := by rw [h_eq]
      _ = d % n := Nat.add_mod_right d n
      _ = d := Nat.mod_eq_of_lt hd
  rw [h2] at h1
  exact decode_inj ω k h1

/-- Tick is a bijection (cyclic case) -/
theorem cyclicVariableTick_bijective (ω : RadixLaw) (k : ℕ) :
    Function.Bijective (cyclicVariableTick ω k) :=
  ⟨variableTick_injective ω k, cyclicVariableTick_surjective ω k⟩

end FdrsFormal.Modes.VariableRadix
