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

# Prefix Projections and Residue Maps

This file defines prefix projections and residue maps, establishing the
fundamental equivalence between prefix constraints and congruence conditions.

## References

- fdrs.md, Phase 1 Fragment 2, Section 1 (lines 273-299)
- Definition 10: Prefix projection π_L
- Definition 11: Prefix residue map r_L
- Proposition 6: Prefix–congruence equivalence

## Status

COMPLETE - All proofs verified
-/

import FdrsFormal.Core.Infinite

namespace FdrsFormal.Topology.PrefixCongruence

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite FdrsFormal.Core.Infinite

/-!
## Projections, Residues, and Prefix-Congruence Equivalence

This section establishes the fundamental equivalence between prefix constraints
and congruence conditions modulo place values.
-/

/-! ### Helper lemmas for prefix-congruence proofs -/

/-- A sum of terms that are each divisible by m is itself divisible by m -/
theorem sum_dvd_of_forall_dvd {α : Type*} {s : Finset α} {f : α → ℕ} {m : ℕ}
    (h : ∀ x ∈ s, m ∣ f x) : m ∣ ∑ x ∈ s, f x := by
  apply Finset.dvd_sum
  exact h

/-- For indices i ≥ L, the term (digit * B_i) is divisible by B_L -/
theorem term_dvd_placeValue_of_ge (b : RadixSeq) (L : ℕ) (i : ℕ) (d : ℕ) (hi : L ≤ i) :
    placeValue b L ∣ d * placeValue b i := by
  have h : placeValue b L ∣ placeValue b i := placeValue.dvd_of_le (b := b) hi
  exact Dvd.dvd.mul_left h d

/-- The prefix sum for any digit function is less than B_L -/
theorem prefix_sum_lt_placeValue (b : RadixSeq) (L : ℕ) (f : (i : Fin L) → Fin (b i)) :
    ∑ i : Fin L, (f i : ℕ) * placeValue b i < placeValue b L := by
  cases L with
  | zero => simp [placeValue.zero]
  | succ L' => exact placeValue.sum_digits_lt L' f

/-- The decode sum can be computed modulo B_L by considering only terms with index < L.
    Terms with index ≥ L are divisible by B_L and vanish in the modular computation. -/
theorem decode_mod_eq_prefix_mod (b : RadixSeq) (τ : DirectLimitSpace b) (L : ℕ) :
    decode b τ % placeValue b L = (∑ i : Fin L, (τ.digits i : ℕ) * placeValue b i) % placeValue b L := by
  unfold decode
  set K := Classical.choose τ.eventually_zero with hK_def
  have hK_spec := Classical.choose_spec τ.eventually_zero

  -- Case 1: L = 0. Both sides are 0 mod 1 = 0.
  cases L with
  | zero =>
    simp only [placeValue.zero, Nat.mod_one]
  | succ L' =>
    -- Case 2: L = L' + 1 > 0
    -- For high terms in decode sum (i : Fin(K+1) with i.val ≥ L):
    have high_terms_dvd : ∀ i : Fin (K + 1), (L' + 1) ≤ i.val →
        placeValue b (L' + 1) ∣ (τ.digits i : ℕ) * placeValue b i := by
      intro i hi
      exact term_dvd_placeValue_of_ge b (L' + 1) i (τ.digits i : ℕ) hi

    -- Split the decode sum at L using Finset.filter
    conv_lhs =>
      rw [show ∑ i : Fin (K + 1), (τ.digits i : ℕ) * placeValue b i =
          (∑ i ∈ Finset.filter (fun i : Fin (K + 1) => i.val < L' + 1) Finset.univ,
              (τ.digits i : ℕ) * placeValue b i) +
          (∑ i ∈ Finset.filter (fun i : Fin (K + 1) => ¬ i.val < L' + 1) Finset.univ,
              (τ.digits i : ℕ) * placeValue b i) by
        exact (Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun i : Fin (K+1) => i.val < L' + 1) _).symm]

    -- The high sum is divisible by B_L
    have high_sum_dvd : placeValue b (L' + 1) ∣
        ∑ i ∈ Finset.filter (fun i : Fin (K + 1) => ¬ i.val < L' + 1) Finset.univ,
            (τ.digits i : ℕ) * placeValue b i := by
      apply sum_dvd_of_forall_dvd
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
      exact high_terms_dvd i hi

    -- Use (a + b) % n = a % n when n | b
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd high_sum_dvd, Nat.add_zero, Nat.mod_mod]

    -- Now we need: filtered sum over Fin(K+1) = sum over Fin L
    congr 1

    by_cases hKL : K + 1 ≤ L' + 1
    · -- Case: K + 1 ≤ L
      have filter_eq : Finset.filter (fun i : Fin (K + 1) => i.val < L' + 1) Finset.univ = Finset.univ := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        exact Nat.lt_of_lt_of_le i.isLt hKL

      rw [filter_eq]

      -- Split Fin L sum into [0, K] and [K+1, L-1] (the latter has zero terms)
      have split_L : ∑ i : Fin (L' + 1), (τ.digits i : ℕ) * placeValue b i =
          (∑ i ∈ Finset.filter (fun i : Fin (L' + 1) => i.val < K + 1) Finset.univ,
              (τ.digits i : ℕ) * placeValue b i) +
          (∑ i ∈ Finset.filter (fun i : Fin (L' + 1) => ¬ i.val < K + 1) Finset.univ,
              (τ.digits i : ℕ) * placeValue b i) := by
        exact (Finset.sum_filter_add_sum_filter_not Finset.univ _ _).symm

      -- High part of L sum is 0 (τ is eventually zero past K)
      have high_L_zero : ∑ i ∈ Finset.filter (fun i : Fin (L' + 1) => ¬ i.val < K + 1) Finset.univ,
          (τ.digits i : ℕ) * placeValue b i = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
        have h_zero := hK_spec i.val (Nat.lt_of_succ_le hi)
        simp [h_zero]

      rw [split_L, high_L_zero, add_zero]

      -- Now show the two sums are equal via bijection
      refine Finset.sum_bij' (fun (i : Fin (K + 1)) _ => ⟨i.val, Nat.lt_of_lt_of_le i.isLt hKL⟩)
                             (fun (i : Fin (L' + 1)) (hi : i ∈ _) => ⟨i.val, by
                               simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
                               exact hi⟩) ?_ ?_ ?_ ?_ ?_
      · intro i _; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact i.isLt
      · intro i _; simp only [Finset.mem_univ]
      · intro i _; rfl
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        rfl
      · intro i _; rfl

    · -- Case: K + 1 > L, so filter restricts to {0, ..., L-1}
      push_neg at hKL
      -- The filter set corresponds exactly to Fin L
      symm
      refine Finset.sum_bij' (fun (i : Fin (L' + 1)) _ => ⟨i.val, Nat.lt_trans i.isLt hKL⟩)
                             (fun (i : Fin (K + 1)) (hi : i ∈ _) => ⟨i.val, by
                               simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
                               exact hi⟩) ?_ ?_ ?_ ?_ ?_
      · intro i _; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact i.isLt
      · intro i _; simp only [Finset.mem_univ]
      · intro i _; rfl
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        rfl
      · intro i _; rfl

/-- Prefix projection π_L: extract first L digits -/
def prefixProjection (b : RadixSeq) (L : ℕ) :
    DirectLimitSpace b → (i : Fin L) → Digit b i :=
  fun τ i => τ.digits i

notation "π_" L => prefixProjection _ L

/-- Prefix residue map r_L: decode a finite prefix -/
def prefixResidue (b : RadixSeq) (L : ℕ)
    (s : (i : Fin L) → Digit b i) : ℕ :=
  ∑ i : Fin L, (s i : ℕ) * placeValue b i

notation "r_" L => prefixResidue _ L

/--
**Proposition 6**: Prefix–congruence equivalence

For τ ∈ ℛ and s ∈ ∏_{i<L} D_i,
  π_L(τ) = s ⟺ dec(τ) ≡ r_L(s) (mod B_L)

This is the same as Topology.Ultrametric.cylinder_iff_congruence, proven here in terms of
the prefixProjection and prefixResidue abstractions.
-/
theorem prefix_congruence_equiv (b : RadixSeq) (L : ℕ)
    (τ : DirectLimitSpace b) (s : (i : Fin L) → Digit b i) :
    prefixProjection b L τ = s ↔
    decode b τ % placeValue b L = prefixResidue b L s % placeValue b L := by
  unfold prefixProjection prefixResidue
  constructor
  · -- Forward: π_L(τ) = s ⟹ dec(τ) ≡ r_L(s) (mod B_L)
    intro h
    -- h : (fun i => τ.digits i) = s (function equality)
    -- Extract pointwise equality
    have h_digits : ∀ i : Fin L, τ.digits i = s i := fun i => congrFun h i

    -- Use the helper lemma: decode ≡ prefix_sum (mod B_L)
    rw [decode_mod_eq_prefix_mod]

    -- Now show prefix sums are equal
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    -- Use h_digits to substitute τ.digits i with s i
    rw [h_digits i]

  · -- Backward: dec(τ) ≡ r_L(s) (mod B_L) ⟹ π_L(τ) = s
    intro h
    -- h : decode τ % B_L = (∑ i<L, s_i * B_i) % B_L
    -- Need to show: (fun i => τ.digits i) = s

    -- Strategy: Both prefix sums < B_L, so congruence → equality → digits_unique

    -- The prefix sum of τ's digits is < B_L
    have τ_prefix_sum_lt : ∑ i : Fin L, (τ.digits i : ℕ) * placeValue b i < placeValue b L :=
      prefix_sum_lt_placeValue b L (fun i => τ.digits i)

    -- The sum of s's digits is < B_L
    have s_sum_lt : ∑ i : Fin L, (s i : ℕ) * placeValue b i < placeValue b L :=
      prefix_sum_lt_placeValue b L s

    -- Both sums are < B_L, so their mods equal themselves
    have τ_prefix_mod : (∑ i : Fin L, (τ.digits i : ℕ) * placeValue b i) % placeValue b L =
        ∑ i : Fin L, (τ.digits i : ℕ) * placeValue b i :=
      Nat.mod_eq_of_lt τ_prefix_sum_lt

    have s_mod : (∑ i : Fin L, (s i : ℕ) * placeValue b i) % placeValue b L =
        ∑ i : Fin L, (s i : ℕ) * placeValue b i :=
      Nat.mod_eq_of_lt s_sum_lt

    -- Use decode_mod_eq_prefix_mod to relate decode to prefix sum
    have h' := h
    rw [decode_mod_eq_prefix_mod] at h'

    -- Now h' says the two prefix sums have the same remainder mod B_L
    -- Since both are < B_L, they must be equal
    have sums_eq : ∑ i : Fin L, (τ.digits i : ℕ) * placeValue b i =
        ∑ i : Fin L, (s i : ℕ) * placeValue b i := by
      rw [← τ_prefix_mod, ← s_mod, h']

    -- Apply digits_unique
    -- For L = 0, there are no digits to compare
    cases L with
    | zero =>
      funext i
      exact i.elim0
    | succ L' =>
      -- Use digits_unique for Fin (L' + 1)
      exact digits_unique (fun i => τ.digits i) s sums_eq

end FdrsFormal.Topology.PrefixCongruence
