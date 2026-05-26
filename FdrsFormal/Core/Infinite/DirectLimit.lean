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

# Direct-Limit Mixed-Radix Space

Defines eventually-zero digit sequences and proves order isomorphism with ℕ (Theorem 1).

References: fdrs.md, Phase 1 Fragment 1, Definitions 3.1-3.2, Theorem 1
-/

import FdrsFormal.Core.Finite

namespace FdrsFormal.Core.Infinite

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite

variable {b : RadixSeq}

/-! ## Definition 3: Direct-limit space (eventually-zero sequences) -/

structure DirectLimitSpace (b : RadixSeq) where
  digits : (i : ℕ) → Fin (b i)
  eventually_zero : ∃ K, ∀ i > K, digits i = ⟨0, b.pos i⟩

namespace DirectLimitSpace

def zero (b : RadixSeq) : DirectLimitSpace b where
  digits := fun i => ⟨0, b.pos i⟩
  eventually_zero := ⟨0, fun _ _ => rfl⟩

instance : Zero (DirectLimitSpace b) := ⟨zero b⟩

@[ext]
theorem ext {τ σ : DirectLimitSpace b} (h : ∀ i, τ.digits i = σ.digits i) : τ = σ := by
  cases τ; cases σ; simp only [mk.injEq]; funext i; exact h i

end DirectLimitSpace

/-! ## Completed mixed-radix space -/

/-- The completed digit space R̂ = ∏_{i=0}^∞ D_i -/
def CompletedSpace (b : RadixSeq) := (i : ℕ) → Fin (b i)

namespace CompletedSpace

instance : Inhabited (CompletedSpace b) := ⟨fun i => ⟨0, b.pos i⟩⟩

/-- Extract a finite prefix of length L -/
def take (x : CompletedSpace b) (L : ℕ) : (i : Fin L) → Fin (b i) :=
  fun i => x i

end CompletedSpace

/-! ## Definition 4: Unbounded decoding

**fdrs.md**: Definition 4 (unbounded decoding) [§3.2 · Phase 1, Fragment 1] (lines 77-84)
dec(d) = Σ d_i · B_i (finite sum for eventually-zero sequences). -/

noncomputable def decode (b : RadixSeq) (τ : DirectLimitSpace b) : ℕ :=
  let K := Classical.choose τ.eventually_zero
  ∑ i : Fin (K + 1), (τ.digits i : ℕ) * placeValue b i

/-! ## Encoding: Convert ℕ to eventually-zero sequences -/

-- Helper lemma: 2n ≤ 2^n for n ≥ 1
private theorem two_mul_le_two_pow : ∀ n : ℕ, n ≥ 1 → 2 * n ≤ 2 ^ n := by
  intro n hn
  match n with
  | 0 => omega  -- Contradicts n ≥ 1
  | 1 => norm_num
  | n + 2 =>
    -- For n ≥ 2, prove 2(n+2) ≤ 2^{n+2} = 4 · 2^n
    have ih : 2 * (n + 1) ≤ 2 ^ (n + 1) := two_mul_le_two_pow (n + 1) (by omega)
    calc 2 * (n + 2)
      _ = 2 * (n + 1) + 2 := by ring
      _ ≤ 2 ^ (n + 1) + 2 := Nat.add_le_add ih (by norm_num)
      _ ≤ 2 ^ (n + 1) + 2 ^ (n + 1) := by
        have : 2 ≤ 2 ^ (n + 1) := by omega
        omega
      _ = 2 * 2 ^ (n + 1) := by ring
      _ = 2 ^ (n + 2) := by
        have : 2 ^ (n + 2) = 2 ^ (n + 1) * 2 := pow_succ _ _
        rw [mul_comm] at this
        exact this.symm

-- Helper lemma: 2^n ≤ B_{n+1} since each b_i ≥ 2
private theorem two_pow_le_placeValue (n : ℕ) : 2 ^ n ≤ placeValue b (n + 1) := by
  induction n with
  | zero =>
    calc (1 : ℕ)
      _ ≤ 2 := by norm_num
      _ ≤ b 0 := b.ge_two 0
      _ = placeValue b 1 := by rw [placeValue.succ, placeValue.zero]; ring
  | succ k ih =>
    calc 2 ^ k.succ
      _ = 2 ^ k * 2 := by rw [pow_succ]
      _ ≤ 2 ^ k * b (k + 1) := Nat.mul_le_mul_left _ (b.ge_two (k + 1))
      _ ≤ placeValue b (k + 1) * b (k + 1) := Nat.mul_le_mul_right _ ih
      _ = placeValue b (k + 1 + 1) := (placeValue.succ (k + 1)).symm

noncomputable def findHorizon (b : RadixSeq) (n : ℕ) : ℕ :=
  if h_eq : n = 0 then 0
  else
    have hn_ne : n ≠ 0 := h_eq
    have h : ∃ K, n < placeValue b (K + 1) := by
      use n
      -- Prove n < B_{n+1} via n < 2n ≤ 2^n ≤ B_{n+1}
      have hn_pos : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr hn_ne
      calc n
        _ < n + 1 := Nat.lt_succ_self n
        _ ≤ 2 * n := by omega
        _ ≤ 2 ^ n := two_mul_le_two_pow n hn_pos
        _ ≤ placeValue b (n + 1) := two_pow_le_placeValue n
    Nat.find h

theorem findHorizon_bound (b : RadixSeq) (n : ℕ) : n < placeValue b (findHorizon b n + 1) := by
  unfold findHorizon
  split_ifs with hn
  · rw [hn]; exact Nat.pos_of_ne_zero (placeValue.ne_zero 1)
  · -- The existence proof was given to Nat.find, apply Nat.find_spec
    have h : ∃ K, n < placeValue b (K + 1) := by
      use n
      have hn_pos : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr hn
      calc n
        _ < n + 1 := Nat.lt_succ_self n
        _ ≤ 2 * n := by omega
        _ ≤ 2 ^ n := two_mul_le_two_pow n hn_pos
        _ ≤ placeValue b (n + 1) := two_pow_le_placeValue n
    exact Nat.find_spec h

noncomputable def encode (b : RadixSeq) (n : ℕ) : DirectLimitSpace b :=
  let K := findHorizon b n
  let h_spec := findHorizon_bound b n
  let finite_enc := encodeFinite b K ⟨n, h_spec⟩
  { digits := fun i => if h : i ≤ K then finite_enc ⟨i, Nat.lt_succ_of_le h⟩ else ⟨0, b.pos i⟩
    eventually_zero := ⟨K, fun i hi => by
      -- For i > K, the if-condition is false, so we get ⟨0, b.pos i⟩
      simp [dif_neg (Nat.not_le.mpr hi)]
    ⟩
  }

/-! ## Theorem 1: Order-theoretic isomorphism with ℕ

**fdrs.md**: Theorem 1 (order-theoretic isomorphism with ℕ) [§3.3 · Phase 1, Fragment 1] (lines 85-96)
dec is a bijection R^∞_fin ≅ ℕ, order-preserving and well-founded. -/

theorem decode_encode (n : ℕ) : decode b (encode b n) = n := by
  -- Strategy: encode n creates a sequence with encodeFinite digits up to K, then zeros
  -- decode sums all digits, but since only finitely many are nonzero, we get
  -- the same sum as decodeFinite, which by bijection equals n

  set K := findHorizon b n
  have h_bound := findHorizon_bound b n

  unfold decode encode
  simp only []

  -- Get the witness from eventually_zero
  set K' := Classical.choose (encode b n).eventually_zero

  -- Key insight: For any K' witnessing eventually_zero, the sum up to K'
  -- contains only the finite encoding terms (up to K) since higher terms are zero

  -- The digits are: encodeFinite values for i ≤ K, zero for i > K
  have digits_below_K : ∀ (i : ℕ) (hi : i ≤ K), ((encode b n).digits i : ℕ) =
      (encodeFinite b K ⟨n, h_bound⟩ ⟨i, Nat.lt_succ_of_le hi⟩ : ℕ) := by
    intro i hi
    simp [encode]
    rw [dif_pos hi]

  have digits_above_K : ∀ i > K, ((encode b n).digits i : ℕ) = 0 := by
    intro i hi
    simp [encode]
    rw [dif_neg (Nat.not_le.mpr hi)]

  -- Strategy: Compute the decode directly using the fact that
  -- digits beyond K are zero, so we can use K as the horizon instead of K'

  -- First, observe that the sum up to K' equals the sum up to max(K, K')
  -- since all terms beyond K are zero
  have sum_to_K : ∑ i : Fin (K + 1), ((encode b n).digits i : ℕ) * placeValue b i = n := by
    calc ∑ i : Fin (K + 1), ((encode b n).digits i : ℕ) * placeValue b i
      _ = ∑ i : Fin (K + 1), (encodeFinite b K ⟨n, h_bound⟩ i : ℕ) * placeValue b i := by
          apply Finset.sum_congr rfl
          intro i _
          congr 1
          exact digits_below_K i.val (Nat.le_of_lt_succ i.isLt)
      _ = decodeFinite b K (encodeFinite b K ⟨n, h_bound⟩) := rfl
      _ = n := decodeFinite_encodeFinite K ⟨n, h_bound⟩

  -- Now show that the sum up to K' also equals n
  -- Strategy: Show directly that the sum equals n by observing that
  -- terms beyond K are zero, so the sum is unchanged

  -- The key insight: all digits beyond K are 0, so the sum only depends on positions ≤ K
  -- Regardless of whether K' < K, K' = K, or K' > K, the sum equals n

  -- First, show that terms beyond K contribute zero
  have terms_beyond_K_zero : ∀ i : Fin (K' + 1), i.val > K →
      ((encode b n).digits i : ℕ) * placeValue b i = 0 := by
    intro i hi
    rw [digits_above_K i.val hi]
    simp

  -- The full sum equals the sum over elements with i.val ≤ K
  have sum_eq : ∑ i : Fin (K' + 1), ((encode b n).digits i : ℕ) * placeValue b i =
                ∑ i ∈ Finset.filter (fun i : Fin (K' + 1) => i.val ≤ K) Finset.univ,
                  ((encode b n).digits i : ℕ) * placeValue b i := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi_in_univ hi_not_in_filter
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hi_not_in_filter
    exact terms_beyond_K_zero i hi_not_in_filter

  -- K is the minimal horizon, so K ≤ K'
  have K_le_K' : K ≤ K' := by
    -- Proof: If K' < K, then all digits beyond K' are zero
    -- This would mean n < B_{K'+1}, contradicting minimality of K
    by_contra h_not
    push_neg at h_not
    have h_K'_lt_K : K' < K := h_not

    -- By Classical.choose_spec, all digits beyond K' are zero
    have h_K'_spec := Classical.choose_spec (encode b n).eventually_zero

    -- The sum up to K' equals n (since digits beyond K' are zero)
    have h_sum_K' : ∑ i : Fin (K' + 1), ((encode b n).digits i : ℕ) * placeValue b i = n := by
      -- We need to show this sum equals n
      -- We know sum up to K equals n (from sum_to_K)
      -- And digits from K'+1 to K are all zero (from h_K'_spec)
      -- So sum up to K = sum up to K'

      -- All digits beyond K' are zero by h_K'_spec
      have h_zero_beyond_K' : ∀ i : ℕ, K' < i → i ≤ K → ((encode b n).digits i : ℕ) = 0 := by
        intro i h_K'_i h_i_K
        have := h_K'_spec i h_K'_i
        simp [this]

      -- Since K' < K, we can extend the sum from K' to K, but all extra terms are zero
      have h_extend : ∑ i : Fin (K + 1), ((encode b n).digits i : ℕ) * placeValue b i =
                      ∑ i : Fin (K' + 1), ((encode b n).digits i : ℕ) * placeValue b i := by
        -- Split the sum at K'+1
        have h_split : ∑ i : Fin (K + 1), ((encode b n).digits i : ℕ) * placeValue b i =
                       (∑ i ∈ Finset.filter (fun (j : Fin (K + 1)) => j.val ≤ K') Finset.univ,
                         ((encode b n).digits i : ℕ) * placeValue b i) +
                       (∑ i ∈ Finset.filter (fun (j : Fin (K + 1)) => j.val > K') Finset.univ,
                         ((encode b n).digits i : ℕ) * placeValue b i) := by
          -- Split using filter + complement: rewrite to use sum_filter_add_sum_filter_not
          have h := Finset.sum_filter_add_sum_filter_not Finset.univ
                      (fun j : Fin (K + 1) => j.val ≤ K')
                      (fun i => ((encode b n).digits i : ℕ) * placeValue b i)
          rw [← h]
          -- The second filter has ¬(≤ K') which equals (> K')
          congr 1
          apply Finset.sum_congr
          · ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
          · intro _ _; rfl

        rw [h_split]
        -- The second sum is zero
        have h_high_zero : ∑ i ∈ Finset.filter (fun (j : Fin (K + 1)) => j.val > K') Finset.univ,
                             ((encode b n).digits i : ℕ) * placeValue b i = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          have : ((encode b n).digits i : ℕ) = 0 := h_zero_beyond_K' i.val hi (Nat.le_of_lt_succ i.isLt)
          simp [this]

        rw [h_high_zero, add_zero]
        -- The first sum equals sum over Fin (K'+1)
        -- Bijection: {i : Fin (K+1) | i.val ≤ K'} ≃ Fin (K'+1)
        -- Since K' < K, elements with val ≤ K' in Fin (K+1) correspond exactly to Fin (K'+1)
        symm
        -- j : Fin (K' + 1) means j.val < K' + 1 ≤ K < K + 1
        have h_bound_embed : ∀ j : Fin (K' + 1), j.val < K + 1 := fun j =>
          Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_succ (Nat.le_of_lt h_K'_lt_K))
        -- sum_bij signature: membership, injectivity, surjectivity, function values
        refine Finset.sum_bij (fun j _ => ⟨j.val, h_bound_embed j⟩) ?_ ?_ ?_ ?_
        · -- Forward map lands in filtered set
          intro j _
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact Nat.le_of_lt_succ j.isLt
        · -- Injectivity: h_eq : ⟨a₁.val, _⟩ = ⟨a₂.val, _⟩ in Fin (K+1)
          intro a₁ _ a₂ _ h_eq
          simp only at h_eq  -- beta-reduce the lambda
          -- h_eq : (⟨a₁.val, _⟩ : Fin (K+1)) = ⟨a₂.val, _⟩
          -- congrArg Fin.val h_eq : a₁.val = a₂.val
          exact Fin.ext (congrArg (fun x => x.val) h_eq)
        · -- Surjectivity: every element in filtered set has a preimage
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          exact ⟨⟨i.val, Nat.lt_succ_of_le hi⟩, Finset.mem_univ _, Fin.ext rfl⟩
        · -- Function values agree
          intro j _; rfl

      rw [← h_extend, sum_to_K]

    -- Therefore n < B_{K'+1}
    have h_n_bound_K' : n < placeValue b (K' + 1) := by
      calc n
        _ = ∑ i : Fin (K' + 1), ((encode b n).digits i : ℕ) * placeValue b i := h_sum_K'.symm
        _ ≤ ∑ i : Fin (K' + 1), (b i - 1) * placeValue b i := by
            apply Finset.sum_le_sum
            intro i _
            apply Nat.mul_le_mul_right
            exact Nat.le_sub_one_of_lt ((encode b n).digits i).isLt
        _ = placeValue b (K' + 1) - 1 := placeValue.sum_max_digits K'
        _ < placeValue b (K' + 1) := Nat.sub_lt (placeValue.pos (K' + 1)) Nat.one_pos

    -- But K is the minimal such value (by findHorizon definition)
    -- So K ≤ K', contradicting K' < K
    have h_K_min : K ≤ K' := by
      unfold K findHorizon
      split_ifs with h_zero
      · exact Nat.zero_le K'
      · exact Nat.find_min' _ h_n_bound_K'

    -- Contradiction
    omega

  -- Now show this filtered sum equals the sum up to K
  have filtered_eq_K : ∑ i ∈ Finset.filter (fun i : Fin (K' + 1) => i.val ≤ K) Finset.univ,
                         ((encode b n).digits i : ℕ) * placeValue b i =
                       ∑ i : Fin (K + 1), ((encode b n).digits i : ℕ) * placeValue b i := by
    -- The filtered set {i : Fin (K' + 1) | i.val ≤ K} corresponds exactly to Fin (K + 1)
    -- Since K_le_K', elements with val ≤ K in Fin (K'+1) bijectively correspond to Fin (K+1)
    symm
    -- j : Fin (K + 1) means j.val < K + 1 ≤ K' + 1 (since K ≤ K')
    have h_bound_embed : ∀ j : Fin (K + 1), j.val < K' + 1 := fun j =>
      Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_succ K_le_K')
    -- sum_bij signature: membership, injectivity, surjectivity, function values
    refine Finset.sum_bij (fun j _ => ⟨j.val, h_bound_embed j⟩) ?_ ?_ ?_ ?_
    · -- Forward map lands in filtered set
      intro j _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Nat.le_of_lt_succ j.isLt
    · -- Injectivity
      intro a₁ _ a₂ _ h_eq
      simp only at h_eq
      exact Fin.ext (congrArg (fun x => x.val) h_eq)
    · -- Surjectivity: every element in filtered set has a preimage
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact ⟨⟨i.val, Nat.lt_succ_of_le hi⟩, Finset.mem_univ _, Fin.ext rfl⟩
    · -- Function values agree
      intro j _; rfl

  -- Show the goal is the sum over Fin (K' + 1)
  show ∑ i : Fin (K' + 1), ((encode b n).digits i : ℕ) * placeValue b i = n
  rw [sum_eq, filtered_eq_K, sum_to_K]

theorem encode_decode (τ : DirectLimitSpace b) : encode b (decode b τ) = τ := by
  -- Strategy: Both encode (decode τ) and τ have the same digits
  -- They're eventually-zero sequences that decode to the same value
  -- So by uniqueness of representation (digits_unique), they must be equal

  ext i

  -- Get the horizon where τ becomes zero
  set K_τ := Classical.choose τ.eventually_zero
  have hK_τ := Classical.choose_spec τ.eventually_zero

  -- Get the horizon for encode (decode τ)
  set n := decode b τ
  set K_n := findHorizon b n
  have h_bound := findHorizon_bound b n

  -- The encoded value has horizon K_n
  set σ := encode b n

  -- We need to show τ.digits i = σ.digits i for all i

  -- Key insight: Both τ and σ decode to n, and both are eventually-zero
  -- So they represent the same natural number n
  -- By uniqueness in the finite case, they must have the same digits

  -- Case split on whether i is beyond the horizons
  by_cases hi_σ : i ≤ K_n
  · -- Case: i ≤ K_n, so σ.digits i comes from encodeFinite
    -- Strategy: Both τ and σ have the same digit at position i
    -- because they both decode to n, and n < B_{K_n+1}
    -- By digits_unique, sequences decoding to the same value have the same digits

    -- First, show τ.digits i = (encodeFinite b K_n ⟨n, h_bound⟩) ⟨i, ...⟩
    -- We know decode τ = n and n < B_{K_n+1}
    -- So τ restricted to K_n positions is a valid finite encoding of n

    have τ_decodes_to_n : decode b τ = n := rfl

    -- The key insight: use digits_unique to show that
    -- if two digit sequences decode to the same value in a finite space,
    -- they must be equal
    --
    -- Both τ (restricted) and encodeFinite ... n decode to n
    -- Therefore they have the same digits

    -- Strategy: Show τ.digits i = σ.digits i by using digits_unique
    -- Both decode to n in the finite space up to K_n

    -- First, unfold σ.digits i to get the encodeFinite expression
    have σ_digit_eq : σ.digits i = encodeFinite b K_n ⟨n, h_bound⟩ ⟨i, Nat.lt_succ_of_le hi_σ⟩ := by
      simp [σ, encode]
      rw [dif_pos hi_σ]

    -- Now show τ.digits i equals this encodeFinite digit
    -- Key: encodeFinite extracts digit via (n / B_i) % b_i
    -- We need to show τ.digits i also equals (n / B_i) % b_i

    -- Show τ.digits i = σ.digits i where σ = encode b n and n = decode b τ
    -- Strategy: Use the digit extraction formula

    rw [σ_digit_eq]

    -- Now we need to show: τ.digits i = encodeFinite b K_n ⟨n, h_bound⟩ ⟨i, Nat.lt_succ_of_le hi_σ⟩
    -- By encodeFinite definition: encodeFinite b K ⟨m, _⟩ ⟨j, _⟩ = ⟨(m / B_j) % b_j, _⟩
    -- So we need: τ.digits i = ⟨(n / B_i) % b_i, _⟩
    -- Which means: (τ.digits i : ℕ) = (n / B_i) % b_i

    -- Show the equality of values first, then apply Fin.ext
    have val_eq : (τ.digits i : ℕ) = (encodeFinite b K_n ⟨n, h_bound⟩ ⟨i, Nat.lt_succ_of_le hi_σ⟩ : ℕ) := by
      simp only [encodeFinite]

      -- Show: (τ.digits i : ℕ) = (n / placeValue b i) % b i
      -- We have n = decode b τ = ∑_{j ≤ K_τ} (τ.digits j : ℕ) * placeValue b j

      -- Unfold the decode to get the explicit sum
      unfold decode at τ_decodes_to_n

      -- Let K_τ be the horizon for τ
      set K_τ := Classical.choose τ.eventually_zero with hK_τ_def
      have hK_τ := Classical.choose_spec τ.eventually_zero

      -- Now n = ∑_{j ≤ K_τ} (τ.digits j : ℕ) * placeValue b j
      -- We want to extract the i-th digit from this sum

      -- We'll prove this using the extraction formula:
      -- For any sum S = ∑_j f_j * B_j, we have (S / B_i) % b_i = f_i
      -- This is the same principle used in digits_unique

      -- First, establish the relationship between i and K_τ
      -- Case 1: i ≤ K_τ - then i is in the sum
      -- Case 2: i > K_τ - then τ.digits i = 0 by eventually_zero

      by_cases h_i_tau : i ≤ K_τ
      · -- Case: i ≤ K_τ, so position i is included in the decode sum
        -- The extraction works directly

        -- The sum can be split: low terms (j < i) + middle (j = i) + high (j > i)
        -- After division by B_i and mod b_i, only the middle term survives

        -- We need to apply a similar argument to extract_from_sum from Bijection.lean
        -- Key fact: (∑_{j ≤ K_τ} (τ.digits j : ℕ) * B_j) / B_i % b_i = (τ.digits i : ℕ)

        -- This follows from the structure of mixed-radix representation:
        -- - Terms with j < i: sum < B_i, so contribute 0 to (sum / B_i)
        -- - Term j = i: contributes τ.digits i to (sum / B_i)
        -- - Terms j > i: B_j divisible by B_{i+1} = B_i * b_i, contribute multiples of b_i

        -- Replicate the extract_from_sum argument for this specific sum
        -- Split sum: S = low + mid + high where
        --   low = ∑_{j < i} ..., mid = (τ.digits i) * B_i, high = ∑_{j > i} ...

        set S := ∑ j : Fin (K_τ + 1), (τ.digits j : ℕ) * placeValue b j

        -- We need to show (S / B_i) % b_i = (τ.digits i : ℕ)
        -- This follows from the mixed-radix extraction property

        -- First, note that we can view τ restricted to Fin (K_τ + 1) as a finite encoding
        -- Create the finite digit function
        have i_in_range : i < K_τ + 1 := Nat.lt_succ_of_le h_i_tau
        set τ_fin : (j : Fin (K_τ + 1)) → Fin (b j) := fun j => τ.digits j

        -- The key insight: S is exactly decodeFinite applied to τ_fin
        have S_eq : S = decodeFinite b K_τ τ_fin := rfl

        -- Now we use the extraction property from the finite case
        -- encodeFinite extracts digit i as (S / B_i) % b_i
        -- Since encodeFinite and decodeFinite are inverses, we have:
        -- (encodeFinite b K_τ ⟨S, _⟩ ⟨i, i_in_range⟩ : ℕ) = (S / B_i) % b_i= (τ_fin ⟨i, i_in_range⟩ : ℕ)

        -- However, to apply digits_unique, we need S < B_{K_τ+1}
        have S_bound : S < placeValue b (K_τ + 1) := by
          calc S
            _ = ∑ j : Fin (K_τ + 1), (τ_fin j : ℕ) * placeValue b j := rfl
            _ ≤ ∑ j : Fin (K_τ + 1), (b j - 1) * placeValue b j := by
              apply Finset.sum_le_sum
              intro j _
              apply Nat.mul_le_mul_right
              exact Nat.le_sub_one_of_lt (τ_fin j).isLt
            _ = placeValue b (K_τ + 1) - 1 := placeValue.sum_max_digits K_τ
            _ < placeValue b (K_τ + 1) := Nat.sub_lt (placeValue.pos (K_τ + 1)) Nat.one_pos

        -- Apply encodeFinite_digit theorem: encodeFinite b K ⟨n, _⟩ ⟨j, _⟩ = ⟨(n / B_j) % b_j, _⟩
        have extract : (S / placeValue b i) % b i =
                       (encodeFinite b K_τ ⟨S, S_bound⟩ ⟨i, i_in_range⟩ : ℕ) := by
          simp [encodeFinite]

        -- Apply the key property: encodeFinite (decodeFinite τ_fin) = τ_fin
        -- This is proven by encodeFinite_decodeFinite
        -- Therefore digit i is extracted correctly

        -- The extraction works because:
        -- 1. S = decodeFinite b K_τ τ_fin (by definition)
        -- 2. encodeFinite b K_τ ⟨S, _⟩ = τ_fin (by encodeFinite_decodeFinite)
        -- 3. Therefore τ_fin i = encodeFinite b K_τ ⟨S, _⟩ i
        -- 4. Taking coercions: (τ_fin i : ℕ) = (S / B_i) % b_i (by extract lemma)

        -- Apply encodeFinite_decodeFinite to show τ_fin = encodeFinite (decodeFinite τ_fin)
        -- The key property: S = decodeFinite b K_τ τ_fin, so
        -- encodeFinite b K_τ ⟨S, _⟩ = encodeFinite b K_τ ⟨decodeFinite b K_τ τ_fin, _⟩ = τ_fin

        -- Apply encodeFinite_decodeFinite: encodeFinite (decodeFinite d) = d
        -- We have S = decodeFinite b K_τ τ_fin
        -- So encodeFinite b K_τ ⟨S, S_bound⟩ should equal τ_fin
        -- The issue is the Subtype proof inequality

        -- Apply encodeFinite_decodeFinite: S = decodeFinite b K_τ τ_fin by S_eq (rfl)
        have encode_decode_eq : encodeFinite b K_τ ⟨S, S_bound⟩ = τ_fin := by
          -- S_eq : S = decodeFinite b K_τ τ_fin (definitionally, via rfl)
          -- So ⟨S, S_bound⟩ has the same value as ⟨decodeFinite b K_τ τ_fin, _⟩
          convert encodeFinite_decodeFinite K_τ τ_fin using 2

        -- Extract component i and show it equals (n / B_i) % b_i
        have digit_eq : (τ.digits i : ℕ) = (n / placeValue b i) % b i := by
          have h1 : (τ.digits i : ℕ) = (τ_fin ⟨i, i_in_range⟩ : ℕ) := rfl
          have h2 : τ_fin ⟨i, i_in_range⟩ = encodeFinite b K_τ ⟨S, S_bound⟩ ⟨i, i_in_range⟩ := by
            rw [← encode_decode_eq]
          have h3 : (encodeFinite b K_τ ⟨S, S_bound⟩ ⟨i, i_in_range⟩ : ℕ) = (S / placeValue b i) % b i := by
            simp [encodeFinite]
          rw [h1, h2, h3]
          -- S = n by definition (decode b τ = n)
          rfl

        exact digit_eq

      · -- Case: i > K_τ, so τ.digits i = 0 by eventually_zero
        push_neg at h_i_tau
        have digit_zero : τ.digits i = ⟨0, b.pos i⟩ := hK_τ i h_i_tau

        -- Show (τ.digits i : ℕ) = 0
        have lhs_zero : (τ.digits i : ℕ) = 0 := by simp [digit_zero]

        -- Show (n / placeValue b i) % b i = 0
        -- Since n = decode b τ < B_{K_τ + 1} ≤ B_i (because i > K_τ)
        -- We have n < B_i, so n / B_i = 0, and thus (n / B_i) % b_i = 0

        have n_bound : n < placeValue b i := by
          calc n
            _ = ∑ j : Fin (K_τ + 1), (τ.digits j : ℕ) * placeValue b j := rfl
            _ ≤ ∑ j : Fin (K_τ + 1), (b j - 1) * placeValue b j := by
              -- Each digit is < b j, so ≤ b j - 1
              apply Finset.sum_le_sum
              intro j _
              apply Nat.mul_le_mul_right
              exact Nat.le_sub_one_of_lt (τ.digits j).isLt
            _ = placeValue b (K_τ + 1) - 1 := placeValue.sum_max_digits K_τ
            _ < placeValue b (K_τ + 1) := Nat.sub_lt (placeValue.pos (K_τ + 1)) Nat.one_pos
            _ ≤ placeValue b i := by
              have h_succ : K_τ + 1 ≤ i := Nat.succ_le_of_lt h_i_tau
              exact placeValue.mono h_succ

        have rhs_zero : (n / placeValue b i) % b i = 0 := by
          calc (n / placeValue b i) % b i
            _ = 0 % b i := by rw [Nat.div_eq_of_lt n_bound]
            _ = 0 := Nat.zero_mod _

        rw [lhs_zero, rhs_zero]

    -- val_eq gives us the equality of coercions to Nat
    exact val_eq.symm
  · -- Case: i > K_n
    -- σ.digits i = 0 by definition of encode
    have hσ_zero : σ.digits i = ⟨0, b.pos i⟩ := by
      simp only [σ, encode]
      exact dif_neg hi_σ

    -- We need to show τ.digits i = 0 too
    -- Strategy: If τ.digits i ≠ 0, then decode τ ≥ B_i > n, contradiction

    rw [hσ_zero]

    -- Show τ.digits i = ⟨0, b.pos i⟩
    -- Proof by contradiction: if τ.digits i ≠ 0, then
    -- the contribution from position i alone would be ≥ B_i > n

    push_neg at hi_σ  -- Now hi_σ : i > K_n (as ℕ)

    -- Key: placeValue is strictly increasing, so i > K_n implies B_i > B_{K_n+1}
    have hBi_large : placeValue b (K_n + 1) ≤ placeValue b i := by
      by_cases h_eq : i = K_n + 1
      · rw [h_eq]
      · apply Nat.le_of_lt
        apply placeValue.strictMono
        omega

    -- Proof: Show τ.digits i = ⟨0, b.pos i⟩ by proving (τ.digits i : ℕ) = 0
    -- Show (τ.digits i : ℕ) = 0 by contradiction
    have h_digit_zero : (τ.digits i : ℕ) = 0 := by
      -- Proof by contradiction: if (τ.digits i : ℕ) ≠ 0, then decode τ ≥ B_i > n
      by_contra h_nonzero

      -- Since τ.digits i : Fin (b i), we have (τ.digits i : ℕ) < b i
      -- If it's nonzero, then (τ.digits i : ℕ) ≥ 1
      have h_digit_ge_one : (τ.digits i : ℕ) ≥ 1 := by
        have : (τ.digits i : ℕ) < b i := (τ.digits i).isLt
        omega

      -- The decode of τ includes the contribution from position i
      -- decode τ = ∑_{j ≤ K_τ} (τ.digits j) * B_j
      -- This sum includes the term (τ.digits i) * B_i

      -- Key: decode τ ≥ (τ.digits i) * B_i ≥ 1 * B_i = B_i
      have decode_ge_Bi : decode b τ ≥ placeValue b i := by
        -- The decode includes all terms, including position i
        unfold decode
        set K_τ := Classical.choose τ.eventually_zero
        -- The sum includes term for index i (if i ≤ K_τ)
        -- Even if i > K_τ, we know τ.digits i ≠ 0, contradicting eventually_zero
        by_cases hi_tau : i ≤ K_τ
        · -- i ≤ K_τ: position i is included in the sum
          -- The sum is ≥ the term at position i
          -- Since all terms are non-negative, we can bound from below
          have i_in_range : i < K_τ + 1 := Nat.lt_succ_of_le hi_tau

          -- The sum includes at least the i-th term (all other terms are ≥ 0)
          have : (τ.digits i : ℕ) * placeValue b i ≤
                 ∑ j : Fin (K_τ + 1), (τ.digits j : ℕ) * placeValue b j := by
            -- Rewrite the sum to isolate the i-th term
            trans (∑ j ∈ ({⟨i, i_in_range⟩} : Finset (Fin (K_τ + 1))),
                    (τ.digits j : ℕ) * placeValue b j)
            · simp
            · apply Finset.sum_le_sum_of_subset_of_nonneg
              · simp [Finset.subset_univ]
              · intro j _ _
                apply Nat.zero_le

          calc ∑ j : Fin (K_τ + 1), (τ.digits j : ℕ) * placeValue b j
            _ ≥ (τ.digits i : ℕ) * placeValue b i := this
            _ ≥ 1 * placeValue b i := Nat.mul_le_mul_right _ h_digit_ge_one
            _ = placeValue b i := Nat.one_mul _
        · -- i > K_τ: but τ.digits i ≠ 0 contradicts eventually_zero
          push_neg at hi_tau
          have hK_τ := Classical.choose_spec τ.eventually_zero
          have : τ.digits i = ⟨0, b.pos i⟩ := hK_τ i hi_tau
          have : (τ.digits i : ℕ) = 0 := by simp [this]
          omega

      -- Now derive contradiction: n = decode τ ≥ B_i ≥ B_{K_n+1} > n
      have : n > n := calc n
        _ = decode b τ := rfl
        _ ≥ placeValue b i := decode_ge_Bi
        _ ≥ placeValue b (K_n + 1) := hBi_large
        _ > n := h_bound
      omega

    -- Use h_digit_zero to conclude τ.digits i = ⟨0, b.pos i⟩
    simp only [h_digit_zero]

theorem decode_injective : Function.Injective (decode b) := by
  intro τ σ h; rw [← encode_decode τ, ← encode_decode σ, h]

theorem decode_surjective : Function.Surjective (decode b) := by
  intro n; exact ⟨encode b n, decode_encode n⟩

noncomputable def decodeEquiv (b : RadixSeq) : DirectLimitSpace b ≃ ℕ where
  toFun := decode b
  invFun := encode b
  left_inv := encode_decode
  right_inv := decode_encode

instance : LE (DirectLimitSpace b) := ⟨fun τ σ => decode b τ ≤ decode b σ⟩
instance : LT (DirectLimitSpace b) := ⟨fun τ σ => decode b τ < decode b σ⟩

/-- **Theorem 1**: Order isomorphism with ℕ -/
noncomputable def decodeOrderIso (b : RadixSeq) : DirectLimitSpace b ≃o ℕ where
  toEquiv := decodeEquiv b
  map_rel_iff' := Iff.rfl

/-! ## Basic Properties -/

@[simp] theorem decode_zero : decode b (0 : DirectLimitSpace b) = 0 := by
  -- All digits of zero are ⟨0, b.pos i⟩, so the sum is 0
  unfold decode
  simp only
  -- The zero element has all digits = ⟨0, b.pos i⟩
  apply Finset.sum_eq_zero
  intro i _
  -- Show ((0 : DirectLimitSpace b).digits i : ℕ) * placeValue b i = 0
  have : ((0 : DirectLimitSpace b).digits i : ℕ) = 0 := rfl
  simp [this]

@[simp] theorem encode_zero : encode b 0 = 0 := by
  -- Show all digits are zero: (encode b 0).digits i = (0 : DirectLimitSpace b).digits i
  ext i
  simp only [encode]
  -- Case split on i ≤ findHorizon b 0
  split_ifs with h_le
  · -- i ≤ findHorizon b 0: Show encodeFinite b (findHorizon b 0) ⟨0, _⟩ i = ⟨0, b.pos i⟩
    -- encodeFinite n i = ⟨(n / B_i) % b_i, _⟩ = ⟨0, _⟩ when n = 0
    simp only [encodeFinite]
    -- Show 0 / placeValue b i % b i = 0, then rfl for Fin equality
    norm_num
    rfl
  · -- i > findHorizon b 0: By definition we get ⟨0, b.pos i⟩ = ⟨0, b.pos i⟩
    rfl

theorem findHorizon_spec (n : ℕ) : n < placeValue b (findHorizon b n + 1) :=
  findHorizon_bound b n

end FdrsFormal.Core.Infinite
