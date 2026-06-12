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

# Odometer Decoding

This file defines odometer decoding for variable radix systems.

## Mathematical Content (fdrs.md lines 4733-4740)

**Definition 59 (Odometer decoding)**:
For τ = (d₀, ..., d_k) ∈ R^{(k)}_ω, define:

dec^{odo}_{ω,k}(τ) := Σ_{i=0}^{k} d_i · β_ω(τ_{<i})

This is the weighted positional sum where β_ω(τ_{<i}) is the place value at position i.

## References

- fdrs.md, Phase 5-6, Section 2 (lines 4733-4740)
-/

import FdrsFormal.Modes.VariableRadix.PrefixWeights.Definition

namespace FdrsFormal.Modes.VariableRadix

/-!
## Odometer Decoding
-/

/--
**Definition 59**: Odometer decoding.

dec^{odo}_{ω,k}(τ) = Σ_{i=0}^{k} d_i · β_ω(τ_{<i})

Each digit is weighted by the prefix weight up to that position.
-/
def odometerDecode (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k) : ℕ :=
  Finset.sum (Finset.univ : Finset (Fin (k + 1)))
    (fun i => τ.digitAt i * prefixWeight ω (τ.getPrefix i.val (by omega)))

/-!
## Place Value Properties
-/

/-- The place value at position i -/
def placeValue (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k) (i : Fin (k + 1)) : ℕ :=
  prefixWeight ω (τ.getPrefix i.val (by omega))

/-- Place values are positive -/
theorem placeValue_pos (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k)
    (i : Fin (k + 1)) :
    0 < placeValue ω k τ i := by
  simp only [placeValue]
  exact prefixWeight_pos ω _

/-- Place values are monotonically increasing -/
theorem placeValue_mono (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k)
    (i j : Fin (k + 1)) (h : i ≤ j) :
    placeValue ω k τ i ≤ placeValue ω k τ j := by
  simp only [placeValue]
  apply prefixWeight_mono
  simp only [FiniteVariableSpace.getPrefix]
  have hi : i.val ≤ j.val := h
  rw [List.take_isPrefix_take]
  left; exact hi

/-!
## Odometer Decomposition
-/

/-- Odometer decode decomposes into digit contributions -/
theorem odometerDecode_sum (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k) :
    odometerDecode ω k τ =
      Finset.sum (Finset.univ : Finset (Fin (k + 1)))
        (fun i => τ.digitAt i * placeValue ω k τ i) := by
  simp only [odometerDecode, placeValue]

/-- The contribution of digit i to the odometer value -/
def digitContribution (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k)
    (i : Fin (k + 1)) : ℕ :=
  τ.digitAt i * placeValue ω k τ i

/-- Helper: Taking i+1 elements equals taking i and appending the i-th element -/
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

/-- Helper: getPrefix (i+1) = getPrefix i ++ [digitAt i] -/
private theorem getPrefix_succ (τ : FiniteVariableSpace ω k) (i : Fin (k + 1)) (hi : i.val < k)
    (h_succ_le : i.val + 1 ≤ k + 1) :
    τ.getPrefix (i.val + 1) h_succ_le =
      τ.getPrefix i.val (Nat.le_of_lt i.isLt) ++ [τ.digitAt i] := by
  simp only [FiniteVariableSpace.getPrefix, FiniteVariableSpace.digitAt]
  have h_len : i.val < τ.digits.length := by rw [τ.length_eq]; exact i.isLt
  exact take_succ_eq τ.digits i.val h_len

/-- Digit contributions are bounded (when i+1 ≤ k) -/
theorem digitContribution_lt (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k)
    (i : Fin k) :
    digitContribution ω k τ ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ <
      placeValue ω k τ ⟨i.val + 1, by omega⟩ := by
  simp only [digitContribution, placeValue]
  let i' : Fin (k + 1) := ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
  let pfx_i := τ.getPrefix i.val (Nat.le_of_lt i'.isLt)
  have h_i_lt_k : i.val < k := i.isLt
  have h_succ_le : i.val + 1 ≤ k + 1 := by omega
  let pfx_i1 := τ.getPrefix (i.val + 1) h_succ_le
  have h_pfx_eq : pfx_i1 = pfx_i ++ [τ.digitAt i'] := getPrefix_succ τ i' h_i_lt_k h_succ_le
  have h_weight : prefixWeight ω pfx_i1 = prefixWeight ω pfx_i * ω.radix pfx_i := by
    rw [h_pfx_eq, prefixWeight_append]
  have h_digit_lt : τ.digitAt i' < ω.radix pfx_i := τ.digitAt_lt i'
  have h_pos : 0 < prefixWeight ω pfx_i := prefixWeight_pos ω pfx_i
  calc τ.digitAt i' * prefixWeight ω pfx_i
      < ω.radix pfx_i * prefixWeight ω pfx_i := Nat.mul_lt_mul_of_pos_right h_digit_lt h_pos
    _ = prefixWeight ω pfx_i * ω.radix pfx_i := Nat.mul_comm _ _
    _ = prefixWeight ω pfx_i1 := h_weight.symm

/-!
## Odometer Bounds and Injectivity
-/

/-- getPrefix (j+1) = getPrefix j ++ [digitAt j] for any j < k+1 -/
private theorem getPrefix_succ' {ω : RadixLaw} {k : ℕ} (τ : FiniteVariableSpace ω k)
    (j : ℕ) (hj : j < k + 1) :
    τ.getPrefix (j + 1) (by omega) = τ.getPrefix j (by omega) ++ [τ.digitAt ⟨j, hj⟩] := by
  simp only [FiniteVariableSpace.getPrefix, FiniteVariableSpace.digitAt]
  exact take_succ_eq τ.digits j (by rw [τ.length_eq]; omega)

/-- Prefix weight step: β(prefix_{j+1}) = β(prefix_j) * radix(prefix_j) -/
private theorem prefixWeight_getPrefix_step {ω : RadixLaw} {k : ℕ}
    (τ : FiniteVariableSpace ω k) (j : ℕ) (hj : j < k + 1) :
    prefixWeight ω (τ.getPrefix (j + 1) (by omega)) =
      prefixWeight ω (τ.getPrefix j (by omega)) * ω.radix (τ.getPrefix j (by omega)) := by
  rw [getPrefix_succ' τ j hj, prefixWeight_append]

/-- Prefix weight divisibility: β(prefix_i) ∣ β(prefix_j) for i ≤ j -/
private theorem prefixWeight_getPrefix_dvd {ω : RadixLaw} {k : ℕ}
    (τ : FiniteVariableSpace ω k) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ k + 1) :
    prefixWeight ω (τ.getPrefix i (by omega)) ∣ prefixWeight ω (τ.getPrefix j (by omega)) := by
  induction j with
  | zero => simp at hij; subst hij; exact dvd_refl _
  | succ m ih =>
    rcases Nat.eq_or_lt_of_le hij with h_eq | h_lt
    · subst h_eq; exact dvd_refl _
    · exact dvd_trans (ih (by omega) (by omega)) (by
        rw [prefixWeight_getPrefix_step τ m (by omega)]
        exact dvd_mul_right _ _)

/-- The odometer value as a function of prefix index, computed recursively.
partialOdo j = Σ_{i<j} d_i * β(prefix_i) -/
private noncomputable def partialOdo {ω : RadixLaw} {k : ℕ}
    (τ : FiniteVariableSpace ω k) : ℕ → ℕ
  | 0 => 0
  | j + 1 =>
    if h : j < k + 1 then
      partialOdo τ j + τ.digitAt ⟨j, h⟩ * prefixWeight ω (τ.getPrefix j (Nat.le_of_lt h))
    else
      partialOdo τ j

/-- Partial odometer sums are bounded by prefix weights -/
private theorem partialOdo_lt {ω : RadixLaw} {k : ℕ}
    (τ : FiniteVariableSpace ω k) (j : ℕ) (hj : j ≤ k + 1) :
    partialOdo τ j < prefixWeight ω (τ.getPrefix j (by omega)) := by
  induction j with
  | zero =>
    simp only [partialOdo, FiniteVariableSpace.getPrefix, List.take_zero]
    exact prefixWeight_pos ω _
  | succ n ih =>
    have hn_lt : n < k + 1 := by omega
    simp only [partialOdo, hn_lt, dite_true]
    rw [prefixWeight_getPrefix_step τ n hn_lt]
    have h_ih := ih (by omega)
    have h_digit := τ.digitAt_lt ⟨n, hn_lt⟩
    have h_pos := prefixWeight_pos ω (τ.getPrefix n (Nat.le_of_lt hn_lt))
    nlinarith

/-- partialOdo equals the Fin-based sum (odometerDecode) at k+1 -/
private theorem partialOdo_eq_odometerDecode {ω : RadixLaw} {k : ℕ}
    (τ : FiniteVariableSpace ω k) :
    partialOdo τ (k + 1) = odometerDecode ω k τ := by
  unfold odometerDecode
  -- We show by induction that partialOdo τ j = sum over {i | i.val < j}
  suffices h : ∀ j, j ≤ k + 1 →
    partialOdo τ j = (Finset.filter (fun i : Fin (k + 1) => i.val < j) Finset.univ).sum
      (fun i => τ.digitAt i * prefixWeight ω (τ.getPrefix i.val (Nat.le_of_lt i.isLt))) by
    have h1 := h (k + 1) le_rfl
    rw [h1]
    -- filter (· < k+1) univ = univ for Fin (k+1)
    have h_filter_eq : (Finset.filter (fun i : Fin (k + 1) => i.val < k + 1) Finset.univ) =
        Finset.univ := by
      ext i; constructor
      · intro _; exact Finset.mem_univ _
      · intro _; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact i.isLt
    rw [h_filter_eq]
  intro j hj
  induction j with
  | zero =>
    simp only [partialOdo]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    simp at hi
  | succ n ih =>
    have hn_le : n ≤ k + 1 := by omega
    have hn_lt : n < k + 1 := by omega
    simp only [partialOdo, hn_lt, dite_true]
    rw [ih hn_le]
    -- The filter for < n+1 equals filter for < n plus {n}
    have h_disj : Disjoint
        (Finset.filter (fun i : Fin (k + 1) => i.val < n) Finset.univ)
        ({⟨n, hn_lt⟩} : Finset (Fin (k + 1))) := by
      rw [Finset.disjoint_left]
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Finset.mem_singleton]
      intro heq
      rw [heq] at hi
      exact absurd hi (lt_irrefl _)
    have h_union : Finset.filter (fun i : Fin (k + 1) => i.val < n + 1) Finset.univ =
        Finset.filter (fun i : Fin (k + 1) => i.val < n) Finset.univ ∪ {⟨n, hn_lt⟩} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
                  Finset.mem_singleton]
      constructor
      · intro h
        rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp h) with heq | hlt
        · right; exact Fin.ext heq
        · left; exact hlt
      · rintro (h | h)
        · omega
        · rw [h]; exact Nat.lt_succ_of_le le_rfl
    rw [h_union, Finset.sum_union h_disj, Finset.sum_singleton]

/-- The full getPrefix equals digits -/
private theorem getPrefix_full {ω : RadixLaw} {k : ℕ} (τ : FiniteVariableSpace ω k) :
    τ.getPrefix (k + 1) (le_refl _) = τ.digits :=
  List.take_of_length_le (le_of_eq τ.length_eq)

/-- **Theorem**: The odometer value is strictly bounded by the prefix weight of the full path. -/
theorem odometerDecode_lt (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k) :
    odometerDecode ω k τ < prefixWeight ω τ.digits := by
  rw [← partialOdo_eq_odometerDecode, ← getPrefix_full]
  exact partialOdo_lt τ (k + 1) (le_refl _)

/-- Prefixes of the same length agree if the full prefixes agree -/
private theorem take_prefix_of_take_eq {l₁ l₂ : List α} {n : ℕ}
    (h : l₁.take n = l₂.take n) (i : ℕ) (hi : i ≤ n) :
    l₁.take i = l₂.take i := by
  have h1 : l₁.take i = (l₁.take n).take i := by
    rw [List.take_take]; congr 1; exact (Nat.min_eq_left hi).symm
  have h2 : l₂.take i = (l₂.take n).take i := by
    rw [List.take_take]; congr 1; exact (Nat.min_eq_left hi).symm
  rw [h1, h, ← h2]

/-- Elements at index i agree when takes agree and i < n -/
private theorem get_of_take_eq {l₁ l₂ : List α} {n : ℕ}
    (h : l₁.take n = l₂.take n) (i : ℕ) (hi : i < n)
    (hi₁ : i < l₁.length) (hi₂ : i < l₂.length) :
    l₁[i] = l₂[i] := by
  have h_take_i1 : (l₁.take n)[i]? = l₁[i]? := by
    simp [hi]
  have h_take_i2 : (l₂.take n)[i]? = l₂[i]? := by
    simp [hi]
  have : l₁[i]? = l₂[i]? := by rw [← h_take_i1, h, h_take_i2]
  simp [hi₁, hi₂] at this
  exact this

/-- partialOdo mod β_{n+1} equals partialOdo(n+1) -/
private theorem partialOdo_mod {ω : RadixLaw} {k : ℕ}
    (τ : FiniteVariableSpace ω k) (n : ℕ) (hn : n < k + 1) :
    partialOdo τ (k + 1) %
      (prefixWeight ω (τ.getPrefix n (by omega)) * ω.radix (τ.getPrefix n (by omega))) =
    partialOdo τ (n + 1) := by
  -- partialOdo(k+1) = partialOdo(n+1) + tail, where β_{n+1} | tail
  suffices h_decomp : ∃ q, partialOdo τ (k + 1) = partialOdo τ (n + 1) +
      q * (prefixWeight ω (τ.getPrefix n (by omega)) * ω.radix (τ.getPrefix n (by omega))) by
    obtain ⟨q, hq⟩ := h_decomp
    rw [hq]
    set m := prefixWeight ω (τ.getPrefix n (by omega)) * ω.radix (τ.getPrefix n (by omega))
    rw [Nat.add_mul_mod_self_right]
    have h_lt := partialOdo_lt τ (n + 1) (by omega)
    rw [prefixWeight_getPrefix_step τ n hn] at h_lt
    exact Nat.mod_eq_of_lt h_lt
  -- Build the decomposition by induction from n+1 to k+1
  suffices h : ∀ m, n + 1 ≤ m → m ≤ k + 1 → ∃ q, partialOdo τ m = partialOdo τ (n + 1) +
      q * (prefixWeight ω (τ.getPrefix n (by omega)) * ω.radix (τ.getPrefix n (by omega))) by
    exact h (k + 1) (by omega) (le_refl _)
  intro m hm_lo hm_hi
  induction m with
  | zero => omega
  | succ p ih =>
    rcases Nat.eq_or_lt_of_le hm_lo with h_eq | h_lt
    · -- p + 1 = n + 1, so m = n + 1
      have hp_eq : p = n := by omega
      subst hp_eq
      use 0; simp
    · -- p + 1 > n + 1, so p ≥ n + 1
      have hp_lo : n + 1 ≤ p := by omega
      have hp_hi : p ≤ k + 1 := by omega
      have hp_lt : p < k + 1 := by omega
      obtain ⟨q', hq'⟩ := ih hp_lo hp_hi
      -- partialOdo (p+1) = partialOdo p + d_p * β_p (since p < k+1)
      have h_unfold : partialOdo τ (p + 1) =
          partialOdo τ p + τ.digitAt ⟨p, hp_lt⟩ * prefixWeight ω (τ.getPrefix p (Nat.le_of_lt hp_lt)) := by
        simp [partialOdo, hp_lt]
      rw [h_unfold, hq']
      -- Need: d_p * β(prefix_p) is divisible by β_{n+1}
      have h_dvd : (prefixWeight ω (τ.getPrefix n (by omega)) *
          ω.radix (τ.getPrefix n (by omega))) ∣
          (τ.digitAt ⟨p, hp_lt⟩ * prefixWeight ω (τ.getPrefix p (Nat.le_of_lt hp_lt))) := by
        apply dvd_mul_of_dvd_right
        rw [← prefixWeight_getPrefix_step τ n hn]
        exact prefixWeight_getPrefix_dvd τ (n + 1) p (by omega) (by omega)
      obtain ⟨c, hc⟩ := h_dvd
      use q' + c
      rw [hc]; ring

/-- partialOdo agrees when digits agree on a prefix -/
private theorem partialOdo_eq_of_prefix_eq {ω : RadixLaw} {k : ℕ}
    (τ σ : FiniteVariableSpace ω k) (n : ℕ) (hn : n ≤ k + 1)
    (h_pfx : τ.getPrefix n (by omega) = σ.getPrefix n (by omega)) :
    partialOdo τ n = partialOdo σ n := by
  induction n with
  | zero => simp [partialOdo]
  | succ m ih =>
    have hm_lt : m < k + 1 := by omega
    simp only [partialOdo, hm_lt, dite_true]
    -- Prefix m agrees
    have h_pm : τ.getPrefix m (by omega) = σ.getPrefix m (by omega) := by
      simp only [FiniteVariableSpace.getPrefix] at h_pfx ⊢
      exact take_prefix_of_take_eq h_pfx m (by omega)
    -- Digit m agrees
    have h_dm : τ.digitAt ⟨m, hm_lt⟩ = σ.digitAt ⟨m, hm_lt⟩ := by
      simp only [FiniteVariableSpace.digitAt] at h_pfx ⊢
      simp only [FiniteVariableSpace.getPrefix] at h_pfx
      exact get_of_take_eq h_pfx m (by omega)
        (by rw [τ.length_eq]; omega) (by rw [σ.length_eq]; omega)
    rw [ih (by omega) h_pm, h_dm, h_pm]

/-- **Theorem**: The odometer decode is injective.

Proof by left-to-right digit recovery using modular arithmetic:
partialOdo(k+1) mod β_{n+1} = partialOdo(n+1), which determines digit n. -/
theorem odometerDecode_injective (ω : RadixLaw) (k : ℕ) (τ σ : FiniteVariableSpace ω k)
    (heq : odometerDecode ω k τ = odometerDecode ω k σ) : τ = σ := by
  apply FiniteVariableSpace.ext
  -- Show digits agree by showing all prefixes agree (using List.take directly)
  suffices h : ∀ j, j ≤ k + 1 → τ.digits.take j = σ.digits.take j by
    have := h (k + 1) (le_refl _)
    rwa [List.take_of_length_le (le_of_eq τ.length_eq),
         List.take_of_length_le (le_of_eq σ.length_eq)] at this
  intro j hj
  induction j with
  | zero => simp
  | succ n ih =>
    have hn_lt : n < k + 1 := by omega
    have h_pfx_eq : τ.getPrefix n (by omega) = σ.getPrefix n (by omega) := by
      simp only [FiniteVariableSpace.getPrefix]
      exact ih (by omega)
    -- Show digitAt n agrees using the mod argument
    have h_digit_eq : τ.digitAt ⟨n, hn_lt⟩ = σ.digitAt ⟨n, hn_lt⟩ := by
      -- partialOdo(k+1) mod β_{n+1} = partialOdo(n+1) for both τ and σ
      have h_mod_τ := partialOdo_mod τ n hn_lt
      have h_mod_σ := partialOdo_mod σ n hn_lt
      -- Rewrite using odometerDecode
      rw [partialOdo_eq_odometerDecode] at h_mod_τ h_mod_σ
      -- σ's modulus equals τ's (prefix n agrees)
      have h_mod_base : prefixWeight ω (σ.getPrefix n (by omega)) *
          ω.radix (σ.getPrefix n (by omega)) =
        prefixWeight ω (τ.getPrefix n (by omega)) *
          ω.radix (τ.getPrefix n (by omega)) := by rw [h_pfx_eq]
      rw [h_mod_base] at h_mod_σ
      -- From heq: the mod values are equal
      rw [heq] at h_mod_τ
      -- So partialOdo_τ(n+1) = partialOdo_σ(n+1)
      have h_po_eq : partialOdo τ (n + 1) = partialOdo σ (n + 1) :=
        h_mod_τ.symm.trans h_mod_σ
      -- Expand partialOdo(n+1)
      simp only [partialOdo, hn_lt, dite_true] at h_po_eq
      -- Since first n digits agree, partialOdo_τ(n) = partialOdo_σ(n)
      have h_po_n_eq : partialOdo τ n = partialOdo σ n :=
        partialOdo_eq_of_prefix_eq τ σ n (by omega) h_pfx_eq
      -- And β_τ(n) = β_σ(n) (prefix n agrees)
      rw [h_po_n_eq, h_pfx_eq] at h_po_eq
      -- d_τ * β = d_σ * β, cancel β > 0
      have h_cancel : τ.digitAt ⟨n, hn_lt⟩ * prefixWeight ω (σ.getPrefix n (by omega)) =
             σ.digitAt ⟨n, hn_lt⟩ * prefixWeight ω (σ.getPrefix n (by omega)) := by omega
      exact Nat.eq_of_mul_eq_mul_right (prefixWeight_pos ω (σ.getPrefix n (by omega))) h_cancel
    -- Combine: getPrefix (n+1) = getPrefix n ++ [digitAt n]
    -- We need τ.digits.take (n+1) = σ.digits.take (n+1)
    simp only [FiniteVariableSpace.getPrefix] at h_pfx_eq
    have h_len_τ : n < τ.digits.length := by rw [τ.length_eq]; omega
    have h_len_σ : n < σ.digits.length := by rw [σ.length_eq]; omega
    rw [take_succ_eq τ.digits n h_len_τ, take_succ_eq σ.digits n h_len_σ]
    simp only [FiniteVariableSpace.digitAt] at h_digit_eq
    rw [h_pfx_eq, h_digit_eq]

end FdrsFormal.Modes.VariableRadix
