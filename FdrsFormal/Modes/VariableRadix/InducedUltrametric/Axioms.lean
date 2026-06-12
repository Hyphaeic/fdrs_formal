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

# Ultrametric Axioms for Variable Radix

This file proves that δ_ω satisfies the ultrametric axioms.

## Mathematical Content (fdrs.md lines 4021-4033)

**Proposition 80 (ultrametric)**:
d is an ultrametric on R^{(∞)}_ω: for all τ, σ, η,
  d(τ,η) ≤ max{d(τ,σ), d(σ,η)}

**Proof**: Longest-common-prefix lengths satisfy
  ℓ(τ,η) ≥ min{ℓ(τ,σ), ℓ(σ,η)}
Exponentiating by ρ^{(·)} yields the ultrametric inequality.

## References

- fdrs.md, Phase 5-6, Section 2 (lines 4021-4033)
-/

import FdrsFormal.Modes.VariableRadix.InducedUltrametric.Definition
import Mathlib.Topology.MetricSpace.Ultra.Basic

namespace FdrsFormal.Modes.VariableRadix

open Classical

/-!
## LCP Length Properties
-/

/-- The first differing position of two unequal sequences -/
theorem lcpLength_spec {ω : RadixLaw} {τ σ : InfiniteVariableSpace ω} (hne : τ ≠ σ) :
    τ.digit (lcpLength τ σ) ≠ σ.digit (lcpLength τ σ) ∧
    ∀ i < lcpLength τ σ, τ.digit i = σ.digit i := by
  -- τ ≠ σ implies there exists a differing position
  have h : ∃ i, τ.digit i ≠ σ.digit i := by
    by_contra h
    push_neg at h
    apply hne
    ext i
    exact h i
  constructor
  · -- At lcpLength, digits differ
    simp only [lcpLength, dif_pos h]
    exact Nat.find_spec h
  · -- Below lcpLength, digits agree
    intro i hi
    exact digit_eq_of_lt_lcpLength τ σ i hi

-- lcpLength_comm is in Definition.lean

/--
LCP transitivity for distinct sequences.

Note: This version requires τ ≠ η because our lcpLength convention gives 0 for equal sequences.
The distance-level ultrametric inequality handles equality separately.
-/
theorem lcpLength_triangle' {ω : RadixLaw} (τ σ η : InfiniteVariableSpace ω)
    (hne : τ ≠ η) :
    min (lcpLength τ σ) (lcpLength σ η) ≤ lcpLength τ η := by
  -- τ ≠ η implies there exists a differing position
  have hτη : ∃ i, τ.digit i ≠ η.digit i := by
    by_contra h
    push_neg at h
    apply hne
    ext i
    exact h i
  simp only [lcpLength, dif_pos hτη]
  -- Prove by contradiction: if min < Nat.find hτη, we get a contradiction
  by_contra hlt
  push_neg at hlt
  -- hlt : Nat.find hτη < min (lcpLength τ σ) (lcpLength σ η)
  have h_lt_both : Nat.find hτη < min (lcpLength τ σ) (lcpLength σ η) := hlt
  have h_lt_τσ : Nat.find hτη < lcpLength τ σ := lt_of_lt_of_le h_lt_both (Nat.min_le_left _ _)
  have h_lt_ση : Nat.find hτη < lcpLength σ η := lt_of_lt_of_le h_lt_both (Nat.min_le_right _ _)
  -- By digit_eq_of_lt_lcpLength:
  have heq1 : τ.digit (Nat.find hτη) = σ.digit (Nat.find hτη) :=
    digit_eq_of_lt_lcpLength τ σ _ h_lt_τσ
  have heq2 : σ.digit (Nat.find hτη) = η.digit (Nat.find hτη) :=
    digit_eq_of_lt_lcpLength σ η _ h_lt_ση
  -- So τ.digit ... = η.digit ...
  have heq : τ.digit (Nat.find hτη) = η.digit (Nat.find hτη) := heq1.trans heq2
  -- But Nat.find_spec says they differ
  exact (Nat.find_spec hτη) heq

/-!
## Ultrametric Properties (Simple ρ-metric)
-/

theorem prefixDist_self {ρ : ℝ} {ω : RadixLaw} (τ : InfiniteVariableSpace ω) :
    prefixDist ρ τ τ = 0 := by
  simp only [prefixDist]
  have h : ¬∃ i, τ.digit i ≠ τ.digit i := by
    push_neg
    intro i
    rfl
  simp only [h, ↓reduceIte]

theorem prefixDist_comm {ρ : ℝ} {ω : RadixLaw} (τ σ : InfiniteVariableSpace ω) :
    prefixDist ρ τ σ = prefixDist ρ σ τ := by
  simp only [prefixDist]
  have h_iff : (∃ i, τ.digit i ≠ σ.digit i) ↔ (∃ i, σ.digit i ≠ τ.digit i) := by
    constructor <;> (intro ⟨i, hi⟩; exact ⟨i, hi.symm⟩)
  by_cases h : ∃ i, τ.digit i ≠ σ.digit i
  · simp only [h, h_iff.mp h, ↓reduceIte, lcpLength_comm]
  · have h' : ¬∃ i, σ.digit i ≠ τ.digit i := fun ⟨i, hi⟩ => h ⟨i, hi.symm⟩
    simp only [h, h', ↓reduceIte]

theorem prefixDist_nonneg {ρ : ℝ} (hρ : 0 < ρ) {ω : RadixLaw}
    (τ σ : InfiniteVariableSpace ω) :
    0 ≤ prefixDist ρ τ σ := by
  simp only [prefixDist]
  by_cases h : ∃ i, τ.digit i ≠ σ.digit i
  · simp only [h, ↓reduceIte]
    exact pow_nonneg (le_of_lt hρ) _
  · simp only [h, ↓reduceIte, le_refl]

/-- prefixDist = 0 iff points are equal -/
theorem prefixDist_eq_zero_iff {ρ : ℝ} (hρ : 0 < ρ) {ω : RadixLaw}
    {τ σ : InfiniteVariableSpace ω} :
    prefixDist ρ τ σ = 0 ↔ τ = σ := by
  constructor
  · -- prefixDist = 0 → τ = σ
    intro h
    simp only [prefixDist] at h
    by_contra hne
    have hneq : ∃ i, τ.digit i ≠ σ.digit i := by
      by_contra hall
      push_neg at hall
      apply hne
      ext i
      exact hall i
    simp only [hneq, ↓reduceIte] at h
    -- ρ^n = 0 implies ρ = 0 or n = ∞, but ρ > 0 and n is finite
    have hpos : 0 < ρ ^ lcpLength τ σ := pow_pos hρ _
    linarith
  · -- τ = σ → prefixDist = 0
    intro heq
    rw [heq]
    exact prefixDist_self σ

/-- Helper: ρ^{min a b} = max(ρ^a, ρ^b) when 0 ≤ ρ < 1 -/
private theorem pow_min_eq_max_of_lt_one {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (a b : ℕ) : ρ ^ min a b = max (ρ ^ a) (ρ ^ b) := by
  rcases Nat.le_or_le a b with hab | hab
  · simp only [Nat.min_eq_left hab]
    rw [max_eq_left]
    exact pow_le_pow_of_le_one hρ0 (le_of_lt hρ1) hab
  · simp only [Nat.min_eq_right hab]
    rw [max_eq_right]
    exact pow_le_pow_of_le_one hρ0 (le_of_lt hρ1) hab

/-- The strong triangle inequality (ultrametric property) -/
theorem prefixDist_ultrametric {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {ω : RadixLaw} (τ σ η : InfiniteVariableSpace ω) :
    prefixDist ρ τ η ≤ max (prefixDist ρ τ σ) (prefixDist ρ σ η) := by
  simp only [prefixDist]
  by_cases hτη : ∃ i, τ.digit i ≠ η.digit i
  · simp only [hτη, ↓reduceIte]
    by_cases hτσ : ∃ i, τ.digit i ≠ σ.digit i
    · by_cases hση : ∃ i, σ.digit i ≠ η.digit i
      · simp only [hτσ, hση, ↓reduceIte]
        -- All three are distinct, use the lcp inequality
        have hne : τ ≠ η := by
          intro heq
          obtain ⟨i, hi⟩ := hτη
          exact hi (congrArg (·.digit i) heq)
        have hlcp := lcpLength_triangle' τ σ η hne
        -- ρ^{lcpLength τ η} ≤ max(ρ^{lcpLength τ σ}, ρ^{lcpLength σ η})
        -- Since ρ < 1 and lcpLength τ η ≥ min(...), we have ρ^{lcpLength τ η} ≤ ρ^{min(...)} = max(...)
        calc ρ ^ lcpLength τ η
            ≤ ρ ^ min (lcpLength τ σ) (lcpLength σ η) := by
              exact pow_le_pow_of_le_one (le_of_lt hρ0) (le_of_lt hρ1) hlcp
          _ = max (ρ ^ lcpLength τ σ) (ρ ^ lcpLength σ η) := by
              exact pow_min_eq_max_of_lt_one (le_of_lt hρ0) hρ1 _ _
      · simp only [hτσ, hση, ↓reduceIte]
        -- τ ≠ σ but σ = η, so prefixDist σ η = 0
        push_neg at hση
        have hσeqη : σ = η := by ext i; exact hση i
        -- After subst, σ becomes η, and hτσ becomes a statement about τ and η
        -- But we already have hτη which is the same
        subst hσeqη
        exact le_max_left _ _
    · simp only [hτσ, ↓reduceIte]
      -- τ = σ, so prefixDist τ σ = 0
      push_neg at hτσ
      have hτeqσ : τ = σ := by ext i; exact hτσ i
      -- After subst, τ becomes σ, and hτη becomes ∃ i, σ.digit i ≠ η.digit i
      subst hτeqσ
      -- After subst, τ became σ, so hτη is now about σ and η
      simp only [hτη, ↓reduceIte]
      exact le_max_right _ _
  · -- τ = η, prefixDist τ η = 0
    simp only [hτη, ↓reduceIte]
    apply le_max_of_le_left
    exact prefixDist_nonneg hρ0 τ σ

/-!
## Ultrametric Properties (β_ω-metric)
-/

/-- δ_ω is zero iff points are equal -/
theorem ultrametricDist_eq_zero_iff {ω : RadixLaw} {τ σ : InfiniteVariableSpace ω} :
    ultrametricDist τ σ = 0 ↔ τ = σ := by
  constructor
  · -- ultrametricDist = 0 → τ = σ
    intro h
    simp only [ultrametricDist] at h
    by_contra hne
    have hneq : ∃ i, τ.digit i ≠ σ.digit i := by
      by_contra hall
      push_neg at hall
      apply hne
      ext i
      exact hall i
    simp only [hneq, ↓reduceIte] at h
    -- (prefixWeight ω (lcp τ σ))⁻¹ = 0 implies prefixWeight = ∞, but it's always finite
    have hpos : 0 < prefixWeight ω (lcp τ σ) := prefixWeight_pos ω _
    rw [inv_eq_zero] at h
    simp only [Nat.cast_eq_zero] at h
    omega
  · -- τ = σ → ultrametricDist = 0
    intro heq
    rw [heq]
    exact ultrametricDist_self σ

/-- Helper for getPrefix equality when sequences agree up to that point -/
theorem getPrefix_eq_of_digit_eq {ω : RadixLaw} (τ σ : InfiniteVariableSpace ω)
    (L : ℕ) (h : ∀ i < L, τ.digit i = σ.digit i) :
    τ.getPrefix L = σ.getPrefix L := by
  simp only [InfiniteVariableSpace.getPrefix]
  apply List.ext_getElem
  · simp only [List.length_ofFn]
  · intro i hi _
    simp only [List.getElem_ofFn]
    simp only [List.length_ofFn] at hi
    exact h i hi

/-- Helper: getPrefix m is a prefix of getPrefix n when m ≤ n -/
theorem getPrefix_prefix_of_le {ω : RadixLaw} (τ : InfiniteVariableSpace ω)
    (m n : ℕ) (hmn : m ≤ n) :
    τ.getPrefix m <+: τ.getPrefix n := by
  simp only [InfiniteVariableSpace.getPrefix]
  rw [List.prefix_iff_eq_take]
  apply List.ext_getElem
  · simp only [List.length_take, List.length_ofFn]
    exact (Nat.min_eq_left hmn).symm
  · intro i hi _
    simp only [List.length_ofFn] at hi
    simp only [List.getElem_take, List.getElem_ofFn]

/-- δ_ω satisfies the strong triangle inequality -/
theorem ultrametricDist_triangle {ω : RadixLaw} (τ σ η : InfiniteVariableSpace ω) :
    ultrametricDist τ η ≤ max (ultrametricDist τ σ) (ultrametricDist σ η) := by
  simp only [ultrametricDist]
  by_cases hτη : ∃ i, τ.digit i ≠ η.digit i
  · simp only [hτη, ↓reduceIte]
    by_cases hτσ : ∃ i, τ.digit i ≠ σ.digit i
    · by_cases hση : ∃ i, σ.digit i ≠ η.digit i
      · simp only [hτσ, hση, ↓reduceIte]
        -- All three distinct, use the lcp inequality
        have hne : τ ≠ η := by
          intro heq
          obtain ⟨i, hi⟩ := hτη
          exact hi (congrArg (·.digit i) heq)
        have hlcp := lcpLength_triangle' τ σ η hne
        -- prefixWeight(lcp τ η)⁻¹ ≤ max(prefixWeight(lcp τ σ)⁻¹, prefixWeight(lcp σ η)⁻¹)
        -- Larger lcp → larger prefixWeight → smaller inverse
        -- Show that prefixWeight ω (lcp τ η) ≥ min(prefixWeight ω (lcp τ σ), prefixWeight ω (lcp σ η))
        have hmono : prefixWeight ω (lcp τ η) ≥ min (prefixWeight ω (lcp τ σ)) (prefixWeight ω (lcp σ η)) := by
          simp only [lcp]
          -- The min of the two lcp lengths
          let m := min (lcpLength τ σ) (lcpLength σ η)
          -- τ and σ agree on [0, lcpLength τ σ), σ and η agree on [0, lcpLength σ η)
          -- So τ and η agree on [0, m)
          have hτη_agree : ∀ i < m, τ.digit i = η.digit i := by
            intro i hi
            have hi1 : i < lcpLength τ σ := lt_of_lt_of_le hi (Nat.min_le_left _ _)
            have hi2 : i < lcpLength σ η := lt_of_lt_of_le hi (Nat.min_le_right _ _)
            calc τ.digit i = σ.digit i := digit_eq_of_lt_lcpLength τ σ i hi1
              _ = η.digit i := digit_eq_of_lt_lcpLength σ η i hi2

          -- τ.getPrefix m = η.getPrefix m
          have hpref_τη : τ.getPrefix m = η.getPrefix m := getPrefix_eq_of_digit_eq τ η m hτη_agree

          -- Since lcpLength τ η ≥ m, getPrefix (lcpLength τ η) extends getPrefix m
          -- So prefixWeight(getPrefix (lcpLength τ η)) ≥ prefixWeight(getPrefix m)
          have hpw_τη : prefixWeight ω (τ.getPrefix (lcpLength τ η)) ≥ prefixWeight ω (τ.getPrefix m) := by
            apply prefixWeight_mono
            exact getPrefix_prefix_of_le τ m (lcpLength τ η) hlcp

          -- Similarly for τσ and ση
          have hpw_τσ : prefixWeight ω (τ.getPrefix (lcpLength τ σ)) ≥ prefixWeight ω (τ.getPrefix m) := by
            apply prefixWeight_mono
            exact getPrefix_prefix_of_le τ m (lcpLength τ σ) (Nat.min_le_left _ _)

          -- τ.getPrefix m = σ.getPrefix m (they agree on first m digits)
          have hτσ_agree : ∀ i < m, τ.digit i = σ.digit i := by
            intro i hi
            exact digit_eq_of_lt_lcpLength τ σ i (lt_of_lt_of_le hi (Nat.min_le_left _ _))
          have hpref_τσ : τ.getPrefix m = σ.getPrefix m := getPrefix_eq_of_digit_eq τ σ m hτσ_agree

          have hpw_ση : prefixWeight ω (σ.getPrefix (lcpLength σ η)) ≥ prefixWeight ω (σ.getPrefix m) := by
            apply prefixWeight_mono
            exact getPrefix_prefix_of_le σ m (lcpLength σ η) (Nat.min_le_right _ _)

          -- Since τ.getPrefix m = σ.getPrefix m, their prefix weights are equal
          have hpw_eq : prefixWeight ω (τ.getPrefix m) = prefixWeight ω (σ.getPrefix m) := by
            rw [hpref_τσ]

          -- Key insight: We need to show that either lcp τ σ or lcp σ η is a prefix of lcp τ η
          -- (depending on which has smaller lcpLength). Since prefix weight is monotone,
          -- the prefix has smaller weight, so min ≤ weight of lcp τ η.

          -- Case analysis on which is smaller
          rcases Nat.le_or_le (lcpLength τ σ) (lcpLength σ η) with hcase | hcase
          · -- lcpLength τ σ ≤ lcpLength σ η, so m = lcpLength τ σ
            -- Since lcpLength τ η ≥ m = lcpLength τ σ, lcp τ σ <+: lcp τ η (both use τ.getPrefix)
            have hmin_eq : m = lcpLength τ σ := Nat.min_eq_left hcase
            -- lcp τ σ = τ.getPrefix(lcpLength τ σ)
            -- lcp τ η = τ.getPrefix(lcpLength τ η)
            -- And lcpLength τ σ ≤ lcpLength τ η, so lcp τ σ <+: lcp τ η
            have hprefix : τ.getPrefix (lcpLength τ σ) <+: τ.getPrefix (lcpLength τ η) := by
              apply getPrefix_prefix_of_le
              rw [← hmin_eq]
              exact hlcp
            have hpw_le : prefixWeight ω (τ.getPrefix (lcpLength τ σ)) ≤ prefixWeight ω (τ.getPrefix (lcpLength τ η)) :=
              prefixWeight_mono ω _ _ hprefix
            exact le_trans (Nat.min_le_left _ _) hpw_le
          · -- lcpLength σ η ≤ lcpLength τ σ, so m = lcpLength σ η
            -- Need to show lcp σ η <+: lcp τ η
            -- lcp σ η = σ.getPrefix(lcpLength σ η)
            -- lcp τ η = τ.getPrefix(lcpLength τ η)
            -- Since lcpLength σ η ≤ lcpLength τ σ, and τ,σ agree on first lcpLength τ σ digits,
            -- τ and σ agree on first lcpLength σ η digits.
            -- So σ.getPrefix(lcpLength σ η) = τ.getPrefix(lcpLength σ η)
            have hmin_eq : m = lcpLength σ η := Nat.min_eq_right hcase
            have hση_digits : ∀ i < lcpLength σ η, σ.digit i = τ.digit i := by
              intro i hi
              -- i < lcpLength σ η ≤ lcpLength τ σ
              have hi' : i < lcpLength τ σ := lt_of_lt_of_le hi hcase
              exact (digit_eq_of_lt_lcpLength τ σ i hi').symm
            have hpref_eq : σ.getPrefix (lcpLength σ η) = τ.getPrefix (lcpLength σ η) :=
              getPrefix_eq_of_digit_eq σ τ (lcpLength σ η) hση_digits
            -- Now τ.getPrefix(lcpLength σ η) <+: τ.getPrefix(lcpLength τ η)
            have hprefix : τ.getPrefix (lcpLength σ η) <+: τ.getPrefix (lcpLength τ η) := by
              apply getPrefix_prefix_of_le
              rw [← hmin_eq]
              exact hlcp
            have hpw_le : prefixWeight ω (σ.getPrefix (lcpLength σ η)) ≤ prefixWeight ω (τ.getPrefix (lcpLength τ η)) := by
              rw [hpref_eq]
              exact prefixWeight_mono ω _ _ hprefix
            exact le_trans (Nat.min_le_right _ _) hpw_le

        -- Convert to inverse inequality
        have hpos_τη : (0 : ℝ) < prefixWeight ω (lcp τ η) := by
          exact_mod_cast prefixWeight_pos ω _
        have hpos_τσ : (0 : ℝ) < prefixWeight ω (lcp τ σ) := by
          exact_mod_cast prefixWeight_pos ω _
        have hpos_ση : (0 : ℝ) < prefixWeight ω (lcp σ η) := by
          exact_mod_cast prefixWeight_pos ω _
        rw [le_max_iff]
        -- prefixWeight τ η ≥ prefixWeight τ σ OR prefixWeight τ η ≥ prefixWeight σ η
        rcases Nat.le_or_le (prefixWeight ω (lcp τ σ)) (prefixWeight ω (lcp σ η)) with h | h
        · left
          -- prefixWeight(lcp τ σ) ≤ prefixWeight(lcp σ η)
          -- So min = prefixWeight(lcp τ σ)
          -- And prefixWeight(lcp τ η) ≥ min = prefixWeight(lcp τ σ)
          -- So (prefixWeight(lcp τ η))⁻¹ ≤ (prefixWeight(lcp τ σ))⁻¹
          apply inv_anti₀ hpos_τσ
          calc (prefixWeight ω (lcp τ σ) : ℝ)
              = min (prefixWeight ω (lcp τ σ)) (prefixWeight ω (lcp σ η)) := by
                simp only [Nat.cast_min]
                exact (min_eq_left (by exact_mod_cast h)).symm
            _ ≤ prefixWeight ω (lcp τ η) := by exact_mod_cast hmono
        · right
          -- prefixWeight(lcp σ η) ≤ prefixWeight(lcp τ σ)
          apply inv_anti₀ hpos_ση
          calc (prefixWeight ω (lcp σ η) : ℝ)
              = min (prefixWeight ω (lcp τ σ)) (prefixWeight ω (lcp σ η)) := by
                simp only [Nat.cast_min]
                exact (min_eq_right (by exact_mod_cast h)).symm
            _ ≤ prefixWeight ω (lcp τ η) := by exact_mod_cast hmono
      · simp only [hτσ, hση, ↓reduceIte]
        -- σ = η
        push_neg at hση
        have hσeqη : σ = η := by ext i; exact hση i
        subst hσeqη
        have heq : lcp τ σ = lcp τ σ := rfl
        exact le_max_left _ _
    · simp only [hτσ, ↓reduceIte]
      -- τ = σ
      push_neg at hτσ
      have hτeqσ : τ = σ := by ext i; exact hτσ i
      subst hτeqσ
      -- After subst, hτη is now ∃ i, σ.digit i ≠ η.digit i
      simp only [hτη, ↓reduceIte]
      exact le_max_right _ _
  · -- τ = η
    simp only [hτη, ↓reduceIte]
    exact le_max_of_le_left (ultrametricDist_nonneg τ σ)

/-!
## MetricSpace Instance
-/

/-- The regular triangle inequality follows from the ultrametric inequality -/
theorem prefixDist_triangle {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {ω : RadixLaw} (τ σ η : InfiniteVariableSpace ω) :
    prefixDist ρ τ η ≤ prefixDist ρ τ σ + prefixDist ρ σ η := by
  calc prefixDist ρ τ η
      ≤ max (prefixDist ρ τ σ) (prefixDist ρ σ η) := prefixDist_ultrametric hρ0 hρ1 τ σ η
    _ ≤ prefixDist ρ τ σ + prefixDist ρ σ η := max_le_add_of_nonneg
        (prefixDist_nonneg hρ0 τ σ) (prefixDist_nonneg hρ0 σ η)

/-- The variable radix space with the ρ-ultrametric forms a metric space -/
noncomputable def variableRadixMetricSpace (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (ω : RadixLaw) :
    MetricSpace (InfiniteVariableSpace ω) where
  dist := prefixDist ρ
  dist_self := fun x => prefixDist_self x
  dist_comm := fun x y => prefixDist_comm x y
  dist_triangle := fun x y z => prefixDist_triangle hρ0 hρ1 x y z
  eq_of_dist_eq_zero := fun h => (prefixDist_eq_zero_iff hρ0).mp h

/-- The dist function of the metric space equals prefixDist -/
theorem dist_eq_prefixDist (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (ω : RadixLaw)
    (τ σ : InfiniteVariableSpace ω) :
    @dist _ (variableRadixMetricSpace ρ hρ0 hρ1 ω).toPseudoMetricSpace.toDist τ σ =
      prefixDist ρ τ σ := rfl

/-- The metric space satisfies the ultrametric inequality -/
def variableRadixIsUltrametric (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (ω : RadixLaw) :
    @IsUltrametricDist (InfiniteVariableSpace ω)
      (variableRadixMetricSpace ρ hρ0 hρ1 ω).toPseudoMetricSpace.toDist :=
  @IsUltrametricDist.mk (InfiniteVariableSpace ω)
    (variableRadixMetricSpace ρ hρ0 hρ1 ω).toPseudoMetricSpace.toDist
    (fun x y z => prefixDist_ultrametric hρ0 hρ1 x y z)

end FdrsFormal.Modes.VariableRadix
