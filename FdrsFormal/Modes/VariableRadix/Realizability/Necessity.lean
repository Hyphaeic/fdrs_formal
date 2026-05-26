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

# Necessity of Realizability Conditions

This file proves the forward direction of THEOREM B:
If δ = δ_ω for some SU radix function ω, then the three conditions hold.

## Mathematical Content (fdrs.md lines 5393-5395)

For the induced ultrametric δ_ω from an SU radix function:
1. Cylinder correspondence holds because δ_ω is defined in terms of cylinders
2. Monotone refinement holds because β_ω is monotone in prefix length
3. Finite branching holds by definition of RadixLaw

## References

- fdrs.md, Phase 6, Section 6.6 (lines 5393-5395)
- DEPENDENCY_BASED_STRUCTURE.md, Modes/VariableRadix/Realizability
- Paper: Theorem B (§6.3), necessity direction
-/

import FdrsFormal.Modes.VariableRadix.Realizability.Conditions
import FdrsFormal.Modes.VariableRadix.SiblingUniformity.SiblingUniformity

namespace FdrsFormal.Modes.VariableRadix

/-!
## Stronger Properties Under SU

We first prove that under SU, balls are exactly cylinders (not just finite unions).
This is the key technical lemma for cylinder correspondence.
-/

/-- Under SU, balls are exactly cylinders (not just unions) -/
theorem su_ball_is_cylinder (ω : RadixLaw)
    (_hsu : ∀ k, isSiblingUniform ω k) (x : InfiniteVariableSpace ω) (r : ℝ)
    (hr : r > 0) :
    ∃ s : PrefixWord, {y : InfiniteVariableSpace ω | ultrametricDist x y < r} =
      cylinderInfinite ω s := by
  by_cases hr1 : r > 1
  · -- r > 1: ball is the whole space = cylinder([])
    use []
    ext y
    simp only [Set.mem_setOf_eq, cylinderInfinite, cylinder, InfiniteVariableSpace.getPrefix,
               List.length_nil, List.ofFn_zero, Set.mem_setOf_eq]
    constructor
    · intro _; trivial
    · intro _
      -- ultrametricDist x y ≤ 1 < r
      have hle : ultrametricDist x y ≤ 1 := by
        simp only [ultrametricDist]
        split_ifs with hdiff
        · have hpw_ge : prefixWeight ω (lcp x y) ≥ 1 := prefixWeight_pos ω (lcp x y)
          have hpw_pos : (0 : ℝ) < prefixWeight ω (lcp x y) :=
            Nat.cast_pos.mpr (prefixWeight_pos ω (lcp x y))
          rw [← one_div, div_le_one hpw_pos]
          exact Nat.one_le_cast.mpr hpw_ge
        · norm_num
      linarith
  · -- r ≤ 1: find n such that ball = cylinder(x.getPrefix n)
    push_neg at hr1
    -- We need to find minimal n with prefixWeight(x.getPrefix n) > 1/r
    -- Since prefixWeight grows unboundedly, such n exists
    have hexists : ∃ n, (prefixWeight ω (x.getPrefix n) : ℝ) > 1/r := by
      -- prefixWeight(x.getPrefix n) ≥ 2^n (each radix ≥ 2)
      have hpw_growth : ∀ n, prefixWeight ω (x.getPrefix n) ≥ 2^n := by
        intro n
        induction n with
        | zero =>
          simp only [InfiniteVariableSpace.getPrefix, List.ofFn_zero, prefixWeight_nil, pow_zero,
                     ge_iff_le, le_refl]
        | succ n ih =>
          have hget : x.getPrefix (n + 1) = x.getPrefix n ++ [x.digit n] := by
            simp only [InfiniteVariableSpace.getPrefix]
            apply List.ext_getElem
            · simp only [List.length_append, List.length_ofFn, List.length_singleton]
            · intro i hi _
              simp only [List.length_ofFn] at hi
              by_cases hi' : i < n
              · rw [List.getElem_append_left (by simp only [List.length_ofFn]; exact hi')]
                simp only [List.getElem_ofFn]
              · have hi'' : i = n := by omega
                subst hi''
                rw [List.getElem_append_right (by simp only [List.length_ofFn]; omega)]
                simp only [List.length_ofFn, Nat.sub_self, List.getElem_singleton,
                           List.getElem_ofFn]
          rw [hget, prefixWeight_append]
          calc prefixWeight ω (x.getPrefix n) * ω.radix (x.getPrefix n)
              ≥ 2^n * ω.radix (x.getPrefix n) := Nat.mul_le_mul_right _ ih
            _ ≥ 2^n * 2 := Nat.mul_le_mul_left _ (ω.radix_ge_two _)
            _ = 2^(n+1) := by ring
      -- Now use Archimedean property
      have ⟨N, hN⟩ := exists_nat_gt (1/r)
      use N
      have hN_le : N ≤ 2^N := Nat.le_of_lt Nat.lt_two_pow_self
      calc (prefixWeight ω (x.getPrefix N) : ℝ)
          ≥ 2^N := by exact_mod_cast hpw_growth N
        _ ≥ N := by exact_mod_cast hN_le
        _ > 1/r := hN
    -- Choose the minimal such n
    let n := Nat.find hexists
    use x.getPrefix n
    ext y
    have hlen : (x.getPrefix n).length = n := InfiniteVariableSpace.getPrefix_length x n
    simp only [Set.mem_setOf_eq, cylinderInfinite, cylinder, Set.mem_setOf_eq, hlen]
    constructor
    · -- y in ball → y in cylinder
      intro hdist
      simp only [ultrametricDist] at hdist
      by_cases hxy : x = y
      · subst hxy; rfl
      · -- x ≠ y: dist = (prefixWeight(lcp))⁻¹ < r
        have hdiff : ∃ i, x.digit i ≠ y.digit i := by
          by_contra hall; push_neg at hall
          exact hxy (InfiniteVariableSpace.ext (fun i => hall i))
        simp only [if_pos hdiff] at hdist
        -- (prefixWeight(lcp))⁻¹ < r → prefixWeight(lcp) > 1/r
        have hpw_pos : (0 : ℝ) < prefixWeight ω (lcp x y) :=
          Nat.cast_pos.mpr (prefixWeight_pos ω (lcp x y))
        have hpw_gt : (prefixWeight ω (lcp x y) : ℝ) > 1/r := by
          have h : (prefixWeight ω (lcp x y) : ℝ)⁻¹ < r := hdist
          have h2 := (inv_lt_comm₀ hpw_pos hr).mp h
          rw [one_div]; exact h2
        -- lcp x y = x.getPrefix (lcpLength x y)
        -- We need: y.getPrefix n = x.getPrefix n
        -- Sufficient: lcpLength x y ≥ n
        have hlcp_ge : n ≤ lcpLength x y := by
          by_contra hlt; push_neg at hlt
          -- By minimality of n, prefixWeight(x.getPrefix (lcpLength x y)) ≤ 1/r
          have hmin := Nat.find_min hexists hlt
          push_neg at hmin
          -- But lcp x y = x.getPrefix (lcpLength x y)
          have hlcp_eq : lcp x y = x.getPrefix (lcpLength x y) := rfl
          rw [hlcp_eq] at hpw_gt
          linarith
        -- Now show y.getPrefix n = x.getPrefix n using mem_cylinder_getPrefix_iff
        have hmem : y ∈ cylinder ω (x.getPrefix n) := by
          rw [mem_cylinder_getPrefix_iff x y n]
          right; exact hlcp_ge
        simp only [cylinder, Set.mem_setOf_eq, hlen] at hmem
        exact hmem
    · -- y in cylinder → y in ball
      intro hmem
      simp only [ultrametricDist]
      by_cases hxy : x = y
      · subst hxy
        have hno : ¬∃ i, x.digit i ≠ x.digit i := by push_neg; intro _; rfl
        simp only [if_neg hno]
        exact hr
      · have hdiff : ∃ i, x.digit i ≠ y.digit i := by
          by_contra hall; push_neg at hall
          exact hxy (InfiniteVariableSpace.ext (fun i => hall i))
        simp only [if_pos hdiff]
        -- hmem : y.getPrefix n = x.getPrefix n
        have hmem' : y ∈ cylinder ω (x.getPrefix n) := by
          simp only [cylinder, Set.mem_setOf_eq, hlen]
          exact hmem
        rw [mem_cylinder_getPrefix_iff x y n] at hmem'
        rcases hmem' with rfl | hle
        · exact absurd rfl hxy
        · -- hle : n ≤ lcpLength x y
          -- prefixWeight(lcp) ≥ prefixWeight(x.getPrefix n) > 1/r
          have hpw_pos : (0 : ℝ) < prefixWeight ω (lcp x y) :=
            Nat.cast_pos.mpr (prefixWeight_pos ω (lcp x y))
          have hn_spec := Nat.find_spec hexists
          have hpw_ge : prefixWeight ω (x.getPrefix n) ≤ prefixWeight ω (lcp x y) := by
            apply prefixWeight_mono
            -- x.getPrefix n <+: lcp x y = x.getPrefix (lcpLength x y)
            -- Since hle : n ≤ lcpLength x y, we have x.getPrefix n <+: x.getPrefix (lcpLength x y)
            -- First show x.getPrefix n = (x.getPrefix (lcpLength x y)).take n
            have hpre : x.getPrefix n = (x.getPrefix (lcpLength x y)).take n := by
              simp only [InfiniteVariableSpace.getPrefix]
              apply List.ext_getElem
              · simp only [List.length_take, List.length_ofFn, Nat.min_eq_left hle]
              · intro i hi _
                simp only [List.length_ofFn] at hi
                simp only [List.getElem_take, List.getElem_ofFn]
            rw [hpre]
            exact List.take_prefix n _
          have hpw_gt : (prefixWeight ω (lcp x y) : ℝ) > 1/r := by
            calc (prefixWeight ω (lcp x y) : ℝ)
                ≥ prefixWeight ω (x.getPrefix n) := by exact_mod_cast hpw_ge
              _ > 1/r := hn_spec
          -- Convert: pw > 1/r to pw⁻¹ < r
          have h2 : r⁻¹ < (prefixWeight ω (lcp x y) : ℝ) := by
            rw [inv_eq_one_div]; exact hpw_gt
          exact (inv_lt_comm₀ hpw_pos hr).mpr h2

/-!
## Necessity: δ_ω Implies the Conditions
-/

/--
The induced ultrametric from an SU radix law has cylinder correspondence.

Every ball is determined by the longest common prefix, hence is a cylinder.
-/
theorem induced_hasCylinderCorrespondence (ω : RadixLaw)
    (hsu : ∀ k, isSiblingUniform ω k) :
    hasCylinderCorrespondence ω := by
  intro x r hr
  -- Under SU, each ball is exactly a single cylinder
  obtain ⟨s, hs⟩ := su_ball_is_cylinder ω hsu x r hr
  use {s}
  rw [hs]
  simp only [Finset.mem_singleton, Set.iUnion_iUnion_eq_left]

/--
The induced ultrametric from an SU radix law has monotone refinement.

Longer prefixes have smaller radii because β_ω grows monotonically.
-/
theorem induced_hasMonotoneRefinement (ω : RadixLaw)
    (_hsu : ∀ k, isSiblingUniform ω k) :
    hasMonotoneRefinement ω :=
  -- Monotone refinement holds for any RadixLaw, not just SU ones
  radixLaw_monotoneRefinement ω

/--
The induced ultrametric from an SU radix law has finite branching.

This is immediate from the definition of RadixLaw.
-/
theorem induced_hasFiniteBranching (ω : RadixLaw) :
    hasFiniteBranching ω :=
  radixLaw_finiteBranching ω

/-!
## Necessity Theorem
-/

/--
**THEOREM B (Necessity)**: If δ = δ_ω for an SU radix function ω,
then the three realizability conditions hold.
-/
theorem theoremB_necessity (ω : RadixLaw)
    (hsu : ∀ k, isSiblingUniform ω k) :
    RealizabilityConditions ω :=
  ⟨induced_hasCylinderCorrespondence ω hsu,
   induced_hasMonotoneRefinement ω hsu,
   induced_hasFiniteBranching ω⟩

/-!
## Additional Properties Under SU
-/

/--
Under SU, the radius spectrum is discrete (no accumulation points in (0, ∞)).

The radii are reciprocals of prefix weights, which are natural numbers ≥ 1.
This means radii are of the form 1/n for n ∈ ℕ⁺, forming a discrete set.

Note: The set has infimum 0 (as prefix length → ∞, prefix weight → ∞, radius → 0),
but 0 is not achieved. Every positive radius r has a neighborhood (r-ε, r+ε)
containing only finitely many other radii.
-/
theorem su_discrete_spectrum (ω : RadixLaw)
    (_hsu : ∀ k, isSiblingUniform ω k) :
    ∀ s : PrefixWord, variableRadixRadius ω s > 0 ∧
      ∃ (n : ℕ), n ≥ 1 ∧ variableRadixRadius ω s = (n : ℝ)⁻¹ := by
  intro s
  constructor
  · -- Radius is positive
    simp only [variableRadixRadius]
    have h := prefixWeight_pos ω s
    exact inv_pos.mpr (Nat.cast_pos.mpr h)
  · -- Radius is 1/n for some n ≥ 1
    use prefixWeight ω s
    constructor
    · exact prefixWeight_pos ω s
    · simp only [variableRadixRadius]

end FdrsFormal.Modes.VariableRadix
