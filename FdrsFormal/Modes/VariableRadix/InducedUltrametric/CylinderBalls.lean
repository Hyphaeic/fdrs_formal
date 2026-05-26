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

# Cylinders as Metric Balls

This file proves that cylinders are exactly metric balls in the variable radix ultrametric.

## Mathematical Content (fdrs.md lines 4034-4041)

**Corollary 24 (cylinders are clopen and form a basis)**:
Each C_ω(s) is both open and closed in the metric topology, and the cylinders
{C_ω(s)} form a basis.

**Proof**: In an ultrametric, balls are clopen. Here C_ω(s) is exactly the ball
of radius ρ^{|s|} around any τ ∈ C_ω(s).

## References

- fdrs.md, Phase 5-6, Section 2 (lines 4034-4041)
- DEPENDENCY_BASED_STRUCTURE.md, Modes/VariableRadix/InducedUltrametric
-/

import FdrsFormal.Modes.VariableRadix.InducedUltrametric.Axioms

namespace FdrsFormal.Modes.VariableRadix

open Classical Topology

/-!
## Cylinder Sets
-/

/--
The cylinder C_ω(s) consists of all infinite sequences with prefix s.

**fdrs.md Definition 58**: C_ω(s) = {τ ∈ R^{(∞)}_ω : τ_{<|s|} = s}
-/
def cylinder (ω : RadixLaw) (s : PrefixWord) : Set (InfiniteVariableSpace ω) :=
  {τ | τ.getPrefix s.length = s}

/-- Membership in a cylinder -/
theorem mem_cylinder_iff {ω : RadixLaw} {s : PrefixWord} {τ : InfiniteVariableSpace ω} :
    τ ∈ cylinder ω s ↔ τ.getPrefix s.length = s := Iff.rfl

/-- The empty cylinder is the whole space -/
theorem cylinder_nil (ω : RadixLaw) : cylinder ω [] = Set.univ := by
  ext τ
  simp only [cylinder, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  simp only [InfiniteVariableSpace.getPrefix, List.length_nil, List.ofFn_zero]

/-- If two sequences share a prefix, their getPrefixes of that length are equal -/
theorem getPrefix_eq_of_mem_cylinder {ω : RadixLaw} {s : PrefixWord}
    {τ σ : InfiniteVariableSpace ω} (hτ : τ ∈ cylinder ω s) (hσ : σ ∈ cylinder ω s) :
    τ.getPrefix s.length = σ.getPrefix s.length := by
  simp only [cylinder, Set.mem_setOf_eq] at hτ hσ
  rw [hτ, hσ]

/-- Cylinder nesting: longer prefix gives smaller cylinder -/
theorem cylinder_subset_of_prefix {ω : RadixLaw} {s t : PrefixWord}
    (h : s.length ≤ t.length) (hpre : t.take s.length = s) :
    cylinder ω t ⊆ cylinder ω s := by
  intro τ hτ
  simp only [cylinder, Set.mem_setOf_eq] at hτ ⊢
  -- τ.getPrefix t.length = t
  -- Need: τ.getPrefix s.length = s
  -- Since s.length ≤ t.length, τ.getPrefix s.length = (τ.getPrefix t.length).take s.length
  have h1 : τ.getPrefix s.length = (τ.getPrefix t.length).take s.length := by
    simp only [InfiniteVariableSpace.getPrefix]
    apply List.ext_getElem
    · simp only [List.length_take, List.length_ofFn]
      exact (Nat.min_eq_left h).symm
    · intro i hi _
      simp only [List.length_ofFn] at hi
      simp only [List.getElem_take, List.getElem_ofFn]
  rw [h1, hτ, hpre]

/-- Extending a prefix shrinks the cylinder -/
theorem cylinder_subset_of_append {ω : RadixLaw} (s : PrefixWord) (d : ℕ) :
    cylinder ω (s ++ [d]) ⊆ cylinder ω s := by
  apply cylinder_subset_of_prefix
  · simp only [List.length_append, List.length_singleton]; omega
  · -- (s ++ [d]).take s.length = s
    rw [List.take_append_of_le_length (le_refl _), List.take_length]

/-- Two cylinders are either disjoint or one contains the other -/
theorem cylinder_disjoint_or_subset {ω : RadixLaw} (s t : PrefixWord) :
    Disjoint (cylinder ω s) (cylinder ω t) ∨
    cylinder ω s ⊆ cylinder ω t ∨
    cylinder ω t ⊆ cylinder ω s := by
  -- Case analysis on which prefix is longer
  rcases Nat.le_or_le s.length t.length with hle | hle
  · -- s.length ≤ t.length
    by_cases hpre : t.take s.length = s
    · -- t extends s, so cylinder t ⊆ cylinder s
      right; right
      exact cylinder_subset_of_prefix hle hpre
    · -- t and s disagree, so cylinders are disjoint
      left
      rw [Set.disjoint_iff]
      intro τ ⟨hτs, hτt⟩
      simp only [cylinder, Set.mem_setOf_eq] at hτs hτt
      apply hpre
      -- τ.getPrefix s.length = s and τ.getPrefix t.length = t
      -- Since s.length ≤ t.length, t.take s.length = (τ.getPrefix t.length).take s.length
      --                                            = τ.getPrefix s.length = s
      have h1 : (τ.getPrefix t.length).take s.length = τ.getPrefix s.length := by
        simp only [InfiniteVariableSpace.getPrefix]
        apply List.ext_getElem
        · simp only [List.length_take, List.length_ofFn, Nat.min_eq_left hle]
        · intro i hi _
          simp only [List.getElem_take, List.getElem_ofFn]
      rw [hτt] at h1
      rw [h1, hτs]
  · -- t.length ≤ s.length (symmetric case)
    by_cases hpre : s.take t.length = t
    · right; left
      exact cylinder_subset_of_prefix hle hpre
    · left
      rw [Set.disjoint_iff]
      intro τ ⟨hτs, hτt⟩
      simp only [cylinder, Set.mem_setOf_eq] at hτs hτt
      apply hpre
      have h1 : (τ.getPrefix s.length).take t.length = τ.getPrefix t.length := by
        simp only [InfiniteVariableSpace.getPrefix]
        apply List.ext_getElem
        · simp only [List.length_take, List.length_ofFn, Nat.min_eq_left hle]
        · intro i hi _
          simp only [List.getElem_take, List.getElem_ofFn]
      rw [hτs] at h1
      rw [h1, hτt]

/-!
## LCP Length and Cylinder Membership

Key insight: σ ∈ cylinder ω (τ.getPrefix n) iff lcpLength τ σ ≥ n (for τ ≠ σ)
or τ = σ.
-/

/-- If τ and σ agree on first n digits, σ is in the cylinder of τ's n-prefix -/
theorem mem_cylinder_of_lcpLength_ge {ω : RadixLaw} (τ σ : InfiniteVariableSpace ω)
    (n : ℕ) (h : ∀ i < n, τ.digit i = σ.digit i) :
    σ ∈ cylinder ω (τ.getPrefix n) := by
  simp only [cylinder, Set.mem_setOf_eq, InfiniteVariableSpace.getPrefix]
  apply List.ext_getElem
  · simp only [List.length_ofFn]
  · intro i hi _
    simp only [List.length_ofFn] at hi
    simp only [List.getElem_ofFn]
    exact (h i hi).symm

/-- If σ is in the cylinder of a prefix of length n, they agree on first n digits -/
theorem digit_eq_of_mem_cylinder {ω : RadixLaw} (τ σ : InfiniteVariableSpace ω)
    (n : ℕ) (h : σ ∈ cylinder ω (τ.getPrefix n)) (i : ℕ) (hi : i < n) :
    τ.digit i = σ.digit i := by
  simp only [cylinder, Set.mem_setOf_eq, InfiniteVariableSpace.getPrefix,
             List.length_ofFn] at h
  -- h : (List.ofFn fun j : Fin n => σ.digit j) = List.ofFn fun j : Fin n => τ.digit j
  -- Use getElem? to compare elements, avoiding dependent type issues
  have h_σ : (List.ofFn (fun j : Fin n => σ.digit j.val))[i]? =
             (List.ofFn (fun j : Fin n => τ.digit j.val))[i]? := congrArg (·[i]?) h
  simp only [List.getElem?_ofFn, hi, ↓reduceDIte] at h_σ
  exact Option.some.inj h_σ.symm

/-- Characterization: σ ∈ cylinder ω (τ.getPrefix n) iff lcpLength τ σ ≥ n or τ = σ -/
theorem mem_cylinder_getPrefix_iff {ω : RadixLaw} (τ σ : InfiniteVariableSpace ω) (n : ℕ) :
    σ ∈ cylinder ω (τ.getPrefix n) ↔ (τ = σ ∨ n ≤ lcpLength τ σ) := by
  constructor
  · intro h
    by_cases heq : τ = σ
    · left; exact heq
    · right
      -- τ ≠ σ, so there exists a differing digit
      have hdiff : ∃ i, τ.digit i ≠ σ.digit i := by
        by_contra hall
        push_neg at hall
        apply heq
        ext i
        exact hall i
      -- lcpLength τ σ = first differing position
      simp only [lcpLength, dif_pos hdiff]
      -- Need: n ≤ Nat.find hdiff
      by_contra hlt
      push_neg at hlt
      -- hlt : Nat.find hdiff < n
      -- But τ and σ agree on first n digits (from h)
      have heq_i : τ.digit (Nat.find hdiff) = σ.digit (Nat.find hdiff) :=
        digit_eq_of_mem_cylinder τ σ n h (Nat.find hdiff) hlt
      -- Contradiction with Nat.find_spec
      exact (Nat.find_spec hdiff) heq_i
  · intro h
    rcases h with heq | hle
    · -- τ = σ
      subst heq
      apply mem_cylinder_of_lcpLength_ge
      intro i _
      rfl
    · -- n ≤ lcpLength τ σ
      apply mem_cylinder_of_lcpLength_ge
      intro i hi
      exact digit_eq_of_lt_lcpLength τ σ i (lt_of_lt_of_le hi hle)

/-!
## Cylinders as Balls

Note: The full proof that cylinder = ball requires the actual MetricSpace instance
to use prefixDist as its distance function. Since variableRadixMetricSpace is
currently an axiom, we add connecting axioms here.
-/

/-- Cylinder membership in terms of distance (closed ball characterization) -/
theorem mem_cylinder_iff_dist_le {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {ω : RadixLaw} (τ σ : InfiniteVariableSpace ω) (n : ℕ) :
    σ ∈ cylinder ω (τ.getPrefix n) ↔
    @dist (InfiniteVariableSpace ω) (variableRadixMetricSpace ρ hρ0 hρ1 ω).toPseudoMetricSpace.toDist τ σ ≤ ρ ^ n := by
  rw [dist_eq_prefixDist]
  rw [mem_cylinder_getPrefix_iff]
  constructor
  · intro h
    rcases h with heq | hle
    · -- τ = σ: distance is 0 ≤ ρ^n
      subst heq
      simp only [prefixDist]
      split_ifs with hdiff
      · -- impossible: τ ≠ τ
        exfalso
        obtain ⟨i, hi⟩ := hdiff
        exact hi rfl
      · exact le_of_lt (pow_pos hρ0 n)
    · -- n ≤ lcpLength τ σ
      simp only [prefixDist]
      by_cases hdiff : ∃ i, τ.digit i ≠ σ.digit i
      · simp only [hdiff, ↓reduceIte]
        -- ρ ^ lcpLength τ σ ≤ ρ ^ n since lcpLength ≥ n and ρ < 1
        exact pow_le_pow_of_le_one (le_of_lt hρ0) (le_of_lt hρ1) hle
      · -- τ = σ (no differing digits)
        simp only [hdiff, ↓reduceIte]
        exact le_of_lt (pow_pos hρ0 n)
  · intro hle
    simp only [prefixDist] at hle
    by_cases hdiff : ∃ i, τ.digit i ≠ σ.digit i
    · simp only [hdiff, ↓reduceIte] at hle
      -- ρ ^ lcpLength τ σ ≤ ρ ^ n means lcpLength ≥ n (since ρ < 1)
      right
      by_contra hlt
      push_neg at hlt
      have := pow_lt_pow_right_of_lt_one₀ hρ0 hρ1 hlt
      linarith
    · -- τ = σ
      left
      push_neg at hdiff
      ext i
      exact hdiff i

/-- A cylinder equals a closed ball (the natural correspondence) -/
theorem cylinder_eq_closedBall' {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {ω : RadixLaw} (s : PrefixWord) (τ : InfiniteVariableSpace ω)
    (hτ : τ ∈ cylinder ω s) :
    letI := variableRadixMetricSpace ρ hρ0 hρ1 ω
    cylinder ω s = Metric.closedBall τ (ρ ^ s.length) := by
  letI := variableRadixMetricSpace ρ hρ0 hρ1 ω
  ext σ
  simp only [Metric.mem_closedBall]
  simp only [cylinder, Set.mem_setOf_eq] at hτ ⊢
  constructor
  · intro hσ
    -- σ.getPrefix s.length = s = τ.getPrefix s.length
    -- So σ and τ agree on first s.length digits
    -- Note: dist σ τ (from Metric.mem_closedBall), so we get prefixDist ρ σ τ
    rw [dist_eq_prefixDist]
    simp only [prefixDist]
    split_ifs with hdiff
    · -- hdiff : ∃ i, σ.digit i ≠ τ.digit i
      -- lcpLength σ τ = lcpLength τ σ ≥ s.length
      have hle : s.length ≤ lcpLength σ τ := by
        by_contra hlt
        push_neg at hlt
        -- lcpLength σ τ < s.length
        -- But σ and τ agree on first s.length digits
        have hlcp := hlt
        rw [lcpLength_comm] at hlcp
        -- hlcp : lcpLength τ σ < s.length
        have heq : τ.digit (lcpLength τ σ) = σ.digit (lcpLength τ σ) := by
          -- τ and σ both have prefix s of length s.length
          -- Since lcpLength τ σ < s.length, their digits at position lcpLength τ σ equal s[lcpLength τ σ]
          have h1 : τ.getPrefix s.length = s := hτ
          have h2 : σ.getPrefix s.length = s := hσ
          simp only [InfiniteVariableSpace.getPrefix] at h1 h2
          have hi' : lcpLength τ σ < s.length := hlcp
          -- Both list prefixes equal s, so their elements at lcpLength τ σ are equal
          have h_eq : (List.ofFn (fun j : Fin s.length => τ.digit j.val))[lcpLength τ σ]? =
                      (List.ofFn (fun j : Fin s.length => σ.digit j.val))[lcpLength τ σ]? := by
            congr 1
            exact h1.trans h2.symm
          simp only [List.getElem?_ofFn, hi', ↓reduceDIte] at h_eq
          exact Option.some.inj h_eq
        -- But lcpLength is the first differing position
        -- We have hdiff : ∃ i, σ.digit i ≠ τ.digit i
        -- Convert using symmetry
        have hdiff' : ∃ i, τ.digit i ≠ σ.digit i := by
          obtain ⟨i, hi⟩ := hdiff
          exact ⟨i, hi.symm⟩
        simp only [lcpLength, dif_pos hdiff'] at heq
        exact (Nat.find_spec hdiff') heq
      -- ρ ^ lcpLength σ τ ≤ ρ ^ s.length
      exact pow_le_pow_of_le_one (le_of_lt hρ0) (le_of_lt hρ1) hle
    · -- ¬∃ i, σ.digit i ≠ τ.digit i
      exact le_of_lt (pow_pos hρ0 s.length)
  · intro hσ
    rw [dist_eq_prefixDist] at hσ
    simp only [prefixDist] at hσ
    -- Note: We have dist σ τ (not dist τ σ) from Metric.mem_closedBall
    -- So after rewrite, we have prefixDist ρ σ τ and lcpLength σ τ
    split_ifs at hσ with hdiff
    · -- hdiff : ∃ i, σ.digit i ≠ τ.digit i
      -- hσ : ρ ^ lcpLength σ τ ≤ ρ ^ s.length
      -- Since lcpLength is symmetric, lcpLength σ τ = lcpLength τ σ
      rw [lcpLength_comm] at hσ
      -- Now: hσ : ρ ^ lcpLength τ σ ≤ ρ ^ s.length
      -- So lcpLength τ σ ≥ s.length
      have hle : s.length ≤ lcpLength τ σ := by
        by_contra hlt
        push_neg at hlt
        have := pow_lt_pow_right_of_lt_one₀ hρ0 hρ1 hlt
        linarith
      -- τ and σ agree on first s.length digits, and τ.getPrefix = s
      -- So σ.getPrefix = s
      simp only [InfiniteVariableSpace.getPrefix] at hτ ⊢
      apply List.ext_getElem
      · simp only [List.length_ofFn]
      · intro i hi _
        simp only [List.length_ofFn] at hi
        simp only [List.getElem_ofFn]
        -- Need: σ.digit i = s[i]
        -- We know: τ.digit i = s[i] (from hτ)
        -- We know: τ.digit i = σ.digit i (from lcpLength bound)
        have heq := digit_eq_of_lt_lcpLength τ σ i (lt_of_lt_of_le hi hle)
        -- From hτ : List.ofFn (fun j => τ.digit j) = s
        -- So s[i]? = (List.ofFn ...)[i]? = some (τ.digit i)
        have h_τ_eq : (List.ofFn (fun j : Fin s.length => τ.digit j.val))[i]? =
                      s[i]? := by
          simp only [hτ]
        simp only [List.getElem?_ofFn, hi, ↓reduceDIte] at h_τ_eq
        have hi_s : i < s.length := hi
        simp only [List.getElem?_eq_getElem hi_s] at h_τ_eq
        -- h_τ_eq : some (τ.digit i) = some (s[i])
        have h1 := Option.some.inj h_τ_eq
        -- h1 : τ.digit i = s[i]
        rw [← heq, h1]
    · -- ¬∃ i, σ.digit i ≠ τ.digit i means σ = τ
      push_neg at hdiff
      have heq : σ = τ := by ext i; exact hdiff i
      rw [heq, hτ]

/--
**Note**: The open ball `Metric.ball τ (ρ ^ s.length)` is strictly smaller than the cylinder.

The cylinder equals the CLOSED ball, not the open ball. This is because:
- Distances in this space are of the form `ρ^k` for k ∈ ℕ
- The radius `ρ^n` is always achieved (by any sequence differing from τ at exactly position n)
- Therefore: open ball ⊊ closed ball = cylinder

Use `cylinder_eq_closedBall` instead for the correct characterization.
-/
theorem cylinder_superset_ball {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {ω : RadixLaw} (s : PrefixWord) (τ : InfiniteVariableSpace ω)
    (hτ : τ ∈ cylinder ω s) :
    letI := variableRadixMetricSpace ρ hρ0 hρ1 ω
    Metric.ball τ (ρ ^ s.length) ⊆ cylinder ω s := by
  letI := variableRadixMetricSpace ρ hρ0 hρ1 ω
  rw [cylinder_eq_closedBall' hρ0 hρ1 s τ hτ]
  exact Metric.ball_subset_closedBall

/-- A cylinder is exactly a closed ball -/
theorem cylinder_eq_closedBall {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {ω : RadixLaw} (s : PrefixWord) (τ : InfiniteVariableSpace ω)
    (hτ : τ ∈ cylinder ω s) :
    letI := variableRadixMetricSpace ρ hρ0 hρ1 ω
    cylinder ω s = Metric.closedBall τ (ρ ^ s.length) :=
  cylinder_eq_closedBall' hρ0 hρ1 s τ hτ

/-!
## Cylinders are Clopen

In an ultrametric space, all balls are clopen. Since cylinders equal balls,
cylinders are clopen.
-/

/-- Cylinders are open -/
theorem cylinder_isOpen {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {ω : RadixLaw} (s : PrefixWord) :
    letI := variableRadixMetricSpace ρ hρ0 hρ1 ω
    IsOpen (cylinder ω s) := by
  letI inst := variableRadixMetricSpace ρ hρ0 hρ1 ω
  haveI : IsUltrametricDist (InfiniteVariableSpace ω) := variableRadixIsUltrametric ρ hρ0 hρ1 ω
  by_cases h : (cylinder ω s).Nonempty
  · obtain ⟨τ, hτ⟩ := h
    rw [cylinder_eq_closedBall hρ0 hρ1 s τ hτ]
    -- In ultrametrics, closed balls with nonzero radius are open
    -- ρ ^ s.length ≠ 0 since ρ > 0
    have hr : ρ ^ s.length ≠ 0 := ne_of_gt (pow_pos hρ0 s.length)
    exact IsUltrametricDist.isOpen_closedBall τ hr
  · -- Empty set is open
    simp only [Set.not_nonempty_iff_eq_empty] at h
    rw [h]
    exact isOpen_empty

/-- Cylinders are closed -/
theorem cylinder_isClosed {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {ω : RadixLaw} (s : PrefixWord) :
    letI := variableRadixMetricSpace ρ hρ0 hρ1 ω
    IsClosed (cylinder ω s) := by
  letI := variableRadixMetricSpace ρ hρ0 hρ1 ω
  by_cases h : (cylinder ω s).Nonempty
  · obtain ⟨τ, hτ⟩ := h
    rw [cylinder_eq_closedBall hρ0 hρ1 s τ hτ]
    exact Metric.isClosed_closedBall
  · simp only [Set.not_nonempty_iff_eq_empty] at h
    rw [h]
    exact isClosed_empty

/-- Cylinders are clopen -/
theorem cylinder_isClopen {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {ω : RadixLaw} (s : PrefixWord) :
    letI := variableRadixMetricSpace ρ hρ0 hρ1 ω
    IsClopen (cylinder ω s) :=
  ⟨cylinder_isClosed hρ0 hρ1 s, cylinder_isOpen hρ0 hρ1 s⟩

/-!
## Cylinders Form a Topological Basis

The cylinders {C_ω(s) : s a finite prefix} form a basis for the topology.
-/

/-- The collection of all cylinders -/
def cylinderBasis (ω : RadixLaw) : Set (Set (InfiniteVariableSpace ω)) :=
  {S | ∃ s : PrefixWord, S = cylinder ω s}

/-- Every point has a neighborhood basis of cylinders -/
theorem cylinder_mem_nhds {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {ω : RadixLaw} (τ : InfiniteVariableSpace ω) (n : ℕ) :
    letI := variableRadixMetricSpace ρ hρ0 hρ1 ω
    cylinder ω (τ.getPrefix n) ∈ 𝓝 τ := by
  letI := variableRadixMetricSpace ρ hρ0 hρ1 ω
  -- τ ∈ cylinder ω (τ.getPrefix n) trivially
  have hτ : τ ∈ cylinder ω (τ.getPrefix n) := by
    simp only [cylinder, Set.mem_setOf_eq, InfiniteVariableSpace.getPrefix_length]
  -- Cylinder is a neighborhood because it's open and contains τ
  exact (cylinder_isOpen hρ0 hρ1 (τ.getPrefix n)).mem_nhds hτ

/-- Cylinders form a topological basis -/
theorem cylinder_isTopologicalBasis {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {ω : RadixLaw} :
    letI := variableRadixMetricSpace ρ hρ0 hρ1 ω
    TopologicalSpace.IsTopologicalBasis (cylinderBasis ω) := by
  letI := variableRadixMetricSpace ρ hρ0 hρ1 ω
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · -- All cylinders are open
    intro S hS
    obtain ⟨s, rfl⟩ := hS
    exact cylinder_isOpen hρ0 hρ1 s
  · -- Every neighborhood contains a cylinder
    intro τ U hτU hU
    -- hτU : τ ∈ U, hU : IsOpen U
    -- Since U is open in a metric space, there exists ε > 0 with ball τ ε ⊆ U
    rw [Metric.isOpen_iff] at hU
    obtain ⟨ε, hε, hball⟩ := hU τ hτU
    -- Choose n large enough that ρ^n < ε
    -- Since ρ < 1, ρ^n → 0, so such n exists
    have hρn : ∃ n, ρ ^ n < ε := by
      have := tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt hρ0) hρ1
      rw [Metric.tendsto_atTop] at this
      obtain ⟨N, hN⟩ := this ε hε
      use N
      specialize hN N (le_refl N)
      simp only [Real.dist_eq, sub_zero, abs_of_pos (pow_pos hρ0 N)] at hN
      exact hN
    obtain ⟨n, hn⟩ := hρn
    -- cylinder ω (τ.getPrefix n) is in the basis
    use cylinder ω (τ.getPrefix n)
    refine ⟨⟨τ.getPrefix n, rfl⟩, ?_, ?_⟩
    · -- τ ∈ cylinder
      simp only [cylinder, Set.mem_setOf_eq, InfiniteVariableSpace.getPrefix_length]
    · -- cylinder ⊆ U
      intro σ hσ
      apply hball
      -- Need: σ ∈ Metric.ball τ ε, i.e., dist τ σ < ε
      -- We have σ ∈ cylinder ω (τ.getPrefix n)
      -- So dist τ σ ≤ ρ^n < ε
      have hτ_in : τ ∈ cylinder ω (τ.getPrefix n) := by
        simp only [cylinder, Set.mem_setOf_eq, InfiniteVariableSpace.getPrefix_length]
      have hcb := cylinder_eq_closedBall' hρ0 hρ1 (τ.getPrefix n) τ hτ_in
      rw [hcb] at hσ
      simp only [Metric.mem_closedBall] at hσ
      -- hσ : dist σ τ ≤ ρ ^ (τ.getPrefix n).length
      have hlen : (τ.getPrefix n).length = n := InfiniteVariableSpace.getPrefix_length τ n
      rw [hlen] at hσ
      -- Now hσ : dist σ τ ≤ ρ ^ n
      simp only [Metric.mem_ball]
      exact lt_of_le_of_lt hσ hn

end FdrsFormal.Modes.VariableRadix
