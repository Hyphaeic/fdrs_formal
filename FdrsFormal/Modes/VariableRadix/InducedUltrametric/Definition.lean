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

# Variable Radix Ultrametric Definition

This file defines the ultrametric δ_ω induced by a radix law.

## Mathematical Content (fdrs.md lines 4010-4019)

**Definition 59 (prefix metric)**:
For τ ≠ σ, let ℓ(τ,σ) be the length of the longest common prefix:
  ℓ(τ,σ) := max{m ≥ 0 : τ_{<m} = σ_{<m}}

Fix any ρ ∈ (0,1) (e.g., ρ = 1/2). Define:
  d(τ,σ) := ρ^{ℓ(τ,σ)},   d(τ,τ) := 0

## Alternative Definition (fdrs.md lines 5135-5148)

Using prefix weights β_ω(s):
  δ_ω(x,y) := β_ω(lcp(x,y))^{-1}  if x ≠ y
  δ_ω(x,x) := 0

where β_ω(s) = ∏_{i=0}^{|s|-1} ω(s_{<i}) is the odometer weight.

## References

- fdrs.md, Phase 5-6, Section 2 (lines 4010-4019)
- fdrs.md, Phase 6, Definition 79 (lines 5135-5148)
- DEPENDENCY_BASED_STRUCTURE.md, Modes/VariableRadix/InducedUltrametric
-/

import FdrsFormal.Modes.VariableRadix.PrefixWeights.Definition
import Mathlib.Topology.MetricSpace.Basic

namespace FdrsFormal.Modes.VariableRadix

open InfiniteVariableSpace Classical

/-!
## Longest Common Prefix
-/

/--
The longest common prefix length of two infinite sequences.

For τ ≠ σ, this is the first index where they differ.
For τ = σ, this is defined as 0 (by convention - the actual distance will be 0 anyway).
-/
noncomputable def lcpLength {ω : RadixLaw} (τ σ : InfiniteVariableSpace ω) : ℕ :=
  if h : ∃ i, τ.digit i ≠ σ.digit i then Nat.find h
  else 0  -- τ = σ case

/-- The longest common prefix as a PrefixWord -/
noncomputable def lcp {ω : RadixLaw} (τ σ : InfiniteVariableSpace ω) : PrefixWord :=
  τ.getPrefix (lcpLength τ σ)

/-!
## Simple Prefix Metric (ρ-based)
-/

/--
The simple prefix metric with base ρ ∈ (0,1).

**Definition**: d(τ,σ) := ρ^{lcpLength(τ,σ)} if τ ≠ σ, d(τ,τ) := 0
-/
noncomputable def prefixDist (ρ : ℝ) {ω : RadixLaw}
    (τ σ : InfiniteVariableSpace ω) : ℝ :=
  if ∃ i, τ.digit i ≠ σ.digit i then ρ ^ lcpLength τ σ
  else 0  -- τ = σ case

/-!
## Ultrametric Using Prefix Weights
-/

/--
The ultrametric δ_ω using prefix weights.

**fdrs.md Definition**:
  δ_ω(x,y) := β_ω(lcp(x,y))^{-1}  if x ≠ y
  δ_ω(x,x) := 0
-/
noncomputable def ultrametricDist {ω : RadixLaw}
    (τ σ : InfiniteVariableSpace ω) : ℝ :=
  if ∃ i, τ.digit i ≠ σ.digit i then (prefixWeight ω (lcp τ σ) : ℝ)⁻¹
  else 0  -- τ = σ case

theorem ultrametricDist_self {ω : RadixLaw} (τ : InfiniteVariableSpace ω) :
    ultrametricDist τ τ = 0 := by
  simp only [ultrametricDist]
  -- No index where τ.digit i ≠ τ.digit i
  have h : ¬∃ i, τ.digit i ≠ τ.digit i := by
    push_neg
    intro i
    rfl
  simp only [h, ↓reduceIte]

/-- Helper: lcpLength is symmetric -/
theorem lcpLength_comm {ω : RadixLaw} (τ σ : InfiniteVariableSpace ω) :
    lcpLength τ σ = lcpLength σ τ := by
  simp only [lcpLength]
  -- First establish the equivalence of existence
  have h_iff : (∃ i, τ.digit i ≠ σ.digit i) ↔ (∃ i, σ.digit i ≠ τ.digit i) := by
    constructor <;> (intro ⟨i, hi⟩; exact ⟨i, hi.symm⟩)
  by_cases h : ∃ i, τ.digit i ≠ σ.digit i
  · have h' := h_iff.mp h
    simp only [dif_pos h, dif_pos h']
    -- The minimum is the same since the predicates are equivalent pointwise
    apply le_antisymm
    · -- Nat.find h ≤ Nat.find h': the predicate for h holds at Nat.find h'
      apply Nat.find_min' h
      -- Need: τ.digit (Nat.find h') ≠ σ.digit (Nat.find h')
      exact (Nat.find_spec h').symm
    · -- Nat.find h' ≤ Nat.find h: the predicate for h' holds at Nat.find h
      apply Nat.find_min' h'
      -- Need: σ.digit (Nat.find h) ≠ τ.digit (Nat.find h)
      exact (Nat.find_spec h).symm
  · have h' : ¬∃ i, σ.digit i ≠ τ.digit i := fun hc => h (h_iff.mpr hc)
    simp only [dif_neg h, dif_neg h']

/-- Helper: at positions below lcpLength, digits agree -/
theorem digit_eq_of_lt_lcpLength {ω : RadixLaw} (τ σ : InfiniteVariableSpace ω)
    (i : ℕ) (hi : i < lcpLength τ σ) : τ.digit i = σ.digit i := by
  simp only [lcpLength] at hi
  split_ifs at hi with h
  · -- There exists a differing index, and i < the first such index
    by_contra hne
    have := Nat.find_min' h hne
    omega
  · -- No differing index exists, so i < 0 is impossible
    omega

/-- Helper: lcp is symmetric -/
theorem lcp_comm {ω : RadixLaw} (τ σ : InfiniteVariableSpace ω) :
    lcp τ σ = lcp σ τ := by
  simp only [lcp]
  rw [lcpLength_comm]
  apply List.ext_getElem
  · simp [getPrefix_length]
  · intro i hi1 hi2
    simp only [getPrefix, List.getElem_ofFn]
    have hi_lt : i < lcpLength σ τ := by
      simp only [getPrefix, List.length_ofFn] at hi1
      exact hi1
    rw [← lcpLength_comm] at hi_lt
    exact digit_eq_of_lt_lcpLength τ σ i hi_lt

theorem ultrametricDist_comm {ω : RadixLaw} (τ σ : InfiniteVariableSpace ω) :
    ultrametricDist τ σ = ultrametricDist σ τ := by
  simp only [ultrametricDist]
  have h_iff : (∃ i, τ.digit i ≠ σ.digit i) ↔ (∃ i, σ.digit i ≠ τ.digit i) := by
    constructor <;> (intro ⟨i, hi⟩; exact ⟨i, hi.symm⟩)
  by_cases h : ∃ i, τ.digit i ≠ σ.digit i
  · simp only [h, h_iff.mp h, ↓reduceIte]
    rw [lcp_comm]
  · simp only [h, ↓reduceIte]
    have h' : ¬∃ i, σ.digit i ≠ τ.digit i := fun ⟨i, hi⟩ => h ⟨i, hi.symm⟩
    simp only [h', ↓reduceIte]

theorem ultrametricDist_nonneg {ω : RadixLaw} (τ σ : InfiniteVariableSpace ω) :
    0 ≤ ultrametricDist τ σ := by
  simp only [ultrametricDist]
  by_cases h : ∃ i, τ.digit i ≠ σ.digit i
  · simp only [h, ↓reduceIte]
    apply inv_nonneg.mpr
    simp only [Nat.cast_nonneg]
  · simp only [h, ↓reduceIte, le_refl]

end FdrsFormal.Modes.VariableRadix
