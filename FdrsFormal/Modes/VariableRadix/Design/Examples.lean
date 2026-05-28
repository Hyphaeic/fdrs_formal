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

# Concrete Ultrametric Design Examples

This file provides concrete examples of custom ultrametric design.

## Mathematical Content (fdrs.md lines 5298-5337)

**Example 6.4.4**: Context-dependent spatial resolution
**Example 6.4.5**: DNA sequence ultrametric respecting biological structure
**Example 6.7.2**: Cache-optimized ultrametric

## References

- fdrs.md, Phase 6, Sections 6.4-6.7 (lines 5298-5337, 5429-5437)
-/

import FdrsFormal.Modes.VariableRadix.Design.InverseProblem
import FdrsFormal.Modes.VariableRadix.Basic.RadixLaw

namespace FdrsFormal.Modes.VariableRadix.Design

/-!
## Context-Dependent Resolution
-/

/--
Partition of prefix space into critical and coarse regions.

**fdrs.md Example 6.4.4 (lines 5298-5315)**: Fine resolution on critical, coarse elsewhere.

**Axiomatized**: Requires formalization of domain knowledge partitioning.
-/
structure RegionPartition where
  /-- Critical regions requiring fine resolution -/
  critical : Set PrefixWord
  /-- Coarse regions allowing coarse resolution -/
  coarse : Set PrefixWord
  /-- Partition covers all prefixes -/
  partition : ∀ s, s ∈ critical ∨ s ∈ coarse

/--
Construction of context-dependent radix law.

**fdrs.md lines 5305-5310**:
  ω(s) = ω_fine   if s ∈ Critical
  ω(s) = ω_coarse if s ∈ Coarse
with ω_fine ≫ ω_coarse.

The piecewise law `ω(s) = if s ∈ Critical then ω_fine else ω_coarse` is a valid
radix law (both branches `≥ 2`) realizing fine resolution on critical regions and
coarse elsewhere.

**Application**: Biological systems, query-adaptive databases.
-/
theorem contextDependentRadix (partition : RegionPartition)
    (ω_fine ω_coarse : ℕ) (hcoarse : 2 ≤ ω_coarse) (h : ω_coarse < ω_fine) :
    ∃ ω : RadixLaw, (∀ s ∈ partition.critical, ω.radix s = ω_fine) ∧
                    (∀ s, s ∉ partition.critical → ω.radix s = ω_coarse) := by
  classical
  refine ⟨⟨fun s => if s ∈ partition.critical then ω_fine else ω_coarse, fun s => ?_⟩, ?_, ?_⟩
  · show 2 ≤ (if s ∈ partition.critical then ω_fine else ω_coarse)
    split <;> omega
  · intro s hs; simp [hs]
  · intro s hs; simp [hs]

/-!
## DNA Sequence Ultrametric
-/

/--
DNA sequence ultrametric respecting codon structure.

**fdrs.md Example 6.4.5 (lines 5318-5337)**:
- Incomplete codon (k < 3): ω = 4 (uniform)
- Codon boundary (k % 3 = 0): ω = 64 (coarse)
- Mid-codon: ω = 4 (fine)

**Result**: Codon-level changes are metrically farther than point mutations.

**Biological interpretation**: Reflects functional distance, not just edit distance.

The branching law `ω(s) = if (3 ≤ |s| ∧ |s| % 3 = 0) then 64 else 4` realizes this:
coarse (64) exactly at codon boundaries, fine (4) within codons and on incomplete codons.
-/
theorem dnaCodonUltrametric :
    ∃ ω : RadixLaw,
      (∀ s, 3 ≤ s.length → s.length % 3 = 0 → ω.radix s = 64) ∧
      (∀ s, (s.length < 3 ∨ s.length % 3 ≠ 0) → ω.radix s = 4) := by
  refine ⟨⟨fun s => if 3 ≤ s.length ∧ s.length % 3 = 0 then 64 else 4, fun s => ?_⟩, ?_, ?_⟩
  · show 2 ≤ (if 3 ≤ s.length ∧ s.length % 3 = 0 then (64 : ℕ) else 4)
    split <;> omega
  · intro s h1 h2
    show (if 3 ≤ s.length ∧ s.length % 3 = 0 then (64 : ℕ) else 4) = 64
    split <;> omega
  · intro s h
    show (if 3 ≤ s.length ∧ s.length % 3 = 0 then (64 : ℕ) else 4) = 4
    split <;> omega

/-!
## Cache-Optimized Ultrametric
-/

/--
Cache-optimized ultrametric design.

**fdrs.md Example 6.7.2 (lines 5429-5437)**:
  β_ω(s) = 2^{-cache_cost(s)}
where cache_cost(s) is measured cache miss rate.

**Result**: δ_ω-locality directly corresponds to cache efficiency.

The radix `ω(s) = cache_cost(s) + 2` is driven by the measured cache cost at `s`
(higher cost ⇒ larger branching ⇒ finer resolution there), always a valid radix `≥ 2`.
-/
theorem cacheOptimizedRadix (cache_cost : PrefixWord → ℕ) :
    ∃ ω : RadixLaw, ∀ s, ω.radix s = cache_cost s + 2 :=
  ⟨⟨fun s => cache_cost s + 2, fun _ => Nat.le_add_left 2 _⟩, fun _ => rfl⟩

end FdrsFormal.Modes.VariableRadix.Design
