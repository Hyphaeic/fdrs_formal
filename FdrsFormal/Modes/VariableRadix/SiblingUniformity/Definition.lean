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

# Sibling Uniformity Definition

This file defines the sibling uniformity (SU) condition for variable radix systems.

## Mathematical Content (fdrs.md lines 4683-4697)

**Definition 57 (Sibling-uniform suffix counts, SU)**:
A radix system is **SU at depth k** if for every prefix s with |s| ≤ k,
the completion counts of its children are equal:

W^{(k)}_ω(s∥d) is independent of d ∈ D_ω(s)

This means all siblings at any node have the same number of completions.

## References

- fdrs.md, Phase 5-6, Section 1 (lines 4683-4697)
- DEPENDENCY_BASED_STRUCTURE.md, Modes/VariableRadix/SiblingUniformity
- Paper: Fragment 5.4
-/

import FdrsFormal.Modes.VariableRadix.Encoding.Encoding

namespace FdrsFormal.Modes.VariableRadix

/-!
## Sibling Uniformity Condition
-/

/--
**Definition 57**: Sibling uniformity at a specific prefix.

At prefix s, SU holds if all children s∥d have the same completion count.
-/
def isSiblingUniformAt (ω : RadixLaw) (k : ℕ) (s : PrefixWord) : Prop :=
  s.length ≤ k →
  ∀ d₁ d₂ : ℕ, d₁ < ω.radix s → d₂ < ω.radix s →
    completionCount ω k (s ++ [d₁]) = completionCount ω k (s ++ [d₂])

/--
**Definition 57**: Sibling uniformity at depth k.

A radix system is SU at depth k if sibling uniformity holds at every prefix of length ≤ k.
-/
def isSiblingUniform (ω : RadixLaw) (k : ℕ) : Prop :=
  ∀ s : PrefixWord, s.length ≤ k → isSiblingUniformAt ω k s

/-!
## Note on Depth Inheritance

**WARNING**: The statement "SU at k+1 implies SU at k" is FALSE in general.

**Counterexample**:
Consider a radix law where:
- radix([]) = 2 (root has children 0, 1)
- radix([0]) = 2, radix([1]) = 3
- radix([0,d]) = 3 for d ∈ {0,1}
- radix([1,d]) = 2 for d ∈ {0,1,2}

At k=1:
- completionCount ω 1 [0] = radix([0]) = 2
- completionCount ω 1 [1] = radix([1]) = 3
- SU FAILS (2 ≠ 3)

At k=2:
- completionCount ω 2 [0] = radix([0,0]) + radix([0,1]) = 3 + 3 = 6
- completionCount ω 2 [1] = radix([1,0]) + radix([1,1]) + radix([1,2]) = 2 + 2 + 2 = 6
- SU HOLDS (6 = 6)

The key insight: completion counts at depth k+1 can "balance out" via products
(2×3 = 3×2) even when depth-k counts differ. SU is NOT monotone in depth.

For position-only radix laws (where radix depends only on prefix length),
SU holds automatically at all depths - see `positionOnly_siblingUniform`.
-/

/-!
## Sibling Uniformity for Position-Only Radix Laws
-/

/-- Position-only radix laws are always sibling uniform -/
-- Note: Concrete statement requires Core.Primitives.RadixSeq
theorem positionOnly_siblingUniform (ω : RadixLaw) (k : ℕ)
    (h_posOnly : ∀ s t : PrefixWord, s.length = t.length → ω.radix s = ω.radix t) :
    isSiblingUniform ω k := by
  intro s hs
  intro hsk d₁ d₂ hd₁ hd₂
  -- s ++ [d₁] and s ++ [d₂] have the same length
  have hlen_eq : (s ++ [d₁]).length = (s ++ [d₂]).length := by simp
  -- Show completion counts are equal by showing the prefixes behave identically
  -- This follows by induction on the remaining depth
  -- For position-only laws, completion count only depends on prefix length
  -- We'll prove completionCount ω k p only depends on p.length for position-only ω
  suffices h : ∀ p q : PrefixWord, p.length = q.length → p.length ≤ k + 1 →
      completionCount ω k p = completionCount ω k q by
    exact h (s ++ [d₁]) (s ++ [d₂]) hlen_eq (by simp; omega)
  intro p q hpq_len hp_bound
  -- Induction on remaining depth k + 1 - p.length
  obtain ⟨n, hn⟩ : ∃ n, n = k + 1 - p.length := ⟨_, rfl⟩
  induction n using Nat.strongRecOn generalizing p q with
  | _ n ih =>
    by_cases heq : p.length = k + 1
    · -- Base case: at full depth, completionCount = 1
      rw [completionCount_of_length_eq ω k p heq]
      rw [completionCount_of_length_eq ω k q (hpq_len ▸ heq)]
    · -- Recursive case
      have hlt : p.length < k + 1 := Nat.lt_of_le_of_ne hp_bound heq
      have hlt_q : q.length < k + 1 := hpq_len ▸ hlt
      rw [completionCount_rec ω k p hlt]
      rw [completionCount_rec ω k q hlt_q]
      -- radix p = radix q by position-only
      have h_radix : ω.radix p = ω.radix q := h_posOnly p q hpq_len
      rw [h_radix]
      apply Finset.sum_congr rfl
      intro d _
      -- Apply IH: completionCount(p ++ [d]) = completionCount(q ++ [d])
      have hlen' : (p ++ [d]).length = (q ++ [d]).length := by simp [hpq_len]
      have hbound' : (p ++ [d]).length ≤ k + 1 := by simp; omega
      have hdec : k + 1 - (p ++ [d]).length < n := by simp at hn ⊢; omega
      exact ih (k + 1 - (p ++ [d]).length) hdec (p ++ [d]) (q ++ [d]) hlen' hbound' rfl

/-!
## Equivalent Characterizations of SU
-/

/-- SU is equivalent to uniform block sizes in the tree -/
theorem siblingUniform_iff_uniformBlocks (ω : RadixLaw) (k : ℕ) :
    isSiblingUniform ω k ↔
      ∀ s : PrefixWord, s.length < k →
        ∃ B : ℕ, ∀ d : ℕ, d < ω.radix s →
          completionCount ω k (s ++ [d]) = B := by
  constructor
  · -- Forward: SU implies uniform blocks
    intro hsu s hs
    -- Use B = completionCount(s ++ [0])
    have h_radix_pos : 0 < ω.radix s := ω.radix_pos s
    use completionCount ω k (s ++ [0])
    intro d hd
    -- By SU, completionCount(s ++ [d]) = completionCount(s ++ [0])
    have hsu_s := hsu s (Nat.le_of_lt hs)
    exact hsu_s (Nat.le_of_lt hs) d 0 hd h_radix_pos
  · -- Backward: uniform blocks implies SU
    intro h_blocks s hs
    intro hsk d₁ d₂ hd₁ hd₂
    by_cases hlt : s.length < k
    · -- s.length < k, use the block characterization
      obtain ⟨B, hB⟩ := h_blocks s hlt
      rw [hB d₁ hd₁, hB d₂ hd₂]
    · -- s.length = k, completion count is 1 for all children
      have heq : s.length = k := Nat.le_antisymm hsk (Nat.not_lt.mp hlt)
      rw [completionCount_of_length_eq ω k (s ++ [d₁]) (by simp [heq])]
      rw [completionCount_of_length_eq ω k (s ++ [d₂]) (by simp [heq])]

/-- SU implies the product formula for completion counts -/
theorem siblingUniform_product_formula (ω : RadixLaw) (k : ℕ)
    (hsu : isSiblingUniform ω k) (s : PrefixWord) (hs : s.length ≤ k) :
    completionCount ω k s = ω.radix s * (completionCount ω k (s ++ [0]) / 1) := by
  simp only [Nat.div_one]
  by_cases hlt : s.length < k
  · -- Case: s.length < k, use the recursive formula
    rw [completionCount_rec ω k s (Nat.lt_add_one_of_lt hlt)]
    -- Under SU, all children have the same completion count
    have hsu_s := hsu s (Nat.le_of_lt hlt)
    have h_eq : ∀ d ∈ Finset.range (ω.radix s),
        completionCount ω k (s ++ [d]) = completionCount ω k (s ++ [0]) := by
      intro d hd
      rw [Finset.mem_range] at hd
      have h0_valid : 0 < ω.radix s := ω.radix_pos s
      exact hsu_s (Nat.le_of_lt hlt) d 0 hd h0_valid
    rw [Finset.sum_congr rfl h_eq]
    simp [Finset.sum_const, Finset.card_range]
  · -- Case: s.length = k
    have heq : s.length = k := Nat.le_antisymm hs (Nat.not_lt.mp hlt)
    -- completionCount ω k s uses recursive formula: sum of children, each = 1
    rw [completionCount_rec ω k s (by omega)]
    have h_child : ∀ d ∈ Finset.range (ω.radix s), completionCount ω k (s ++ [d]) = 1 := by
      intro d _
      exact completionCount_of_length_eq ω k (s ++ [d]) (by simp [heq])
    rw [Finset.sum_congr rfl h_child]
    simp [Finset.sum_const, Finset.card_range, completionCount_of_length_eq ω k (s ++ [0]) (by simp [heq])]

end FdrsFormal.Modes.VariableRadix
