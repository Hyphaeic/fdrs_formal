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

# THEOREM F: Depth-L Operators Preserved

This file proves THEOREM F: structure-preserving transitions preserve L-local operators.

## Mathematical Content (fdrs.md lines 5651-5670)

**Theorem 47 (Depth-L operators preserved)**:
If transition c → c' is structure-preserving at depth L, then:

1. All L-local gates remain valid (cylinder boundaries unchanged)
2. Ultrametric δ_c agrees with δ_{c'} on Σ_L-indexed points
3. Projection operators P_L commute with context switch

**Proof**:
(1) Gates depend only on Σ_L partition, which is combinatorial.
(2) For any x,y with |lcp(x,y)| ≤ L: δ_c(x,y) = β_c(lcp)^{-1} = β_{c'}(lcp)^{-1} = δ_{c'}(x,y).
(3) P_L averages over suffix within each depth-L cylinder. Since structure is preserved, P_L commutes.

**Implication**: Can change radix law for depth > L without invalidating depth-L computations.

## References

- fdrs.md, Phase 7, Section 7.4 (lines 5651-5670)
- DEPENDENCY_BASED_STRUCTURE.md, Modes/ContextDependent/Preservation
- Paper: THEOREM F
-/

import FdrsFormal.Modes.ContextDependent.Preservation.MonotoneRefinement

namespace FdrsFormal.Modes.ContextDependent

open FdrsFormal.Modes.VariableRadix

/-!
## THEOREM F: Depth-L Operators Preserved
-/

/--
**THEOREM F, Part 1**: L-local gates remain valid under structure-preserving transition.

Gates are defined by cylinder boundaries at depth L, which are unchanged.
The cylinder volumes (prefixWeights) at depth L are preserved.
-/
theorem theoremF_gates_valid {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) (c c' : C) (L : ℕ)
    (h : isStructurePreserving 𝒮 c c' L) :
    -- Gates at depth L for c are valid for c'
    -- This is essentially: the cylinder partition at depth L is the same
    -- The cylinder boundaries (prefixWeights) are preserved
    ∀ s : PrefixWord, s.length = L →
      prefixWeight (𝒮.radixAt c) s = prefixWeight (𝒮.radixAt c') s := by
  intro s hs
  exact structurePreserving_prefixWeight 𝒮 c c' L h s (Nat.le_of_eq hs)

/--
**THEOREM F, Part 2**: Ultrametric agrees on depth-L points.

For points whose LCP has length ≤ L, the distance is the same in both contexts.
-/
theorem theoremF_ultrametric_agrees {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) (c c' : C) (L : ℕ)
    (h : isStructurePreserving 𝒮 c c' L)
    (s : PrefixWord) (hs : s.length ≤ L) :
    variableRadixRadius (𝒮.radixAt c) s = variableRadixRadius (𝒮.radixAt c') s := by
  -- variableRadixRadius = (prefixWeight)⁻¹
  -- Structure preservation implies prefixWeight is equal for s.length ≤ L
  unfold variableRadixRadius
  rw [structurePreserving_prefixWeight 𝒮 c c' L h s hs]

/--
**THEOREM F, Part 3**: Projection operators commute with context switch.

P_L computed in context c equals P_L computed in context c'.
-/
theorem theoremF_projection_commutes {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) (c c' : C) (L : ℕ)
    (h : isStructurePreserving 𝒮 c c' L) :
    -- Block sizes at depth L are the same
    blockSize (𝒮.radixAt c) L ([] : PrefixWord) =
      blockSize (𝒮.radixAt c') L ([] : PrefixWord) := by
  unfold blockSize
  by_cases hL : 0 < L
  · -- L > 0, so [].length < L and radix [] > 0
    have h1 : ([] : PrefixWord).length < L := by simp [hL]
    have h2 : 0 < (𝒮.radixAt c).radix ([] : PrefixWord) :=
      (𝒮.radixAt c).radix_pos ([] : PrefixWord)
    have h2' : 0 < (𝒮.radixAt c').radix ([] : PrefixWord) :=
      (𝒮.radixAt c').radix_pos ([] : PrefixWord)
    -- Reduce the dite conditions
    rw [dif_pos ⟨h1, h2⟩, dif_pos ⟨h1, h2'⟩]
    -- Need: completionCount_c L [0] = completionCount_c' L [0]
    suffices hsuff : ∀ s : PrefixWord, s.length ≤ L + 1 →
        completionCount (𝒮.radixAt c) L s = completionCount (𝒮.radixAt c') L s by
      exact hsuff ([0] : PrefixWord) (by simp only [List.length_singleton]; omega)
    intro s hs
    obtain ⟨n, hn⟩ : ∃ n, n = L + 1 - s.length := ⟨_, rfl⟩
    induction n using Nat.strongRecOn generalizing s with
    | _ n ih =>
      by_cases heq : s.length = L + 1
      · rw [completionCount_of_length_eq (𝒮.radixAt c) L s heq]
        rw [completionCount_of_length_eq (𝒮.radixAt c') L s heq]
      · have hlt : s.length < L + 1 := Nat.lt_of_le_of_ne hs heq
        rw [completionCount_rec (𝒮.radixAt c) L s hlt]
        rw [completionCount_rec (𝒮.radixAt c') L s hlt]
        have hradix : (𝒮.radixAt c).radix s = (𝒮.radixAt c').radix s :=
          structurePreserving_radix_agree 𝒮 c c' L h s (by omega)
        rw [hradix]
        apply Finset.sum_congr rfl
        intro d _
        have hle' : (s ++ [d]).length ≤ L + 1 := by simp; omega
        have hdec : L + 1 - (s ++ [d]).length < n := by simp at hn ⊢; omega
        exact ih (L + 1 - (s ++ [d]).length) hdec (s ++ [d]) hle' rfl
  · -- L = 0, blockSize = 1 for both
    simp only [Nat.not_lt, Nat.le_zero] at hL
    simp only [List.length_nil, hL, Nat.lt_irrefl, false_and, ↓reduceDIte]

/-!
## Complete THEOREM F Statement
-/

/--
**THEOREM F (Complete)**: Structure-preserving transitions preserve depth-L structure.

All depth-L operators (gates, projections, metric structure) are invariant.
-/
theorem theoremF_complete {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) (c c' : C) (L : ℕ)
    (h : isStructurePreserving 𝒮 c c' L) :
    -- 1. Gates valid (cylinder boundaries/prefixWeights at depth L are the same)
    (∀ s : PrefixWord, s.length = L →
      prefixWeight (𝒮.radixAt c) s = prefixWeight (𝒮.radixAt c') s) ∧
    -- 2. Metric agrees
    (∀ s : PrefixWord, s.length ≤ L →
      variableRadixRadius (𝒮.radixAt c) s = variableRadixRadius (𝒮.radixAt c') s) ∧
    -- 3. Projections commute
    (blockSize (𝒮.radixAt c) L ([] : PrefixWord) =
      blockSize (𝒮.radixAt c') L ([] : PrefixWord)) :=
  ⟨theoremF_gates_valid 𝒮 c c' L h,
   theoremF_ultrametric_agrees 𝒮 c c' L h,
   theoremF_projection_commutes 𝒮 c c' L h⟩

/-!
## Implication: Safe Context Changes
-/

/-- Can safely change radix at depth > L without affecting depth-L computations -/
theorem safe_deep_change {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) (c c' : C) (L : ℕ)
    (h : isStructurePreserving 𝒮 c c' L)
    (computation_depth : ℕ) (hdepth : computation_depth ≤ L) :
    -- Any computation at depth ≤ L gives the same result
    completionCount (𝒮.radixAt c) computation_depth ([] : PrefixWord) =
      completionCount (𝒮.radixAt c') computation_depth ([] : PrefixWord) := by
  -- completionCount only depends on radix values for prefixes of length < computation_depth
  -- Structure preservation at L ≥ computation_depth ensures these radix values match
  suffices hsuff : ∀ s : PrefixWord, s.length ≤ computation_depth + 1 →
      completionCount (𝒮.radixAt c) computation_depth s =
        completionCount (𝒮.radixAt c') computation_depth s by
    exact hsuff ([] : PrefixWord) (Nat.zero_le _)
  intro s hs
  obtain ⟨n, hn⟩ : ∃ n, n = computation_depth + 1 - s.length := ⟨_, rfl⟩
  induction n using Nat.strongRecOn generalizing s with
  | _ n ih =>
    by_cases heq : s.length = computation_depth + 1
    · rw [completionCount_of_length_eq (𝒮.radixAt c) computation_depth s heq]
      rw [completionCount_of_length_eq (𝒮.radixAt c') computation_depth s heq]
    · have hlt : s.length < computation_depth + 1 := Nat.lt_of_le_of_ne hs heq
      rw [completionCount_rec (𝒮.radixAt c) computation_depth s hlt]
      rw [completionCount_rec (𝒮.radixAt c') computation_depth s hlt]
      have hradix : (𝒮.radixAt c).radix s = (𝒮.radixAt c').radix s :=
        structurePreserving_radix_agree 𝒮 c c' L h s (by omega)
      rw [hradix]
      apply Finset.sum_congr rfl
      intro d _
      have hle' : (s ++ [d]).length ≤ computation_depth + 1 := by simp; omega
      have hdec : computation_depth + 1 - (s ++ [d]).length < n := by simp at hn ⊢; omega
      exact ih (computation_depth + 1 - (s ++ [d]).length) hdec (s ++ [d]) hle' rfl

end FdrsFormal.Modes.ContextDependent
