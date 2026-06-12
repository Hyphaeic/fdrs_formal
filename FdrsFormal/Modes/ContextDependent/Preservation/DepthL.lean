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

# Depth-L Structure Preservation

This file defines structure-preserving context transitions.

## Mathematical Content (fdrs.md lines 5641-5649)

**Definition 93 (Structure-preserving context transition)**:
A context transition c → c' is **structure-preserving at depth L** if:

∀ s ∈ Σ_L: β_c(s) = β_{c'}(s)

**Interpretation**: Cylinder volumes at depth L are unchanged;
only structure at depth > L may differ.

## References

- fdrs.md, Phase 7, Section 7.4 (lines 5641-5649)
-/

import FdrsFormal.Modes.ContextDependent.Realization.Realization

namespace FdrsFormal.Modes.ContextDependent

open FdrsFormal.Modes.VariableRadix

/-!
## Structure-Preserving Transitions
-/

/--
**Definition 93**: A context transition is structure-preserving at depth L.

Radix values agree at depth ≤ L, which implies cylinder volumes (prefix weights) are unchanged.
-/
def isStructurePreserving {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) (c c' : C) (L : ℕ) : Prop :=
  ∀ s : PrefixWord, s.length ≤ L →
    (𝒮.radixAt c).radix s = (𝒮.radixAt c').radix s

/-- Structure preservation implies prefixWeight agreement -/
theorem structurePreserving_prefixWeight {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) (c c' : C) (L : ℕ)
    (h : isStructurePreserving 𝒮 c c' L)
    (s : PrefixWord) (hs : s.length ≤ L) :
    prefixWeight (𝒮.radixAt c) s = prefixWeight (𝒮.radixAt c') s := by
  -- prefixWeight s = ∏_{i < s.length} radix (s.take i)
  -- All these prefixes have length < s.length ≤ L, so radix agrees
  induction s using List.reverseRecOn with
  | nil => simp [prefixWeight]
  | append_singleton ds d ih =>
    -- prefixWeight (ds ++ [d]) = prefixWeight ds * radix ds
    rw [prefixWeight_append, prefixWeight_append]
    have hds : ds.length ≤ L := by simp at hs; omega
    rw [ih hds]
    congr 1
    exact h ds hds

/-- Structure preservation is reflexive -/
theorem structurePreserving_refl {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) (c : C) (L : ℕ) :
    isStructurePreserving 𝒮 c c L := by
  intro s _
  rfl

/-- Structure preservation is symmetric -/
theorem structurePreserving_symm {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) (c c' : C) (L : ℕ)
    (h : isStructurePreserving 𝒮 c c' L) :
    isStructurePreserving 𝒮 c' c L := by
  intro s hs
  exact (h s hs).symm

/-- Structure preservation is transitive -/
theorem structurePreserving_trans {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) (c₁ c₂ c₃ : C) (L : ℕ)
    (h₁₂ : isStructurePreserving 𝒮 c₁ c₂ L)
    (h₂₃ : isStructurePreserving 𝒮 c₂ c₃ L) :
    isStructurePreserving 𝒮 c₁ c₃ L := by
  intro s hs
  rw [h₁₂ s hs, h₂₃ s hs]

/-!
## Depth-L Equivalence
-/

/-- Two contexts are depth-L equivalent if they preserve structure at depth L -/
def depthLEquivalent {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) (c c' : C) (L : ℕ) : Prop :=
  isStructurePreserving 𝒮 c c' L

/-- Depth-L equivalence is an equivalence relation -/
theorem depthLEquivalent_equivalence {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) (L : ℕ) :
    Equivalence (fun c c' => depthLEquivalent 𝒮 c c' L) :=
  ⟨fun c => structurePreserving_refl 𝒮 c L,
   fun h => structurePreserving_symm 𝒮 _ _ L h,
   fun h₁ h₂ => structurePreserving_trans 𝒮 _ _ _ L h₁ h₂⟩

/-!
## Radix Agreement
-/

/-- Structure preservation implies radix agreement (now direct from definition) -/
theorem structurePreserving_radix_agree {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) (c c' : C) (L : ℕ)
    (h : isStructurePreserving 𝒮 c c' L)
    (s : PrefixWord) (hs : s.length ≤ L) :
    (𝒮.radixAt c).radix s = (𝒮.radixAt c').radix s :=
  h s hs

/-- Completion counts agree for structure-preserving transitions -/
theorem structurePreserving_completionCount {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) (c c' : C) (k : ℕ) (L : ℕ)
    (hL : L ≤ k)
    (h : isStructurePreserving 𝒮 c c' L) :
    completionCount (𝒮.radixAt c) L ([] : PrefixWord) =
      completionCount (𝒮.radixAt c') L ([] : PrefixWord) := by
  -- Completion count only depends on radix values for prefixes of length < L
  -- We have radix agreement for all s with length < L
  -- Prove by induction that completionCount agrees for all prefixes
  suffices hsuff : ∀ s : PrefixWord, s.length ≤ L + 1 →
      completionCount (𝒮.radixAt c) L s = completionCount (𝒮.radixAt c') L s by
    exact hsuff ([] : PrefixWord) (Nat.zero_le _)
  intro s hs
  -- Induction on remaining depth L + 1 - s.length
  obtain ⟨n, hn⟩ : ∃ n, n = L + 1 - s.length := ⟨_, rfl⟩
  induction n using Nat.strongRecOn generalizing s with
  | _ n ih =>
    by_cases heq : s.length = L + 1
    · -- Base case: s is at full depth, completionCount = 1
      rw [completionCount_of_length_eq (𝒮.radixAt c) L s heq]
      rw [completionCount_of_length_eq (𝒮.radixAt c') L s heq]
    · -- Recursive case: s.length < L + 1
      have hlt : s.length < L + 1 := Nat.lt_of_le_of_ne hs heq
      rw [completionCount_rec (𝒮.radixAt c) L s hlt]
      rw [completionCount_rec (𝒮.radixAt c') L s hlt]
      -- Radix agreement for s (length ≤ L, since s.length < L + 1)
      have hradix : (𝒮.radixAt c).radix s = (𝒮.radixAt c').radix s :=
        structurePreserving_radix_agree 𝒮 c c' L h s (by omega)
      rw [hradix]
      apply Finset.sum_congr rfl
      intro d _
      -- Apply IH
      have hle' : (s ++ [d]).length ≤ L + 1 := by simp; omega
      have hdec : L + 1 - (s ++ [d]).length < n := by simp at hn ⊢; omega
      exact ih (L + 1 - (s ++ [d]).length) hdec (s ++ [d]) hle' rfl

end FdrsFormal.Modes.ContextDependent
