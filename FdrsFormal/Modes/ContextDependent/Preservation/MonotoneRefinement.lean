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

# Monotone Context Refinement

This file defines monotone refining context transitions.

## Mathematical Content (fdrs.md lines 5672-5694)

**Definition 94 (Monotone context refinement)**:
A context transition c → c' is **monotone refining** if:

∀ s: β_c(s) ≤ β_{c'}(s)

**Proposition 98 (Metric dominance under refinement)**:
If c → c' is monotone refining, then:

δ_c(x, y) ≥ δ_{c'}(x, y)

for all x, y. The finer metric δ_{c'} dominates δ_c.

## References

- fdrs.md, Phase 7, Section 7.4 (lines 5672-5694)
-/

import FdrsFormal.Modes.ContextDependent.Preservation.DepthL
import FdrsFormal.Modes.VariableRadix.MetricComparison.Definition

namespace FdrsFormal.Modes.ContextDependent

open FdrsFormal.Modes.VariableRadix

/-!
## Monotone Refinement
-/

/--
**Definition 94**: A context transition is monotone refining.

Prefix weights can only increase (metric becomes finer).
-/
def isMonotoneRefining {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) (c c' : C) : Prop :=
  ∀ s : PrefixWord, prefixWeight (𝒮.radixAt c) s ≤ prefixWeight (𝒮.radixAt c') s

/-- Monotone refinement is reflexive -/
theorem monotoneRefining_refl {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) (c : C) :
    isMonotoneRefining 𝒮 c c := by
  intro s
  exact Nat.le_refl _

/-- Monotone refinement is transitive -/
theorem monotoneRefining_trans {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) (c₁ c₂ c₃ : C)
    (h₁₂ : isMonotoneRefining 𝒮 c₁ c₂)
    (h₂₃ : isMonotoneRefining 𝒮 c₂ c₃) :
    isMonotoneRefining 𝒮 c₁ c₃ := by
  intro s
  exact Nat.le_trans (h₁₂ s) (h₂₃ s)

/-!
## Metric Dominance
-/

/--
**Proposition 98**: Monotone refinement implies metric dominance.

If c → c' is monotone refining, then δ_c(x,y) ≥ δ_{c'}(x,y).
-/
theorem monotoneRefining_metric_dominance {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) (c c' : C)
    (h : isMonotoneRefining 𝒮 c c') :
    metricDominance (𝒮.radixAt c) (𝒮.radixAt c') :=
  -- isMonotoneRefining and metricDominance are both ∀ s, prefixWeight ω s ≤ prefixWeight ω' s
  h

/-- If radix values are pointwise ≤, then prefixWeights are pointwise ≤ -/
theorem prefixWeight_mono_of_radix_le (ω ω' : RadixLaw)
    (h : ∀ s, ω.radix s ≤ ω'.radix s) (s : PrefixWord) :
    prefixWeight ω s ≤ prefixWeight ω' s := by
  -- Use reverse induction: prefixWeight (ds ++ [d]) = prefixWeight ds * radix ds
  induction s using List.reverseRecOn with
  | nil => simp [prefixWeight]
  | append_singleton ds d ih =>
    rw [prefixWeight_append, prefixWeight_append]
    exact Nat.mul_le_mul ih (h ds)

/-- Radix increase implies finer metric -/
theorem radix_increase_finer_metric {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) (c c' : C)
    (hradix : ∀ s, (𝒮.radixAt c).radix s ≤ (𝒮.radixAt c').radix s) :
    isMonotoneRefining 𝒮 c c' := by
  intro s
  exact prefixWeight_mono_of_radix_le (𝒮.radixAt c) (𝒮.radixAt c') hradix s

/-!
## Refinement Chains
-/

/-- A refinement chain is a sequence of monotone refining transitions -/
def isRefinementChain {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) (contexts : List C) : Prop :=
  ∀ i : ℕ, (hi : i + 1 < contexts.length) →
    isMonotoneRefining 𝒮
      (contexts.get ⟨i, Nat.lt_of_succ_lt hi⟩)
      (contexts.get ⟨i + 1, hi⟩)

/-- A refinement chain composes to a single refinement -/
theorem refinementChain_composed {C E : Type*}
    [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) (contexts : List C)
    (hchain : isRefinementChain 𝒮 contexts)
    (hne : contexts ≠ []) :
    isMonotoneRefining 𝒮 (contexts.head hne) (contexts.getLast hne) := by
  -- Induction on the list
  induction contexts with
  | nil => exact absurd rfl hne
  | cons hd rest ih =>
    cases rest with
    | nil =>
      -- Single element: head = getLast, use reflexivity
      simp only [List.head_cons, List.getLast_singleton]
      exact monotoneRefining_refl 𝒮 hd
    | cons c₁ rest' =>
      -- At least two elements: use transitivity
      simp only [List.head_cons]
      have hne' : c₁ :: rest' ≠ [] := List.cons_ne_nil _ _
      have hchain' : isRefinementChain 𝒮 (c₁ :: rest') := by
        intro i hi
        exact hchain (i + 1) (by simp at hi ⊢; omega)
      have hrec := ih hchain' hne'
      -- First step: hd → c₁
      have h01 : isMonotoneRefining 𝒮 hd c₁ := hchain 0 (by simp)
      -- getLast (hd :: c₁ :: rest') = getLast (c₁ :: rest')
      have hlast : (hd :: c₁ :: rest').getLast hne = (c₁ :: rest').getLast hne' := by
        simp only [List.getLast_cons hne']
      rw [hlast]
      exact monotoneRefining_trans 𝒮 hd c₁ _ h01 hrec

end FdrsFormal.Modes.ContextDependent
