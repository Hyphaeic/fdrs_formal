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

# Prefix Weights Definition

This file defines the prefix weight function β_ω for variable radix systems.

## Mathematical Content (fdrs.md lines 5144-5147)

**Definition 58 (Prefix weights)**:
For a prefix s = (d₀, ..., d_{n-1}), the prefix weight is:

β_ω(s) := ∏_{i=0}^{|s|-1} ω(s_{<i})

This is the "odometer weight" - the cumulative product of radices up to prefix s.

## References

- fdrs.md, Phase 5-6, Section 2 (lines 5144-5147)
- DEPENDENCY_BASED_STRUCTURE.md, Modes/VariableRadix/PrefixWeights
- Paper: Fragment 5.4
-/

import FdrsFormal.Modes.VariableRadix.Basic.Basic

namespace FdrsFormal.Modes.VariableRadix

/-!
## Prefix Weight Function
-/

/--
**Definition 58**: The prefix weight β_ω(s).

β_ω(s) = ∏_{i=0}^{|s|-1} ω(s_{<i})

This is the cumulative product of radices along the path to s.

We compute this by "shifting" the radix law at each step:
β_ω([d₀, d₁, ...]) = ω([]) * β_{ω'}([d₁, ...])
where ω'(s) = ω([d₀] ++ s).
-/
def prefixWeight (ω : RadixLaw) : PrefixWord → ℕ
  | [] => 1
  | d :: ds =>
    -- ω([]) is the radix at the root, then shift the radix law
    let ω' : RadixLaw := {
      radix := fun s => ω.radix (d :: s)
      radix_ge_two := fun s => ω.radix_ge_two (d :: s)
    }
    ω.radix [] * prefixWeight ω' ds

/-!
## Basic Properties
-/

/-- Prefix weight of empty prefix is 1 -/
@[simp]
theorem prefixWeight_nil (ω : RadixLaw) : prefixWeight ω [] = 1 := by
  rfl

/-- Prefix weight is always positive -/
theorem prefixWeight_pos (ω : RadixLaw) (s : PrefixWord) : 0 < prefixWeight ω s := by
  induction s generalizing ω with
  | nil => simp [prefixWeight]
  | cons d ds ih =>
    simp only [prefixWeight]
    apply Nat.mul_pos (ω.radix_pos [])
    -- Apply IH to the shifted radix law
    exact ih (ω.shift d)

/-- Prefix weight of extension -/
theorem prefixWeight_append (ω : RadixLaw) (s : PrefixWord) (d : ℕ) :
    prefixWeight ω (s ++ [d]) = prefixWeight ω s * ω.radix s := by
  induction s generalizing ω with
  | nil =>
    -- LHS = prefixWeight ω [d] = ω.radix [] * 1 = ω.radix []
    -- RHS = 1 * ω.radix [] = ω.radix []
    simp [prefixWeight]
  | cons d₀ s' ih =>
    -- prefixWeight ω ((d₀ :: s') ++ [d]) = prefixWeight ω (d₀ :: s') * ω.radix (d₀ :: s')
    simp only [List.cons_append, prefixWeight]
    -- Goal now involves the inline struct. Use ih directly with conversion.
    -- The inline struct { radix := fun s => ω.radix (d₀ :: s), ... } is ω.shift d₀
    have h_shift : { radix := fun s => ω.radix (d₀ :: s),
                     radix_ge_two := fun s => ω.radix_ge_two (d₀ :: s) : RadixLaw } = ω.shift d₀ := rfl
    simp only [h_shift]
    rw [ih (ω.shift d₀)]
    -- Goal: ω.radix [] * (prefixWeight (ω.shift d₀) s' * (ω.shift d₀).radix s') =
    --       ω.radix [] * prefixWeight (ω.shift d₀) s' * ω.radix (d₀ :: s')
    simp only [RadixLaw.shift]
    ring

/-!
## Monotonicity Properties
-/

/-- Prefix weight is monotone in prefix length -/
theorem prefixWeight_mono (ω : RadixLaw) (s t : PrefixWord) (h : s <+: t) :
    prefixWeight ω s ≤ prefixWeight ω t := by
  -- If s <+: t, then t = s ++ u for some u
  obtain ⟨u, rfl⟩ := h
  -- Induction on u
  induction u generalizing s with
  | nil => simp
  | cons d u ih =>
    -- s ++ (d :: u) = (s ++ [d]) ++ u
    have heq : s ++ d :: u = (s ++ [d]) ++ u := by simp
    rw [heq]
    -- By IH: prefixWeight ω (s ++ [d]) ≤ prefixWeight ω ((s ++ [d]) ++ u)
    calc prefixWeight ω s
        ≤ prefixWeight ω (s ++ [d]) := by
          rw [prefixWeight_append]
          exact Nat.le_mul_of_pos_right _ (ω.radix_pos s)
      _ ≤ prefixWeight ω ((s ++ [d]) ++ u) := ih (s ++ [d])

/-- Strict monotonicity when extending -/
theorem prefixWeight_strictMono (ω : RadixLaw) (s : PrefixWord) (d : ℕ)
    (_hd : d < ω.radix s) :
    prefixWeight ω s < prefixWeight ω (s ++ [d]) := by
  rw [prefixWeight_append]
  -- Goal: prefixWeight ω s < prefixWeight ω s * ω.radix s
  -- Since ω.radix s ≥ 2 and prefixWeight ω s > 0
  have hpos : 0 < prefixWeight ω s := prefixWeight_pos ω s
  have hrad : 2 ≤ ω.radix s := ω.radix_ge_two s
  calc prefixWeight ω s
      = prefixWeight ω s * 1 := by ring
    _ < prefixWeight ω s * ω.radix s := by
        apply Nat.mul_lt_mul_of_pos_left
        · omega
        · exact hpos

/-!
## Relationship to Completion Count

Note: Theorems relating prefix weight to completion count are in
ArithmeticCylinders.lean to avoid circular dependencies with Encoding.
-/

end FdrsFormal.Modes.VariableRadix
