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

# Radix Tree Structure

This file defines the rooted tree T_ω induced by a radix law.

## Mathematical Content (fdrs.md lines 3967-3968)

Interpretation: at prefix s, the next digit ranges over D_ω(s). This is exactly
a rooted tree T_ω whose node s has ω(s) children.

The tree structure:
- Root: empty prefix ε
- Children of node s: {s ++ [d] : d ∈ D_ω(s)}
- Node s has exactly ω(s) children

## References

- fdrs.md, Phase 5-6, Section 1.1 (lines 3967-3968)
-/

import FdrsFormal.Modes.VariableRadix.Basic.DigitAlphabet

namespace FdrsFormal.Modes.VariableRadix

/-!
## Tree Structure
-/

/-- Shift the radix law by prepending a digit to all prefixes -/
def RadixLaw.shift (ω : RadixLaw) (d : ℕ) : RadixLaw where
  radix := fun s => ω.radix (d :: s)
  radix_ge_two := fun s => ω.radix_ge_two (d :: s)

/--
A prefix s is valid under radix law ω if each digit is within bounds.

This recursively checks that for each position i, the digit s[i] is
a valid digit given the prefix s[0..i-1].
-/
def isValidPrefix (ω : RadixLaw) : PrefixWord → Prop
  | [] => True
  | d :: ds => isValidDigit ω [] d ∧ isValidPrefix (ω.shift d) ds

/-- Alternative formulation: check validity position by position -/
def isValidPrefix' (ω : RadixLaw) (s : PrefixWord) : Prop :=
  ∀ i (hi : i < s.length), s.get ⟨i, hi⟩ < ω.radix (s.take i)

/-- The empty prefix is always valid -/
theorem isValidPrefix'_nil (ω : RadixLaw) : isValidPrefix' ω [] := by
  intro i hi
  exact absurd hi (Nat.not_lt_zero i)

/-- Extending a valid prefix with a valid digit gives a valid prefix -/
theorem isValidPrefix'_append_singleton {ω : RadixLaw} {s : PrefixWord} {d : ℕ}
    (hs : isValidPrefix' ω s) (hd : d < ω.radix s) : isValidPrefix' ω (s ++ [d]) := by
  intro i hi
  have hlen : (s ++ [d]).length = s.length + 1 := by simp
  rw [hlen] at hi
  by_cases hcase : i < s.length
  · -- Position i is in the original prefix s
    have hi' : i < (s ++ [d]).length := by simp; omega
    have h_take : (s ++ [d]).take i = s.take i := by
      exact List.take_append_of_le_length (Nat.le_of_lt hcase)
    rw [h_take]
    -- Need to show (s ++ [d])[i] = s[i] when i < s.length
    conv_lhs => rw [show (s ++ [d]).get ⟨i, hi'⟩ = s.get ⟨i, hcase⟩ from by
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [List.getElem_append]
      split
      · rfl
      · omega]
    exact hs i hcase
  · -- Position i = s.length (the new digit)
    have hi_eq : i = s.length := Nat.eq_of_lt_succ_of_not_lt hi hcase
    subst hi_eq
    have hi' : s.length < (s ++ [d]).length := by simp
    have h_take : (s ++ [d]).take s.length = s := by simp
    rw [h_take]
    -- Need to show (s ++ [d])[s.length] = d
    conv_lhs => rw [show (s ++ [d]).get ⟨s.length, hi'⟩ = d from by
      rw [List.get_eq_getElem]
      simp only [List.getElem_append, Nat.lt_irrefl, ↓reduceDIte, Nat.sub_self,
        List.getElem_cons_zero]]
    exact hd

/-!
## Children and Parent Relations
-/

/-- The children of a valid prefix s are s ++ [d] for each valid digit d -/
def children (ω : RadixLaw) (s : PrefixWord) : Finset PrefixWord :=
  Finset.image (fun d : Fin (ω.radix s) => s ++ [d.val]) Finset.univ

/-- The number of children equals the radix -/
theorem children_card (ω : RadixLaw) (s : PrefixWord) :
    (children ω s).card = ω.radix s := by
  simp only [children]
  rw [Finset.card_image_of_injective]
  · simp only [Finset.card_fin]
  · intro a b hab
    simp only [List.append_cancel_left_eq, List.cons.injEq, and_true] at hab
    exact Fin.ext hab

/-- The parent of a nonempty prefix -/
def parent (s : PrefixWord) : Option PrefixWord :=
  match s with
  | [] => none
  | _ :: _ => some s.dropLast

/-- The root has no parent -/
theorem parent_nil : parent ([] : PrefixWord) = none := rfl

/-- A nonempty prefix has a parent -/
theorem parent_cons (d : ℕ) (ds : PrefixWord) :
    parent (d :: ds) = some (d :: ds).dropLast := rfl

end FdrsFormal.Modes.VariableRadix
