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

# Variable Radix Spaces

This file defines the finite and infinite variable-radix spaces R^{(k)}_ω and R^{(∞)}_ω.

## Mathematical Content (fdrs.md lines 3971-3992)

**Definition 57 (Finite depth space)**:
Fix depth k ≥ 0. Define the finite variable-radix space:
  R^{(k)}_ω := {τ = (d_0, ..., d_k) : d_i ∈ D_ω(τ_{<i}) for all i}

where τ_{<i} := (d_0, ..., d_{i-1}) is the length-i prefix.

So R^{(k)}_ω is the set of root-to-level-k paths in T_ω.

**Definition 72 (Infinite depth space)**:
  R^{(∞)}_ω := {τ = (d_0, d_1, ...) : d_i ∈ D_ω(τ_{<i}) for all i}

This is the boundary/path space of the rooted tree T_ω.

## References

- fdrs.md, Phase 5-6, Section 1.1-1.2 (lines 3971-3992)
-/

import FdrsFormal.Modes.VariableRadix.Basic.TreeStructure

namespace FdrsFormal.Modes.VariableRadix

/-!
## Finite Variable-Radix Space
-/

/--
A finite variable-radix sequence of depth k.

**fdrs.md Definition 57**: R^{(k)}_ω = {τ = (d_0, ..., d_k) : d_i ∈ D_ω(τ_{<i})}

This is a dependent type: the digit at position i depends on all previous digits.
We represent this as a valid prefix of length k+1.
-/
structure FiniteVariableSpace (ω : RadixLaw) (k : ℕ) where
  /-- The underlying digit sequence -/
  digits : PrefixWord
  /-- The sequence has the correct length -/
  length_eq : digits.length = k + 1
  /-- Each digit is valid given its prefix -/
  valid : isValidPrefix' ω digits

namespace FiniteVariableSpace

variable {ω : RadixLaw} {k : ℕ}

/-- Get the digit at position i -/
def digitAt (τ : FiniteVariableSpace ω k) (i : Fin (k + 1)) : ℕ :=
  τ.digits.get ⟨i.val, by rw [τ.length_eq]; exact i.isLt⟩

/-- The prefix of length L -/
def getPrefix (τ : FiniteVariableSpace ω k) (L : ℕ) (hL : L ≤ k + 1) : PrefixWord :=
  τ.digits.take L

/-- Two finite sequences are equal iff their digits are equal -/
@[ext]
theorem ext {τ σ : FiniteVariableSpace ω k} (h : τ.digits = σ.digits) : τ = σ := by
  cases τ; cases σ; simp only at h; subst h; rfl

/-- The digit at each position is bounded by the radix at that prefix -/
theorem digitAt_lt (τ : FiniteVariableSpace ω k) (i : Fin (k + 1)) :
    τ.digitAt i < ω.radix (τ.getPrefix i.val (Nat.le_of_lt i.isLt)) := by
  simp only [digitAt, getPrefix]
  have hi : i.val < τ.digits.length := by rw [τ.length_eq]; exact i.isLt
  exact τ.valid i.val hi

end FiniteVariableSpace

/-!
## Infinite Variable-Radix Space
-/

/--
An infinite variable-radix sequence.

**fdrs.md Definition 72**: R^{(∞)}_ω = {τ = (d_0, d_1, ...) : d_i ∈ D_ω(τ_{<i})}

This is the boundary of the tree T_ω: infinite paths from the root.
-/
structure InfiniteVariableSpace (ω : RadixLaw) where
  /-- The digit at each position -/
  digit : ℕ → ℕ
  /-- Each digit is valid given its prefix -/
  valid : ∀ i, digit i < ω.radix (List.ofFn (fun j : Fin i => digit j.val))

namespace InfiniteVariableSpace

variable {ω : RadixLaw}

/-- Get the prefix of length L as a PrefixWord -/
def getPrefix (τ : InfiniteVariableSpace ω) (L : ℕ) : PrefixWord :=
  List.ofFn (fun i : Fin L => τ.digit i.val)

/-- The prefix has the expected length -/
theorem getPrefix_length (τ : InfiniteVariableSpace ω) (L : ℕ) :
    (τ.getPrefix L).length = L := by simp [getPrefix]

/-- Any prefix of an infinite sequence is a valid prefix -/
theorem getPrefix_valid (τ : InfiniteVariableSpace ω) (n : ℕ) :
    isValidPrefix' ω (τ.getPrefix n) := by
  intro i hi
  simp only [getPrefix, List.length_ofFn] at hi ⊢
  simp only [List.get_eq_getElem, List.getElem_ofFn]
  -- The prefix of length i is List.ofFn (fun j : Fin i => τ.digit j)
  have h_take : (List.ofFn (fun j : Fin n => τ.digit j.val)).take i =
      List.ofFn (fun j : Fin i => τ.digit j.val) := by
    apply List.ext_getElem
    · simp [Nat.min_eq_left (Nat.le_of_lt hi)]
    · intro m hm _
      simp only [List.getElem_take, List.getElem_ofFn]
  rw [h_take]
  exact τ.valid i

/-- Two infinite sequences are equal iff all digits are equal -/
@[ext]
theorem ext {τ σ : InfiniteVariableSpace ω} (h : ∀ i, τ.digit i = σ.digit i) : τ = σ := by
  cases τ; cases σ; simp only at h
  congr; ext i; exact h i

/-- Truncate an infinite sequence to depth k -/
def truncate (τ : InfiniteVariableSpace ω) (k : ℕ) : FiniteVariableSpace ω k where
  digits := τ.getPrefix (k + 1)
  length_eq := τ.getPrefix_length (k + 1)
  valid := by
    intro i hi
    simp only [getPrefix] at hi ⊢
    simp only [List.length_ofFn] at hi
    -- Goal: List.ofFn(fun j => τ.digit j)[i] < ω.radix (List.ofFn(fun j => τ.digit j).take i)
    -- Use the fact that taking i elements and getting the i-th element work as expected
    have hi' : i < (k + 1) := hi
    rw [List.get_eq_getElem]
    simp only [List.getElem_ofFn]
    -- Now goal is: τ.digit i < ω.radix (...)
    -- The prefix of length i is List.ofFn (fun j : Fin i => τ.digit j)
    have h_take : (List.ofFn (fun j : Fin (k + 1) => τ.digit j.val)).take i =
        List.ofFn (fun j : Fin i => τ.digit j.val) := by
      apply List.ext_getElem
      · simp [Nat.min_eq_left (Nat.le_of_lt hi')]
      · intro n h1 h2
        simp only [List.getElem_take, List.getElem_ofFn]
    rw [h_take]
    exact τ.valid i

end InfiniteVariableSpace

/-!
## Relationship Between Spaces
-/

/-- Helper: extend a valid prefix with zeros -/
private def extendWithZeros (ω : RadixLaw) (s : PrefixWord) (n : ℕ) : PrefixWord :=
  match n with
  | 0 => s
  | n + 1 => extendWithZeros ω (s ++ [0]) n

/-- Extended prefix with zeros has the right length -/
private theorem extendWithZeros_length (ω : RadixLaw) (s : PrefixWord) (n : ℕ) :
    (extendWithZeros ω s n).length = s.length + n := by
  induction n generalizing s with
  | zero => simp [extendWithZeros]
  | succ n ih =>
    simp only [extendWithZeros, ih, List.length_append, List.length_singleton]
    omega

/-- Extended prefix with zeros is valid if original is valid -/
private theorem extendWithZeros_valid (ω : RadixLaw) (s : PrefixWord) (n : ℕ)
    (hs : isValidPrefix' ω s) : isValidPrefix' ω (extendWithZeros ω s n) := by
  induction n generalizing s with
  | zero => simp [extendWithZeros]; exact hs
  | succ n ih =>
    simp only [extendWithZeros]
    apply ih
    -- Need to show isValidPrefix' ω (s ++ [0])
    apply isValidPrefix'_append_singleton hs
    exact ω.radix_pos s

/-- Extended prefix with zeros preserves the original as a prefix -/
private theorem extendWithZeros_take (ω : RadixLaw) (s : PrefixWord) (n : ℕ) :
    (extendWithZeros ω s n).take s.length = s := by
  induction n generalizing s with
  | zero => simp [extendWithZeros]
  | succ n ih =>
    simp only [extendWithZeros]
    -- Goal: (extendWithZeros ω (s ++ [0]) n).take s.length = s
    -- By IH: (extendWithZeros ω (s ++ [0]) n).take (s ++ [0]).length = s ++ [0]
    have h1 : (extendWithZeros ω (s ++ [0]) n).take (s ++ [0]).length = s ++ [0] := ih (s ++ [0])
    -- Taking s.length elements: first take (s.length + 1) then take s.length
    have h2 : s.length ≤ (s ++ [0]).length := by simp
    have h3 : (extendWithZeros ω (s ++ [0]) n).take s.length =
        ((extendWithZeros ω (s ++ [0]) n).take (s ++ [0]).length).take s.length := by
      rw [List.take_take]
      congr 1
      simp [Nat.min_eq_left h2]
    rw [h3, h1]
    simp

/-- Embedding of finite space into a larger finite space by padding with zeros -/
def FiniteVariableSpace.embed {ω : RadixLaw} {k k' : ℕ}
    (τ : FiniteVariableSpace ω k) (hk : k < k') :
    { σ : FiniteVariableSpace ω k' // σ.getPrefix (k + 1) (Nat.lt_succ_of_lt hk) = τ.digits } := by
  -- Extend τ.digits with (k' - k) zeros
  let extended := extendWithZeros ω τ.digits (k' - k)
  have hlen : extended.length = k' + 1 := by
    rw [extendWithZeros_length, τ.length_eq]
    omega
  have hvalid : isValidPrefix' ω extended := extendWithZeros_valid ω τ.digits (k' - k) τ.valid
  refine ⟨⟨extended, hlen, hvalid⟩, ?_⟩
  simp only [getPrefix]
  -- Need: (extendWithZeros ω τ.digits (k' - k)).take (k + 1) = τ.digits
  have h : τ.digits.length = k + 1 := τ.length_eq
  rw [← h]
  exact extendWithZeros_take ω τ.digits (k' - k)

/--
The cardinality of the finite space.

This counts the number of valid paths of length k+1 in the tree T_ω.
For k=0, it's just ω([]) (the number of valid first digits).
For k+1, we sum over all valid first digits d the cardinality of the subtree rooted at d.
-/
def FiniteVariableSpace.card (ω : RadixLaw) : ℕ → ℕ
  | 0 => ω.radix []
  | k + 1 => Finset.sum (Finset.range (ω.radix [])) fun d => card (ω.shift d) k

end FdrsFormal.Modes.VariableRadix
