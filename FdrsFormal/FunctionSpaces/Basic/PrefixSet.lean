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

# Prefix Index Sets

This file defines the prefix index set Σ_L, which indexes cylinders at resolution L.

## Mathematical Content (fdrs.md lines 549-556)

**Definition 15 (Prefix Index Set)**: For L ≥ 1, define
  Σ_L := ∏_{i=0}^{L-1} D_i,  with |Σ_L| = B_L.

This is the set of all length-L prefixes (finite digit sequences).

## Implementation Notes

- PrefixSet L is a dependent type: the product of Fin (b i) for i < L
- Uses `Fin L → Fin (b i)` with appropriate typing constraints
- Cardinality is placeValue b L = B_L

## References

- fdrs.md, Section 1, Definition 15 (lines 549-556)
- THEOREM_MAPPING.md, FunctionSpaces/Basic section
-/

import FdrsFormal.Core.Primitives.RadixSeq
import FdrsFormal.Core.Primitives.PlaceValue
import FdrsFormal.Core.Finite.Bijection
import Mathlib.Data.Fintype.Pi

namespace FdrsFormal.FunctionSpaces.Basic

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite

/-!
## Prefix Index Set Definition
-/

/--
The prefix index set Σ_L: all length-L prefixes over the radix sequence b.

**fdrs.md Definition 15**: Σ_L := ∏_{i=0}^{L-1} D_i

This is the set of all valid digit sequences of length L, where the i-th digit
is in the range [0, b_i - 1].

Implementation: For a radix sequence b, a prefix of length L is a function
from Fin L to digits, where the i-th digit is in Fin (b i).
-/
def PrefixSet (b : RadixSeq) (L : ℕ) : Type :=
  (i : Fin L) → Fin (b i.val)

/-- Extensionality for PrefixSet: two prefixes are equal iff they agree at all positions. -/
@[ext]
theorem PrefixSet.ext {b : RadixSeq} {L : ℕ} {s t : PrefixSet b L}
    (h : ∀ i : Fin L, s i = t i) : s = t :=
  funext h

/--
Alternative formulation using dependent product (Pi type).
This makes the mathematical structure more explicit.
-/
def PrefixSet' (b : RadixSeq) (L : ℕ) : Type :=
  ∀ i : Fin L, Fin (b i.val)

/--
Equivalence between the two formulations.
-/
def prefixSetEquiv (b : RadixSeq) (L : ℕ) : PrefixSet b L ≃ PrefixSet' b L where
  toFun s i := s i
  invFun s i := s i
  left_inv _ := rfl
  right_inv _ := rfl

/-!
## Cardinality
-/

/--
PrefixSet is a finite type.
-/
instance prefixSetFintype (b : RadixSeq) (L : ℕ) : Fintype (PrefixSet b L) := by
  unfold PrefixSet
  infer_instance

/--
The cardinality of PrefixSet b L equals B_L = placeValue b L.

**fdrs.md**: |Σ_L| = B_L

This follows from the fact that we have b_i choices for each position i < L,
and the product is ∏_{i=0}^{L-1} b_i = B_L.
-/
theorem prefixSet_card (b : RadixSeq) (L : ℕ) :
    Fintype.card (PrefixSet b L) = placeValue b L := by
  -- PrefixSet b L = (i : Fin L) → Fin (b i.val)
  -- card of Pi type = product of cards
  unfold PrefixSet
  rw [Fintype.card_pi]
  -- Now need ∏ i : Fin L, card (Fin (b i.val)) = placeValue b L
  induction L with
  | zero =>
    simp [placeValue]
  | succ L ih =>
    rw [placeValue.succ, Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fintype.card_fin, Fin.val_last]
    -- Goal: (∏ x : Fin L, b ↑x) * b L = placeValue b L * b L
    -- ih: ∏ i : Fin L, Fintype.card (Fin (b ↑i)) = placeValue b L
    -- After simp, card (Fin (b ↑i)) = b ↑i
    have h : ∏ x : Fin L, b x.val = placeValue b L := by
      convert ih using 2
      simp [Fintype.card_fin]
    rw [h]

/-!
## Accessors and Constructors
-/

/--
Get the i-th digit from a prefix.
-/
def PrefixSet.digit {b : RadixSeq} {L : ℕ} (s : PrefixSet b L) (i : Fin L) : Fin (b i.val) :=
  s i

/--
The empty prefix (L = 0).
-/
def emptyPrefix (b : RadixSeq) : PrefixSet b 0 :=
  fun i => i.elim0

/--
Extend a prefix by one digit.
-/
def extendPrefix {b : RadixSeq} {L : ℕ} (s : PrefixSet b L) (d : Fin (b L)) :
    PrefixSet b (L + 1) :=
  Fin.lastCases d (fun i => s i)

/--
Truncate a prefix by removing the last digit.
-/
def truncatePrefix {b : RadixSeq} {L : ℕ} (s : PrefixSet b (L + 1)) : PrefixSet b L :=
  fun i => s (Fin.castSucc i)

/--
Get the last digit of a non-empty prefix.
-/
def lastDigit {b : RadixSeq} {L : ℕ} (s : PrefixSet b (L + 1)) : Fin (b L) :=
  s (Fin.last L)

/-!
## Residue Computation

The residue r_L(s) computes the natural number represented by a prefix.
-/

/--
The residue of a prefix: the natural number it represents.

**fdrs.md lines 282-290**: r_L(s) = Σ_{i=0}^{L-1} s_i · B_i

This is the "decode" function restricted to prefixes.
-/
def prefixResidue {b : RadixSeq} {L : ℕ} (s : PrefixSet b L) : ℕ :=
  Finset.sum (Finset.univ : Finset (Fin L)) fun i =>
    (s i).val * placeValue b i.val

/--
Residue of empty prefix is zero.
-/
theorem prefixResidue_empty (b : RadixSeq) : prefixResidue (emptyPrefix b) = 0 := by
  simp [prefixResidue, emptyPrefix]

/--
Residue is bounded by B_L.
-/
theorem prefixResidue_lt_placeValue {b : RadixSeq} {L : ℕ} (s : PrefixSet b L) :
    prefixResidue s < placeValue b L := by
  cases L with
  | zero =>
    -- Empty sum is 0 < 1 = placeValue b 0
    simp [prefixResidue, placeValue]
  | succ k =>
    -- Use sum_digits_lt from PlaceValue
    unfold prefixResidue
    -- Need to convert s to the right form for sum_digits_lt
    have h := placeValue.sum_digits_lt k (fun i => s i)
    convert h using 2

/--
The residue determines the prefix uniquely.

This connects to `digits_unique` from Core/Finite.
-/
theorem prefixResidue_injective (b : RadixSeq) (L : ℕ) :
    Function.Injective (prefixResidue (b := b) (L := L)) := by
  intro s t h
  cases L with
  | zero =>
    -- Empty prefixes: both are the unique function from Fin 0
    funext i
    exact i.elim0
  | succ k =>
    -- Use digits_unique: if residues are equal, digits are equal
    unfold prefixResidue at h
    have huniq := digits_unique (b := b) s t h
    exact huniq

/-!
## Prefix Comparison
-/

/--
Two prefixes agree if they represent the same digit sequence.
-/
def prefixAgree {b : RadixSeq} {L : ℕ} (s t : PrefixSet b L) : Prop :=
  ∀ i : Fin L, s i = t i

/--
Prefix agreement is an equivalence relation (actually just equality).
-/
theorem prefixAgree_iff_eq {b : RadixSeq} {L : ℕ} (s t : PrefixSet b L) :
    prefixAgree s t ↔ s = t := by
  constructor
  · intro h
    funext i
    exact h i
  · intro h
    simp [prefixAgree, h]

end FdrsFormal.FunctionSpaces.Basic
