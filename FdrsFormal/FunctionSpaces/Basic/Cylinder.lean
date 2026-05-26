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

# Cylinder Sets

This file defines cylinder sets U(s) in the completed radix space R̂.

## Mathematical Content (fdrs.md lines 557-563)

**Definition 16 (Cylinders)**: For s = (s_0, ..., s_{L-1}) ∈ Σ_L, define the length-L cylinder
  U(s) := {x ∈ R̂ : x_i = s_i for 0 ≤ i < L}.

The family {U(s) : s ∈ Σ_L} is a partition of R̂ into B_L clopen sets.

## Implementation Notes

- Cylinders are defined on CompletedSpace (all infinite sequences)
- Each cylinder is a clopen set in the ultrametric topology
- Cylinders at level L partition the space into B_L disjoint sets
- This connects to Topology/Ultrametric/Definition.lean cylinder definition

## References

- fdrs.md, Section 1, Definition 16 (lines 557-563)
- THEOREM_MAPPING.md, FunctionSpaces/Basic section
-/

import FdrsFormal.FunctionSpaces.Basic.PrefixSet
import FdrsFormal.Core.Infinite.DirectLimit

namespace FdrsFormal.FunctionSpaces.Basic

open FdrsFormal.Core.Primitives FdrsFormal.Core.Infinite

/-!
## Cylinder Set Definition
-/

/--
A cylinder set U(s) is the set of all completed sequences whose first L digits
match the prefix s.

**fdrs.md Definition 16**: U(s) := {x ∈ R̂ : x_i = s_i for 0 ≤ i < L}
-/
def cylinderSet (b : RadixSeq) (L : ℕ) (s : PrefixSet b L) : Set (CompletedSpace b) :=
  {x : CompletedSpace b | ∀ i : Fin L, x i.val = s i}

/--
Alternative notation-friendly definition using prefix projection.
-/
def cylinderSet' (b : RadixSeq) (L : ℕ) (s : PrefixSet b L) : Set (CompletedSpace b) :=
  {x : CompletedSpace b | (fun i : Fin L => x i.val) = s}

/--
The two definitions are equivalent.
-/
theorem cylinderSet_eq_cylinderSet' (b : RadixSeq) (L : ℕ) (s : PrefixSet b L) :
    cylinderSet b L s = cylinderSet' b L s := by
  ext x
  simp only [cylinderSet, cylinderSet', Set.mem_setOf_eq]
  constructor
  · intro h
    funext i
    exact h i
  · intro h i
    exact congrFun h i

/-!
## Membership Characterization
-/

/--
Membership in a cylinder is determined by prefix agreement.
-/
theorem mem_cylinderSet_iff (b : RadixSeq) (L : ℕ) (s : PrefixSet b L) (x : CompletedSpace b) :
    x ∈ cylinderSet b L s ↔ ∀ i : Fin L, x i.val = s i :=
  Iff.rfl

/--
Extract the prefix of a completed sequence.
-/
def prefixOf (b : RadixSeq) (L : ℕ) (x : CompletedSpace b) : PrefixSet b L :=
  fun i => x i.val

/--
A sequence is in the cylinder of its own prefix.
-/
theorem mem_cylinderSet_prefixOf (b : RadixSeq) (L : ℕ) (x : CompletedSpace b) :
    x ∈ cylinderSet b L (prefixOf b L x) := by
  intro i
  rfl

/--
Cylinder membership is equivalent to prefix equality.
-/
theorem mem_cylinderSet_iff_prefixOf (b : RadixSeq) (L : ℕ) (s : PrefixSet b L)
    (x : CompletedSpace b) :
    x ∈ cylinderSet b L s ↔ prefixOf b L x = s := by
  constructor
  · intro h
    funext i
    exact h i
  · intro h i
    simp only [← h, prefixOf]

/-!
## Partition Property
-/

/--
Cylinders at level L partition R̂: every point is in exactly one cylinder.

**fdrs.md**: The family {U(s) : s ∈ Σ_L} is a partition of R̂.
-/
theorem cylinderSet_partition (b : RadixSeq) (L : ℕ) :
    ∀ x : CompletedSpace b, ∃! s : PrefixSet b L, x ∈ cylinderSet b L s := by
  intro x
  use prefixOf b L x
  constructor
  · exact mem_cylinderSet_prefixOf b L x
  · intro s hs
    funext i
    exact (hs i).symm

/--
Two cylinders at the same level are either equal or disjoint.
-/
theorem cylinderSet_disjoint_or_eq (b : RadixSeq) (L : ℕ) (s t : PrefixSet b L) :
    cylinderSet b L s = cylinderSet b L t ∨ Disjoint (cylinderSet b L s) (cylinderSet b L t) := by
  by_cases h : s = t
  · left; rw [h]
  · right
    rw [Set.disjoint_iff]
    intro x ⟨hs, ht⟩
    apply h
    funext i
    rw [← hs i, ht i]

/--
The union of all cylinders at level L is the whole space.
-/
theorem cylinderSet_union_univ (b : RadixSeq) (L : ℕ) :
    ⋃ s : PrefixSet b L, cylinderSet b L s = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨prefixOf b L x, mem_cylinderSet_prefixOf b L x⟩

/--
Every cylinder is nonempty.

For any prefix s, we can construct a completed sequence x with prefix s by
extending s with arbitrary digits beyond L.
-/
theorem cylinder_nonempty (b : RadixSeq) (L : ℕ) (s : PrefixSet b L) :
    (cylinderSet b L s).Nonempty := by
  -- Construct a sequence x with prefix s and all zeros beyond L
  let x : CompletedSpace b := fun i => if h : i < L then s ⟨i, h⟩ else ⟨0, b.pos i⟩
  use x
  intro i
  simp only [x]
  rw [dif_pos i.isLt]

/--
Number of cylinders at level L is B_L.
-/
theorem cylinderSet_count (b : RadixSeq) (L : ℕ) :
    Fintype.card (PrefixSet b L) = placeValue b L := by
  exact prefixSet_card b L

/-!
## Cylinder Refinement
-/

/--
Every cylinder at level L is a union of cylinders at level L+1.

**fdrs.md Proof of Def 1.3**: Every length-L cylinder is a union of length-(L+1) cylinders.
-/
theorem cylinderSet_refine (b : RadixSeq) (L : ℕ) (s : PrefixSet b L) :
    cylinderSet b L s = ⋃ d : Fin (b L), cylinderSet b (L + 1) (extendPrefix s d) := by
  ext x
  simp only [Set.mem_iUnion, mem_cylinderSet_iff]
  constructor
  · -- Forward: x matches s → x is in some extended cylinder
    intro hx
    -- The L-th digit of x determines which extended cylinder
    use x L
    intro i
    -- Use Fin.lastCases to case split on i
    refine Fin.lastCases ?_ ?_ i
    · -- i = Fin.last L: x L = extendPrefix s (x L) (Fin.last L)
      simp only [extendPrefix, Fin.lastCases_last, Fin.val_last]
    · -- i = castSucc j for some j
      intro j
      simp only [extendPrefix, Fin.lastCases_castSucc, Fin.val_castSucc]
      exact hx j
  · -- Backward: x in some extended cylinder → x matches s
    rintro ⟨d, hd⟩ i
    have h := hd (Fin.castSucc i)
    simp only [extendPrefix, Fin.lastCases_castSucc, Fin.val_castSucc] at h
    exact h

/--
A cylinder at level L+1 is contained in exactly one cylinder at level L.
-/
theorem cylinderSet_coarsen (b : RadixSeq) (L : ℕ) (s : PrefixSet b (L + 1)) :
    cylinderSet b (L + 1) s ⊆ cylinderSet b L (truncatePrefix s) := by
  intro x hx i
  exact hx (Fin.castSucc i)

/-!
## Connection to Topology/Ultrametric

These definitions should be compatible with the cylinder definition in
Topology/Ultrametric/Definition.lean.
-/

/--
Link to the ultrametric cylinder definition.

The cylinder at level L corresponds to the ball of radius 1/B_L centered at
any point in the cylinder.
-/
theorem cylinderSet_eq_ultrametric_cylinder (b : RadixSeq) (L : ℕ) (s : PrefixSet b L) :
    ∀ x ∈ cylinderSet b L s, cylinderSet b L s =
      {y : CompletedSpace b | ∀ i : Fin L, y i.val = x i.val} := by
  intro x hx
  ext y
  constructor
  · intro hy i
    rw [hy i, hx i]
  · intro hy i
    rw [hy i, ← hx i]

end FdrsFormal.FunctionSpaces.Basic
