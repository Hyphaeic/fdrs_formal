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
-/
import FdrsFormal.FunctionSpaces.Haar.Definition

/-!
# Support Level of Haar Atoms

This file defines the support level ℓ(α) of a Haar atom, which indicates
the finest scale at which the atom has non-constant behavior.

## Main Definitions

* `supportLevel` - The index ℓ(α) := max{i : α_i ≠ 0}
* `isConstant` - Predicate for atoms with all α_i = 0

## Main Results

* `eq_zero_of_gt_supportLevel` - α_i = 0 when i > ℓ(α)
* `supportLevel_of_constant` - ℓ(α) = 0 for constant atoms
* `supportLevel_characterization` - α_i ≠ 0 implies i ≤ ℓ(α)
* `supportLevel_le_of_zero_above` - zeros above L implies ℓ(α) ≤ L
* `supportLevel_mem_support` - α_{ℓ(α)} ≠ 0 for non-constant atoms

## References

* fdrs.md, Lines 1358-1364: Definition 36
-/

open FdrsFormal Core.Primitives

variable {b : RadixSeq} {k : ℕ}

namespace FdrsFormal.Haar

/--
**Definition 36** (support level):
The support level ℓ(α) is the largest digit position where α has non-zero component:
ℓ(α) := max{i : α_i ≠ 0}

If all α_i = 0 (constant function), we define ℓ(α) = 0 by convention.

**fdrs.md Reference:** Lines 1358-1364, Definition 36
-/
def supportLevel (α : HaarAtom b k) : Fin (k + 1) :=
  let S := Finset.univ.filter (fun i : Fin (k + 1) => α i ≠ 0)
  if h : S.Nonempty then S.max' h else 0

/--
An atom is constant if α_i = 0 for all i (only uses constant components).

**fdrs.md Reference:** Lines 1358-1364
-/
def isConstant (α : HaarAtom b k) : Prop :=
  ∀ i, α i = 0

instance : DecidablePred (isConstant (b := b) (k := k)) := by
  intro α; unfold isConstant; infer_instance

private abbrev supportFilter (α : HaarAtom b k) :=
  Finset.univ.filter (fun i : Fin (k + 1) => α i ≠ 0)

private theorem supportLevel_eq_of_nonempty (α : HaarAtom b k)
    (hS : (supportFilter α).Nonempty) :
    supportLevel α = (supportFilter α).max' hS := by
  simp only [supportLevel, supportFilter]
  exact dif_pos hS

/--
If `supportLevel α < i` then `α i = 0`.

**Proof**: By contradiction. If `α i ≠ 0` then `i ∈ S`, so `i ≤ max' S = supportLevel α`,
contradicting `supportLevel α < i`.
-/
theorem eq_zero_of_gt_supportLevel (α : HaarAtom b k) (i : Fin (k + 1))
    (h : supportLevel α < i) : α i = 0 := by
  by_contra hne
  have hi : i ∈ supportFilter α := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩
  have hS : (supportFilter α).Nonempty := ⟨i, hi⟩
  rw [supportLevel_eq_of_nonempty α hS] at h
  exact absurd (Finset.le_max' _ i hi) (not_le.mpr h)

/--
For constant atoms, support level is 0 by convention.

**Proof**: If all α_i = 0, the filter set S is empty, so we take the `else` branch.
-/
theorem supportLevel_of_constant (α : HaarAtom b k) (h : isConstant α) :
    supportLevel α = 0 := by
  have hS : ¬ (supportFilter α).Nonempty := by
    intro ⟨i, hi⟩
    exact (Finset.mem_filter.mp hi).2 (h i)
  simp only [supportLevel, dif_neg hS]

/--
If α_i ≠ 0 then i ≤ supportLevel α.

**Proof**: `i ∈ S`, so `i ≤ max' S = supportLevel α`.
-/
theorem supportLevel_characterization (α : HaarAtom b k) (i : Fin (k + 1))
    (h : α i ≠ 0) : i ≤ supportLevel α := by
  have hi : i ∈ supportFilter α := Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩
  have hS : (supportFilter α).Nonempty := ⟨i, hi⟩
  rw [supportLevel_eq_of_nonempty α hS]
  exact Finset.le_max' _ i hi

/--
If α_i = 0 for all i > L, then support level ℓ(α) ≤ L.

**Proof**: By contraposition. If ℓ(α) > L, then α at ℓ(α) is nonzero (since S is nonempty),
but ℓ(α) > L means h forces α(ℓ(α)) = 0, contradiction.
-/
theorem supportLevel_le_of_zero_above (α : HaarAtom b k) (L : Fin (k + 1))
    (h : ∀ i > L, α i = 0) : supportLevel α ≤ L := by
  by_contra hgt
  push_neg at hgt
  -- supportLevel α > L ≥ 0, so the filter set is nonempty
  have hS : (supportFilter α).Nonempty := by
    by_contra hempty
    have : supportLevel α = 0 := by
      simp only [supportLevel, dif_neg hempty]
    rw [this] at hgt
    exact absurd hgt (not_lt.mpr (Fin.zero_le L))
  rw [supportLevel_eq_of_nonempty α hS] at hgt
  have hmem := Finset.max'_mem (supportFilter α) hS
  have hne : α ((supportFilter α).max' hS) ≠ 0 := (Finset.mem_filter.mp hmem).2
  exact hne (h _ hgt)

/--
For non-constant atoms, α at the support level is nonzero.

**Proof**: Since α is non-constant, S is nonempty, and supportLevel α = max' S ∈ S.
-/
theorem supportLevel_mem_support (α : HaarAtom b k) (hnc : ¬ isConstant α) :
    α (supportLevel α) ≠ 0 := by
  unfold isConstant at hnc; push_neg at hnc
  obtain ⟨j, hj⟩ := hnc
  have hS : (supportFilter α).Nonempty :=
    ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
  rw [supportLevel_eq_of_nonempty α hS]
  exact (Finset.mem_filter.mp (Finset.max'_mem _ hS)).2

/--
Sum of haarComponent for non-constant component is 0 (mean-zero property).

**Proof**: When α_i ≠ 0, the component is a contrast vector, which sums to 0.
-/
theorem haarComponent_sum_zero (i : Fin (k + 1)) (αᵢ : Fin (b i)) (h : αᵢ ≠ 0) :
    ∑ d : Fin (b i), haarComponent i αᵢ d = 0 := by
  have hval : αᵢ.val ≠ 0 := fun hv => h (Fin.ext hv)
  simp only [haarComponent, hval, ↓reduceDIte]
  exact contrastVector_mean_zero (b.ge_two i) _

end FdrsFormal.Haar
