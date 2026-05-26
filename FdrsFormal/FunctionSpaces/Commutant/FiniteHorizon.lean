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

# Finite Horizon Function Spaces

This file defines finite-horizon versions of function spaces, cylinders, and measures.

## Mathematical Content (fdrs.md lines 787-809)

**Definition 25 (finite prefix sets and cylinders)**:
For 1 ≤ L ≤ k+1, and s ∈ Σ_L, define
  U_k(s) := {τ ∈ R^(k) : π_L(τ) = s}
The set {U_k(s) : s ∈ Σ_L} partitions R^(k) into B_L blocks, each of size
  m_{k,L} := |R^(k)|/|Σ_L| = B_{k+1}/B_L = ∏_{i=L}^k b_i

**Definition 26 (uniform measure on R^(k))**:
Let μ_k be the uniform probability measure on R^(k): μ_k({τ}) = 1/B_{k+1}

## Implementation Notes

- R^(k) = FiniteRadixSpace b k (already defined in Core)
- Cylinders are finite sets (use Finset for computability)
- Measure is counting measure scaled by 1/B_{k+1}
- This is the "implementable" truncation of CompletedSpace

## References

- fdrs.md, Phase 2 Fragment 2 (lines 787-809)
- THEOREM_MAPPING.md, FunctionSpaces/Commutant section
-/

import FdrsFormal.Core.Finite.Bijection
import FdrsFormal.FunctionSpaces.Basic.PrefixSet
import FdrsFormal.FunctionSpaces.Basic.Cylinder
import Mathlib.MeasureTheory.Measure.Count

open scoped Classical ENNReal

namespace FdrsFormal.FunctionSpaces.Commutant

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite
open FdrsFormal.FunctionSpaces.Basic
open MeasureTheory

/-!
## Finite Cylinders

Cylinders on finite horizon spaces R^(k).
-/

section FiniteCylinders

variable {b : RadixSeq}

/--
Extract the first L digits from a finite radix element.

This is the finite version of prefixOf from FunctionSpaces/Basic/Cylinder.lean.
-/
def finitePrefix (b : RadixSeq) (L : ℕ) (τ : FiniteRadixSpace b k) (hLk : L ≤ k + 1) : PrefixSet b L :=
  fun i => τ ⟨i.val, by have := i.isLt; omega⟩

/--
A finite cylinder U_k(s) is the set of all elements of R^(k) whose first L digits match s.

**fdrs.md Definition 25**: U_k(s) := {τ ∈ R^(k) : π_L(τ) = s}
-/
def finiteCylinderSet (b : RadixSeq) (k L : ℕ) (hLk : L ≤ k + 1) (s : PrefixSet b L) :
    Set (FiniteRadixSpace b k) :=
  {τ : FiniteRadixSpace b k | ∀ i : Fin L, τ ⟨i.val, by have := i.isLt; omega⟩ = s i}

/--
Membership in a finite cylinder is determined by prefix agreement.
-/
theorem mem_finiteCylinderSet_iff (k L : ℕ) (hLk : L ≤ k + 1) (s : PrefixSet b L)
    (τ : FiniteRadixSpace b k) :
    τ ∈ finiteCylinderSet b k L hLk s ↔
    ∀ i : Fin L, τ ⟨i.val, by have := i.isLt; omega⟩ = s i :=
  Iff.rfl

/--
The cylinder of τ's own prefix contains τ.
-/
theorem mem_finiteCylinderSet_finitePrefix (k L : ℕ) (hLk : L ≤ k + 1) (τ : FiniteRadixSpace b k) :
    τ ∈ finiteCylinderSet b k L hLk (finitePrefix b L τ hLk) := by
  intro i
  rfl

/--
Finite cylinders partition R^(k).

Every element belongs to exactly one cylinder at each level L.
-/
theorem finiteCylinderSet_partition (k L : ℕ) (hLk : L ≤ k + 1) :
    ∀ τ : FiniteRadixSpace b k,
      ∃! s : PrefixSet b L, τ ∈ finiteCylinderSet b k L hLk s := by
  intro τ
  use finitePrefix b L τ hLk
  constructor
  · exact mem_finiteCylinderSet_finitePrefix k L hLk τ
  · intro s' hs'
    funext i
    show s' i = finitePrefix b L τ hLk i
    simp only [finitePrefix]
    exact (hs' i).symm

end FiniteCylinders

/-!
## Cardinality of Finite Cylinders

The key formula: |U_k(s)| = B_{k+1}/B_L.
-/

section Cardinality

variable {b : RadixSeq}

/--
Helper: Product of radices from L to k equals B_{k+1}/B_L.

This is the key formula: the "suffix product" ∏_{i=L}^k b_i equals the quotient B_{k+1}/B_L.
-/
theorem placeValue_div_eq_prod (k L : ℕ) (hLk : L ≤ k + 1) :
    placeValue b (k + 1) / placeValue b L = ∏ i ∈ Finset.Ico L (k + 1), b i := by
  -- Use division formula: B_{k+1} = B_L · ∏_{i=L}^k b_i
  have h_dvd : placeValue b L ∣ placeValue b (k + 1) := placeValue.dvd_of_le hLk
  rw [Nat.div_eq_iff_eq_mul_left (placeValue.pos L) h_dvd]
  -- Need: B_{k+1} = B_L * ∏_{i=L}^k b_i
  clear h_dvd
  revert L
  induction k with
  | zero =>
    intro L hLk
    interval_cases L <;> simp [Finset.Ico_self]
  | succ k ih =>
    intro L hLk
    rcases Nat.eq_or_lt_of_le hLk with rfl | hLt
    · simp [Finset.Ico_self]
    · rw [placeValue.succ]
      have hLk' : L ≤ k + 1 := Nat.le_of_succ_le_succ hLt
      rw [ih L hLk']
      -- Need: B_{k+1} * b_{k+1} = (∏_{i=L}^k b_i) * B_L * b_{k+1}
      -- Split product: ∏_{i=L}^{k+1} b_i = (∏_{i=L}^k b_i) * b_{k+1}
      have h_split : ∏ i ∈ Finset.Ico L (k + 1 + 1), b i =
                    (∏ i ∈ Finset.Ico L (k + 1), b i) * b (k + 1) := by
        -- Use prod_Ico_succ_top: requires L ≤ k+1
        have h_bound : L ≤ k + 1 := hLk'
        rw [Finset.prod_Ico_succ_top h_bound]
      rw [h_split]
      ring

/--
The suffix space for a cylinder: indices from L to k.

This is the type of "suffixes" that complete a prefix of length L to a full element of R^(k).
-/
def SuffixSpace (b : RadixSeq) (k L : ℕ) : Type :=
  (i : Fin (k + 1 - L)) → Fin (b (L + i.val))

instance suffixSpaceFintype (k L : ℕ) : Fintype (SuffixSpace b k L) := by
  unfold SuffixSpace
  infer_instance

/--
Cardinality of suffix space equals B_{k+1}/B_L.

Proven by showing it equals the Finset.Ico product from placeValue_div_eq_prod.
-/
theorem suffixSpace_card (k L : ℕ) (hLk : L ≤ k + 1) :
    Fintype.card (SuffixSpace b k L) = placeValue b (k + 1) / placeValue b L := by
  unfold SuffixSpace
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  rw [placeValue_div_eq_prod k L hLk]
  -- Need: ∏ x : Fin (k + 1 - L), b (L + x) = ∏ j ∈ Finset.Ico L (k + 1), b j
  rw [Finset.prod_Ico_eq_prod_range]
  -- Now: ∏ x : Fin (k + 1 - L), b (L + x) = ∏ j ∈ Finset.range (k + 1 - L), b (L + j)
  exact Fin.prod_univ_eq_prod_range (fun j => b (L + j)) (k + 1 - L)

/--
Injection from cylinder to suffix space (extract suffix).
-/
def cylinderToSuffix (k L : ℕ) (hLk : L ≤ k + 1) (s : PrefixSet b L)
    (τ : finiteCylinderSet b k L hLk s) : SuffixSpace b k L :=
  fun i => τ.val ⟨L + i.val, by have hi := i.isLt; omega⟩

/--
Injection from suffix space to cylinder (prepend prefix).
-/
def suffixToCylinder (k L : ℕ) (hLk : L ≤ k + 1) (s : PrefixSet b L)
    (σ : SuffixSpace b k L) : finiteCylinderSet b k L hLk s :=
  ⟨fun j =>
    if h : j.val < L then
      s ⟨j.val, h⟩
    else
      -- σ ⟨j.val - L, _⟩ : Fin (b (L + (j.val - L))), need Fin (b j.val)
      -- Use Fin.cast with the equality L + (j.val - L) = j.val
      Fin.cast (by congr 1; exact Nat.add_sub_cancel' (Nat.le_of_not_lt h))
        (σ ⟨j.val - L, by have := j.isLt; omega⟩),
  by intro i; simp only [dif_pos i.isLt]⟩

/--
cylinderToSuffix and suffixToCylinder are inverse.
-/
theorem cylinder_suffix_left_inv (k L : ℕ) (hLk : L ≤ k + 1) (s : PrefixSet b L)
    (τ : finiteCylinderSet b k L hLk s) :
    suffixToCylinder k L hLk s (cylinderToSuffix k L hLk s τ) = τ := by
  apply Subtype.ext
  funext j
  simp only [suffixToCylinder, cylinderToSuffix]
  by_cases hj : j.val < L
  · simp only [dif_pos hj]
    have h_mem := τ.property ⟨j.val, hj⟩
    simp only [Fin.ext_iff] at h_mem ⊢
    exact h_mem.symm
  · simp only [dif_neg hj]
    -- Goal: Fin.cast _ (τ.val ⟨L + (j.val - L), ...⟩) = τ.val j
    -- The Fin indices are equal since L + (j.val - L) = j.val
    have h_idx : L + (j.val - L) = j.val := Nat.add_sub_cancel' (Nat.le_of_not_lt hj)
    have h_fin_eq : (⟨L + (j.val - L), by omega⟩ : Fin (k + 1)) = j := Fin.ext h_idx
    -- Use heterogeneous equality: if indices are equal, function values are HEq
    have h_heq : HEq (τ.val ⟨L + (j.val - L), by omega⟩) (τ.val j) := congr_arg_heq τ.val h_fin_eq
    -- The bound types are equal (b (L + (j.val - L)) = b j.val)
    have h_type_eq : b (L + (j.val - L)) = b j.val := congrArg b h_idx
    -- Convert HEq to equality on vals using Fin.heq_ext_iff
    simp only [Fin.ext_iff, Fin.val_cast]
    exact (Fin.heq_ext_iff h_type_eq).mp h_heq

theorem cylinder_suffix_right_inv (k L : ℕ) (hLk : L ≤ k + 1) (s : PrefixSet b L)
    (σ : SuffixSpace b k L) :
    cylinderToSuffix k L hLk s (suffixToCylinder k L hLk s σ) = σ := by
  funext i
  simp only [cylinderToSuffix, suffixToCylinder]
  have hL_le : ¬ (L + i.val) < L := by omega
  simp only [dif_neg hL_le]
  -- Goal: Fin.cast _ (σ ⟨L + i.val - L, _⟩) = σ i
  -- The index simplifies: L + i.val - L = i.val
  have h_idx : L + i.val - L = i.val := Nat.add_sub_cancel_left L i.val
  have h_fin_eq : (⟨L + i.val - L, by omega⟩ : Fin (k + 1 - L)) = i := Fin.ext h_idx
  -- Use heterogeneous equality: if indices are equal, function values are HEq
  have h_heq : HEq (σ ⟨L + i.val - L, by omega⟩) (σ i) := congr_arg_heq σ h_fin_eq
  -- The bound types are equal (b (L + (L + i.val - L)) = b (L + i.val))
  have h_type_eq : b (L + (L + i.val - L)) = b (L + i.val) := congrArg b (congrArg (L + ·) h_idx)
  -- Convert HEq to equality on vals using Fin.heq_ext_iff
  simp only [Fin.ext_iff, Fin.val_cast]
  exact (Fin.heq_ext_iff h_type_eq).mp h_heq

/--
Equivalence between cylinder and suffix space.
-/
def cylinderSuffixEquiv (k L : ℕ) (hLk : L ≤ k + 1) (s : PrefixSet b L) :
    finiteCylinderSet b k L hLk s ≃ SuffixSpace b k L where
  toFun := cylinderToSuffix k L hLk s
  invFun := suffixToCylinder k L hLk s
  left_inv := cylinder_suffix_left_inv k L hLk s
  right_inv := cylinder_suffix_right_inv k L hLk s

/--
**Theorem**: The cardinality of a finite cylinder at level L is m_{k,L} = B_{k+1}/B_L.

**fdrs.md**: m_{k,L} = ∏_{i=L}^k b_i

**Mathematical proof**:
The cylinder U_k(s) consists of all τ : R^(k) with first L digits = s.
This is isomorphic to the suffix product: (i : Fin(k+1-L)) → Fin(b_(L+i)).

Card(cylinder) = ∏_{i : Fin(k+1-L)} b_(L+i) = ∏_{j=L}^k b_j = B_{k+1}/B_L.

**Construction**: Via cylinderSuffixEquiv which maps cylinder elements to their suffixes.
-/
theorem finiteCylinder_card (k L : ℕ) (hLk : L ≤ k + 1) (s : PrefixSet b L) :
    Fintype.card (finiteCylinderSet b k L hLk s) = placeValue b (k + 1) / placeValue b L := by
  rw [Fintype.card_congr (cylinderSuffixEquiv k L hLk s)]
  exact suffixSpace_card k L hLk

/--
All finite cylinders at the same level have equal cardinality.
-/
theorem finiteCylinder_card_eq (k L : ℕ) (hLk : L ≤ k + 1) (s t : PrefixSet b L) :
    Fintype.card (finiteCylinderSet b k L hLk s) =
    Fintype.card (finiteCylinderSet b k L hLk t) := by
  rw [finiteCylinder_card k L hLk s, finiteCylinder_card k L hLk t]

/--
The number of cylinders at level L is B_L.
-/
theorem finiteCylinder_count (k L : ℕ) (hLk : L ≤ k + 1) :
    Fintype.card (PrefixSet b L) = placeValue b L :=
  prefixSet_card b L

end Cardinality

/-!
## Uniform Measure on Finite Spaces

The counting measure scaled to be a probability measure.
-/

section FiniteMeasure

variable {b : RadixSeq}

/--
The uniform probability measure on R^(k).

**fdrs.md Definition 26**: μ_k({τ}) = 1/B_{k+1} for all τ ∈ R^(k).
-/
noncomputable def finiteUniformMeasure (b : RadixSeq) (k : ℕ) :
    MeasureTheory.Measure (FiniteRadixSpace b k) :=
  (1 / (placeValue b (k + 1) : ℝ≥0∞)) • MeasureTheory.Measure.count

/-- Notation for the finite uniform measure -/
scoped notation "μ_k[" k "]" => finiteUniformMeasure _ k

/--
The finite uniform measure is a probability measure.

**Proof**: The measure of the whole space is:
  μ_k(R^(k)) = (1/B_{k+1}) · |R^(k)| = (1/B_{k+1}) · B_{k+1} = 1

where |R^(k)| = ∏_{i=0}^k b_i = placeValue b (k+1).

**Technical details**:
- Fintype.card (FiniteRadixSpace b k) = Fintype.card ((i : Fin(k+1)) → Fin(b_i))
- = ∏ i : Fin(k+1), Fintype.card (Fin(b_i)) = ∏ i, b_i
- = placeValue b (k+1)  [by definition]

Then: (1/N) * N = 1 as ENNReal (using ENNReal.div_mul_cancel).

**Mathlib approach**: Would use:
- ENat.card_eq_coe_fintype_card
- Fintype.card_fun
- ENNReal.div_mul_cancel (requires N ≠ 0 and N ≠ ∞, both trivial for Nat)

**Note**: Now proven using cardinality formula for dependent Pi types.
-/
theorem finiteUniformMeasure_isProbability (b : RadixSeq) (k : ℕ) :
    MeasureTheory.IsProbabilityMeasure (finiteUniformMeasure b k) := by
  constructor
  simp only [finiteUniformMeasure, MeasureTheory.Measure.smul_apply, smul_eq_mul]
  rw [MeasureTheory.Measure.count_apply_finite _ (Set.toFinite _)]
  -- Need to show card of Set.univ equals placeValue b (k+1)
  have hcard : (Set.toFinite (Set.univ : Set (FiniteRadixSpace b k))).toFinset.card =
      placeValue b (k + 1) := by
    simp only [Set.Finite.toFinset, Set.toFinset_univ, Finset.card_univ]
    -- Fintype.card (FiniteRadixSpace b k) = Fintype.card ((i : Fin (k+1)) → Fin (b i))
    unfold FiniteRadixSpace
    rw [Fintype.card_pi]
    -- Need ∏ i : Fin (k+1), card (Fin (b i)) = placeValue b (k+1)
    induction k with
    | zero =>
      simp [placeValue]
    | succ k ih =>
      rw [placeValue.succ, Fin.prod_univ_castSucc]
      simp only [Fin.val_castSucc, Fintype.card_fin, Fin.val_last]
      -- Goal: (∏ x : Fin (k+1), b ↑x) * b (k+1) = placeValue b (k+1) * b (k+1)
      -- ih: ∏ i : Fin (k+1), Fintype.card (Fin (b ↑i)) = placeValue b (k+1)
      congr 1
      convert ih using 1
      congr 1
      ext i
      simp [Fintype.card_fin]
  rw [hcard]
  rw [ENNReal.div_mul_cancel]
  · exact Nat.cast_ne_zero.mpr (placeValue.ne_zero (k + 1))
  · exact ENNReal.natCast_ne_top (placeValue b (k + 1))

/--
The measure of a singleton is 1/B_{k+1}.
-/
theorem finiteUniformMeasure_singleton (k : ℕ) (τ : FiniteRadixSpace b k) :
    finiteUniformMeasure b k {τ} = 1 / (placeValue b (k + 1) : ℝ≥0∞) := by
  simp only [finiteUniformMeasure, MeasureTheory.Measure.smul_apply]
  rw [MeasureTheory.Measure.count_singleton]
  simp only [smul_eq_mul, mul_one]

/--
The measure of a finite cylinder is 1/B_L.

**Proof**: By definition:
  μ_k(U_k(s)) = (1/B_{k+1}) · |U_k(s)|
              = (1/B_{k+1}) · (B_{k+1}/B_L)    [by finiteCylinder_card]
              = 1/B_L

The key arithmetic: (1/a) * (a/b) = 1/b, carried out in ENNReal using
divisibility (`placeValue.dvd_of_le`) and `Nat.div_mul_cancel`.
-/
theorem finiteCylinder_measure (k L : ℕ) (hLk : L ≤ k + 1) (s : PrefixSet b L) :
    finiteUniformMeasure b k (finiteCylinderSet b k L hLk s) = (placeValue b L : ℝ≥0∞)⁻¹ := by
  simp only [finiteUniformMeasure, MeasureTheory.Measure.smul_apply, smul_eq_mul]
  rw [MeasureTheory.Measure.count_apply_finite _ (Set.toFinite _)]
  -- Bridge toFinite.toFinset.card to Fintype.card
  have hcard : (Set.toFinite (finiteCylinderSet b k L hLk s)).toFinset.card =
      placeValue b (k + 1) / placeValue b L := by
    have h_eq : (Set.toFinite (finiteCylinderSet b k L hLk s)).toFinset =
        (finiteCylinderSet b k L hLk s).toFinset := by
      ext x
      simp only [Set.Finite.mem_toFinset, Set.mem_toFinset]
    rw [h_eq, Set.toFinset_card]
    exact finiteCylinder_card k L hLk s
  rw [hcard]
  -- Goal: 1 / ↑B_{k+1} * ↑(B_{k+1}/B_L) = (↑B_L)⁻¹
  have h_dvd : placeValue b L ∣ placeValue b (k + 1) := placeValue.dvd_of_le hLk
  have hBL_ne : (placeValue b L : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (placeValue.ne_zero L)
  have hBL_ne_top : (placeValue b L : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top (placeValue b L)
  have hBk_ne : (placeValue b (k + 1) : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (placeValue.ne_zero (k + 1))
  have hBk_ne_top : (placeValue b (k + 1) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top (placeValue b (k + 1))
  -- Key: (B_{k+1}/B_L) * B_L = B_{k+1}, so ↑(B_{k+1}/B_L) * ↑B_L = ↑B_{k+1}
  have h_mul : (placeValue b (k + 1) / placeValue b L) * placeValue b L =
      placeValue b (k + 1) := Nat.div_mul_cancel h_dvd
  -- Lift to ENNReal: ↑(B_{k+1}/B_L) = ↑B_{k+1} / ↑B_L
  have h_cast_div : (↑(placeValue b (k + 1) / placeValue b L) : ℝ≥0∞) =
      ↑(placeValue b (k + 1)) / ↑(placeValue b L) := by
    rw [ENNReal.eq_div_iff hBL_ne hBL_ne_top]
    rw [mul_comm]
    exact_mod_cast h_mul
  rw [h_cast_div, one_div, ENNReal.div_eq_inv_mul]
  -- Goal: (↑B_{k+1})⁻¹ * ((↑B_L)⁻¹ * ↑B_{k+1}) = (↑B_L)⁻¹
  conv_lhs => rw [mul_comm (↑(placeValue b L) : ℝ≥0∞)⁻¹ ↑(placeValue b (k + 1))]
  -- Goal: (↑B_{k+1})⁻¹ * (↑B_{k+1} * (↑B_L)⁻¹) = (↑B_L)⁻¹
  rw [← mul_assoc, ENNReal.inv_mul_cancel hBk_ne hBk_ne_top, one_mul]

end FiniteMeasure

/-!
## Finite Filtration

The σ-algebra generated by finite cylinders.
-/

section FiniteFiltration

variable {b : RadixSeq}

/--
The σ-algebra F_{k,L} generated by cylinders at level L.

This is the finite version of cylinderAlgebra.
-/
def finiteCylinderAlgebra (b : RadixSeq) (k L : ℕ) (hLk : L ≤ k + 1) :
    MeasurableSpace (FiniteRadixSpace b k) :=
  MeasurableSpace.generateFrom {U | ∃ s : PrefixSet b L, U = finiteCylinderSet b k L hLk s}

/--
Finite cylinders are measurable in the generated σ-algebra.
-/
theorem finiteCylinder_measurableSet (k L : ℕ) (hLk : L ≤ k + 1) (s : PrefixSet b L) :
    @MeasurableSet (FiniteRadixSpace b k) (finiteCylinderAlgebra b k L hLk)
      (finiteCylinderSet b k L hLk s) := by
  apply MeasurableSpace.measurableSet_generateFrom
  exact ⟨s, rfl⟩

/--
An L-cylinder is the union of (L+1)-cylinders: one for each extension digit.

This is the finite version of the decomposition used in filtration_monotone.
For s : PrefixSet b L:
  U_k(s) = ⋃ d : Fin (b L), U_k(extendPrefix s d)

**Proof**: τ ∈ U_k(s) iff first L digits of τ equal s
         iff first L digits equal s AND L-th digit is some d ∈ D_L
         iff τ ∈ U_k(extendPrefix s d) for some d
-/
theorem finiteCylinder_union_extension (k L : ℕ) (hLk : L ≤ k + 1) (hL1k : L + 1 ≤ k + 1)
    (s : PrefixSet b L) :
    finiteCylinderSet b k L hLk s =
    ⋃ d : Fin (b L), finiteCylinderSet b k (L + 1) hL1k (extendPrefix s d) := by
  ext τ
  simp only [Set.mem_iUnion, finiteCylinderSet, Set.mem_setOf_eq]
  constructor
  · intro hτ
    -- τ is in L-cylinder of s, so τ agrees with s on first L positions
    -- Use τ's L-th digit as the extension digit
    have hL_lt : L < k + 1 := by omega
    use τ ⟨L, hL_lt⟩
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · -- Position j < L: use that τ agrees with s at j
      simp only [extendPrefix, Fin.lastCases_castSucc]
      have h := hτ j
      convert h using 2
    · -- Position L: use that τ ⟨L, _⟩ equals the extension digit
      simp only [extendPrefix, Fin.lastCases_last, Fin.val_last]
  · intro ⟨d, hd⟩
    intro i
    -- τ agrees with (extendPrefix s d) on first L+1 positions
    -- In particular, at position i < L, it agrees with s
    have h := hd (Fin.castSucc i)
    simp only [extendPrefix, Fin.lastCases_castSucc] at h
    convert h using 2

/--
**Single-step monotonicity**: F_{k,L} ⊆ F_{k,L+1}.

Each L-cylinder decomposes into a finite union of (L+1)-cylinders.
-/
theorem finiteFiltration_monotone_succ (k L : ℕ) (hLk : L ≤ k + 1) (hL1k : L + 1 ≤ k + 1) :
    finiteCylinderAlgebra b k L hLk ≤ finiteCylinderAlgebra b k (L + 1) hL1k := by
  apply MeasurableSpace.generateFrom_le
  intro S hS
  obtain ⟨s, rfl⟩ := hS
  -- S = finiteCylinderSet b k L _ s
  -- Need to show this is measurable in F_{k,L+1}
  rw [finiteCylinder_union_extension k L hLk hL1k s]
  apply MeasurableSet.iUnion
  intro d
  exact MeasurableSpace.measurableSet_generateFrom ⟨extendPrefix s d, rfl⟩

/--
The filtration is monotone: F_{k,L} ⊆ F_{k,M} for L ≤ M.

**Proof**: By induction on gap M - L:
- Base (M = L): Reflexivity
- Step: Transitivity via F_{k,L} ⊆ F_{k,L+d} ⊆ F_{k,L+d+1}
-/
theorem finiteFiltration_monotone (k L M : ℕ) (hLk : L ≤ k + 1) (hMk : M ≤ k + 1) (hLM : L ≤ M) :
    finiteCylinderAlgebra b k L hLk ≤ finiteCylinderAlgebra b k M hMk := by
  -- Prove by induction on the gap M - L
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hLM
  clear hLM
  induction d with
  | zero =>
    -- L = M: reflexivity
    simp only [Nat.add_zero]
    rfl
  | succ d ih =>
    -- L ≤ L+d ≤ L+d+1: transitivity
    have hLdk : L + d ≤ k + 1 := by omega
    have hLd1k : L + d + 1 ≤ k + 1 := by omega
    calc finiteCylinderAlgebra b k L hLk
        ≤ finiteCylinderAlgebra b k (L + d) hLdk := ih hLdk
      _ ≤ finiteCylinderAlgebra b k (L + d + 1) hLd1k :=
          finiteFiltration_monotone_succ k (L + d) hLdk hLd1k
      _ ≤ finiteCylinderAlgebra b k (L + d + 1) hMk := by rfl

end FiniteFiltration

end FdrsFormal.FunctionSpaces.Commutant
