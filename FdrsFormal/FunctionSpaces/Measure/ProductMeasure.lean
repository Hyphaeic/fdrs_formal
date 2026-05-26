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

# Uniform Product Measure on CompletedSpace

This file defines the uniform product probability measure μ on R̂.

## Mathematical Content (fdrs.md lines 621-627)

**Definition 21 (uniform product measure)**:
Let μ be the product probability measure on R̂ where each digit x_i is uniform on D_i.
Then every cylinder has measure:
  μ(U(s)) = 1/B_L  for s ∈ Σ_L

## Implementation Notes

- We use Mathlib's MeasureTheory framework
- The measure is the infinite product of uniform measures on Fin (b i)
- Cylinder measures follow from the product structure
- This is the canonical "fair" measure on R̂

## References

- fdrs.md, Section 3, Definition 21 (lines 621-627)
- THEOREM_MAPPING.md, FunctionSpaces/Measure section
-/

import FdrsFormal.FunctionSpaces.Basic
import FdrsFormal.Topology.Filtration
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProductMeasure

open scoped Classical ENNReal NNReal

namespace FdrsFormal.FunctionSpaces.Measure

open FdrsFormal.Core.Primitives FdrsFormal.Core.Infinite
open FdrsFormal.Topology.Ultrametric FdrsFormal.Topology.Filtration
open FdrsFormal.FunctionSpaces.Basic

/-!
## Uniform Digit Measure

First we define the uniform probability measure on each digit alphabet Fin (b i).
-/

section DigitMeasure

variable {b : RadixSeq}

/--
The uniform probability measure on the digit alphabet D_i = Fin (b i).

Each digit value has probability 1/(b i).
-/
noncomputable def digitMeasure (b : RadixSeq) (i : ℕ) : MeasureTheory.Measure (Fin (b i)) :=
  (1 / (b i : ℝ≥0∞)) • MeasureTheory.Measure.count

/--
The digit measure is a probability measure (total mass 1).

**Proof**: Total mass = (1/b_i) * |Fin (b i)| = (1/b_i) * b_i = 1.
-/
theorem digitMeasure_isProbability (b : RadixSeq) (i : ℕ) :
    MeasureTheory.IsProbabilityMeasure (digitMeasure b i) := by
  constructor
  simp only [digitMeasure, MeasureTheory.Measure.smul_apply, smul_eq_mul]
  rw [MeasureTheory.Measure.count_apply_finite _ (Set.toFinite _)]
  -- The cardinality of Set.univ : Set (Fin n) is n
  have hcard : (Set.toFinite (Set.univ : Set (Fin (b i)))).toFinset.card = b i := by
    simp only [Set.Finite.toFinset, Set.toFinset_univ, Finset.card_univ, Fintype.card_fin]
  rw [hcard]
  -- Goal: 1 / ↑(b i) * ↑(b i) = 1
  rw [ENNReal.div_mul_cancel]
  · exact Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (b.pos i))
  · exact ENNReal.natCast_ne_top (b i)

/--
The measure of a singleton in digitMeasure is 1/(b i).
-/
theorem digitMeasure_singleton (b : RadixSeq) (i : ℕ) (d : Fin (b i)) :
    digitMeasure b i {d} = 1 / (b i : ℝ≥0∞) := by
  simp only [digitMeasure, MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.count_singleton,
    smul_eq_mul, mul_one]

end DigitMeasure

/-!
## Product Measure on CompletedSpace

The uniform product measure μ on R̂ = ∏_{i≥0} Fin (b i).
-/

section ProductMeasure

variable {b : RadixSeq}

/--
The standard product σ-algebra on CompletedSpace.

For countable products of Polish spaces (like our product of finite discrete spaces),
the product σ-algebra coincides with the Borel σ-algebra from the product topology.

We use MeasurableSpace.pi to enable direct use of Mathlib's `Measure.infinitePi`.
-/
def completedSpaceMeasurableSpace (b : RadixSeq) : MeasurableSpace (CompletedSpace b) :=
  MeasurableSpace.pi

/-- Use the product σ-algebra as the canonical measurable space on CompletedSpace -/
noncomputable instance instMeasurableSpaceCompletedSpace : MeasurableSpace (CompletedSpace b) :=
  MeasurableSpace.pi

/--
The uniform product probability measure μ on R̂.

**fdrs.md Definition 21 (lines 621-627)**: μ is the product measure where each digit is uniform.

This is the canonical "fair" measure on the mixed-radix completed space.

**Construction**: We use Mathlib's `Measure.infinitePi` which constructs infinite product
measures via the Ionescu-Tulcea theorem and Carathéodory extension. Each coordinate
uses the uniform measure `digitMeasure b i`.
-/
noncomputable def uniformProductMeasure (b : RadixSeq) : MeasureTheory.Measure (CompletedSpace b) :=
  MeasureTheory.Measure.infinitePi (fun i => digitMeasure b i)

/-- Notation for the uniform measure -/
scoped notation "μ_" b => uniformProductMeasure b

/--
Each digitMeasure is a probability measure (needed for infinitePi).
-/
instance digitMeasure_isProbabilityMeasure (b : RadixSeq) (i : ℕ) :
    MeasureTheory.IsProbabilityMeasure (digitMeasure b i) :=
  digitMeasure_isProbability b i

/--
The uniform product measure is a probability measure.

**Proof**: Each `digitMeasure b i` is a probability measure, and `Measure.infinitePi`
preserves the probability measure property.
-/
instance uniformProductMeasure_isProbability (b : RadixSeq) :
    MeasureTheory.IsProbabilityMeasure (uniformProductMeasure b) := by
  show MeasureTheory.IsProbabilityMeasure (MeasureTheory.Measure.infinitePi (fun i => digitMeasure b i))
  have : ∀ i, MeasureTheory.IsProbabilityMeasure (digitMeasure b i) :=
    fun i => digitMeasure_isProbability b i
  infer_instance

end ProductMeasure

/-!
## Cylinder Measures

The key property: μ(U(s)) = 1/B_L for s ∈ Σ_L.
-/

section CylinderMeasure

variable {b : RadixSeq}

/-- Helper lemma: Fintype product over Fin L equals placeValue -/
private theorem fin_prod_eq_placeValue (b : RadixSeq) (L : ℕ) :
    ∏ i : Fin L, b i.val = placeValue b L := by
  induction L with
  | zero => simp [placeValue.zero]
  | succ L' ih =>
    rw [Fin.prod_univ_castSucc (fun i => b i.val)]
    simp only [Fin.val_last, Fin.val_castSucc]
    rw [ih, placeValue.succ]

/--
**Core theorem**: The measure of a cylinder at level L is 1/B_L.

**fdrs.md Definition 21 (lines 621-627)**: μ(U(s)) = 1/B_L for s ∈ Σ_L.

**Proof**: Express the cylinder as a preimage under the restriction map to Fin L,
apply `infinitePi_map_restrict` to get the finite product measure, then compute
the product of marginal measures.
-/
theorem cylinder_measure (L : ℕ) (s : PrefixSet b L) :
    uniformProductMeasure b (cylinderSet b L s) = (placeValue b L : ℝ≥0∞)⁻¹ := by
  unfold uniformProductMeasure
  
  -- Define the set function for the pi-set
  let t_fun (i : ℕ) : Set (Fin (b i)) :=
    if h : i < L then {s ⟨i, h⟩} else Set.univ
  
  -- Show cylinderSet equals the pi-set
  have cyl_eq : cylinderSet b L s = Set.pi (↑(Finset.range L)) t_fun := by
    ext x
    simp only [cylinderSet, Set.mem_setOf_eq, Set.mem_pi]
    constructor
    · intro hx i hi
      rw [Finset.mem_coe, Finset.mem_range] at hi
      show x i ∈ t_fun i
      simp only [t_fun, hi, dite_true, Set.mem_singleton_iff]
      exact hx ⟨i, hi⟩
    · intro hx ⟨i, hi⟩  
      have hmem : i ∈ (↑(Finset.range L) : Set ℕ) := by
        simp [hi]
      have := hx i hmem
      simp only [t_fun, hi, dite_true, Set.mem_singleton_iff] at this
      exact this
  
  trans (∏ i ∈ Finset.range L, digitMeasure b i (t_fun i))
  
  · -- First part: measure equals product
    rw [cyl_eq]
    have meas_t : ∀ i ∈ Finset.range L, MeasurableSet (t_fun i) := by
      intro i hi
      simp only [Finset.mem_range] at hi
      simp only [t_fun, hi, dite_true]
      exact MeasurableSet.singleton _
    exact MeasureTheory.Measure.infinitePi_pi (fun i => digitMeasure b i) meas_t
  
  · -- Second part: product simplifies to inverse of placeValue
    trans (∏ i ∈ Finset.range L, (1 / (b i : ℝ≥0∞)))
    · apply Finset.prod_congr rfl
      intro i hi
      simp only [Finset.mem_range] at hi
      simp [t_fun, hi]
      rw [digitMeasure_singleton, one_div]
    
    rw [Finset.prod_range]
    simp_rw [one_div]

    -- Goal: ∏ i : Fin L, (b i.val)⁻¹ = (placeValue b L)⁻¹
    have key : (∏ i : Fin L, ((b i.val : ℝ≥0∞))⁻¹) = (∏ i : Fin L, (b i.val : ℝ≥0∞))⁻¹ := by
      -- Product of inverses equals inverse of product for ENNReal
      symm
      apply ENNReal.prod_inv_distrib
      -- Need: (Finset.univ : Set (Fin L)).Pairwise (fun i j => b i.val ≠ 0 ∨ b j.val ≠ ∞)
      intro i _ j _ hij
      left
      exact Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (b.pos i.val))
    rw [key]
    congr 1
    rw [← Nat.cast_prod]
    congr 1
    -- Use the helper lemma
    exact fin_prod_eq_placeValue b L
/--
Alternative statement: cylinder measure in terms of B_L.
-/
theorem cylinder_measure' (L : ℕ) (s : PrefixSet b L) :
    uniformProductMeasure b (cylinderSet b L s) = 1 / (placeValue b L : ℝ≥0∞) := by
  rw [one_div, cylinder_measure L s]

/--
All cylinders at the same level have equal measure.

This is the "uniformity" property: the measure doesn't depend on which
cylinder we choose, only on the level L.
-/
theorem cylinder_measure_eq (L : ℕ) (s t : PrefixSet b L) :
    uniformProductMeasure b (cylinderSet b L s) =
    uniformProductMeasure b (cylinderSet b L t) := by
  rw [cylinder_measure, cylinder_measure]

/--
Cylinder measure is positive.
-/
theorem cylinder_measure_pos (L : ℕ) (s : PrefixSet b L) :
    0 < uniformProductMeasure b (cylinderSet b L s) := by
  rw [cylinder_measure]
  -- Need: 0 < (placeValue b L)⁻¹
  apply ENNReal.inv_pos.mpr
  -- Need: placeValue b L ≠ ⊤
  exact ENNReal.natCast_ne_top (placeValue b L)

/--
Cylinder measure is finite.
-/
theorem cylinder_measure_ne_top (L : ℕ) (s : PrefixSet b L) :
    uniformProductMeasure b (cylinderSet b L s) ≠ (⊤ : ℝ≥0∞) := by
  rw [cylinder_measure]
  -- Need: (placeValue b L)⁻¹ ≠ ⊤
  apply ENNReal.inv_ne_top.mpr
  -- Need: placeValue b L ≠ 0
  exact Nat.cast_ne_zero.mpr (placeValue.ne_zero L)

/--
The number of cylinders at level L is B_L, and they partition R̂.
-/
theorem cylinder_partition_measure (L : ℕ) :
    ∑ s : PrefixSet b L, uniformProductMeasure b (cylinderSet b L s) = 1 := by
  simp_rw [cylinder_measure]
  -- Sum of B_L copies of 1/B_L = B_L · (1/B_L) = 1
  rw [Finset.sum_const, Finset.card_univ]
  simp only [nsmul_eq_mul]
  -- Card of PrefixSet b L equals placeValue b L
  rw [prefixSet_card]
  rw [ENNReal.mul_inv_cancel]
  · exact Nat.cast_ne_zero.mpr (placeValue.ne_zero L)
  · exact ENNReal.natCast_ne_top _

end CylinderMeasure

/-!
## Measure-Theoretic Properties
-/

section Properties

variable {b : RadixSeq}

/--
Cylinders are measurable sets (in the product σ-algebra).

**Proof**: A cylinder is a finite intersection of preimages under coordinate projections.
-/
theorem cylinder_measurableSet (L : ℕ) (s : PrefixSet b L) :
    MeasurableSet (cylinderSet b L s) := by
  -- Cylinder = intersection of coordinate level sets
  have : cylinderSet b L s = ⋂ i : Fin L, {x : CompletedSpace b | x i.val = s i} := by
    ext x
    simp only [cylinderSet, Set.mem_setOf_eq, Set.mem_iInter]
  rw [this]
  apply MeasurableSet.iInter
  intro i
  -- {x | x i.val = s i} = (fun x => x i.val) ⁻¹' {s i}
  have eq : {x : CompletedSpace b | x i.val = s i} = (fun x => x i.val) ⁻¹' {s i} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
  rw [eq]
  -- Preimage of measurable set under measurable function
  exact MeasurableSet.preimage (MeasurableSet.singleton (s i)) (measurable_pi_apply i.val)

/--
The uniform measure assigns full mass to R̂: μ(R̂) = 1.

Since μ is a probability measure, `μ(Set.univ) = 1`.
-/
theorem uniformProductMeasure_fullSupport (b : RadixSeq) :
    uniformProductMeasure b Set.univ = 1 :=
  MeasureTheory.measure_univ

/--
The uniform measure is finite (being a probability measure).
-/
instance uniformProductMeasure_isFinite (b : RadixSeq) :
    MeasureTheory.IsFiniteMeasure (uniformProductMeasure b) :=
  inferInstance

end Properties

/-!
## Integration Basics

Setup for integrating functions over R̂.
-/

section Integration

variable {b : RadixSeq} {V : Type*}

/--
For a block-constant function f ∈ 𝕋_L(V), the set integral over a cylinder
equals (1/B_L) times the constant value of f on that cylinder.

∫_{U(s)} f dμ = (1/B_L) · f(x)  for any x ∈ U(s)
-/
theorem integral_blockConstant [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {L : ℕ} (f : BlockConstantSpace b L V) (s : PrefixSet b L)
    (x : CompletedSpace b) (hx : x ∈ cylinderSet b L s) :
    ∫ y in cylinderSet b L s, f.val y ∂(uniformProductMeasure b) =
      (placeValue b L : ℝ)⁻¹ • f.val x := by
  have hconst : ∀ y ∈ cylinderSet b L s, f.val y = f.val x :=
    fun y hy => f.property s y x hy hx
  rw [MeasureTheory.setIntegral_congr_fun (cylinder_measurableSet L s) hconst,
    MeasureTheory.setIntegral_const]
  congr 1
  rw [MeasureTheory.Measure.real_def, cylinder_measure L s,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]

/--
The integral of a cylinder indicator is the cylinder measure.

∫ 1_{U(s)} dμ = μ(U(s)).toReal = 1/B_L
-/
theorem integral_cylinderIndicator (L : ℕ) (s : PrefixSet b L) :
    ∫ x, (cylinderSet b L s).indicator (fun _ => (1 : ℝ)) x ∂(uniformProductMeasure b) =
      (placeValue b L : ℝ)⁻¹ := by
  rw [MeasureTheory.integral_indicator (cylinder_measurableSet L s)]
  rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
  rw [MeasureTheory.Measure.real_def, cylinder_measure L s,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]

end Integration

end FdrsFormal.FunctionSpaces.Measure
