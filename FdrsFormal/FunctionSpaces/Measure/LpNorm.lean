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

# Lp Norm Definitions and Properties for Finite Radix Spaces

This file defines Lp norms on finite radix spaces and proves fundamental
properties including the triangle inequality (Minkowski's inequality).

## Mathematical Content

For functions f : R^(k) → V where V is a normed vector space, the Lp norm is:
- For p < ∞: |f|_{p,k} := (1/B_{k+1} ∑_τ |f(τ)|^p)^{1/p}
- For p = ∞: |f|_{∞,k} := sup_τ |f(τ)|

**Minkowski's inequality (triangle inequality for Lp norms)**:
  |f + g|_p ≤ |f|_p + |g|_p

This is a standard result in functional analysis.

## References

- fdrs.md, Phase 2 Fragment 2 (lines 877-918)
- Mathlib: `MeasureTheory.Lp`, `Analysis.NormedSpace.lpSpace`
-/

import FdrsFormal.FunctionSpaces.Commutant.FiniteProjection
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.ENNReal.Operations
import Mathlib.Analysis.MeanInequalities

open scoped Classical ENNReal NNReal

namespace FdrsFormal.FunctionSpaces.Measure

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite
open FdrsFormal.FunctionSpaces.Basic

/-!
## Lp Norm Definitions
-/

section Definitions

variable {b : RadixSeq} {V : Type*}

/--
The Lp norm on finite function spaces.

For p < ∞: |f|_{p,k} := (1/B_{k+1} ∑_τ |f(τ)|^p)^{1/p}
For p = ∞: |f|_{p,k} := max_τ |f(τ)|
-/
noncomputable def finiteLpNorm (p : ℝ≥0∞) (b : RadixSeq) (k : ℕ)
    [NormedAddCommGroup V] (f : FiniteRadixSpace b k → V) : ℝ≥0∞ :=
  if p = ∞ then
    ⨆ τ : FiniteRadixSpace b k, ↑‖f τ‖₊
  else
    let N := placeValue b (k + 1)
    (N : ℝ≥0∞)⁻¹ * (∑ τ : FiniteRadixSpace b k, (‖f τ‖₊ : ℝ≥0∞) ^ p.toReal) ^ (1 / p.toReal)

/--
The supremum norm (p = ∞ case).
-/
noncomputable def finiteSupNorm (b : RadixSeq) (k : ℕ)
    [NormedAddCommGroup V] (f : FiniteRadixSpace b k → V) : ℝ≥0∞ :=
  ⨆ τ : FiniteRadixSpace b k, ↑‖f τ‖₊

end Definitions

/-!
## Basic Properties
-/

section BasicProperties

variable {b : RadixSeq} {V : Type*}
variable [NormedAddCommGroup V]

/--
The Lp norm is always non-negative (values in ℝ≥0∞).
-/
theorem finiteLpNorm_nonneg (p : ℝ≥0∞) (k : ℕ)
    (f : FiniteRadixSpace b k → V) :
    0 ≤ finiteLpNorm p b k f := by
  simp only [finiteLpNorm]
  split_ifs with hp
  · exact bot_le
  · exact mul_nonneg (by positivity) (by positivity)

/--
The Lp norm of the zero function is zero.
-/
theorem finiteLpNorm_zero (p : ℝ≥0∞) (hp : 1 ≤ p) (k : ℕ) :
    finiteLpNorm p b k (0 : FiniteRadixSpace b k → V) = 0 := by
  simp only [finiteLpNorm, Pi.zero_apply, nnnorm_zero, ENNReal.coe_zero]
  split_ifs with hp_top
  · simp only [iSup_const]
  · have hp_pos : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le one_pos hp)) hp_top
    have h_inv_pos : 0 < 1 / p.toReal := by positivity
    simp only [ENNReal.zero_rpow_of_pos hp_pos, Finset.sum_const_zero,
      ENNReal.zero_rpow_of_pos h_inv_pos, mul_zero]

/--
Sup norm equals finiteLpNorm at p = ∞.
-/
theorem finiteSupNorm_eq_finiteLpNorm_top (k : ℕ) (f : FiniteRadixSpace b k → V) :
    finiteSupNorm b k f = finiteLpNorm ⊤ b k f := by
  simp only [finiteSupNorm, finiteLpNorm, if_true]

end BasicProperties

/-!
## Triangle Inequality for Sup Norm (p = ∞)
-/

section SupNormTriangle

variable {b : RadixSeq} {V : Type*}
variable [NormedAddCommGroup V]

/--
Triangle inequality for sup norm (p = ∞ case).

**Proof**: For each τ, ‖(f + g)(τ)‖ ≤ ‖f(τ)‖ + ‖g(τ)‖ ≤ sup|f| + sup|g|.
Taking sup over τ gives sup|f + g| ≤ sup|f| + sup|g|.
-/
theorem finiteSupNorm_add_le (k : ℕ) (f g : FiniteRadixSpace b k → V) :
    finiteSupNorm b k (f + g) ≤ finiteSupNorm b k f + finiteSupNorm b k g := by
  simp only [finiteSupNorm]
  apply iSup_le
  intro τ
  calc (‖(f + g) τ‖₊ : ℝ≥0∞)
      = ‖f τ + g τ‖₊ := rfl
    _ ≤ ‖f τ‖₊ + ‖g τ‖₊ := by exact_mod_cast nnnorm_add_le (f τ) (g τ)
    _ ≤ (⨆ σ, ↑‖f σ‖₊) + (⨆ σ, ↑‖g σ‖₊) := by
        apply add_le_add
        · exact le_iSup (fun σ => (‖f σ‖₊ : ℝ≥0∞)) τ
        · exact le_iSup (fun σ => (‖g σ‖₊ : ℝ≥0∞)) τ

/--
Triangle inequality for sup norm with subtraction.
-/
theorem finiteSupNorm_sub_le (k : ℕ) (f g : FiniteRadixSpace b k → V) :
    finiteSupNorm b k (f - g) ≤ finiteSupNorm b k f + finiteSupNorm b k g := by
  simp only [finiteSupNorm]
  apply iSup_le
  intro τ
  calc (‖(f - g) τ‖₊ : ℝ≥0∞)
      = ‖f τ - g τ‖₊ := rfl
    _ ≤ ‖f τ‖₊ + ‖g τ‖₊ := by exact_mod_cast nnnorm_sub_le (f τ) (g τ)
    _ ≤ (⨆ σ, ↑‖f σ‖₊) + (⨆ σ, ↑‖g σ‖₊) := by
        apply add_le_add
        · exact le_iSup (fun σ => (‖f σ‖₊ : ℝ≥0∞)) τ
        · exact le_iSup (fun σ => (‖g σ‖₊ : ℝ≥0∞)) τ

end SupNormTriangle

/-!
## Triangle Inequality for General Lp (1 ≤ p < ∞)

The triangle inequality for Lp norms with 1 ≤ p < ∞ is Minkowski's inequality.
-/

section MinkowskiInequality

variable {b : RadixSeq} {V : Type*}
variable [NormedAddCommGroup V]

/--
**Minkowski's inequality (finite Lp triangle inequality)**

For 1 ≤ p < ∞:
  (∑_τ ‖f(τ) + g(τ)‖^p)^{1/p} ≤ (∑_τ ‖f(τ)‖^p)^{1/p} + (∑_τ ‖g(τ)‖^p)^{1/p}

**Proof sketch**:
This is the discrete version of Minkowski's inequality. The key steps are:

1. **Hölder's inequality**: For conjugate exponents p, q with 1/p + 1/q = 1:
   ∑ |a_i · b_i| ≤ (∑ |a_i|^p)^{1/p} · (∑ |b_i|^q)^{1/q}

2. **Apply to |f + g|^p**:
   |f + g|^p = |f + g|^{p-1} · |f + g|
            ≤ |f + g|^{p-1} · (|f| + |g|)

3. **Sum and apply Hölder with exponents p and p/(p-1)**:
   ∑ |f + g|^p ≤ (∑ |f + g|^p)^{(p-1)/p} · [(∑ |f|^p)^{1/p} + (∑ |g|^p)^{1/p}]

4. **Divide** both sides by (∑ |f + g|^p)^{(p-1)/p} to get Minkowski.

**mathlib references**:
- `NNReal.inner_le_Lp_mul_Lq` (Hölder's inequality)
- `MeasureTheory.snorm_add_le` (continuous version)
-/
theorem finiteLpNorm_add_le_of_finite (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hp2 : p ≠ ⊤) (k : ℕ)
    (f g : FiniteRadixSpace b k → V) :
    finiteLpNorm p b k (f + g) ≤ finiteLpNorm p b k f + finiteLpNorm p b k g := by
  simp only [finiteLpNorm, hp2, ↓reduceIte]
  rw [← mul_add]
  apply mul_le_mul_right
  -- Goal: (∑ τ, ‖(f+g) τ‖₊^p)^{1/p} ≤ (∑ τ, ‖f τ‖₊^p)^{1/p} + (∑ τ, ‖g τ‖₊^p)^{1/p}
  have hp_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le one_pos hp1)) hp2
  have hp_ge : 1 ≤ p.toReal := by
    have : (1 : ℝ≥0∞).toReal ≤ p.toReal :=
      ENNReal.toReal_le_toReal (by norm_num) hp2 |>.mpr hp1
    simpa using this
  -- Pointwise triangle: ‖(f+g) τ‖₊ ≤ ‖f τ‖₊ + ‖g τ‖₊
  have h_pointwise : ∀ τ : FiniteRadixSpace b k,
      (‖(f + g) τ‖₊ : ℝ≥0∞) ≤ (‖f τ‖₊ : ℝ≥0∞) + (‖g τ‖₊ : ℝ≥0∞) := by
    intro τ
    exact_mod_cast nnnorm_add_le (f τ) (g τ)
  -- Step 1: Monotonicity of rpow and sum
  have h_sum_le : ∑ τ : FiniteRadixSpace b k, (‖(f + g) τ‖₊ : ℝ≥0∞) ^ p.toReal ≤
      ∑ τ : FiniteRadixSpace b k, ((‖f τ‖₊ : ℝ≥0∞) + (‖g τ‖₊ : ℝ≥0∞)) ^ p.toReal := by
    apply Finset.sum_le_sum
    intro τ _
    exact ENNReal.rpow_le_rpow (h_pointwise τ) (le_of_lt hp_pos)
  -- Step 2: Apply ENNReal.Lp_add_le (Minkowski)
  have h_mink := ENNReal.Lp_add_le (s := Finset.univ)
    (fun τ => (‖f τ‖₊ : ℝ≥0∞)) (fun τ => (‖g τ‖₊ : ℝ≥0∞)) hp_ge
  -- Combine
  calc (∑ τ, (‖(f + g) τ‖₊ : ℝ≥0∞) ^ p.toReal) ^ (1 / p.toReal)
      ≤ (∑ τ, ((‖f τ‖₊ : ℝ≥0∞) + (‖g τ‖₊ : ℝ≥0∞)) ^ p.toReal) ^ (1 / p.toReal) :=
        ENNReal.rpow_le_rpow h_sum_le (by positivity)
    _ ≤ _ := h_mink

/--
Minkowski's inequality for subtraction (finite Lp case).

Follows from the addition version since ‖f - g‖ = ‖f + (-g)‖ and ‖-g‖ = ‖g‖.
-/
theorem finiteLpNorm_sub_le_of_finite (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hp2 : p ≠ ⊤) (k : ℕ)
    (f g : FiniteRadixSpace b k → V) :
    finiteLpNorm p b k (f - g) ≤ finiteLpNorm p b k f + finiteLpNorm p b k g := by
  have h_neg : finiteLpNorm p b k (-g) = finiteLpNorm p b k g := by
    simp only [finiteLpNorm]
    split_ifs with hp
    · simp only [Pi.neg_apply, nnnorm_neg]
    · congr 2; apply Finset.sum_congr rfl; intro τ _; simp only [Pi.neg_apply, nnnorm_neg]
  calc finiteLpNorm p b k (f - g)
      = finiteLpNorm p b k (f + (-g)) := by rw [sub_eq_add_neg]
    _ ≤ finiteLpNorm p b k f + finiteLpNorm p b k (-g) :=
        finiteLpNorm_add_le_of_finite p hp1 hp2 k f (-g)
    _ = finiteLpNorm p b k f + finiteLpNorm p b k g := by rw [h_neg]

end MinkowskiInequality

/-!
## Combined Triangle Inequality (All p ≥ 1)
-/

section CombinedTriangle

variable {b : RadixSeq} {V : Type*}
variable [NormedAddCommGroup V]

/--
**Triangle inequality for finiteLpNorm** (all p ≥ 1).

For any 1 ≤ p ≤ ∞:
  |f + g|_{p,k} ≤ |f|_{p,k} + |g|_{p,k}

This combines the p = ∞ case (proven directly) with the 1 ≤ p < ∞ case
(Minkowski's inequality, axiomatized).
-/
theorem finiteLpNorm_add_le (p : ℝ≥0∞) (hp : 1 ≤ p) (k : ℕ)
    (f g : FiniteRadixSpace b k → V) :
    finiteLpNorm p b k (f + g) ≤ finiteLpNorm p b k f + finiteLpNorm p b k g := by
  by_cases hp_top : p = ⊤
  · -- Case p = ∞: Use sup norm triangle inequality
    simp only [finiteLpNorm, hp_top, if_true]
    exact finiteSupNorm_add_le k f g
  · -- Case 1 ≤ p < ∞: Use Minkowski's inequality
    exact finiteLpNorm_add_le_of_finite p hp hp_top k f g

/--
**Triangle inequality for differences** (all p ≥ 1).

For any 1 ≤ p ≤ ∞:
  |f - g|_{p,k} ≤ |f|_{p,k} + |g|_{p,k}

This is the key lemma needed for the detail operator bound.
-/
theorem finiteLpNorm_sub_le (p : ℝ≥0∞) (hp : 1 ≤ p) (k : ℕ)
    (f g : FiniteRadixSpace b k → V) :
    finiteLpNorm p b k (f - g) ≤ finiteLpNorm p b k f + finiteLpNorm p b k g := by
  by_cases hp_top : p = ⊤
  · -- Case p = ∞: Use sup norm triangle inequality
    simp only [finiteLpNorm, hp_top, if_true]
    exact finiteSupNorm_sub_le k f g
  · -- Case 1 ≤ p < ∞: Use Minkowski's inequality for subtraction
    exact finiteLpNorm_sub_le_of_finite p hp hp_top k f g

end CombinedTriangle

/-!
## Negation
-/

section Negation

variable {b : RadixSeq} {V : Type*}
variable [NormedAddCommGroup V]

/--
The Lp norm of negation equals the original norm.

|−f|_p = |f|_p

**Proof**: ‖−v‖ = ‖v‖ for all v in a normed space.
-/
theorem finiteLpNorm_neg (p : ℝ≥0∞) (k : ℕ)
    (f : FiniteRadixSpace b k → V) :
    finiteLpNorm p b k (-f) = finiteLpNorm p b k f := by
  simp only [finiteLpNorm]
  split_ifs with hp
  · -- p = ∞ case
    simp only [Pi.neg_apply, nnnorm_neg]
  · -- p < ∞ case
    congr 2
    apply Finset.sum_congr rfl
    intro τ _
    simp only [Pi.neg_apply, nnnorm_neg]

end Negation

end FdrsFormal.FunctionSpaces.Measure
