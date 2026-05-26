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

# Block Projection Properties

This file proves the key properties of block projections: idempotence,
tower property, and contraction bounds.

## Mathematical Content (fdrs.md lines 640-655)

**Proposition 16 (projection / tower properties)**:
For 1 ≤ L ≤ M and f ∈ L^1:
1. P_L f ∈ 𝕋_L(V)  [block-constant]
2. P_L(P_L f) = P_L f  [idempotent]
3. P_L(P_M f) = P_L f  [tower property]

**Proposition 17 (compatibility with block coordinates)**:
If f ∈ 𝕋_M(V) with M ≥ L, then P_L f is obtained by averaging the M-level
block values over the children cylinders refining each U(s).

## References

- fdrs.md, Section 3, Propositions 3.3-3.4 (lines 640-655)
- THEOREM_MAPPING.md, FunctionSpaces/Projections section
-/

import FdrsFormal.FunctionSpaces.Projections.Definition
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace FdrsFormal.FunctionSpaces.Projections.Properties

open FdrsFormal.Core.Primitives FdrsFormal.Core.Infinite
open FdrsFormal.Topology.Ultrametric
open FdrsFormal.FunctionSpaces.Basic FdrsFormal.FunctionSpaces.Measure
open FdrsFormal.FunctionSpaces.Projections
open MeasureTheory

/-!
## Summary of Key Properties

The block projections (P_L)_{L≥1} satisfy:

1. **Image**: P_L f ∈ 𝕋_L(V) for all f
2. **Idempotent**: P_L ∘ P_L = P_L
3. **Tower**: P_L ∘ P_M = P_L for L ≤ M
4. **Filtration**: 𝕋_1(V) ⊆ 𝕋_2(V) ⊆ 𝕋_3(V) ⊆ ...
5. **Linear**: P_L(af + bg) = a·P_L(f) + b·P_L(g)
6. **Positive**: P_L preserves positivity of real-valued functions
7. **Contraction**: ‖P_L f‖ ≤ ‖f‖ in L^p norms

These make (P_L) a martingale-like sequence of operators.
-/

section Idempotent

variable {b : RadixSeq} {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/--
**Proposition 16(2)**: P_L is idempotent: P_L ∘ P_L = P_L.

**Proof**: P_L f is block-constant at level L. Applying P_L again to a
block-constant function just returns the same function, since the average
of a constant over its cylinder is that constant.
-/
theorem blockProjection_idempotent' (L : ℕ) :
    ∀ f : CompletedSpace b → V, blockProjection b L (blockProjection b L f) = blockProjection b L f :=
  blockProjection_idempotent L

/--
P_L restricts to the identity on 𝕋_L(V).
-/
theorem blockProjection_on_blockConstant (L : ℕ) (f : BlockConstantSpace b L V) :
    blockProjection b L f.val = f.val :=
  blockProjection_fixedPoint L f

end Idempotent

/-!
## Tower Properties
-/

section Tower

variable {b : RadixSeq} {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/--
**Proposition 16(3)**: Tower property: P_L ∘ P_M = P_L for L ≤ M.

**Proof**: Let g = P_M f. Then g is constant on each level-M cylinder.
Applying P_L averages g over level-L cylinders. Since each level-L cylinder
is a disjoint union of level-M cylinders, and g is constant on each of those,
this is equivalent to averaging f directly over level-L cylinders.
-/
theorem blockProjection_tower' (L M : ℕ) (hLM : L ≤ M) :
    ∀ f : CompletedSpace b → V, Integrable f (uniformProductMeasure b) →
      blockProjection b L (blockProjection b M f) = blockProjection b L f :=
  fun f hf => blockProjection_tower L M hLM f hf

/--
The tower property in terms of function composition.
-/
theorem blockProjection_comp_le (L M : ℕ) (hLM : L ≤ M) (f : CompletedSpace b → V)
    (hf : Integrable f (uniformProductMeasure b)) :
    blockProjection b L (blockProjection b M f) = blockProjection b L f :=
  blockProjection_tower L M hLM f hf

/--
Projections satisfy P_L ∘ P_M = P_{min(L,M)}.
-/
theorem blockProjection_comp_eq_min (L M : ℕ) (f : CompletedSpace b → V)
    (hf : Integrable f (uniformProductMeasure b)) :
    blockProjection b L (blockProjection b M f) = blockProjection b (min L M) f := by
  rcases Nat.lt_or_ge L M with hLM | hML
  · -- L < M: P_L ∘ P_M = P_L = P_{min(L,M)}
    rw [min_eq_left (Nat.le_of_lt hLM)]
    exact blockProjection_tower L M (Nat.le_of_lt hLM) f hf
  · -- M ≤ L: need P_L ∘ P_M = P_M = P_{min(L,M)}
    rw [min_eq_right hML]
    -- P_M f is block-constant at level M
    have hM : IsBlockConstant (blockProjection b M f) M := blockProjection_isBlockConstant M f
    -- Hence block-constant at level L (since M ≤ L)
    have hL : IsBlockConstant (blockProjection b M f) L := isBlockConstant_of_le hML hM
    -- So P_L(P_M f) = P_M f (by fixed point)
    exact blockProjection_fixedPoint L ⟨blockProjection b M f, hL⟩

/--
Projections commute: P_L ∘ P_M = P_M ∘ P_L = P_{min(L,M)}.
-/
theorem blockProjection_comm' (L M : ℕ) (f : CompletedSpace b → V)
    (hf : Integrable f (uniformProductMeasure b)) :
    blockProjection b L (blockProjection b M f) = blockProjection b M (blockProjection b L f) := by
  rw [blockProjection_comp_eq_min L M f hf, blockProjection_comp_eq_min M L f hf, min_comm]

end Tower

/-!
## Monotonicity and Filtration
-/

section Filtration

variable {b : RadixSeq} {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/--
The ranges of P_L form an increasing chain: range(P_L) ⊆ range(P_M) for L ≤ M.
-/
theorem blockProjection_range_chain (L M : ℕ) (hLM : L ≤ M) :
    Set.range (fun f => blockProjection b L f) ⊆ Set.range (fun f => blockProjection b M (f : CompletedSpace b → V)) := by
  -- This is already proved in Definition.lean as blockProjection_range_mono
  exact blockProjection_range_mono L M hLM

/--
The kernels of P_L form a decreasing chain.
-/
theorem blockProjection_ker_chain (L M : ℕ) (hLM : L ≤ M) :
    {f : CompletedSpace b → V | Integrable f (uniformProductMeasure b) ∧
      blockProjection b M f = 0} ⊆
    {f | blockProjection b L f = 0} := by
  intro f ⟨hfi, hf⟩
  simp only [Set.mem_setOf_eq]
  -- By tower property: P_L f = P_L(P_M f)
  rw [← blockProjection_tower L M hLM f hfi]
  -- P_M f = 0, so P_L(P_M f) = P_L 0
  rw [hf]
  -- P_L 0 = 0 (P_L of constant 0 is constant 0)
  exact blockProjection_const L (0 : V)

end Filtration

/-!
## Contraction Properties
-/

section Contraction

variable {b : RadixSeq}

/--
P_L is a contraction in sup norm: if ‖f x‖ ≤ M for all x, then ‖P_L f x‖ ≤ M.

**Proof**: ‖B_L • ∫_{U(s)} f dμ‖ = B_L · ‖∫ f‖ ≤ B_L · M · μ(U(s)) = B_L · M / B_L = M.
-/
theorem blockProjection_supNorm_le (L : ℕ) (f : CompletedSpace b → ℝ) (M : ℝ)
    (hM : 0 ≤ M)
    (hf : ∀ x, ‖f x‖ ≤ M)
    (hfi : Integrable f (uniformProductMeasure b)) :
    ∀ x, ‖blockProjection b L f x‖ ≤ M := by
  intro x
  simp only [blockProjection]
  rw [norm_smul, Real.norm_natCast]
  -- Goal: ↑(placeValue b L) * ‖∫ y in U(s), f y ∂μ‖ ≤ M
  set s := prefixOf b L x
  set B := (placeValue b L : ℝ)
  have hBne : B ≠ 0 := Nat.cast_ne_zero.mpr (placeValue.ne_zero L)
  have hBpos : (0 : ℝ) < B := Nat.cast_pos.mpr (placeValue.pos L)
  suffices h : ‖∫ y in cylinderSet b L s, f y ∂(uniformProductMeasure b)‖ ≤ M * B⁻¹ by
    calc B * ‖∫ y in cylinderSet b L s, f y ∂(uniformProductMeasure b)‖
        ≤ B * (M * B⁻¹) := by gcongr
      _ = M := by rw [mul_comm M, ← mul_assoc, mul_inv_cancel₀ hBne, one_mul]
  calc ‖∫ y in cylinderSet b L s, f y ∂(uniformProductMeasure b)‖
      ≤ ∫ y in cylinderSet b L s, ‖f y‖ ∂(uniformProductMeasure b) :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ y in cylinderSet b L s, M ∂(uniformProductMeasure b) :=
        MeasureTheory.setIntegral_mono hfi.norm.integrableOn
          (integrable_const M).integrableOn hf
    _ = M * B⁻¹ := by
        rw [MeasureTheory.setIntegral_const, smul_eq_mul,
          MeasureTheory.Measure.real_def, cylinder_measure L s,
          ENNReal.toReal_inv, ENNReal.toReal_natCast]
        ring

/--
P_L is a contraction in L^1 norm: ‖P_L f‖_1 ≤ ‖f‖_1.

**Proof**: This is Jensen's inequality applied to conditional expectation.

**Mathlib approach**: Would use `MeasureTheory.Integrable.norm_condexp_le` or
Jensen's inequality for conditional expectations. Since blockProjection is
the conditional expectation E[f | ℱ_L], we have:
  ‖E[f | ℱ_L]‖_1 ≤ ‖f‖_1

**Note**: Axiomatized since measure is axiomatized.
-/
theorem blockProjection_L1_le (L : ℕ) (f : CompletedSpace b → ℝ)
    (hf : Integrable f (uniformProductMeasure b)) :
    ∫ x, ‖blockProjection b L f x‖ ∂(uniformProductMeasure b) ≤
    ∫ x, ‖f x‖ ∂(uniformProductMeasure b) := by
  -- Pointwise bound: ‖P_L f(x)‖ ≤ P_L(‖f‖)(x)
  have hpw : ∀ x, ‖blockProjection b L f x‖ ≤ blockProjection b L (fun y => ‖f y‖) x := by
    intro x
    simp only [blockProjection]
    rw [norm_smul, Real.norm_natCast, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (Nat.cast_nonneg _)
  -- Combine: ∫ ‖P_L f‖ dμ ≤ ∫ P_L(‖f‖) dμ = ∫ ‖f‖ dμ
  calc ∫ x, ‖blockProjection b L f x‖ ∂(uniformProductMeasure b)
      ≤ ∫ x, blockProjection b L (fun y => ‖f y‖) x ∂(uniformProductMeasure b) :=
        MeasureTheory.integral_mono (blockProjection_integrable L f hf).norm
          (blockProjection_integrable L _ hf.norm) hpw
    _ = ∫ x, ‖f x‖ ∂(uniformProductMeasure b) :=
        integral_blockProjection L _ hf.norm

/--
P_L is a contraction in L^2 norm: ‖P_L f‖_2 ≤ ‖f‖_2.

**Proof**: P_L is an orthogonal projection, hence a contraction.

**Mathlib approach**: P_L is the orthogonal projection onto the subspace of
L-block-constant functions in L². Orthogonal projections are contractions:
  ‖P_L f‖₂² = ‖P_L f‖₂² + ‖f - P_L f‖₂² ≤ ‖f‖₂²
This uses Pythagoras theorem and the fact that P_L f ⊥ (f - P_L f).

In mathlib: `OrthogonalProjection.norm_le` or `Submodule.norm_orthogonalProjection_le`

**Note**: Axiomatized since measure is axiomatized.
-/
theorem blockProjection_L2_le (L : ℕ) (f : CompletedSpace b → ℝ)
    (hf : Integrable f (uniformProductMeasure b))
    (hf2 : Integrable (fun x => f x ^ 2) (uniformProductMeasure b)) :
    ∫ x, (blockProjection b L f x) ^ 2 ∂(uniformProductMeasure b) ≤
    ∫ x, (f x) ^ 2 ∂(uniformProductMeasure b) := by
  set μ := uniformProductMeasure b
  have hms := fun s => @cylinder_measurableSet b L s
  have hpd := cylinderSet_pairwiseDisjoint (b := b) L
  -- Integrability of (P_L f)² via block-constant decomposition
  have hPf2 : Integrable (fun x => (blockProjection b L f x) ^ 2) μ := by
    -- P_L f is block-constant, so (P_L f)² is a step function
    have h_bc := blockProjection_isBlockConstant (b := b) L f
    -- Step functions on finite cylinders are integrable
    have h_eq : (fun x => (blockProjection b L f x) ^ 2) =
        fun x => ∑ s : PrefixSet b L, (cylinderSet b L s).indicator
          (fun _ => ((placeValue b L : ℝ) *
            ∫ y in cylinderSet b L s, f y ∂(uniformProductMeasure b)) ^ 2) x := by
      ext x; simp only [blockProjection, smul_eq_mul]
      rw [Finset.sum_eq_single (prefixOf b L x)]
      · simp [Set.indicator_of_mem (mem_cylinderSet_prefixOf b L x)]
      · intro t _ hne; rw [Set.indicator_of_notMem]
        intro hmem; exact hne ((mem_cylinderSet_iff_prefixOf b L t x).mp hmem).symm
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [h_eq]; apply integrable_finset_sum; intro s _
    exact (integrable_indicator_iff (hms s)).mpr (integrableOn_const (cylinder_measure_ne_top L s))
  -- Decompose both integrals over L-cylinders
  conv_lhs => rw [← setIntegral_univ, ← cylinderSet_union_univ b L]
  conv_rhs => rw [← setIntegral_univ, ← cylinderSet_union_univ b L]
  rw [integral_iUnion_fintype hms hpd (fun s => hPf2.integrableOn),
      integral_iUnion_fintype hms hpd (fun s => hf2.integrableOn)]
  -- Per-cylinder inequality: ∫_{U(s)} (P_L f)² ≤ ∫_{U(s)} f²
  apply Finset.sum_le_sum
  intro s _
  obtain ⟨x₀, hx₀⟩ := cylinder_nonempty b L s
  set B := (placeValue b L : ℝ)
  set I := ∫ y in cylinderSet b L s, f y ∂μ
  set c := B * I
  -- P_L f = c on U(s)
  have hconst : ∀ y ∈ cylinderSet b L s,
      blockProjection b L f y = c := by
    intro y hy
    have hps := (mem_cylinderSet_iff_prefixOf b L s y).mp hy
    show (placeValue b L : ℝ) • ∫ z in cylinderSet b L (prefixOf b L y), f z ∂μ = c
    rw [hps, smul_eq_mul]
  -- LHS = c² / B
  rw [setIntegral_congr_fun (hms s) (fun y hy => by rw [hconst y hy])]
  rw [setIntegral_const, smul_eq_mul, Measure.real_def,
      cylinder_measure L s, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  -- Goal: c² * B⁻¹ ≤ ∫ f²
  have hBpos : (0 : ℝ) < B := Nat.cast_pos.mpr (placeValue.pos L)
  -- Variance non-negativity: 0 ≤ ∫_U (f - c)²
  have h_nn : 0 ≤ ∫ y in cylinderSet b L s, (f y - c) ^ 2 ∂μ :=
    setIntegral_nonneg (hms s) (fun _ _ => sq_nonneg _)
  -- Expand ∫ (f - c)² = ∫ f² + (-2c·I + c²/B)
  have h_expand : ∫ y in cylinderSet b L s, (f y - c) ^ 2 ∂μ =
      ∫ y in cylinderSet b L s, (f y) ^ 2 ∂μ +
        ((-2) * c * I + c ^ 2 * B⁻¹) := by
    have h_eq : ∀ y, (f y - c) ^ 2 = f y ^ 2 + ((-2) * c * f y + c ^ 2) := by intro y; ring
    simp_rw [h_eq]
    have hg_int : IntegrableOn (fun y => (-2) * c * f y + c ^ 2) (cylinderSet b L s) μ :=
      ((hf.const_mul ((-2) * c)).add (integrable_const (c ^ 2))).integrableOn
    rw [integral_add hf2.integrableOn hg_int]
    congr 1
    have hcf_int : IntegrableOn (fun y => (-2) * c * f y) (cylinderSet b L s) μ :=
      (hf.const_mul ((-2) * c)).integrableOn
    rw [integral_add hcf_int (integrable_const (c ^ 2)).integrableOn]
    rw [integral_const_mul, setIntegral_const, smul_eq_mul, Measure.real_def,
        cylinder_measure L s, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    ring
  -- From h_nn and h_expand: c²/B ≤ ∫ f²
  have h_combined : 0 ≤ ∫ y in cylinderSet b L s, f y ^ 2 ∂μ + (-2 * c * I + c ^ 2 * B⁻¹) := by
    rw [← h_expand]; exact h_nn
  -- Key: since c = B*I, -2cI + c²/B = -(c²/B)
  have h_alg : -2 * c * I + c ^ 2 * B⁻¹ = -(c ^ 2 * B⁻¹) := by
    show -2 * (B * I) * I + (B * I) ^ 2 * B⁻¹ = -((B * I) ^ 2 * B⁻¹)
    field_simp
    ring
  linarith

/--
P_L is a contraction in L^p norm for 1 ≤ p: ∫|P_L f|^p ≤ ∫|f|^p.

**Proof**: Pointwise |P_L f(x)|^p ≤ P_L(|f|^p)(x) by Jensen's inequality
(convexity of t ↦ t^p on [0,∞) for p ≥ 1), then integrate and use
∫ P_L g = ∫ g.
-/
theorem blockProjection_Lp_le (L : ℕ) (p : ℝ) (hp : 1 ≤ p) (f : CompletedSpace b → ℝ)
    (hf : Integrable f (uniformProductMeasure b))
    (hfp : Integrable (fun x => |f x| ^ p) (uniformProductMeasure b)) :
    ∫ x, |blockProjection b L f x| ^ p ∂(uniformProductMeasure b) ≤
    ∫ x, |f x| ^ p ∂(uniformProductMeasure b) := by
  have hp_pos : 0 < p := lt_of_lt_of_le one_pos hp
  have hms := fun s => @cylinder_measurableSet b L s
  have hPfp_int := blockProjection_integrable L (fun x => |f x| ^ p) hfp
  -- Integrability of |P_L f|^p (block-constant step function)
  have h_int_lhs : Integrable (fun x => |blockProjection b L f x| ^ p)
      (uniformProductMeasure b) := by
    have h_eq : (fun x => |blockProjection b L f x| ^ p) =
        fun x => ∑ s : PrefixSet b L, (cylinderSet b L s).indicator
          (fun _ => |(placeValue b L : ℝ) *
            ∫ y in cylinderSet b L s, f y ∂(uniformProductMeasure b)| ^ p) x := by
      ext x; simp only [blockProjection, smul_eq_mul]
      rw [Finset.sum_eq_single (prefixOf b L x)]
      · simp [Set.indicator_of_mem (mem_cylinderSet_prefixOf b L x)]
      · intro t _ hne; rw [Set.indicator_of_notMem]
        intro hmem; exact hne ((mem_cylinderSet_iff_prefixOf b L t x).mp hmem).symm
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [h_eq]; apply integrable_finset_sum; intro s _
    exact (integrable_indicator_iff (hms s)).mpr
      (integrableOn_const (cylinder_measure_ne_top L s))
  -- Suffices: pointwise |P_L f(x)|^p ≤ P_L(|f|^p)(x)
  suffices h_pw : ∀ x, |blockProjection b L f x| ^ p ≤
      blockProjection b L (fun y => |f y| ^ p) x by
    calc ∫ x, |blockProjection b L f x| ^ p ∂(uniformProductMeasure b)
        ≤ ∫ x, blockProjection b L (fun y => |f y| ^ p) x ∂(uniformProductMeasure b) :=
          MeasureTheory.integral_mono h_int_lhs hPfp_int h_pw
      _ = ∫ x, |f x| ^ p ∂(uniformProductMeasure b) := integral_blockProjection L _ hfp
  -- Prove pointwise bound via Jensen on each cylinder
  intro x
  set s := prefixOf b L x
  set S := cylinderSet b L s
  set B := (placeValue b L : ℝ)
  set μ := uniformProductMeasure b
  have hB_pos : (0 : ℝ) < B := Nat.cast_pos.mpr (placeValue.pos L)
  have hS_ne : μ S ≠ 0 := by
    rw [cylinder_measure L s]; exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  have hS_fin : μ S ≠ ⊤ := cylinder_measure_ne_top L s
  -- Unfold blockProjection to B * ∫_S
  simp only [blockProjection, smul_eq_mul]
  -- Jensen: (⨍ |f|)^p ≤ ⨍ |f|^p for convex (·^p) on [0,∞)
  have h_j := ConvexOn.map_set_average_le (convexOn_rpow hp)
    (continuousOn_id.rpow_const (fun _ _ => Or.inr (le_of_lt hp_pos)))
    isClosed_Ici hS_ne hS_fin
    (ae_of_all _ (fun y => Set.mem_Ici.mpr (abs_nonneg (f y))))
    hf.norm.integrableOn hfp.integrableOn
  -- Convert ⨍ to B * ∫ form
  rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq, smul_eq_mul, smul_eq_mul] at h_j
  rw [show (μ.real S)⁻¹ = B from by
    rw [MeasureTheory.Measure.real_def, cylinder_measure L s,
        ENNReal.toReal_inv, ENNReal.toReal_natCast, inv_inv]] at h_j
  -- Chain: |B * ∫f|^p ≤ (B * ∫|f|)^p ≤ B * ∫|f|^p
  have h_tri : |B * ∫ y in S, f y ∂μ| ≤ B * ∫ y in S, |f y| ∂μ := by
    rw [abs_mul, abs_of_nonneg (le_of_lt hB_pos)]
    gcongr
    rw [← Real.norm_eq_abs]
    exact le_trans (norm_integral_le_integral_norm _) (le_of_eq (by congr))
  calc |B * ∫ y in S, f y ∂μ| ^ p
      ≤ (B * ∫ y in S, |f y| ∂μ) ^ p :=
        Real.rpow_le_rpow (abs_nonneg _) h_tri (le_of_lt hp_pos)
    _ ≤ B * ∫ y in S, |f y| ^ p ∂μ := h_j

end Contraction

/-!
## Positivity Preservation
-/

section Positivity

variable {b : RadixSeq}

/--
P_L preserves non-negativity: if f ≥ 0 then P_L f ≥ 0.

**Proof**: Averaging non-negative values gives a non-negative result.
-/
theorem blockProjection_nonneg (L : ℕ) (f : CompletedSpace b → ℝ)
    (hf : ∀ x, 0 ≤ f x) : ∀ x, 0 ≤ blockProjection b L f x := by
  intro x
  simp only [blockProjection]
  -- Need: 0 ≤ (placeValue b L : ℝ) • ∫ y in U(s), f y dμ
  apply smul_nonneg
  · -- placeValue b L ≥ 0
    exact Nat.cast_nonneg (placeValue b L)
  · -- Integral of non-negative function is non-negative
    apply MeasureTheory.setIntegral_nonneg
    · exact @cylinder_measurableSet b L (prefixOf b L x)
    · intro y _
      exact hf y

/--
P_L preserves ordering: if f ≤ g pointwise then P_L f ≤ P_L g pointwise.

**Proof**: Each value of P_L f is B_L • ∫_{U(s)} f dμ. Since f ≤ g on U(s),
`setIntegral_mono` gives ∫ f ≤ ∫ g, and multiplication by B_L ≥ 0 preserves ≤.
-/
theorem blockProjection_mono (L : ℕ) (f g : CompletedSpace b → ℝ)
    (hfg : ∀ x, f x ≤ g x)
    (hf : Integrable f (uniformProductMeasure b))
    (hg : Integrable g (uniformProductMeasure b)) :
    ∀ x, blockProjection b L f x ≤ blockProjection b L g x := by
  intro x
  simp only [blockProjection]
  apply smul_le_smul_of_nonneg_left
  · exact MeasureTheory.setIntegral_mono hf.integrableOn hg.integrableOn hfg
  · exact Nat.cast_nonneg _

end Positivity

/-!
## Coarsening Interpretation

P_L as the coarsening map in the block tree.
-/

section Coarsening

variable {b : RadixSeq} {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/--
**Proposition 17**: P_L coarsens by averaging over children.

For f ∈ 𝕋_M(V) and s ∈ Σ_L, (P_L f) on U(s) equals the average of f
over U(s), which decomposes into a weighted average of f's values on the
B_{M}/B_{L} child cylinders at level M. Since f is M-block-constant,
P_M(f) = f, so P_L(f) = P_L(P_M(f)), giving the tower property.
-/
theorem blockProjection_as_coarsening (L M : ℕ) (hLM : L ≤ M)
    (f : BlockConstantSpace b M V) :
    blockProjection b L f.val = blockProjection b L (blockProjection b M f.val) := by
  rw [blockProjection_fixedPoint M f]

/--
The number of children: B_L divides B_M for L ≤ M.

Each level-L cylinder contains B_M / B_L = ∏_{i=L}^{M-1} b_i level-M sub-cylinders.

**Proof**: By induction on L ≤ M. The step uses B_{M+1} = B_M · b_M.
-/
theorem cylinder_children_count (L M : ℕ) (hLM : L ≤ M) :
    placeValue b L ∣ placeValue b M := by
  induction hLM with
  | refl => exact dvd_refl _
  | step _ ih => exact dvd_mul_of_dvd_left ih _

end Coarsening

end FdrsFormal.FunctionSpaces.Projections.Properties
