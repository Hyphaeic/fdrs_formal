/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Detail Operators and Telescoping

This file defines the detail operators Δ_L that capture the "new information"
when moving from resolution L to resolution L+1.

## Mathematical Content (fdrs.md lines 660-696)

**Definition 23 (detail operators)**:
Define the **detail** (increment) operators on L^1 by
  Δ_L f := P_{L+1} f - P_L f  (L ≥ 1)
and define P_0 f := ∫ f dμ (a constant function) if desired.

**Proposition 18 (telescoping identity)**:
For any N > 1,
  P_N f = P_1 f + ∑_{L=1}^{N-1} Δ_L f

**Theorem 4 (convergence to f)**:
Let 1 ≤ p < ∞ and f ∈ L^p(R̂, μ; V). Then
  P_L f → f in L^p as L → ∞
If additionally f is continuous, then
  ‖P_L f - f‖_∞ → 0

## Implementation Notes

- Δ_L captures the "detail at scale L": information lost when coarsening from L+1 to L
- The telescoping identity shows f ≈ P_1 f + Δ_1 f + Δ_2 f + ...
- This is the mixed-radix analog of wavelet decomposition
- Convergence uses martingale convergence theorem

## References

- fdrs.md, Section 4, Definitions 4.1-4.3 (lines 660-696)
- THEOREM_MAPPING.md, FunctionSpaces/Projections section
-/

import FdrsFormal.FunctionSpaces.Projections.Properties
import Mathlib.Topology.UniformSpace.HeineCantor

namespace FdrsFormal.FunctionSpaces.Projections.Details

open FdrsFormal.Core.Primitives FdrsFormal.Core.Infinite
open FdrsFormal.FunctionSpaces.Basic FdrsFormal.FunctionSpaces.Measure
open FdrsFormal.FunctionSpaces.Projections
open MeasureTheory

/-!
## Detail Operator Definition
-/

section Definition

variable {b : RadixSeq} {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/--
**Definition 23**: The detail operator Δ_L := P_{L+1} - P_L.

This captures the "new information" revealed when refining from resolution L
to resolution L+1.
-/
noncomputable def detailOperator (b : RadixSeq) (L : ℕ)
    (f : CompletedSpace b → V) : CompletedSpace b → V :=
  blockProjection b (L + 1) f - blockProjection b L f

/-- Notation for detail operator -/
scoped notation "Δ_" L => detailOperator _ L

/--
Alternative definition expanding the formula.
-/
theorem detailOperator_def (L : ℕ) (f : CompletedSpace b → V) (x : CompletedSpace b) :
    detailOperator b L f x = blockProjection b (L + 1) f x - blockProjection b L f x := rfl

/--
The "constant average" operator P_0: integrate over all of R̂.

P_0 f := ∫ f dμ (extended to a constant function).
-/
noncomputable def globalAverage (b : RadixSeq)
    (f : CompletedSpace b → V) : CompletedSpace b → V :=
  fun _ => ∫ x, f x ∂(uniformProductMeasure b)

-- Note: Use globalAverage b f for the "P_0" operator

/--
P_0 equals the global average: blockProjection b 0 = globalAverage b.

At level 0, there is only one cylinder (the entire space), so block projection
at level 0 averages over all of R̂.
-/
theorem blockProjection_zero (f : CompletedSpace b → V) :
    blockProjection b 0 f = globalAverage b f := by
  ext x
  simp only [blockProjection, globalAverage]
  -- The cylinder at level 0 is the entire space
  have h_cylinder : cylinderSet b 0 (prefixOf b 0 x) = Set.univ := by
    ext y
    simp only [cylinderSet, Set.mem_univ, iff_true]
    intro i
    -- Fin 0 is empty, so this is vacuously true
    exact Fin.elim0 i
  rw [h_cylinder, MeasureTheory.Measure.restrict_univ]
  -- placeValue b 0 = 1
  have h_place_zero : placeValue b 0 = 1 := rfl
  simp only [h_place_zero, Nat.cast_one, one_smul]

end Definition

/-!
## Basic Properties of Detail Operators
-/

section BasicProperties

variable {b : RadixSeq} {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/--
Δ_L f is block-constant at level L+1 (not L!).

The detail lives in the finer resolution.
-/
theorem detailOperator_isBlockConstant (L : ℕ) (f : CompletedSpace b → V) :
    IsBlockConstant (detailOperator b L f) (L + 1) := by
  -- Both P_{L+1} f and P_L f are block-constant at level L+1
  -- (P_L f is block-constant at L, hence also at L+1)
  intro s x y hx hy
  simp only [detailOperator, Pi.sub_apply]
  have h1 := blockProjection_isBlockConstant (L + 1) f s x y hx hy
  have h2 : IsBlockConstant (blockProjection b L f) (L + 1) :=
    isBlockConstant_of_le (Nat.le_succ L) (blockProjection_isBlockConstant L f)
  have h3 := h2 s x y hx hy
  rw [h1, h3]

/--
Δ_L is linear.
-/
theorem detailOperator_add (L : ℕ) (f g : CompletedSpace b → V)
    (hf : Integrable f (uniformProductMeasure b))
    (hg : Integrable g (uniformProductMeasure b)) :
    detailOperator b L (f + g) = detailOperator b L f + detailOperator b L g := by
  simp only [detailOperator]
  rw [blockProjection_add _ _ _ hf hg, blockProjection_add _ _ _ hf hg]
  -- (P_{L+1}(f) + P_{L+1}(g)) - (P_L(f) + P_L(g))
  -- = (P_{L+1}(f) - P_L(f)) + (P_{L+1}(g) - P_L(g))
  abel

theorem detailOperator_smul (L : ℕ) (r : ℝ) (f : CompletedSpace b → V) :
    detailOperator b L (r • f) = r • detailOperator b L f := by
  simp only [detailOperator]
  rw [blockProjection_smul, blockProjection_smul]
  -- r • P_{L+1}(f) - r • P_L(f) = r • (P_{L+1}(f) - P_L(f))
  rw [← smul_sub]

/--
Δ_L of a constant function is zero.

Constants have no detail at any level.
-/
theorem detailOperator_const (L : ℕ) (c : V) :
    detailOperator b L (fun _ => c) = 0 := by
  simp only [detailOperator, blockProjection_const, sub_self]

/--
Δ_L annihilates functions that are already block-constant at level L.

If f ∈ 𝕋_L(V), then Δ_L f = 0.
-/
theorem detailOperator_zero_on_coarse (L : ℕ) (f : BlockConstantSpace b L V) :
    detailOperator b L f.val = 0 := by
  -- Both P_{L+1} f.val and P_L f.val equal f.val
  simp only [detailOperator]
  -- f is block-constant at level L, so it's also block-constant at level L+1
  have hL1 : IsBlockConstant f.val (L + 1) := isBlockConstant_of_le (Nat.le_succ L) f.property
  -- P_L f.val = f.val
  have hL : blockProjection b L f.val = f.val := blockProjection_fixedPoint L f
  -- P_{L+1} f.val = f.val
  have hL1_fix : blockProjection b (L + 1) f.val = f.val :=
    blockProjection_fixedPoint (L + 1) ⟨f.val, hL1⟩
  rw [hL1_fix, hL, sub_self]

end BasicProperties

/-!
## Telescoping Identity
-/

section Telescoping

variable {b : RadixSeq} {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/--
Alternative form: P_N = P_1 + Δ_1 + Δ_2 + ... + Δ_{N-1}.
-/
theorem telescoping_identity' (N : ℕ) (hN : 1 ≤ N) (f : CompletedSpace b → V) (x : CompletedSpace b) :
    blockProjection b N f x = blockProjection b 1 f x +
      ∑ L ∈ Finset.Ico 1 N, detailOperator b L f x := by
  -- Standard telescoping sum
  simp only [detailOperator, Pi.sub_apply]
  -- Use induction on N
  induction N, hN using Nat.le_induction with
  | base =>
    -- N = 1: P_1 = P_1 + ∑_{L ∈ Ico 1 1} (P_{L+1} - P_L)
    simp [Finset.Ico_self]
  | succ N hN ih =>
    -- P_{N+1} = P_1 + ∑_{L ∈ Ico 1 (N+1)} (P_{L+1} - P_L)
    rw [Finset.sum_Ico_succ_top hN]
    -- = P_1 + (∑_{L ∈ Ico 1 N} (P_{L+1} - P_L)) + (P_{N+1} - P_N)
    rw [← add_assoc]
    rw [← ih]
    -- = P_N + (P_{N+1} - P_N)
    simp [sub_add_cancel]

/--
**Proposition 18**: Telescoping identity.

P_N f = P_1 f + ∑_{L=1}^{N-1} Δ_L f

**Proof**: Direct telescoping:
  P_1 f + ∑_{L=1}^{N-1} (P_{L+1} f - P_L f)
  = P_1 f + (P_2 f - P_1 f) + (P_3 f - P_2 f) + ... + (P_N f - P_{N-1} f)
  = P_N f

**Note**: This follows from telescoping_identity' by reindexing
  ∑_{L ∈ range(N-1)} Δ_{L+1} = ∑_{M ∈ Ico 1 N} Δ_M via the bijection M = L+1.
-/
theorem telescoping_identity (N : ℕ) (hN : 1 ≤ N) (f : CompletedSpace b → V) :
    blockProjection b N f = blockProjection b 1 f +
      ∑ L ∈ Finset.range (N - 1), detailOperator b (L + 1) f := by
  -- Bridge: Ico 1 N ↔ range(N-1) via canonical Finset reindexing
  -- telescoping_identity' gives the Ico version; we need the range version
  ext x
  rw [telescoping_identity' N hN f x]
  simp only [Pi.add_apply]
  -- Now have: blockProjection b N f x = blockProjection b 1 f x + ∑ L ∈ Ico 1 N, detailOperator b L f x
  -- Want: blockProjection b N f x = blockProjection b 1 f x + ∑ L ∈ range(N-1), detailOperator b (L+1) f x
  congr 1
  -- Show: ∑ L ∈ Ico 1 N, Δ_L f x = (∑ L ∈ range(N-1), Δ_{L+1} f) x
  -- First move x inside the RHS sum using Finset.sum_apply
  rw [Finset.sum_apply]
  -- Now: ∑ L ∈ Ico 1 N, Δ_L f x = ∑ L ∈ range(N-1), (Δ_{L+1} f) x
  -- Use Finset.sum_Ico_eq_sum_range: ∑ k ∈ Ico a b, g k = ∑ t ∈ range(b-a), g(a+t)
  rw [Finset.sum_Ico_eq_sum_range]
  -- Goal: ∑ k ∈ range(N-1), detailOperator b (1+k) f x = ∑ L ∈ range(N-1), detailOperator b (L+1) f x
  -- Apply commutativity: 1 + k = k + 1
  congr 1; ext k; congr 1; omega

/--
Compact form using cumulative sums.
-/
theorem cumulative_detail (N : ℕ) (hN : 0 < N) (f : CompletedSpace b → V) :
    blockProjection b N f = globalAverage b f +
      ∑ L ∈ Finset.range N, detailOperator b L f := by
  -- Use blockProjection_zero: P_0 = globalAverage
  rw [← blockProjection_zero f]
  -- Now prove: P_N f = P_0 f + ∑_{L=0}^{N-1} Δ_L f
  -- This is direct telescoping: P_N = P_0 + (P_1 - P_0) + (P_2 - P_1) + ... + (P_N - P_{N-1})
  ext x
  simp only [Pi.add_apply]
  -- Move x inside the sum using Finset.sum_apply
  rw [Finset.sum_apply]
  -- Now prove pointwise: P_N x = P_0 x + ∑_{L ∈ range N} Δ_L x
  -- Use induction on N (starting from 1, not 0)
  induction N, hN using Nat.le_induction with
  | base =>
    -- N = 1: P_1 x = P_0 x + ∑_{L ∈ range 1} Δ_L x
    -- range 1 = {0}, so ∑_{L ∈ {0}} Δ_L = Δ_0 = P_1 - P_0
    simp only [Finset.range_one, Finset.sum_singleton]
    -- Δ_0 x = (P_1 - P_0) x = P_1 x - P_0 x
    simp only [detailOperator, Pi.sub_apply]
    -- Goal: P_1 x = P_0 x + (P_1 x - P_0 x)
    abel
  | succ N hN ih =>
    -- P_{N+1} x = P_0 x + ∑_{L ∈ range(N+1)} Δ_L x
    -- Expand range(N+1) = range N ∪ {N}
    rw [Finset.sum_range_succ]
    -- Keep detailOperator symbolic; use calc to apply IH cleanly
    calc blockProjection b (N + 1) f x
        = blockProjection b N f x + (detailOperator b N f x) := by
          simp only [detailOperator, Pi.sub_apply]; abel
      _ = (blockProjection b 0 f x + ∑ L ∈ Finset.range N, detailOperator b L f x) +
          detailOperator b N f x := by rw [← ih]
      _ = blockProjection b 0 f x + (∑ L ∈ Finset.range N, detailOperator b L f x + detailOperator b N f x) := by abel

end Telescoping

/-!
## Orthogonality of Details
-/

section Orthogonality

variable {b : RadixSeq}

/-- For L < M, ∫ Δ_L f · Δ_M g dμ = 0.
On each (L+1)-cylinder, Δ_L f is constant, and the integral of Δ_M g
over each such cylinder is zero by the set-integral tower property. -/
private theorem integral_detailOperator_orthogonal_lt (L M : ℕ) (hLM : L < M)
    (f g : CompletedSpace b → ℝ)
    (hf : Integrable f (uniformProductMeasure b))
    (hg : Integrable g (uniformProductMeasure b)) :
    ∫ x, detailOperator b L f x * detailOperator b M g x ∂(uniformProductMeasure b) = 0 := by
  set μ := uniformProductMeasure b
  set K := L + 1
  have hKM : K ≤ M := hLM
  have hms := fun s => @cylinder_measurableSet b K s
  have hpd := cylinderSet_pairwiseDisjoint (b := b) K
  have hΔM : Integrable (detailOperator b M g) μ :=
    (blockProjection_integrable (M + 1) g hg).sub (blockProjection_integrable M g hg)
  -- Per-cylinder integrability of the product
  have h_intOn : ∀ s : PrefixSet b K,
      IntegrableOn (fun x => detailOperator b L f x * detailOperator b M g x)
        (cylinderSet b K s) μ := by
    intro s
    obtain ⟨x₀, hx₀⟩ := cylinder_nonempty b K s
    exact ((hΔM.const_mul (detailOperator b L f x₀)).integrableOn).congr_fun
      (fun y hy => by rw [detailOperator_isBlockConstant L f s y x₀ hy hx₀]) (hms s)
  -- Decompose over K-cylinders
  conv_lhs => rw [← setIntegral_univ, ← cylinderSet_union_univ b K]
  rw [integral_iUnion_fintype hms hpd h_intOn]
  -- Each summand is zero
  apply Finset.sum_eq_zero
  intro s _
  obtain ⟨x₀, hx₀⟩ := cylinder_nonempty b K s
  -- Δ_L f is constant on U_K(s)
  have hconst : ∀ y ∈ cylinderSet b K s,
      detailOperator b L f y = detailOperator b L f x₀ :=
    fun y hy => detailOperator_isBlockConstant L f s y x₀ hy hx₀
  -- Factor out the constant
  rw [setIntegral_congr_fun (hms s) (fun y hy => by rw [hconst y hy])]
  rw [integral_const_mul]
  -- Suffices: ∫_{U_K(s)} Δ_M g = 0
  suffices h : ∫ x in cylinderSet b K s, detailOperator b M g x ∂μ = 0 by
    rw [h, mul_zero]
  -- Expand Δ_M g = P_{M+1} g - P_M g
  simp only [detailOperator, Pi.sub_apply]
  rw [integral_sub (blockProjection_integrable (M + 1) g hg).integrableOn
      (blockProjection_integrable M g hg).integrableOn]
  rw [setIntegral_blockProjection_le K (M + 1) (by omega) s g hg,
      setIntegral_blockProjection_le K M hKM s g hg]
  exact sub_self _

theorem detailOperator_orthogonal (L M : ℕ) (hLM : L ≠ M)
    (f g : CompletedSpace b → ℝ)
    (hf : Integrable f (uniformProductMeasure b))
    (hg : Integrable g (uniformProductMeasure b)) :
    ∫ x, detailOperator b L f x * detailOperator b M g x ∂(uniformProductMeasure b) = 0 := by
  rcases lt_or_gt_of_ne hLM with hlt | hgt
  · exact integral_detailOperator_orthogonal_lt L M hlt f g hf hg
  · -- M < L: swap using mul_comm
    have : (fun x => detailOperator b L f x * detailOperator b M g x) =
           (fun x => detailOperator b M g x * detailOperator b L f x) := by
      ext x; ring
    rw [this]
    exact integral_detailOperator_orthogonal_lt M L hgt g f hg hf

/--
The detail spaces D_L := range(Δ_L) are mutually orthogonal.
-/
theorem detail_spaces_orthogonal (L M : ℕ) (hLM : L ≠ M)
    (f g : CompletedSpace b → ℝ)
    (hf : Integrable f (uniformProductMeasure b))
    (hg : Integrable g (uniformProductMeasure b)) :
    ∫ x, detailOperator b L f x * detailOperator b M g x ∂(uniformProductMeasure b) = 0 :=
  detailOperator_orthogonal L M hLM f g hf hg

/-- Any block-constant function has an integrable square on the probability space. -/
private theorem integrable_sq_of_blockConstant (L : ℕ) (g : CompletedSpace b → ℝ)
    (hg : IsBlockConstant g L) :
    Integrable (fun x => g x ^ 2) (uniformProductMeasure b) := by
  set μ := uniformProductMeasure b
  have hms := fun s => @cylinder_measurableSet b L s
  have h_eq : (fun x => g x ^ 2) =
      fun x => ∑ s : PrefixSet b L, (cylinderSet b L s).indicator
        (fun _ => g (cylinder_nonempty b L s).choose ^ 2) x := by
    ext x
    rw [Finset.sum_eq_single (prefixOf b L x)]
    · rw [Set.indicator_of_mem (mem_cylinderSet_prefixOf b L x)]
      congr 1
      exact hg _ x _ (mem_cylinderSet_prefixOf b L x) (cylinder_nonempty b L _).choose_spec
    · intro t _ hne; rw [Set.indicator_of_notMem]
      intro hmem; exact hne ((mem_cylinderSet_iff_prefixOf b L t x).mp hmem).symm
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h_eq]; apply integrable_finset_sum; intro s _
  exact (integrable_indicator_iff (hms s)).mpr (integrableOn_const (cylinder_measure_ne_top L s))

/-- One-step L² identity: ∫ (P_{N+1} f)² = ∫ (P_N f)² + ∫ (Δ_N f)².
Uses the variance decomposition per N-cylinder: on each cylinder, P_N f is constant,
so (P_{N+1} f)² = (const + Δ_N f)², and the cross term vanishes by the tower property. -/
private theorem L2_step (N : ℕ) (f : CompletedSpace b → ℝ)
    (hf : Integrable f (uniformProductMeasure b)) :
    ∫ x, (blockProjection b (N + 1) f x) ^ 2 ∂(uniformProductMeasure b) =
    ∫ x, (blockProjection b N f x) ^ 2 ∂(uniformProductMeasure b) +
    ∫ x, (detailOperator b N f x) ^ 2 ∂(uniformProductMeasure b) := by
  set μ := uniformProductMeasure b
  have hms := fun s => @cylinder_measurableSet b N s
  have hpd := cylinderSet_pairwiseDisjoint (b := b) N
  have hPN_int := blockProjection_integrable (N + 1) f hf
  have hPN12 := integrable_sq_of_blockConstant (N + 1) _ (blockProjection_isBlockConstant (N + 1) f)
  have hPN2 := integrable_sq_of_blockConstant N _ (blockProjection_isBlockConstant N f)
  have hΔ2 := integrable_sq_of_blockConstant (N + 1) _ (detailOperator_isBlockConstant N f)
  -- Decompose all three integrals over N-cylinders
  have hLHS : ∫ x, (blockProjection b (N + 1) f x) ^ 2 ∂μ =
      ∑ s : PrefixSet b N, ∫ x in cylinderSet b N s,
        (blockProjection b (N + 1) f x) ^ 2 ∂μ := by
    rw [← setIntegral_univ, ← cylinderSet_union_univ b N]
    exact integral_iUnion_fintype hms hpd (fun s => hPN12.integrableOn)
  have hRHS1 : ∫ x, (blockProjection b N f x) ^ 2 ∂μ =
      ∑ s : PrefixSet b N, ∫ x in cylinderSet b N s,
        (blockProjection b N f x) ^ 2 ∂μ := by
    rw [← setIntegral_univ, ← cylinderSet_union_univ b N]
    exact integral_iUnion_fintype hms hpd (fun s => hPN2.integrableOn)
  have hRHS2 : ∫ x, (detailOperator b N f x) ^ 2 ∂μ =
      ∑ s : PrefixSet b N, ∫ x in cylinderSet b N s,
        (detailOperator b N f x) ^ 2 ∂μ := by
    rw [← setIntegral_univ, ← cylinderSet_union_univ b N]
    exact integral_iUnion_fintype hms hpd (fun s => hΔ2.integrableOn)
  rw [hLHS, hRHS1, hRHS2, ← Finset.sum_add_distrib]
  -- Per-cylinder equality
  congr 1; ext s
  obtain ⟨x₀, hx₀⟩ := cylinder_nonempty b N s
  set B := (placeValue b N : ℝ)
  set I := ∫ y in cylinderSet b N s, f y ∂μ
  set c := B * I
  have hBne : B ≠ 0 := Nat.cast_ne_zero.mpr (placeValue.ne_zero N)
  have hBpos : (0 : ℝ) < B := Nat.cast_pos.mpr (placeValue.pos N)
  -- P_N f = c on U_N(s)
  have hconst : ∀ y ∈ cylinderSet b N s, blockProjection b N f y = c := by
    intro y hy
    have hps := (mem_cylinderSet_iff_prefixOf b N s y).mp hy
    show (placeValue b N : ℝ) • ∫ z in cylinderSet b N (prefixOf b N y), f z ∂μ = c
    rw [hps, smul_eq_mul]
  -- ∫_U P_{N+1} f = ∫_U f = I (by tower property)
  have hJ : ∫ y in cylinderSet b N s, blockProjection b (N + 1) f y ∂μ = I :=
    setIntegral_blockProjection_le N (N + 1) (Nat.le_succ N) s f hf
  -- Variance expansion: ∫_U (P_{N+1} f - c)² = ∫_U (P_{N+1} f)² + (-2cI + c²/B)
  have h_expand : ∫ y in cylinderSet b N s, (blockProjection b (N + 1) f y - c) ^ 2 ∂μ =
      ∫ y in cylinderSet b N s, (blockProjection b (N + 1) f y) ^ 2 ∂μ +
        ((-2) * c * I + c ^ 2 * B⁻¹) := by
    have h_eq : ∀ y, (blockProjection b (N + 1) f y - c) ^ 2 =
        (blockProjection b (N + 1) f y) ^ 2 +
        ((-2) * c * blockProjection b (N + 1) f y + c ^ 2) := by intro y; ring
    simp_rw [h_eq]
    have hg_int : IntegrableOn
        (fun y => (-2) * c * blockProjection b (N + 1) f y + c ^ 2)
        (cylinderSet b N s) μ :=
      ((hPN_int.const_mul ((-2) * c)).add (integrable_const (c ^ 2))).integrableOn
    rw [integral_add hPN12.integrableOn hg_int]
    congr 1
    have hcf_int : IntegrableOn (fun y => (-2) * c * blockProjection b (N + 1) f y)
        (cylinderSet b N s) μ :=
      (hPN_int.const_mul ((-2) * c)).integrableOn
    rw [integral_add hcf_int (integrable_const (c ^ 2)).integrableOn]
    rw [integral_const_mul, hJ, setIntegral_const, smul_eq_mul, Measure.real_def,
        cylinder_measure N s, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    ring
  -- Algebraic simplification: -2cI + c²/B = -(c²/B) since c = BI
  have h_alg : -2 * c * I + c ^ 2 * B⁻¹ = -(c ^ 2 * B⁻¹) := by
    show -2 * (B * I) * I + (B * I) ^ 2 * B⁻¹ = -((B * I) ^ 2 * B⁻¹)
    field_simp; ring
  -- ∫_U (P_N f)² = c²/B
  have hPN_sq : ∫ x in cylinderSet b N s, (blockProjection b N f x) ^ 2 ∂μ =
      c ^ 2 * B⁻¹ := by
    rw [setIntegral_congr_fun (hms s) (fun y hy => by rw [hconst y hy])]
    rw [setIntegral_const, smul_eq_mul, Measure.real_def,
        cylinder_measure N s, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    ring
  -- Δ_N f = P_{N+1} f - c on U_N(s)
  have hΔ_sq : ∫ x in cylinderSet b N s, (detailOperator b N f x) ^ 2 ∂μ =
      ∫ x in cylinderSet b N s, (blockProjection b (N + 1) f x - c) ^ 2 ∂μ := by
    exact setIntegral_congr_fun (hms s) (fun y hy => by
      simp only [detailOperator, Pi.sub_apply]; rw [hconst y hy])
  -- Combine: ∫_U (P_{N+1} f)² = c²/B + ∫_U (Δ_N f)²
  linarith [h_expand, h_alg, hPN_sq, hΔ_sq]

/--
L² norm decomposition: ‖P_N f‖₂² = ‖P_1 f‖₂² + ∑_{L=1}^{N-1} ‖Δ_L f‖₂².

This is the Pythagoras theorem for the orthogonal telescoping decomposition
  P_N f = P_1 f + Δ_1 f + Δ_2 f + ... + Δ_{N-1} f
where the detail terms are mutually orthogonal (by `detailOperator_orthogonal`).

**Proof**: By induction on N. The step uses `L2_step` which shows
  ∫ (P_{N+1} f)² = ∫ (P_N f)² + ∫ (Δ_N f)²
via a variance decomposition on each N-cylinder.
-/
theorem L2_norm_decomposition (N : ℕ) (hN : 1 ≤ N) (f : CompletedSpace b → ℝ)
    (hf : Integrable f (uniformProductMeasure b)) :
    ∫ x, (blockProjection b N f x) ^ 2 ∂(uniformProductMeasure b) =
    ∫ x, (blockProjection b 1 f x) ^ 2 ∂(uniformProductMeasure b) +
    ∑ L ∈ Finset.Ico 1 N, ∫ x, (detailOperator b L f x) ^ 2 ∂(uniformProductMeasure b) := by
  induction N, hN using Nat.le_induction with
  | base =>
    -- N = 1: ∫ (P_1 f)² = ∫ (P_1 f)² + 0
    simp
  | succ N hN ih =>
    -- ∫ (P_{N+1} f)² = ∫ (P_N f)² + ∫ (Δ_N f)²  [by L2_step]
    --                 = (∫ (P_1 f)² + ∑_{Ico 1 N} ∫ (Δ_L f)²) + ∫ (Δ_N f)²  [by IH]
    rw [L2_step N f hf, ih]
    rw [Finset.sum_Ico_succ_top hN]
    ring

end Orthogonality

/-!
## Convergence
-/

section Convergence

variable {b : RadixSeq} {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/--
**Theorem 4(a)**: L^p convergence.

For f ∈ L^p(R̂, μ; V) with 1 ≤ p < ∞, P_L f → f in L^p as L → ∞.

**Proof**: This is the (vector-valued) martingale convergence theorem
applied to the filtration (ℱ_L).
-/
-- INFRASTRUCTURE PLACEHOLDER: L^p martingale convergence theorem.
-- Needs: Bochner integral on CompletedSpace, MeasureSpace instance, L^p topology.
theorem blockProjection_Lp_convergence_placeholder (p : ℝ) (hp : 1 ≤ p)
    (f : CompletedSpace b → V) :
    True := by trivial

/--
Helper: pointwise bound ‖P_L f(x) - f(x)‖ ≤ M when ∀ y in cyl(x), ‖f(y) - f(x)‖ ≤ M.

This is the per-cylinder averaging bound: the block projection averages f over the
cylinder, so it deviates from f(x) by at most the oscillation of f on that cylinder.
-/
private theorem blockProjection_pointwise_le (L : ℕ) (f : CompletedSpace b → V)
    (hfi : Integrable f (uniformProductMeasure b))
    (x : CompletedSpace b) (M : ℝ) (hM : 0 ≤ M)
    (hf_cyl : ∀ y ∈ cylinderSet b L (prefixOf b L x), ‖f y - f x‖ ≤ M) :
    ‖blockProjection b L f x - f x‖ ≤ M := by
  set s := prefixOf b L x
  set S := cylinderSet b L s
  set B := (placeValue b L : ℝ)
  set μ := uniformProductMeasure b
  have hB_pos : (0 : ℝ) < B := Nat.cast_pos.mpr (placeValue.pos L)
  have hB_ne : B ≠ 0 := ne_of_gt hB_pos
  have hS_fin : μ S < ⊤ := by
    rw [cylinder_measure L s]; exact ENNReal.inv_lt_top.mpr (by exact_mod_cast placeValue.pos L)
  -- P_L f(x) - f(x) = B • ∫_S (f - f(x)) dμ
  have h_rewrite : blockProjection b L f x - f x =
      B • ∫ y in S, (f y - f x) ∂μ := by
    simp only [blockProjection]
    -- Goal: B • ∫_S f dμ - f x = B • ∫_S (f - fx) dμ
    conv_lhs => rw [show f x = B • (B⁻¹ • f x) from
      (smul_inv_smul₀ hB_ne (f x)).symm]
    rw [← smul_sub, MeasureTheory.integral_sub hfi.integrableOn
        (integrable_const (f x)).integrableOn,
        MeasureTheory.setIntegral_const, Measure.real_def, cylinder_measure L s,
        ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [h_rewrite, norm_smul, Real.norm_natCast]
  -- ‖B • ∫_S (f - fx) dμ‖ = B · ‖∫_S (f - fx) dμ‖ ≤ B · M · μ(S) = M
  calc B * ‖∫ y in S, (f y - f x) ∂μ‖
      ≤ B * (M * (μ S).toReal) := by
        gcongr
        exact MeasureTheory.norm_setIntegral_le_of_norm_le_const hS_fin hf_cyl
    _ = M := by
        rw [cylinder_measure L s, ENNReal.toReal_inv, ENNReal.toReal_natCast]
        rw [mul_comm M, ← mul_assoc, mul_inv_cancel₀ hB_ne, one_mul]

/--
**Theorem 4(b)**: Uniform convergence for continuous functions.

If f is continuous, then ‖P_L f - f‖_∞ → 0 as L → ∞.

**Proof**: R̂ is compact (Heine-Cantor), so continuous f is uniformly continuous.
For large L, cylinder diameter 1/B_L < δ, so the per-cylinder oscillation < ε.
-/
theorem blockProjection_uniform_convergence
    (f : CompletedSpace b → V) (hf : Continuous f)
    (hfi : Integrable f (uniformProductMeasure b))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ x : CompletedSpace b,
      ‖blockProjection b L f x - f x‖ ≤ ε := by
  -- Uniform continuity (Heine-Cantor)
  have huc := CompactSpace.uniformContinuous_of_continuous hf
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.uniformContinuous_iff.mp huc ε hε
  -- Find L₀ with 1/B_{L₀} < δ
  obtain ⟨L₀, hL₀⟩ := FdrsFormal.Topology.Compactness.placeValue_unbounded b ⌈δ⁻¹⌉₊
  use L₀
  intro L hL x
  apply blockProjection_pointwise_le L f hfi x ε (le_of_lt hε)
  intro y hy
  -- y ∈ cyl(x) → dist x y ≤ 1/B_L < δ → ‖f y - f x‖ < ε
  have h_agree : ∀ i : Fin L, (x : CompletedSpace b) i = y i := by
    intro ⟨i, hi⟩; exact (hy ⟨i, hi⟩).symm
  have h_dist : dist x y ≤ (placeValue b L : ℝ)⁻¹ := by
    rw [show dist x y = FdrsFormal.Topology.Ultrametric.ultrametricDist b x y from rfl,
        FdrsFormal.Topology.Ultrametric.ultrametricDist_le_placeValue_inv_iff]
    exact (FdrsFormal.Topology.Ultrametric.agree_on_prefix_iff L).mp h_agree
  have h_lt_δ : dist x y < δ := calc
    dist x y ≤ (placeValue b L : ℝ)⁻¹ := h_dist
    _ ≤ (placeValue b L₀ : ℝ)⁻¹ := by
        exact inv_anti₀ (Nat.cast_pos.mpr (placeValue.pos L₀))
          (Nat.cast_le.mpr (placeValue.mono hL))
    _ < δ := by
        rw [inv_lt_comm₀ (Nat.cast_pos.mpr (placeValue.pos L₀)) hδ_pos]
        exact lt_of_le_of_lt (Nat.le_ceil _) (Nat.cast_lt.mpr hL₀)
  have h_norm := hδ h_lt_δ
  rw [dist_comm, dist_eq_norm] at h_norm
  exact le_of_lt h_norm

/--
Corollary: The detail series partial sums P_N f converge uniformly to f.
(Since P_N f = P_1 f + ∑_{L ∈ Ico 1 N} Δ_L f by telescoping.)
-/
theorem detail_series_converges (f : CompletedSpace b → V) (hf : Continuous f)
    (hfi : Integrable f (uniformProductMeasure b))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ L₀ : ℕ, ∀ N ≥ L₀, ∀ x : CompletedSpace b,
      ‖blockProjection b N f x - f x‖ ≤ ε :=
  blockProjection_uniform_convergence f hf hfi ε hε

/--
Convergence rate: ‖P_L f(x) - f(x)‖ ≤ M when f oscillates by at most M
on each L-cylinder.
-/
theorem blockProjection_convergence_rate
    (f : CompletedSpace b → V) (hf : Continuous f)
    (hfi : Integrable f (uniformProductMeasure b))
    (L : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hf_osc : ∀ x y : CompletedSpace b, prefixOf b L x = prefixOf b L y →
      ‖f x - f y‖ ≤ M) :
    ∀ x : CompletedSpace b, ‖blockProjection b L f x - f x‖ ≤ M := by
  intro x
  apply blockProjection_pointwise_le L f hfi x M hM
  intro y hy
  exact hf_osc y x (by ext ⟨i, hi⟩; simp [prefixOf, hy ⟨i, hi⟩])

end Convergence

/-!
## Interpretation: Hierarchical Decomposition
-/

section Interpretation

variable {b : RadixSeq} {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/--
**Summary**: Every function admits a canonical hierarchy of approximations.

P_N f = (global average) + Δ_0 f + Δ_1 f + ... + Δ_{N-1} f

This is the mixed-radix analog of wavelet/martingale decomposition.
Each Δ_L f captures the "new information" at scale L that wasn't visible
at coarser resolutions.
-/
theorem hierarchical_decomposition_interpretation (N : ℕ) (hN : 0 < N)
    (f : CompletedSpace b → V) :
    blockProjection b N f = globalAverage b f +
      ∑ L ∈ Finset.range N, detailOperator b L f :=
  cumulative_detail N hN f

end Interpretation

end FdrsFormal.FunctionSpaces.Projections.Details
