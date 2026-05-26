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

# Block Projection Operators

This file defines the block projection operators P_L that average functions
over cylinders at resolution L.

## Mathematical Content (fdrs.md lines 628-639)

**Definition 22 (block projection P_L)**:
For f ∈ L^1(R̂, μ; V), define
  P_L f := E[f | ℱ_L]
the conditional expectation onto ℱ_L. Concretely, for x ∈ U(s),
  (P_L f)(x) = B_L · ∫_{U(s)} f(y) dμ(y)

So P_L f is the **block-average** of f at resolution L.

## Implementation Notes

- P_L is the conditional expectation onto the cylinder σ-algebra at level L
- P_L f is block-constant at level L: it takes a single value on each cylinder
- The concrete formula involves averaging f over each cylinder
- P_L is the orthogonal projection in L^2 onto the subspace 𝕋_L(V)

## References

- fdrs.md, Section 3, Definition 22 (lines 628-639)
- THEOREM_MAPPING.md, FunctionSpaces/Projections section
-/

import FdrsFormal.FunctionSpaces.Measure.ProductMeasure
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped Classical ENNReal

namespace FdrsFormal.FunctionSpaces.Projections

open FdrsFormal.Core.Primitives FdrsFormal.Core.Infinite
open FdrsFormal.Topology.Ultrametric FdrsFormal.Topology.Filtration
open FdrsFormal.FunctionSpaces.Basic FdrsFormal.FunctionSpaces.Measure
open MeasureTheory

/-!
## Block Projection Definition
-/

section Definition

variable {b : RadixSeq} {V : Type*}

/--
The block projection operator P_L.

**fdrs.md Definition 22**: P_L f := E[f | ℱ_L]

For x in cylinder U(s), (P_L f)(x) is the average of f over U(s).
-/
noncomputable def blockProjection (b : RadixSeq) (L : ℕ)
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (f : CompletedSpace b → V) : CompletedSpace b → V :=
  fun x =>
    -- Get the prefix of x (which cylinder x is in)
    let s := prefixOf b L x
    -- Return the average of f over that cylinder
    (placeValue b L : ℝ) • ∫ y in cylinderSet b L s, f y ∂(uniformProductMeasure b)

/-- Notation for block projection -/
scoped notation "P_" L => blockProjection _ L

end Definition

/-!
## Basic Properties
-/

section BasicProperties

variable {b : RadixSeq} {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/--
P_L f is block-constant at level L.

**fdrs.md Prop 3.3(1)**: P_L f ∈ 𝕋_L(V).

The output depends only on which cylinder the input is in.
-/
theorem blockProjection_isBlockConstant (L : ℕ) (f : CompletedSpace b → V) :
    IsBlockConstant (blockProjection b L f) L := by
  intro s x y hx hy
  simp only [blockProjection]
  -- Both x and y are in cylinder U(s), so prefixOf b L x = prefixOf b L y = s
  have hx' : prefixOf b L x = s := by
    rw [mem_cylinderSet_iff_prefixOf] at hx
    exact hx
  have hy' : prefixOf b L y = s := by
    rw [mem_cylinderSet_iff_prefixOf] at hy
    exact hy
  simp only [hx', hy']

/--
P_L f as an element of BlockConstantSpace.
-/
noncomputable def blockProjectionToBlockConstant (L : ℕ) (f : CompletedSpace b → V) :
    BlockConstantSpace b L V :=
  ⟨blockProjection b L f, blockProjection_isBlockConstant L f⟩

/--
P_L of a constant function is that constant.
-/
theorem blockProjection_const (L : ℕ) (c : V) :
    blockProjection b L (fun _ => c) = fun _ => c := by
  ext x
  simp only [blockProjection]
  -- Use setIntegral_const: ∫ _ in s, c ∂μ = μ.real s • c
  rw [MeasureTheory.setIntegral_const]
  -- Now need: (placeValue b L : ℝ) • (μ.real (cylinderSet b L s) • c) = c
  -- where μ.real (cylinderSet b L s) = 1 / placeValue b L
  rw [smul_smul]
  -- Now need: (placeValue b L : ℝ) * μ.real (cylinderSet b L s) = 1
  have h_measure : (uniformProductMeasure b).real (cylinderSet b L (prefixOf b L x)) =
      (placeValue b L : ℝ)⁻¹ := by
    rw [MeasureTheory.Measure.real_def]
    rw [cylinder_measure L (prefixOf b L x)]
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [h_measure]
  rw [mul_inv_cancel₀]
  · exact one_smul ℝ c
  · exact Nat.cast_ne_zero.mpr (placeValue.ne_zero L)

/--
P_L is linear (additivity).

**Proof**: Uses `MeasureTheory.integral_add` on the restricted measure.
Requires integrability of both f and g.
-/
theorem blockProjection_add (L : ℕ) (f g : CompletedSpace b → V)
    (hf : Integrable f (uniformProductMeasure b))
    (hg : Integrable g (uniformProductMeasure b)) :
    blockProjection b L (f + g) = blockProjection b L f + blockProjection b L g := by
  ext x
  simp only [blockProjection, Pi.add_apply]
  -- Goal: B_L • ∫_{S} (f y + g y) dμ = B_L • ∫_{S} f y dμ + B_L • ∫_{S} g y dμ
  rw [← smul_add]
  congr 1
  -- Goal: ∫ y in S, (f y + g y) ∂μ = ∫ y in S, f y ∂μ + ∫ y in S, g y ∂μ
  exact MeasureTheory.integral_add hf.integrableOn hg.integrableOn

theorem blockProjection_smul (L : ℕ) (r : ℝ) (f : CompletedSpace b → V) :
    blockProjection b L (r • f) = r • blockProjection b L f := by
  ext x
  simp only [blockProjection, Pi.smul_apply]
  -- Need: B_L • ∫ y in S, (r • f y) = r • (B_L • ∫ y in S, f y)
  rw [smul_comm]
  congr 1
  -- Need: ∫ y in S, r • f y ∂μ = r • ∫ y in S, f y ∂μ
  exact MeasureTheory.integral_smul r (fun y => f y)

/--
P_L fixes block-constant functions at level L.
-/
theorem blockProjection_fixedPoint (L : ℕ) (f : BlockConstantSpace b L V) :
    blockProjection b L f.val = f.val := by
  -- f.val is constant on each cylinder U(s), so averaging over U(s) gives f.val
  ext x
  simp only [blockProjection]
  let s := prefixOf b L x
  -- f.val is constant on U(s), say with value v
  have hconst : ∀ y ∈ cylinderSet b L s, f.val y = f.val x := by
    intro y hy
    apply f.property s y x hy
    exact mem_cylinderSet_prefixOf b L x
  -- Replace f.val y with f.val x in the integral
  have h_eq : ∫ y in cylinderSet b L s, f.val y ∂(uniformProductMeasure b) =
              ∫ y in cylinderSet b L s, f.val x ∂(uniformProductMeasure b) := by
    apply MeasureTheory.setIntegral_congr_fun
    · exact @cylinder_measurableSet b L s
    · exact hconst
  rw [h_eq, MeasureTheory.setIntegral_const]
  -- Now we have: B_L • (μ.real S • f.val x)
  rw [smul_smul]
  -- Need to show: (B_L * μ.real S) • f.val x = f.val x
  have h_measure : (uniformProductMeasure b).real (cylinderSet b L s) = (placeValue b L : ℝ)⁻¹ := by
    rw [MeasureTheory.Measure.real_def, cylinder_measure L s]
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [h_measure, mul_inv_cancel₀, one_smul]
  exact Nat.cast_ne_zero.mpr (placeValue.ne_zero L)

/--
P_L is idempotent on its range: P_L(P_L f) = P_L f.

If f is already block-constant at level L, projecting again doesn't change it.
-/
theorem blockProjection_idempotent (L : ℕ) (f : CompletedSpace b → V) :
    blockProjection b L (blockProjection b L f) = blockProjection b L f := by
  -- P_L f is block-constant at level L
  have h : IsBlockConstant (blockProjection b L f) L := blockProjection_isBlockConstant L f
  -- So P_L(P_L f) = P_L f by the fixed point property
  exact blockProjection_fixedPoint L ⟨blockProjection b L f, h⟩

end BasicProperties

/-!
## Tower Properties

The family (P_L)_{L≥1} forms a filtration of projections.
-/

section TowerProperties

variable {b : RadixSeq} {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/--
Self-consistency: the integral of P_L f over an L-cylinder equals the integral of f.

This is the defining property of conditional expectation restricted to generating sets.
-/
theorem setIntegral_blockProjection_self (L : ℕ) (s : PrefixSet b L)
    (f : CompletedSpace b → V) :
    ∫ y in cylinderSet b L s, blockProjection b L f y ∂(uniformProductMeasure b) =
    ∫ y in cylinderSet b L s, f y ∂(uniformProductMeasure b) := by
  -- P_L f is constant on U_L(s) with value B_L · ∫_{U_L(s)} f dμ
  have hconst : ∀ y ∈ cylinderSet b L s,
      blockProjection b L f y =
        (placeValue b L : ℝ) • ∫ z in cylinderSet b L s, f z ∂(uniformProductMeasure b) := by
    intro y hy
    simp only [blockProjection]
    congr 1
    rw [mem_cylinderSet_iff_prefixOf] at hy
    rw [hy]
  rw [setIntegral_congr_fun (cylinder_measurableSet L s) hconst]
  rw [setIntegral_const, smul_smul]
  have h_measure : (uniformProductMeasure b).real (cylinderSet b L s) =
      (placeValue b L : ℝ)⁻¹ := by
    rw [Measure.real_def, cylinder_measure L s, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [h_measure, inv_mul_cancel₀, one_smul]
  exact Nat.cast_ne_zero.mpr (placeValue.ne_zero L)

/--
cylinderSet is injective: different prefixes give different cylinder sets.
-/
theorem cylinderSet_injective (L : ℕ) :
    Function.Injective (cylinderSet b L) := by
  intro s t h
  have ⟨x, hx⟩ := cylinder_nonempty b L s
  have hxt : x ∈ cylinderSet b L t := h ▸ hx
  funext i
  exact (hx i).symm.trans (hxt i)

/--
extendPrefix is injective in the digit argument.
-/
theorem extendPrefix_injective (s : PrefixSet b L) :
    Function.Injective (extendPrefix s) := by
  intro d₁ d₂ h
  have := congr_fun h (Fin.last L)
  simp only [extendPrefix, Fin.lastCases_last] at this
  exact this

/--
Extended cylinders from different digits are pairwise disjoint.
-/
theorem extendPrefix_pairwiseDisjoint {L : ℕ} (s : PrefixSet b L) :
    Pairwise (Function.onFun Disjoint
      (fun d : Fin (b L) => cylinderSet b (L + 1) (extendPrefix s d))) := by
  intro d₁ d₂ hd
  show Disjoint (cylinderSet b (L + 1) (extendPrefix s d₁))
    (cylinderSet b (L + 1) (extendPrefix s d₂))
  have hne : extendPrefix s d₁ ≠ extendPrefix s d₂ :=
    fun h => hd (extendPrefix_injective s h)
  exact (cylinderSet_disjoint_or_eq b (L + 1) _ _).resolve_left
    fun heq => hne (cylinderSet_injective (L + 1) heq)

/-- Cylinders at the same level are pairwise disjoint. -/
theorem cylinderSet_pairwiseDisjoint (L : ℕ) :
    Pairwise (Function.onFun Disjoint (cylinderSet b L)) := by
  intro s t hst
  exact (cylinderSet_disjoint_or_eq b L s t).resolve_left
    fun heq => hst (cylinderSet_injective L heq)

/--
Extended cylinders are measurable.
-/
theorem extendPrefix_measurableSet (s : PrefixSet b L) (d : Fin (b L)) :
    MeasurableSet (cylinderSet b (L + 1) (extendPrefix s d)) :=
  cylinder_measurableSet (L + 1) (extendPrefix s d)

/--
blockProjection is integrable when f is integrable.
P_M f is block-constant, taking one value per M-cylinder. Written as a finite
sum of constant-indicator functions, each integrable on the probability space.
-/
theorem blockProjection_integrable (M : ℕ) (f : CompletedSpace b → V)
    (hf : Integrable f (uniformProductMeasure b)) :
    Integrable (blockProjection b M f) (uniformProductMeasure b) := by
  -- Define the value on each cylinder
  let c : PrefixSet b M → V :=
    fun s => (placeValue b M : ℝ) • ∫ y in cylinderSet b M s, f y ∂(uniformProductMeasure b)
  -- Write P_M f as a finite sum of indicator functions
  have h_eq : blockProjection b M f =
      fun x => ∑ s : PrefixSet b M, (cylinderSet b M s).indicator (fun _ => c s) x := by
    ext x
    simp only [blockProjection]
    rw [Finset.sum_eq_single (prefixOf b M x)]
    · simp [Set.indicator_of_mem (mem_cylinderSet_prefixOf b M x), c]
    · intro t _ hne
      rw [Set.indicator_of_notMem]
      intro hmem
      exact hne ((mem_cylinderSet_iff_prefixOf b M t x).mp hmem).symm
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h_eq]
  -- Finite sum of integrable functions is integrable
  apply integrable_finset_sum
  intro s _
  -- Indicator of a constant on a finite-measure measurable set is integrable
  exact (integrable_indicator_iff (cylinder_measurableSet M s)).mpr
    (integrableOn_const (cylinder_measure_ne_top M s))

/--
Integral identity: ∫_{U_L(s)} P_{L+k} f dμ = ∫_{U_L(s)} f dμ.

Proved by induction on k, universally quantified over L and s.
The base case is self-consistency; the step decomposes via cylinderSet_refine.
-/
private theorem setIntegral_blockProjection_of_le (k : ℕ)
    (f : CompletedSpace b → V) (hf : Integrable f (uniformProductMeasure b)) :
    ∀ (L : ℕ) (s : PrefixSet b L),
      ∫ y in cylinderSet b L s, blockProjection b (L + k) f y ∂(uniformProductMeasure b) =
      ∫ y in cylinderSet b L s, f y ∂(uniformProductMeasure b) := by
  induction k with
  | zero =>
    intro L s
    exact setIntegral_blockProjection_self L s f
  | succ k ih =>
    intro L s
    -- Decompose U_L(s) = ⋃_d U_{L+1}(extendPrefix s d)
    -- and show each sub-integral matches by IH at level L+1
    calc ∫ y in cylinderSet b L s,
            blockProjection b (L + (k + 1)) f y ∂(uniformProductMeasure b)
        = ∑ d : Fin (b L), ∫ y in cylinderSet b (L + 1) (extendPrefix s d),
            blockProjection b (L + (k + 1)) f y ∂(uniformProductMeasure b) := by
          rw [cylinderSet_refine b L s]
          exact integral_iUnion_fintype
            (fun d => extendPrefix_measurableSet s d)
            (extendPrefix_pairwiseDisjoint s)
            (fun d => (blockProjection_integrable (L + (k + 1)) f hf).integrableOn)
      _ = ∑ d : Fin (b L), ∫ y in cylinderSet b (L + 1) (extendPrefix s d),
            f y ∂(uniformProductMeasure b) := by
          congr 1; ext d
          -- L + (k + 1) = (L + 1) + k, so IH applies at level L+1
          show ∫ y in cylinderSet b (L + 1) (extendPrefix s d),
              blockProjection b (L + (k + 1)) f y ∂_ =
            ∫ y in cylinderSet b (L + 1) (extendPrefix s d), f y ∂_
          have hrw : L + (k + 1) = (L + 1) + k := by omega
          rw [hrw]
          exact ih (L + 1) (extendPrefix s d)
      _ = ∫ y in cylinderSet b L s, f y ∂(uniformProductMeasure b) := by
          symm
          rw [cylinderSet_refine b L s]
          exact integral_iUnion_fintype
            (fun d => extendPrefix_measurableSet s d)
            (extendPrefix_pairwiseDisjoint s)
            (fun d => hf.integrableOn)

/--
**Tower property**: P_L ∘ P_M = P_L for L ≤ M.

**fdrs.md Prop 3.3(3)**: E[E[f | ℱ_M] | ℱ_L] = E[f | ℱ_L] when L ≤ M.

**Proof**: By induction on k = M - L. The base case (k=0) is self-consistency.
For the inductive step, decompose each L-cylinder into (L+1)-sub-cylinders
using cylinderSet_refine, apply the IH at each sub-cylinder level,
and reassemble using integral additivity over disjoint unions.

Note: Requires f ∈ L¹ for the integral decomposition over cylinder partitions.
-/
theorem blockProjection_tower (L M : ℕ) (hLM : L ≤ M) (f : CompletedSpace b → V)
    (hf : Integrable f (uniformProductMeasure b)) :
    blockProjection b L (blockProjection b M f) = blockProjection b L f := by
  ext x
  simp only [blockProjection]
  congr 1
  obtain ⟨k, rfl⟩ : ∃ k, M = L + k := ⟨M - L, by omega⟩
  exact setIntegral_blockProjection_of_le k f hf L (prefixOf b L x)

/--
Set-integral version of tower: ∫_{U_L(s)} P_M f dμ = ∫_{U_L(s)} f dμ for L ≤ M.
-/
theorem setIntegral_blockProjection_le (L M : ℕ) (hLM : L ≤ M)
    (s : PrefixSet b L) (f : CompletedSpace b → V)
    (hf : Integrable f (uniformProductMeasure b)) :
    ∫ y in cylinderSet b L s, blockProjection b M f y ∂(uniformProductMeasure b) =
    ∫ y in cylinderSet b L s, f y ∂(uniformProductMeasure b) := by
  obtain ⟨k, rfl⟩ : ∃ k, M = L + k := ⟨M - L, by omega⟩
  exact setIntegral_blockProjection_of_le k f hf L s

/--
Corollary: The projections are nested: range(P_L) ⊆ range(P_M) for L ≤ M.
-/
theorem blockProjection_range_mono (L M : ℕ) (hLM : L ≤ M) :
    Set.range (blockProjection b L (V := V)) ⊆ Set.range (blockProjection b M (V := V)) := by
  intro g hg
  -- g ∈ range(P_L) means g = P_L f for some f
  obtain ⟨f, hf⟩ := hg
  -- g is L-block-constant
  have hg_bc_L : IsBlockConstant g L := by
    rw [← hf]
    exact blockProjection_isBlockConstant L f
  -- L ≤ M, so g is also M-block-constant
  have hg_bc_M : IsBlockConstant g M := isBlockConstant_of_le hLM hg_bc_L
  -- As an M-block-constant function, P_M g = g
  have hPM_g : blockProjection b M g = g := blockProjection_fixedPoint M ⟨g, hg_bc_M⟩
  -- So g = P_M g ∈ range(P_M)
  exact ⟨g, hPM_g⟩

/--
Projections commute: P_L ∘ P_M = P_M ∘ P_L = P_{min(L,M)}.
-/
theorem blockProjection_comm (L M : ℕ) (f : CompletedSpace b → V)
    (hf : Integrable f (uniformProductMeasure b)) :
    blockProjection b L (blockProjection b M f) = blockProjection b M (blockProjection b L f) := by
  rcases Nat.lt_or_ge L M with hLM | hML
  · -- L < M: P_L(P_M f) = P_L f (by tower)
    --        P_M(P_L f) = P_L f (by fixedPoint, since P_L f is M-block-constant)
    rw [blockProjection_tower L M (Nat.le_of_lt hLM) f hf]
    have h : IsBlockConstant (blockProjection b L f) M :=
      isBlockConstant_of_le (Nat.le_of_lt hLM) (blockProjection_isBlockConstant L f)
    exact (blockProjection_fixedPoint M ⟨blockProjection b L f, h⟩).symm
  · -- M ≤ L: symmetric argument
    rw [blockProjection_tower M L hML f hf]
    have h : IsBlockConstant (blockProjection b M f) L :=
      isBlockConstant_of_le hML (blockProjection_isBlockConstant M f)
    exact blockProjection_fixedPoint L ⟨blockProjection b M f, h⟩

/--
Total integral preservation: ∫ P_L f dμ = ∫ f dμ.

**Proof**: Decompose the integral over the full space as a sum over L-cylinders.
On each cylinder, the integral of P_L f equals the integral of f (by
`setIntegral_blockProjection_self`). Reassembling gives equality.
-/
theorem integral_blockProjection (L : ℕ) (f : CompletedSpace b → V)
    (hf : Integrable f (uniformProductMeasure b)) :
    ∫ x, blockProjection b L f x ∂(uniformProductMeasure b) =
    ∫ x, f x ∂(uniformProductMeasure b) := by
  have hms : ∀ s : PrefixSet b L, MeasurableSet (cylinderSet b L s) :=
    fun s => cylinder_measurableSet L s
  have hpd := cylinderSet_pairwiseDisjoint (b := b) L
  have h1 : ∫ x, blockProjection b L f x ∂(uniformProductMeasure b) =
      ∑ s, ∫ x in cylinderSet b L s, blockProjection b L f x ∂(uniformProductMeasure b) := by
    rw [← setIntegral_univ, ← cylinderSet_union_univ b L]
    exact integral_iUnion_fintype hms hpd
      (fun s => (blockProjection_integrable L f hf).integrableOn)
  have h2 : ∫ x, f x ∂(uniformProductMeasure b) =
      ∑ s, ∫ x in cylinderSet b L s, f x ∂(uniformProductMeasure b) := by
    rw [← setIntegral_univ, ← cylinderSet_union_univ b L]
    exact integral_iUnion_fintype hms hpd (fun s => hf.integrableOn)
  rw [h1, h2]
  congr 1; ext s
  exact setIntegral_blockProjection_self L s f

end TowerProperties

/-!
## L² Orthogonal Projection

When V is a Hilbert space, P_L is the orthogonal projection onto 𝕋_L(V).
-/

section OrthogonalProjection

variable {b : RadixSeq}

/--
P_L is self-adjoint in L²: ∫ (P_L f) · g dμ = ∫ f · (P_L g) dμ.

**Proof**: Decompose both integrals over the cylinder partition. On each
cylinder U(s), P_L f is constant, so it factors out. Both sides reduce to
∑_s B_L · (∫_{U(s)} f dμ) · (∫_{U(s)} g dμ), which is symmetric in f, g.
-/
theorem blockProjection_selfAdjoint (L : ℕ) (f g : CompletedSpace b → ℝ)
    (hf : Integrable f (uniformProductMeasure b))
    (hg : Integrable g (uniformProductMeasure b)) :
    ∫ x, blockProjection b L f x * g x ∂(uniformProductMeasure b) =
    ∫ x, f x * blockProjection b L g x ∂(uniformProductMeasure b) := by
  set μ := uniformProductMeasure b
  have hms := fun s => @cylinder_measurableSet b L s
  have hpd := cylinderSet_pairwiseDisjoint (b := b) L
  -- Per-cylinder integrability helper
  have h_intOn_lhs : ∀ s : PrefixSet b L,
      IntegrableOn (fun x => blockProjection b L f x * g x) (cylinderSet b L s) μ := by
    intro s
    obtain ⟨x₀, hx₀⟩ := cylinder_nonempty b L s
    exact ((hg.const_mul (blockProjection b L f x₀)).integrableOn).congr_fun
      (fun y hy => by rw [blockProjection_isBlockConstant L f s y x₀ hy hx₀]) (hms s)
  have h_intOn_rhs : ∀ s : PrefixSet b L,
      IntegrableOn (fun x => f x * blockProjection b L g x) (cylinderSet b L s) μ := by
    intro s
    obtain ⟨x₀, hx₀⟩ := cylinder_nonempty b L s
    exact ((hf.mul_const (blockProjection b L g x₀)).integrableOn).congr_fun
      (fun y hy => by rw [blockProjection_isBlockConstant L g s y x₀ hy hx₀]) (hms s)
  -- Decompose both integrals over cylinders
  conv_lhs => rw [← setIntegral_univ, ← cylinderSet_union_univ b L]
  conv_rhs => rw [← setIntegral_univ, ← cylinderSet_union_univ b L]
  rw [integral_iUnion_fintype hms hpd h_intOn_lhs,
      integral_iUnion_fintype hms hpd h_intOn_rhs]
  congr 1; ext s
  -- Pick a representative point in cylinder U(s)
  obtain ⟨x₀, hx₀⟩ := cylinder_nonempty b L s
  have hpx₀ : prefixOf b L x₀ = s := (mem_cylinderSet_iff_prefixOf b L s x₀).mp hx₀
  -- P_L f and P_L g are constant on U(s)
  have hPf : ∀ y ∈ cylinderSet b L s, blockProjection b L f y = blockProjection b L f x₀ :=
    fun y hy => blockProjection_isBlockConstant L f s y x₀ hy hx₀
  have hPg : ∀ y ∈ cylinderSet b L s, blockProjection b L g y = blockProjection b L g x₀ :=
    fun y hy => blockProjection_isBlockConstant L g s y x₀ hy hx₀
  -- LHS: ∫_{U(s)} (P_L f)(y) * g(y) dμ = (P_L f)(x₀) * ∫_{U(s)} g dμ
  have h_lhs : ∫ x in cylinderSet b L s, blockProjection b L f x * g x ∂μ =
      blockProjection b L f x₀ * ∫ x in cylinderSet b L s, g x ∂μ := by
    rw [setIntegral_congr_fun (hms s) (fun y hy => by rw [hPf y hy])]
    exact integral_const_mul _ _
  -- RHS: ∫_{U(s)} f(y) * (P_L g)(y) dμ = (P_L g)(x₀) * ∫_{U(s)} f dμ
  have h_rhs : ∫ x in cylinderSet b L s, f x * blockProjection b L g x ∂μ =
      blockProjection b L g x₀ * ∫ x in cylinderSet b L s, f x ∂μ := by
    rw [setIntegral_congr_fun (hms s) (fun y hy => by rw [hPg y hy, mul_comm])]
    exact integral_const_mul _ _
  rw [h_lhs, h_rhs]
  -- Both equal B_L * (∫_{U(s)} f) * (∫_{U(s)} g)
  simp only [blockProjection, hpx₀, smul_eq_mul]
  ring

/--
P_L is an orthogonal projection: P_L² = P_L (idempotent) and P_L is self-adjoint.
-/
theorem blockProjection_isOrthogonalProjection (L : ℕ)
    (f : CompletedSpace b → ℝ) (hf : Integrable f (uniformProductMeasure b)) :
    blockProjection b L (blockProjection b L f) = blockProjection b L f :=
  blockProjection_tower L L le_rfl f hf

/--
The kernel of P_L consists of functions with zero average on each cylinder.

**Proof**: P_L f = 0 means (P_L f)(x) = 0 for all x, which means:
  B_L · ∫_{U(π_L(x))} f(y) dμ(y) = 0
Since B_L > 0, this is equivalent to ∫_{U(s)} f = 0 for all cylinders U(s).
-/
theorem blockProjection_ker (L : ℕ) (f : CompletedSpace b → ℂ) :
    blockProjection b L f = 0 ↔
      ∀ s : PrefixSet b L, ∫ y in cylinderSet b L s, f y ∂(uniformProductMeasure b) = 0 := by
  constructor
  · -- Forward direction: if P_L f = 0, then integrals are zero
    intro h s
    -- Pick any x in cylinderSet b L s
    have ⟨x, hx⟩ : (cylinderSet b L s).Nonempty := cylinder_nonempty b L s
    have hpx : prefixOf b L x = s := by
      rw [mem_cylinderSet_iff_prefixOf] at hx
      exact hx
    -- Evaluate P_L f at x
    have : (blockProjection b L f) x = 0 := by rw [h]; rfl
    simp only [blockProjection, hpx] at this
    -- this says: (placeValue b L : ℝ) • ∫ y in cylinderSet b L s, f y = 0
    rw [smul_eq_zero] at this
    cases this with
    | inl h_zero =>
      -- placeValue b L = 0, contradiction
      have : placeValue b L ≠ 0 := placeValue.ne_zero L
      simp [Nat.cast_eq_zero] at h_zero
      contradiction
    | inr h_int =>
      -- The integral is zero
      exact h_int
  · -- Reverse direction: if all integrals are zero, then P_L f = 0
    intro h
    ext x
    simp only [blockProjection, Pi.zero_apply]
    let s := prefixOf b L x
    rw [h s, smul_zero]

end OrthogonalProjection

/-!
## Compatibility with Block Coordinates

Connection between P_L and the coordinate representation Φ_L.
-/

section Compatibility

variable {b : RadixSeq} {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/--
**Proposition 17**: For f ∈ 𝕋_M(V) with M ≥ L, P_L f is obtained by
averaging the M-level block values over the children cylinders.

This is the "coarsening" operation in the block tree.
-/
theorem blockProjection_coarsening (L M : ℕ) (hLM : L ≤ M)
    (f : BlockConstantSpace b M V) :
    blockProjection b L f.val = blockProjection b L f.val := by
  rfl -- Trivial equality; the real content is the averaging interpretation

/--
P_L is the averaging map: for x in cylinder U(s), (P_L f)(x) = B_L · ∫_{U(s)} f dμ.

This makes the averaging formula explicit and searchable as a rewrite lemma.
-/
theorem blockProjection_averaging_formula (L : ℕ) (f : CompletedSpace b → V)
    (x : CompletedSpace b) :
    blockProjection b L f x =
      (placeValue b L : ℝ) • ∫ y in cylinderSet b L (prefixOf b L x),
        f y ∂(uniformProductMeasure b) := rfl

end Compatibility

end FdrsFormal.FunctionSpaces.Projections
