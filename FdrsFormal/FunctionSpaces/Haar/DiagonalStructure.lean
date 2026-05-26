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
import FdrsFormal.FunctionSpaces.Haar.ProjectionAction
import FdrsFormal.FunctionSpaces.Haar.Orthonormality
import FdrsFormal.FunctionSpaces.Commutant

/-!
# Diagonal Structure of Commutant Algebra

This file characterizes operators commuting with all block projections as
being diagonal-by-scale in the Haar basis.

## Main Results

* `operator_vanishes_cross_level` - Cross-level matrix entries vanish
* `commutant_diagonal_by_scale` - **Theorem 12**: Commutant ops are block diagonal
* `commutant_algebra_product` - **Corollary 9**: Comm(P) ≅ ℝ × ∏ Mat(n_ℓ, ℝ)

## References

* fdrs.md, Lines 1405-1423: Theorem 12 and Corollary 9
-/

open FdrsFormal Core.Primitives FunctionSpaces.Commutant

variable {b : RadixSeq} {k : ℕ}

namespace FdrsFormal.Haar

/-- Number of Haar atoms at support level ℓ -/
def levelDimension (b : RadixSeq) (k ℓ : ℕ) : ℕ :=
  if h : ℓ < k + 1 then
    (Finset.univ.filter (fun α : HaarAtom b k => supportLevel α = ⟨ℓ, h⟩)).card
  else
    0

/--
**Theorem 12** (cross-level vanishing):
If A commutes with all block projections P_L, then matrix entries between
Haar atoms at different support levels vanish:
⟨A h_α, h_β⟩ = 0 whenever ℓ(α) ≠ ℓ(β).

**Proof**: WLOG ℓ(α) < ℓ(β). Set L = ℓ(β).
- P_L h_α = h_α (preservation), P_L h_β = 0 (annihilation since β non-constant)
- By commutation + preservation: A h_α = P_L(A h_α)
- ⟨A h_α, h_β⟩ = ⟨P_L(A h_α), h_β⟩ = ⟨A h_α, P_L h_β⟩ = ⟨A h_α, 0⟩ = 0

**fdrs.md Reference:** Lines 1405-1413, Theorem 12
-/
theorem operator_vanishes_cross_level
    (A : (Core.Finite.FiniteRadixSpace b k → ℝ) →ₗ[ℝ]
      (Core.Finite.FiniteRadixSpace b k → ℝ))
    (hcomm : ∀ (L : ℕ) (hL : L ≤ k + 1)
      (f : Core.Finite.FiniteRadixSpace b k → ℝ),
      A (finiteBlockProjection b k L hL f) =
      finiteBlockProjection b k L hL (A f))
    (α β : HaarAtom b k) (hαβ : supportLevel α ≠ supportLevel β) :
    ∑ σ : Core.Finite.FiniteRadixSpace b k,
      (A (haarFunction α)) σ * haarFunction β σ = 0 := by
  rcases lt_or_gt_of_ne hαβ with hlt | hgt
  · -- Case ℓ(α) < ℓ(β): use L = ℓ(β)
    have hLk : (supportLevel β).val ≤ k + 1 := by omega
    have hβ_nc : ¬ isConstant β := by
      intro hc; rw [supportLevel_of_constant β hc] at hlt
      exact absurd hlt (not_lt.mpr (Fin.zero_le _))
    have hpres := haarAtom_preserved_by_projection α (supportLevel β) hlt
    have hann := haarAtom_annihilated_by_projection β (supportLevel β) le_rfl hβ_nc
    have hAα_eq : A (haarFunction α) =
        finiteBlockProjection b k (supportLevel β).val hLk (A (haarFunction α)) := by
      have := hcomm (supportLevel β).val hLk (haarFunction α)
      rw [hpres] at this; exact this
    -- Chain: LHS = ⟨P_L(A h_α), h_β⟩ = ⟨A h_α, P_L h_β⟩ = ⟨A h_α, 0⟩ = 0
    have h1 : ∑ σ, (A (haarFunction α)) σ * haarFunction β σ =
        ∑ σ, (finiteBlockProjection b k (supportLevel β).val hLk
          (A (haarFunction α))) σ * haarFunction β σ := by
      congr 1; ext σ; exact congr_arg (fun f => f σ * haarFunction β σ) hAα_eq
    have h2 := finiteBlockProjection_isOrthogonalProjection k (supportLevel β).val hLk
        (A (haarFunction α)) (haarFunction β)
    have h3 : ∑ σ, (A (haarFunction α)) σ *
        (finiteBlockProjection b k (supportLevel β).val hLk (haarFunction β)) σ = 0 := by
      simp [hann]
    linarith
  · -- Case ℓ(β) < ℓ(α): use L = ℓ(α)
    have hLk : (supportLevel α).val ≤ k + 1 := by omega
    have hα_nc : ¬ isConstant α := by
      intro hc; rw [supportLevel_of_constant α hc] at hgt
      exact absurd hgt (not_lt.mpr (Fin.zero_le _))
    have hann := haarAtom_annihilated_by_projection α (supportLevel α) le_rfl hα_nc
    have hpres := haarAtom_preserved_by_projection β (supportLevel α) hgt
    have hPAα_zero : finiteBlockProjection b k (supportLevel α).val hLk
        (A (haarFunction α)) = 0 := by
      have := hcomm (supportLevel α).val hLk (haarFunction α)
      rw [hann, map_zero] at this; exact this.symm
    -- Chain: LHS = ⟨A h_α, P_L h_β⟩ = ⟨P_L(A h_α), h_β⟩ = ⟨0, h_β⟩ = 0
    have h1 : ∑ σ, (A (haarFunction α)) σ * haarFunction β σ =
        ∑ σ, (A (haarFunction α)) σ *
          (finiteBlockProjection b k (supportLevel α).val hLk (haarFunction β)) σ := by
      congr 1; ext σ; exact congr_arg (fun f => (A (haarFunction α)) σ * f σ) hpres.symm
    have h2 := (finiteBlockProjection_isOrthogonalProjection k (supportLevel α).val hLk
        (A (haarFunction α)) (haarFunction β)).symm
    have h3 : ∑ σ, (finiteBlockProjection b k (supportLevel α).val hLk
          (A (haarFunction α))) σ * haarFunction β σ = 0 := by
      simp [hPAα_zero]
    linarith

/--
**Theorem 12** (diagonal-by-scale structure):
Operators commuting with all block projections are block diagonal by support level
in the Haar basis.

**fdrs.md Reference:** Lines 1405-1413, Theorem 12
-/
theorem commutant_diagonal_by_scale
    (A : (Core.Finite.FiniteRadixSpace b k → ℝ) →ₗ[ℝ]
      (Core.Finite.FiniteRadixSpace b k → ℝ))
    (hcomm : ∀ (L : ℕ) (hL : L ≤ k + 1)
      (f : Core.Finite.FiniteRadixSpace b k → ℝ),
      A (finiteBlockProjection b k L hL f) =
      finiteBlockProjection b k L hL (A f))
    (α β : HaarAtom b k) (hαβ : supportLevel α ≠ supportLevel β) :
    ∑ σ : Core.Finite.FiniteRadixSpace b k,
      (A (haarFunction α)) σ * haarFunction β σ = 0 :=
  operator_vanishes_cross_level A hcomm α β hαβ

/-! ### Scale block decomposition for Corollary 9 -/

/-- Scale block index: `none` for the constant atom, `some ℓ` for non-constant
atoms at support level ℓ. This refines `supportLevel` by separating the
1-dimensional constant subspace C₀ from the detail subspace D₀. -/
def scaleBlock (α : HaarAtom b k) : Option (Fin (k + 1)) :=
  if isConstant α then none else some (supportLevel α)

/-- The constant atom's haarFunction is the constant-1 function. -/
theorem haarFunction_of_constant (α : HaarAtom b k) (hc : isConstant α) :
    haarFunction α = fun _ => 1 := by
  ext σ; simp only [haarFunction]
  apply Finset.prod_eq_one; intro i _
  simp [haarComponent, hc i]

/-- Haar function of a non-constant atom sums to zero (mean-zero property). -/
theorem haarFunction_sum_zero (α : HaarAtom b k) (hnc : ¬isConstant α) :
    ∑ σ : Core.Finite.FiniteRadixSpace b k, haarFunction α σ = 0 := by
  simp only [haarFunction]
  rw [show ∑ σ : Core.Finite.FiniteRadixSpace b k, ∏ i, haarComponent i (α i) (σ i) =
    ∏ i, ∑ d, haarComponent i (α i) d from by
    unfold Core.Finite.FiniteRadixSpace; exact (Fintype.prod_sum _).symm]
  unfold isConstant at hnc; push_neg at hnc
  obtain ⟨i, hi⟩ := hnc
  exact Finset.prod_eq_zero (Finset.mem_univ i) (haarComponent_sum_zero i (α i) hi)

/-- P_L preserves the haarFunction of a constant atom for any L. -/
theorem constant_haarAtom_preserved (α : HaarAtom b k) (hc : isConstant α)
    (L : ℕ) (hL : L ≤ k + 1) :
    finiteBlockProjection b k L hL (haarFunction α) = haarFunction α := by
  rw [haarFunction_of_constant α hc]
  exact finiteBlockProjection_const k L hL 1

/-- P_L annihilates non-constant Haar atoms with supportLevel ≥ L.
Wraps `haarAtom_annihilated_by_projection` for ℕ-valued L. -/
private theorem annihilate_nat (α : HaarAtom b k) (L : ℕ) (hL : L ≤ k + 1)
    (hnc : ¬isConstant α) (hge : L ≤ (supportLevel α).val) :
    finiteBlockProjection b k L hL (haarFunction α) = 0 := by
  have hLk1 : L < k + 1 := by omega
  exact haarAtom_annihilated_by_projection α ⟨L, hLk1⟩
    (Fin.mk_le_of_le_val hge) hnc

/-- P_L preserves non-constant Haar atoms with supportLevel < L.
Wraps `haarAtom_preserved_by_projection` for ℕ-valued L. -/
private theorem preserve_nat (α : HaarAtom b k) (L : ℕ) (hL : L ≤ k + 1)
    (hlt : (supportLevel α).val < L) :
    finiteBlockProjection b k L hL (haarFunction α) = haarFunction α := by
  by_cases hLk1 : L < k + 1
  · exact haarAtom_preserved_by_projection α ⟨L, hLk1⟩ hlt
  · -- L = k+1: P_{k+1} is the identity (all functions are (k+1)-block-constant)
    have hL_eq : L = k + 1 := by omega
    apply finiteBlockProjection_fixedPoint
    intro τ τ' hpre
    have : τ = τ' := by
      funext ⟨i, hi⟩
      have hi' : i < L := by omega
      have h := congr_fun hpre ⟨i, hi'⟩
      simp only [finitePrefix] at h
      exact h
    rw [this]

/-- If ⟨f, h_β⟩ = 0 for all Haar atoms β, then f = 0.
Follows from the completeness relation (resolution of identity). -/
theorem haar_inner_injective
    (f : Core.Finite.FiniteRadixSpace b k → ℝ)
    (h : ∀ β : HaarAtom b k,
      ∑ σ : Core.Finite.FiniteRadixSpace b k, f σ * haarFunction β σ = 0) :
    f = 0 := by
  have B_pos : (0 : ℝ) < ∏ i : Fin (k + 1), (b i : ℝ) := by
    apply Finset.prod_pos; intro i _; exact Nat.cast_pos.mpr (b.pos i)
  ext σ; simp only [Pi.zero_apply]
  have key : (∏ i : Fin (k + 1), (b i : ℝ)) * f σ =
      ∑ α : HaarAtom b k,
        (∑ τ : Core.Finite.FiniteRadixSpace b k, f τ * haarFunction α τ) *
        haarFunction α σ := by
    symm
    -- Step 1: distribute (∑_τ ...) * h_α(σ)
    simp only [Finset.sum_mul]
    -- Step 2: swap ∑_α ∑_τ → ∑_τ ∑_α
    rw [Finset.sum_comm]
    -- Step 3: factor out f(τ) and apply completeness
    simp_rw [show ∀ (τ : Core.Finite.FiniteRadixSpace b k) (α : HaarAtom b k),
        f τ * haarFunction α τ * haarFunction α σ =
        f τ * (haarFunction α τ * haarFunction α σ) from fun _ _ => mul_assoc _ _ _]
    simp_rw [← Finset.mul_sum, haarBasis_complete]
    simp [Finset.sum_ite_eq', Finset.mem_univ, mul_comm]
  have key2 : (∏ i : Fin (k + 1), (b i : ℝ)) * f σ = 0 := by
    rw [key]; exact Finset.sum_eq_zero (fun α _ => by rw [h α, zero_mul])
  exact (mul_eq_zero.mp key2).resolve_left (ne_of_gt B_pos)

/--
**Forward direction of Corollary 9**: commuting with all P_L implies
scale-block-diagonal structure. Extends Theorem 12 by separating the
constant subspace C₀ from the detail subspace D₀ at support level 0.

**Proof**: For atoms at the same support level but different scale blocks,
one is constant and the other isn't. Use commutation with P₀ and
self-adjointness to show the cross-term vanishes.
-/
theorem commutant_scaleBlock_vanishing
    (A : (Core.Finite.FiniteRadixSpace b k → ℝ) →ₗ[ℝ]
      (Core.Finite.FiniteRadixSpace b k → ℝ))
    (hcomm : ∀ (L : ℕ) (hL : L ≤ k + 1)
      (f : Core.Finite.FiniteRadixSpace b k → ℝ),
      A (finiteBlockProjection b k L hL f) =
      finiteBlockProjection b k L hL (A f))
    (α β : HaarAtom b k) (hne : scaleBlock α ≠ scaleBlock β) :
    ∑ σ : Core.Finite.FiniteRadixSpace b k,
      (A (haarFunction α)) σ * haarFunction β σ = 0 := by
  -- If supportLevels differ, use Theorem 12
  by_cases h_sl : supportLevel α ≠ supportLevel β
  · exact operator_vanishes_cross_level A hcomm α β h_sl
  -- supportLevels agree but scaleBlocks differ → one constant, other not
  push_neg at h_sl
  by_cases hcα : isConstant α <;> by_cases hcβ : isConstant β
  · -- Both constant → same scaleBlock, contradiction
    exact absurd (by simp [scaleBlock, hcα, hcβ]) hne
  · -- α constant, β non-constant: use P₀
    have h0 := hcomm 0 (Nat.zero_le _) (haarFunction α)
    rw [constant_haarAtom_preserved α hcα 0 (Nat.zero_le _)] at h0
    have hβ_ann := annihilate_nat β 0 (Nat.zero_le _) hcβ (Nat.zero_le _)
    have hsa := finiteBlockProjection_isOrthogonalProjection k 0 (Nat.zero_le _)
        (A (haarFunction α)) (haarFunction β)
    have h_lhs : ∑ σ, (A (haarFunction α)) σ * haarFunction β σ =
        ∑ σ, (finiteBlockProjection b k 0 (Nat.zero_le _) (A (haarFunction α))) σ *
          haarFunction β σ := by
      congr 1; ext σ; congr 1; exact congr_fun h0 σ
    have h_rhs : ∑ σ, (A (haarFunction α)) σ *
        (finiteBlockProjection b k 0 (Nat.zero_le _) (haarFunction β)) σ = 0 := by
      simp [hβ_ann]
    linarith
  · -- α non-constant, β constant: use P₀
    have hα_ann := annihilate_nat α 0 (Nat.zero_le _) hcα (Nat.zero_le _)
    have h0 := hcomm 0 (Nat.zero_le _) (haarFunction α)
    rw [hα_ann, map_zero] at h0
    have hβ_pres := constant_haarAtom_preserved β hcβ 0 (Nat.zero_le _)
    have hsa := finiteBlockProjection_isOrthogonalProjection k 0 (Nat.zero_le _)
        (A (haarFunction α)) (haarFunction β)
    have h_lhs : ∑ σ, (finiteBlockProjection b k 0 (Nat.zero_le _)
        (A (haarFunction α))) σ * haarFunction β σ = 0 := by
      simp [h0.symm]
    have h_rhs : ∑ σ, (A (haarFunction α)) σ *
        (finiteBlockProjection b k 0 (Nat.zero_le _) (haarFunction β)) σ =
        ∑ σ, (A (haarFunction α)) σ * haarFunction β σ := by
      congr 1; ext σ; congr 1; exact congr_fun hβ_pres σ
    linarith
  · -- Both non-constant, same supportLevel → same scaleBlock, contradiction
    exact absurd (by simp [scaleBlock, hcα, hcβ, h_sl]) hne

/--
**Corollary 9** (commutant algebra is a direct product of full matrix algebras):

An operator A commutes with all block projections P_L if and only if it has
zero matrix entries between different scale blocks in the Haar basis.

The scale blocks are: {constant atom} and {non-constant atoms at level ℓ}
for each 0 ≤ ℓ ≤ k. This gives the algebra isomorphism
  Comm(P) ≅ ℝ × ∏_{ℓ=0}^k Mat(n_ℓ, ℝ)
since each scale block admits arbitrary linear maps (no additional constraints).

**Forward** (→): Theorem 12 (cross-level vanishing) + constant separation.
**Reverse** (←): Self-adjointness of P_L + completeness of Haar basis.

-- fdrs.md lines 1415-1423, Corollary 9
-/
theorem commutant_algebra_product
    (A : (Core.Finite.FiniteRadixSpace b k → ℝ) →ₗ[ℝ]
      (Core.Finite.FiniteRadixSpace b k → ℝ)) :
    (∀ (L : ℕ) (hL : L ≤ k + 1)
      (f : Core.Finite.FiniteRadixSpace b k → ℝ),
      A (finiteBlockProjection b k L hL f) =
      finiteBlockProjection b k L hL (A f)) ↔
    (∀ α β : HaarAtom b k, scaleBlock α ≠ scaleBlock β →
      ∑ σ : Core.Finite.FiniteRadixSpace b k,
        (A (haarFunction α)) σ * haarFunction β σ = 0) := by
  constructor
  · -- Forward: commutes → scaleBlock-diagonal
    exact fun hcomm α β hne => commutant_scaleBlock_vanishing A hcomm α β hne
  · -- Reverse: scaleBlock-diagonal → commutes
    intro hdiag L hL f
    -- Step 1: Per-atom commutation via haar_inner_injective on difference
    have h_atom : ∀ α : HaarAtom b k,
        finiteBlockProjection b k L hL (A (haarFunction α)) =
        A (finiteBlockProjection b k L hL (haarFunction α)) := by
      intro α
      have h_diff : (fun σ =>
          A (finiteBlockProjection b k L hL (haarFunction α)) σ -
          finiteBlockProjection b k L hL (A (haarFunction α)) σ) = 0 := by
        apply haar_inner_injective; intro β
        simp only [sub_mul, Finset.sum_sub_distrib]
        have hsa := finiteBlockProjection_isOrthogonalProjection k L hL
            (A (haarFunction α)) (haarFunction β)
        -- Case split on P_L's action on h_α
        by_cases hcα : isConstant α
        · -- α constant: P_L h_α = h_α
          rw [constant_haarAtom_preserved α hcα L hL]
          by_cases hcβ : isConstant β
          · rw [constant_haarAtom_preserved β hcβ L hL] at hsa; linarith
          · by_cases hltβ : (supportLevel β).val < L
            · rw [preserve_nat β L hL hltβ] at hsa; linarith
            · push_neg at hltβ
              have hβ_ann := annihilate_nat β L hL hcβ hltβ
              have hdiag_αβ := hdiag α β (by simp [scaleBlock, hcα, hcβ])
              simp only [hβ_ann, Pi.zero_apply, mul_zero,
                Finset.sum_const_zero] at hsa; linarith
        · by_cases hltα : (supportLevel α).val < L
          · -- α non-constant, preserved: P_L h_α = h_α
            rw [preserve_nat α L hL hltα]
            by_cases hcβ : isConstant β
            · rw [constant_haarAtom_preserved β hcβ L hL] at hsa; linarith
            · by_cases hltβ : (supportLevel β).val < L
              · rw [preserve_nat β L hL hltβ] at hsa; linarith
              · push_neg at hltβ
                have hβ_ann := annihilate_nat β L hL hcβ hltβ
                have hdiag_αβ := hdiag α β (by
                  simp only [scaleBlock, hcα, hcβ, ite_false]
                  intro h; exact absurd (Fin.ext_iff.mp (Option.some.inj h)) (by omega))
                simp only [hβ_ann, Pi.zero_apply, mul_zero,
                Finset.sum_const_zero] at hsa; linarith
          · -- α non-constant, annihilated: P_L h_α = 0
            push_neg at hltα
            have hα_ann := annihilate_nat α L hL hcα hltα
            rw [hα_ann, map_zero]
            simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero]
            by_cases hcβ : isConstant β
            · rw [constant_haarAtom_preserved β hcβ L hL] at hsa
              have hdiag_αβ := hdiag α β (by simp [scaleBlock, hcα, hcβ])
              linarith
            · by_cases hltβ : (supportLevel β).val < L
              · rw [preserve_nat β L hL hltβ] at hsa
                have hdiag_αβ := hdiag α β (by
                  simp only [scaleBlock, hcα, hcβ, ite_false]
                  intro h; exact absurd (Fin.ext_iff.mp (Option.some.inj h)) (by omega))
                linarith
              · push_neg at hltβ
                have hβ_ann := annihilate_nat β L hL hcβ hltβ
                simp only [hβ_ann, Pi.zero_apply, mul_zero,
                Finset.sum_const_zero] at hsa; linarith
      -- Convert difference = 0 to function equality
      ext σ; have := congr_fun h_diff σ
      simp only [Pi.zero_apply] at this; linarith
    -- Step 2: Extend from atoms to general f via Haar expansion + linearity
    -- Wrap P_L as a linear map so T = P_L∘A - A∘P_L is a LinearMap
    let P_lm : (Core.Finite.FiniteRadixSpace b k → ℝ) →ₗ[ℝ]
        (Core.Finite.FiniteRadixSpace b k → ℝ) :=
      { toFun := finiteBlockProjection b k L hL
        map_add' := finiteBlockProjection_add k L hL
        map_smul' := finiteBlockProjection_smul k L hL }
    have hT_atom : ∀ α : HaarAtom b k, (P_lm ∘ₗ A - A ∘ₗ P_lm) (haarFunction α) = 0 := by
      intro α; simp only [LinearMap.sub_apply, LinearMap.comp_apply]
      show finiteBlockProjection b k L hL (A (haarFunction α)) -
        A (finiteBlockProjection b k L hL (haarFunction α)) = 0
      exact sub_eq_zero.mpr (h_atom α)
    -- Haar expansion: f = B⁻¹ • ∑_α ⟨f,h_α⟩ • h_α
    have B_ne : (∏ i : Fin (k + 1), (b i : ℝ)) ≠ 0 :=
      ne_of_gt (Finset.prod_pos (fun i _ => Nat.cast_pos.mpr (b.pos i)))
    have f_exp : f = (∏ i : Fin (k + 1), (b i : ℝ))⁻¹ •
        ∑ α : HaarAtom b k,
          (∑ τ : Core.Finite.FiniteRadixSpace b k, f τ * haarFunction α τ) •
          haarFunction α := by
      ext σ; simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      -- Goal: f σ = B⁻¹ * ∑_α (∑_τ f τ * h_α τ) * h_α σ
      have key : (∏ i : Fin (k + 1), (b i : ℝ)) * f σ =
          ∑ α : HaarAtom b k,
            (∑ τ : Core.Finite.FiniteRadixSpace b k, f τ * haarFunction α τ) *
            haarFunction α σ := by
        symm
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
        simp_rw [show ∀ (τ : Core.Finite.FiniteRadixSpace b k) (α : HaarAtom b k),
            f τ * haarFunction α τ * haarFunction α σ =
            f τ * (haarFunction α τ * haarFunction α σ) from fun _ _ => mul_assoc _ _ _]
        simp_rw [← Finset.mul_sum, haarBasis_complete]
        simp [Finset.sum_ite_eq', Finset.mem_univ, mul_comm]
      have B_ne' := B_ne
      field_simp at key ⊢; linarith
    -- T f = 0 by linearity + T h_α = 0
    have hTf : (P_lm ∘ₗ A - A ∘ₗ P_lm) f = 0 := by
      rw [f_exp]; simp only [map_smul, map_sum]
      simp_rw [hT_atom, smul_zero, Finset.sum_const_zero, smul_zero]
    -- Extract goal from T f = 0
    have h_eq : finiteBlockProjection b k L hL (A f) = A (finiteBlockProjection b k L hL f) := by
      have := hTf; simp only [LinearMap.sub_apply, LinearMap.comp_apply] at this
      exact sub_eq_zero.mp this
    exact h_eq.symm

/--
Dimension of the level-ℓ detail subspace D_ℓ.

**fdrs.md Reference:** Line 1416

**Proof**: `Fintype.card` of a subtype equals `Finset.filter.card` on `Finset.univ`.
-/
theorem levelDimension_def (ℓ : Fin (k + 1)) :
    levelDimension b k ℓ = Fintype.card {α : HaarAtom b k // supportLevel α = ℓ} := by
  simp only [levelDimension, dif_pos ℓ.isLt, Fin.eta, Fintype.card_subtype]

end FdrsFormal.Haar
