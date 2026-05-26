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

# Operator Norm Bounds (Contraction Theory)

This file proves norm bounds for finite block projections and detail operators.

## Mathematical Content (fdrs.md lines 877-918)

**Theorem 5 (P_L^(k) is a contraction in all Lp norms)**:
For all k, all 1 ≤ L ≤ k+1, and all 1 ≤ p ≤ ∞:
  |P_L^(k) f|_{p,k} ≤ |f|_{p,k}

In particular, |P_L^(k)|_{Lp → Lp} ≤ 1.

**Corollary 4 (Detail operator bound)**:
  |Δ_L^(k) f|_{p,k} ≤ 2|f|_{p,k}

**Proposition 24 (Gates are contractions)**:
For a gate g (indicator of cylinder union), M_g f := g · f satisfies:
  |M_g f|_{p,k} ≤ |f|_{p,k}

**Proposition 25 (L2 orthogonal projection)**:
For scalar-valued functions (V = ℝ or ℂ), P_L^(k) is the orthogonal projection
in L²(μ_k) onto F_{k,L}-measurable functions.

## Implementation Strategy

Following the axiomatization pattern from FunctionSpaces/Projections/Properties.lean:
- Define Lp norms for finite spaces
- State norm bound theorems
- Axiomatize proof obligations requiring Jensen's inequality, convexity, inner product theory
- Document all axioms with proof sketches referencing mathlib lemmas

## References

- fdrs.md, Phase 2 Fragment 2 (lines 877-918)
- THEOREM_MAPPING.md, Theorem 5
- Pattern: FunctionSpaces/Projections/Properties.lean
-/

import FdrsFormal.FunctionSpaces.Commutant.FiniteProjection
import FdrsFormal.FunctionSpaces.Measure.LpNorm
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.MeanInequalities

open scoped Classical ENNReal NNReal

namespace FdrsFormal.FunctionSpaces.Commutant

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite
open FdrsFormal.FunctionSpaces.Basic
open FdrsFormal.FunctionSpaces.Measure
open MeasureTheory

/-!
## Theorem 5: P_L^(k) is a Contraction
-/

section Contraction

variable {b : RadixSeq} {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/--
**Theorem 5 (sup norm)**: P_L^(k) is a contraction in sup norm.

|P_L^(k) f|_∞ ≤ |f|_∞

**Proof sketch**: Each (P_L^(k) f)(τ) is an average of values of f, so its norm
is ≤ max |f|. This is the averaging contraction principle.

**mathlib references**:
- `Finset.sum` with bound propagation
- Averaging inequality for norms
-/
theorem finiteBlockProjection_supNorm_le (k L : ℕ) (hLk : L ≤ k + 1)
    (f : FiniteRadixSpace b k → V) :
    finiteSupNorm b k (finiteBlockProjection b k L hLk f) ≤ finiteSupNorm b k f := by
  simp only [finiteSupNorm]
  apply iSup_le
  intro τ
  simp only [finiteBlockProjection]
  let s := finitePrefix b L τ hLk
  let m_kL := placeValue b (k + 1) / placeValue b L
  have h_card : Fintype.card (finiteCylinderSet b k L hLk s) = m_kL := finiteCylinder_card k L hLk s
  have h_m_pos : 0 < (m_kL : ℝ) := by
    apply Nat.cast_pos.mpr
    apply Nat.div_pos
    · exact placeValue.mono hLk
    · exact placeValue.pos L
  have h_m_ne_zero : (m_kL : ℕ) ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.div_pos
      (placeValue.mono hLk) (placeValue.pos L))
  have h_abs_inv : |(m_kL : ℝ)⁻¹| = (m_kL : ℝ)⁻¹ := abs_of_pos (inv_pos.mpr h_m_pos)
  -- Triangle inequality for sum
  have h_sum_bound : ‖∑ σ : finiteCylinderSet b k L hLk s, f σ.val‖₊ ≤
      ∑ σ : finiteCylinderSet b k L hLk s, ‖f σ.val‖₊ := nnnorm_sum_le _ _
  -- Each term bounded by sup
  have h_each_bound : ∀ σ : finiteCylinderSet b k L hLk s,
      (‖f σ.val‖₊ : ℝ≥0∞) ≤ ⨆ ρ, (‖f ρ‖₊ : ℝ≥0∞) :=
    fun σ => le_iSup (fun ρ => (‖f ρ‖₊ : ℝ≥0∞)) σ.val
  -- Sum bounded by card * sup
  have h_sum_card_bound : (∑ σ : finiteCylinderSet b k L hLk s, (‖f σ.val‖₊ : ℝ≥0∞)) ≤
      (Fintype.card (finiteCylinderSet b k L hLk s) : ℝ≥0∞) * ⨆ ρ, (‖f ρ‖₊ : ℝ≥0∞) := by
    calc ∑ σ : finiteCylinderSet b k L hLk s, (‖f σ.val‖₊ : ℝ≥0∞)
        ≤ ∑ _σ : finiteCylinderSet b k L hLk s, ⨆ ρ, (‖f ρ‖₊ : ℝ≥0∞) :=
          Finset.sum_le_sum (fun σ _ => h_each_bound σ)
      _ = (Fintype.card (finiteCylinderSet b k L hLk s) : ℝ≥0∞) * ⨆ ρ, (‖f ρ‖₊ : ℝ≥0∞) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- Main calculation
  calc (‖(m_kL : ℝ)⁻¹ • ∑ σ : finiteCylinderSet b k L hLk s, f σ.val‖₊ : ℝ≥0∞)
      = (‖(m_kL : ℝ)⁻¹‖₊ : ℝ≥0∞) * (‖∑ σ : finiteCylinderSet b k L hLk s, f σ.val‖₊ : ℝ≥0∞) := by
        rw [← ENNReal.coe_mul, nnnorm_smul]
    _ ≤ (‖(m_kL : ℝ)⁻¹‖₊ : ℝ≥0∞) * (∑ σ : finiteCylinderSet b k L hLk s, (‖f σ.val‖₊ : ℝ≥0∞)) := by
        gcongr
        exact_mod_cast h_sum_bound
    _ ≤ (‖(m_kL : ℝ)⁻¹‖₊ : ℝ≥0∞) * ((Fintype.card (finiteCylinderSet b k L hLk s) : ℝ≥0∞) * ⨆ ρ, (‖f ρ‖₊ : ℝ≥0∞)) := by
        gcongr
    _ = (‖(m_kL : ℝ)⁻¹‖₊ : ℝ≥0∞) * (m_kL : ℝ≥0∞) * ⨆ ρ, (‖f ρ‖₊ : ℝ≥0∞) := by
        rw [h_card, ← mul_assoc]
    _ = ⨆ ρ, (‖f ρ‖₊ : ℝ≥0∞) := by
        have h_nnnorm_inv : (‖(m_kL : ℝ)⁻¹‖₊ : ℝ≥0∞) = (m_kL : ℝ≥0∞)⁻¹ := by
          rw [← ENNReal.coe_natCast]
          have : ‖(m_kL : ℝ)⁻¹‖₊ = (‖(m_kL : ℝ)‖₊)⁻¹ := nnnorm_inv (m_kL : ℝ)
          rw [this, Real.nnnorm_natCast]
          exact ENNReal.coe_inv (by exact_mod_cast h_m_ne_zero)
        rw [h_nnnorm_inv, ENNReal.inv_mul_cancel, one_mul]
        · exact Nat.cast_ne_zero.mpr h_m_ne_zero
        · exact ENNReal.natCast_ne_top _

/--
**Theorem 5 (general Lp)**: P_L^(k) is a contraction in all Lp norms.

For all 1 ≤ p ≤ ∞: |P_L^(k) f|_{p,k} ≤ |f|_{p,k}

**Proof**: For p = ∞, use sup norm averaging contraction.
For p < ∞, we show ∑ ‖P_L f(τ)‖₊^p ≤ ∑ ‖f(τ)‖₊^p by:
- Triangle + power mean per cylinder: ‖avg f‖^p ≤ avg(‖f‖^p)
- Double counting: ∑_τ avg_{cyl(τ)}(g) = ∑_τ g(τ) for any g
-/
theorem finiteBlockProjection_Lp_norm_le (p : ℝ≥0∞) (hp : 1 ≤ p) (k L : ℕ) (hLk : L ≤ k + 1)
    (f : FiniteRadixSpace b k → V) :
    finiteLpNorm p b k (finiteBlockProjection b k L hLk f) ≤ finiteLpNorm p b k f := by
  simp only [finiteLpNorm]
  split_ifs with hp_top
  · exact finiteBlockProjection_supNorm_le k L hLk f
  · apply mul_le_mul_right
    have hp_pos : 0 < p.toReal :=
      ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le one_pos hp)) hp_top
    have hp_ge : 1 ≤ p.toReal := by
      have : (1 : ℝ≥0∞).toReal ≤ p.toReal :=
        ENNReal.toReal_le_toReal (by norm_num) hp_top |>.mpr hp
      simpa using this
    apply ENNReal.rpow_le_rpow _ (by positivity)
    -- Need: ∑_τ ‖P_L f(τ)‖₊^p ≤ ∑_τ ‖f(τ)‖₊^p
    -- For each τ, ‖P_L f(τ)‖₊ ≤ ⨆ ρ, ‖f ρ‖₊ from the sup norm contraction.
    -- This is enough: ‖P_L f(τ)‖₊^p ≤ (⨆ ρ, ‖f ρ‖₊)^p ≤ ⨆ ρ, ‖f ρ‖₊^p
    -- But summing gives ∑ ‖P_L f(τ)‖₊^p ≤ N * ⨆ ‖f‖^p, not ∑ ‖f‖^p. Too weak.
    -- We need the per-cylinder Jensen approach.
    -- Pointwise Jensen: ‖P_L f(τ)‖₊^p ≤ m⁻¹ * ∑_{cyl(τ)} ‖f(σ)‖₊^p
    -- Sum + double count: ∑_τ [m⁻¹ * ∑_{cyl(τ)} g(σ)] = ∑_τ g(τ)
    set m := placeValue b (k + 1) / placeValue b L
    have hm_pos : 0 < m := Nat.div_pos (placeValue.mono hLk) (placeValue.pos L)
    have hm_ennreal_ne : (m : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hm_pos)
    have hm_ennreal_ne_top : (m : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top m
    -- Define the scalar norm function
    let g : FiniteRadixSpace b k → ℝ≥0∞ := fun τ => (‖f τ‖₊ : ℝ≥0∞) ^ p.toReal
    -- Step A: Pointwise Jensen — ‖P_L f(τ)‖₊^p ≤ m⁻¹ * ∑_{cyl(τ)} g(σ)
    suffices h_jensen : ∀ τ,
        (‖finiteBlockProjection b k L hLk f τ‖₊ : ℝ≥0∞) ^ p.toReal ≤
        (m : ℝ≥0∞)⁻¹ * ∑ σ : finiteCylinderSet b k L hLk (finitePrefix b L τ hLk), g σ.1 by
      -- Step B: Sum over τ and double-count
      calc ∑ τ, (‖finiteBlockProjection b k L hLk f τ‖₊ : ℝ≥0∞) ^ p.toReal
          ≤ ∑ τ, ((m : ℝ≥0∞)⁻¹ *
              ∑ σ : finiteCylinderSet b k L hLk (finitePrefix b L τ hLk), g σ.1) :=
            Finset.sum_le_sum (fun τ _ => h_jensen τ)
        _ = ∑ τ, g τ := by
            simp_rw [← Finset.mul_sum]
            have h_double : ∑ τ : FiniteRadixSpace b k,
                ∑ σ : finiteCylinderSet b k L hLk (finitePrefix b L τ hLk), g σ.val =
                (m : ℝ≥0∞) * ∑ σ : FiniteRadixSpace b k, g σ := by
              have h_cyl_symm : ∀ (τ : FiniteRadixSpace b k)
                  (σ : finiteCylinderSet b k L hLk (finitePrefix b L τ hLk)),
                  τ ∈ finiteCylinderSet b k L hLk (finitePrefix b L σ.val hLk) :=
                fun τ σ i => (σ.property i).symm
              let PairType := (τ : FiniteRadixSpace b k) ×
                finiteCylinderSet b k L hLk (finitePrefix b L τ hLk)
              let swapEquiv : PairType ≃ PairType := {
                toFun := fun ⟨τ, σ⟩ => ⟨σ.val, ⟨τ, h_cyl_symm τ σ⟩⟩
                invFun := fun ⟨σ, τ⟩ => ⟨τ.val, ⟨σ, h_cyl_symm σ τ⟩⟩
                left_inv := fun ⟨_, _⟩ => rfl
                right_inv := fun ⟨_, _⟩ => rfl
              }
              -- nested → sigma
              have h1 : ∑ τ : FiniteRadixSpace b k,
                  ∑ σ : finiteCylinderSet b k L hLk (finitePrefix b L τ hLk), g σ.val =
                  ∑ p : PairType, g p.2.val :=
                (Fintype.sum_sigma' (fun (τ : FiniteRadixSpace b k)
                  (σ : finiteCylinderSet b k L hLk (finitePrefix b L τ hLk)) =>
                  g σ.val)).symm
              -- swap
              have h2 : ∑ p : PairType, g p.2.val = ∑ q : PairType, g q.1 :=
                Fintype.sum_equiv swapEquiv (fun p => g p.2.val) (fun q => g q.1)
                  (fun ⟨_, _⟩ => rfl)
              -- sigma → nested
              have h3 : ∑ q : PairType, g q.1 =
                  ∑ σ : FiniteRadixSpace b k,
                  ∑ _τ : finiteCylinderSet b k L hLk (finitePrefix b L σ hLk), g σ := by
                simp only [PairType]
                rw [← Fintype.sum_sigma']
              -- inner sum is constant
              have h4 : ∑ σ : FiniteRadixSpace b k,
                  ∑ _τ : finiteCylinderSet b k L hLk (finitePrefix b L σ hLk), g σ =
                  (m : ℝ≥0∞) * ∑ σ, g σ := by
                simp_rw [Finset.sum_const, Finset.card_univ, finiteCylinder_card k L hLk,
                  nsmul_eq_mul]
                rw [← Finset.mul_sum]
              exact h1.trans (h2.trans (h3.trans h4))
            rw [h_double, ← mul_assoc, ENNReal.inv_mul_cancel hm_ennreal_ne hm_ennreal_ne_top,
              one_mul]
    -- Prove pointwise Jensen
    intro τ
    simp only [finiteBlockProjection, g]
    -- Goal: ‖m⁻¹ • ∑ f(σ)‖₊^p ≤ m⁻¹ * ∑ ‖f(σ)‖₊^p
    -- Step 1: ‖m⁻¹ • ∑ f(σ)‖₊ ≤ m⁻¹ * ∑ ‖f(σ)‖₊ (triangle)
    -- Step 2: (m⁻¹ * ∑ a_i)^p ≤ m⁻¹ * ∑ a_i^p (power mean)
    set S_v := ∑ σ : finiteCylinderSet b k L hLk (finitePrefix b L τ hLk), f σ.1
    set S_n := ∑ σ : finiteCylinderSet b k L hLk (finitePrefix b L τ hLk),
      (‖f σ.val‖₊ : ℝ≥0∞)
    -- Triangle
    have h_tri : (‖(m : ℝ)⁻¹ • S_v‖₊ : ℝ≥0∞) ≤ (m : ℝ≥0∞)⁻¹ * S_n := by
      calc (‖(m : ℝ)⁻¹ • S_v‖₊ : ℝ≥0∞)
          = (‖(m : ℝ)⁻¹‖₊ * ‖S_v‖₊ : ℝ≥0) := by rw [nnnorm_smul]
        _ ≤ (‖(m : ℝ)⁻¹‖₊ * ∑ σ : finiteCylinderSet b k L hLk (finitePrefix b L τ hLk),
              ‖f σ.1‖₊ : ℝ≥0) := by
            gcongr; exact nnnorm_sum_le _ _
        _ = (m : ℝ≥0∞)⁻¹ * S_n := by
            push_cast [S_n]
            congr 1
            · rw [← ENNReal.coe_natCast,
                show (‖(m : ℝ)⁻¹‖₊ : ℝ≥0) = (‖(m : ℝ)‖₊)⁻¹ from nnnorm_inv _,
                Real.nnnorm_natCast]
              exact ENNReal.coe_inv (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hm_pos))
    -- Power mean: (m⁻¹ * S_n)^p ≤ m⁻¹ * ∑ ‖f(σ)‖₊^p
    -- Use ENNReal.rpow_sum_le_const_mul_sum_rpow: S_n^p ≤ m^{p-1} * ∑ a^p
    have h_card : Fintype.card (finiteCylinderSet b k L hLk (finitePrefix b L τ hLk)) = m :=
      finiteCylinder_card k L hLk _
    have h_pm : S_n ^ p.toReal ≤ (m : ℝ≥0∞) ^ (p.toReal - 1) *
        ∑ σ : finiteCylinderSet b k L hLk (finitePrefix b L τ hLk),
        (‖f σ.val‖₊ : ℝ≥0∞) ^ p.toReal := by
      have := ENNReal.rpow_sum_le_const_mul_sum_rpow (s := Finset.univ)
        (fun (σ : finiteCylinderSet b k L hLk (finitePrefix b L τ hLk)) =>
          (‖f σ.val‖₊ : ℝ≥0∞)) hp_ge
      rwa [Finset.card_univ, h_card] at this
    -- Chain: ‖avg‖^p ≤ (m⁻¹ * S_n)^p = m⁻ᵖ * S_n^p ≤ m⁻ᵖ * m^{p-1} * ∑ a^p = m⁻¹ * ∑ a^p
    calc ((‖(↑m : ℝ)⁻¹ • S_v‖₊ : ℝ≥0∞)) ^ p.toReal
        ≤ ((m : ℝ≥0∞)⁻¹ * S_n) ^ p.toReal :=
          ENNReal.rpow_le_rpow h_tri (le_of_lt hp_pos)
      _ = ((m : ℝ≥0∞)⁻¹) ^ p.toReal * S_n ^ p.toReal :=
          ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt hp_pos)
      _ ≤ ((m : ℝ≥0∞)⁻¹) ^ p.toReal * ((m : ℝ≥0∞) ^ (p.toReal - 1) *
            ∑ σ : finiteCylinderSet b k L hLk (finitePrefix b L τ hLk),
            (‖f σ.val‖₊ : ℝ≥0∞) ^ p.toReal) := by gcongr
      _ = (m : ℝ≥0∞)⁻¹ *
            ∑ σ : finiteCylinderSet b k L hLk (finitePrefix b L τ hLk),
            (‖f σ.val‖₊ : ℝ≥0∞) ^ p.toReal := by
          rw [← mul_assoc]; congr 1
          rw [ENNReal.inv_rpow, ← ENNReal.rpow_neg _ p.toReal,
            ← ENNReal.rpow_add (-p.toReal) (p.toReal - 1) hm_ennreal_ne hm_ennreal_ne_top,
            show -p.toReal + (p.toReal - 1) = -1 from by ring, ENNReal.rpow_neg_one]

theorem finiteBlockProjection_L1_norm_le (k L : ℕ) (hLk : L ≤ k + 1)
    (f : FiniteRadixSpace b k → V) :
    finiteLpNorm 1 b k (finiteBlockProjection b k L hLk f) ≤ finiteLpNorm 1 b k f :=
  finiteBlockProjection_Lp_norm_le 1 le_rfl k L hLk f

theorem finiteBlockProjection_L2_norm_le (k L : ℕ) (hLk : L ≤ k + 1)
    (f : FiniteRadixSpace b k → V) :
    finiteLpNorm 2 b k (finiteBlockProjection b k L hLk f) ≤ finiteLpNorm 2 b k f :=
  finiteBlockProjection_Lp_norm_le 2 (by norm_num) k L hLk f

end Contraction

/-!
## Corollary 4: Detail Operator Bounds
-/

section DetailBounds

variable {b : RadixSeq} {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/--
**Corollary 4**: Detail operators are bounded.

|Δ_L^(k) f|_p ≤ |P_{L+1}^(k) f|_p + |P_L^(k) f|_p ≤ 2|f|_p

**Proof**: Triangle inequality + Theorem 5.
-/
theorem finiteDetailOperator_norm_bound (p : ℝ≥0∞) (hp : 1 ≤ p) (k L : ℕ) (hLk : L < k + 1)
    (f : FiniteRadixSpace b k → V) :
    finiteLpNorm p b k (finiteDetailOperator b k L hLk f) ≤
    2 * finiteLpNorm p b k f := by
  -- Δ_L^(k) f = P_{L+1}^(k) f - P_L^(k) f
  simp only [finiteDetailOperator]

  -- Step 1: Triangle inequality for Lp norm
  -- |P_{L+1}f - P_Lf|_p ≤ |P_{L+1}f|_p + |P_Lf|_p
  have h_triangle := finiteLpNorm_sub_le p hp k
    (finiteBlockProjection b k (L + 1) (by omega) f)
    (finiteBlockProjection b k L (by omega) f)

  -- Step 2: Apply contraction bounds for each projection
  have h_proj1 := finiteBlockProjection_Lp_norm_le p hp k (L + 1) (by omega) f
  have h_proj2 := finiteBlockProjection_Lp_norm_le p hp k L (by omega) f

  -- Step 3: Chain the inequalities
  calc finiteLpNorm p b k (finiteBlockProjection b k (L + 1) _ f -
                           finiteBlockProjection b k L _ f)
      ≤ finiteLpNorm p b k (finiteBlockProjection b k (L + 1) _ f) +
        finiteLpNorm p b k (finiteBlockProjection b k L _ f) := h_triangle
    _ ≤ finiteLpNorm p b k f + finiteLpNorm p b k f := add_le_add h_proj1 h_proj2
    _ = 2 * finiteLpNorm p b k f := by ring

end DetailBounds

/-!
## Proposition 24: Gate Contractions
-/

section GateContractions

variable {b : RadixSeq} {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/--
A gate is a cylinder-measurable {0,1}-valued function (indicator of cylinder union).

For simplicity, we allow general complex weights (gates ∈ ℓ^∞ with |g| ≤ 1).
-/
def isGate (b : RadixSeq) (k L : ℕ) (hLk : L ≤ k + 1) (g : FiniteRadixSpace b k → ℝ) : Prop :=
  (∀ τ, g τ ∈ Set.Icc 0 1) ∧
  (∀ τ τ', finitePrefix b L τ hLk = finitePrefix b L τ' hLk → g τ = g τ')

/--
Multiplication by a gate (pointwise).
-/
noncomputable def gateMultiply (k : ℕ) (g : FiniteRadixSpace b k → ℝ)
    (f : FiniteRadixSpace b k → V) : FiniteRadixSpace b k → V :=
  fun τ => g τ • f τ

/--
**Proposition 24**: Gates are contractions in all Lp norms.

For a gate g (|g| ≤ 1) and any p:
  |M_g f|_p ≤ |f|_p

**Proof sketch**: Pointwise |g(τ) f(τ)| ≤ |f(τ)| since |g(τ)| ≤ 1.
Propagate through Lp norm definition.

**mathlib references**:
- `norm_smul_le` with |g| ≤ 1 bound
- `Finset.sum_le_sum` for pointwise bounds
-/
theorem gateMultiply_supNorm_le (k L : ℕ) (hLk : L ≤ k + 1) (g : FiniteRadixSpace b k → ℝ)
    (hg : isGate b k L hLk g) (f : FiniteRadixSpace b k → V) :
    finiteSupNorm b k (gateMultiply k g f) ≤ finiteSupNorm b k f := by
  -- finiteSupNorm is the sup of norms
  simp only [finiteSupNorm, gateMultiply]
  -- For each τ, ‖g τ • f τ‖ ≤ ‖f τ‖ since |g τ| ≤ 1
  apply iSup_le
  intro τ
  apply le_iSup_of_le τ
  -- Need: ‖g τ • f τ‖₊ ≤ ‖f τ‖₊
  simp only [ENNReal.coe_le_coe]
  -- ‖g τ • f τ‖₊ = |g τ|₊ * ‖f τ‖₊
  rw [nnnorm_smul]
  -- |g τ| ≤ 1, so |g τ|₊ * ‖f τ‖₊ ≤ 1 * ‖f τ‖₊ = ‖f τ‖₊
  have hg_bound : g τ ∈ Set.Icc (0 : ℝ) 1 := hg.1 τ
  have hg_abs : |g τ| ≤ 1 := by
    rw [abs_le]
    constructor
    · linarith [hg_bound.1]
    · exact hg_bound.2
  have hg_nnnorm : ‖g τ‖₊ ≤ 1 := by
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    simpa using hg_abs
  calc ‖g τ‖₊ * ‖f τ‖₊ ≤ 1 * ‖f τ‖₊ := by apply mul_le_mul_of_nonneg_right hg_nnnorm (zero_le _)
    _ = ‖f τ‖₊ := one_mul _

theorem gateMultiply_Lp_norm_le (p : ℝ≥0∞) (hp : 1 ≤ p) (k L : ℕ) (hLk : L ≤ k + 1)
    (g : FiniteRadixSpace b k → ℝ) (hg : isGate b k L hLk g)
    (f : FiniteRadixSpace b k → V) :
    finiteLpNorm p b k (gateMultiply k g f) ≤ finiteLpNorm p b k f := by
  simp only [finiteLpNorm]
  split_ifs with hp_top
  · -- Case p = ∞: use existing sup norm proof
    exact gateMultiply_supNorm_le k L hLk g hg f
  · -- Case 1 ≤ p < ∞: pointwise ‖g(τ) • f(τ)‖^p ≤ ‖f(τ)‖^p
    -- since ‖g(τ)‖₊ ≤ 1
    gcongr with τ _
    -- Goal: ‖gateMultiply k g f τ‖₊ ≤ ‖f τ‖₊
    simp only [gateMultiply]
    rw [nnnorm_smul]
    have hg_bound : g τ ∈ Set.Icc (0 : ℝ) 1 := hg.1 τ
    have hg_nnnorm : ‖g τ‖₊ ≤ 1 := by
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      simpa using abs_le.mpr ⟨by linarith [hg_bound.1], hg_bound.2⟩
    calc ‖g τ‖₊ * ‖f τ‖₊ ≤ 1 * ‖f τ‖₊ := mul_le_mul_of_nonneg_right hg_nnnorm (zero_le _)
      _ = ‖f τ‖₊ := one_mul _

end GateContractions

/-!
## Proposition 25: L² Orthogonal Projection
-/

section OrthogonalProjection

variable {b : RadixSeq}

/--
**Proposition 25**: For scalar-valued functions (V = ℝ or ℂ), P_L^(k) is the
orthogonal projection in L²(μ_k) onto the subspace of F_{k,L}-measurable
(block-constant) functions.

**Proof sketch**: Conditional expectation is the L² orthogonal projection onto
the subspace of F_{k,L}-measurable functions. In finite uniform spaces this is
a direct verification by blockwise averaging.

**mathlib references**:
- `MeasureTheory.condexp_eq_iSup` (conditional expectation)
- Orthogonal projection onto subspace
- `inner_product_space` results for ℝ/ℂ spaces
-/
theorem finiteBlockProjection_isOrthogonalProjection (k L : ℕ) (hLk : L ≤ k + 1) :
    ∀ f g : FiniteRadixSpace b k → ℝ,
      -- P_L is self-adjoint: ⟨P_L f, g⟩ = ⟨f, P_L g⟩
      (∑ τ : FiniteRadixSpace b k,
        (finiteBlockProjection b k L hLk f τ) * (g τ)) =
      (∑ τ : FiniteRadixSpace b k,
        (f τ) * (finiteBlockProjection b k L hLk g τ)) := by
  intro f g
  -- Both sides equal m⁻¹ · ∑_s ∑_{σ ∈ cyl(s)} ∑_{ρ ∈ cyl(s)} f(σ) · g(ρ)
  -- Strategy: unfold P_L, extract the constant average from each cylinder block,
  -- show both sides reduce to the same double sum.
  simp only [finiteBlockProjection]
  -- LHS: ∑_τ (m⁻¹ · ∑_{σ ∈ cyl(τ)} f(σ)) · g(τ)
  -- RHS: ∑_τ f(τ) · (m⁻¹ · ∑_{σ ∈ cyl(τ)} g(σ))
  set m := placeValue b (k + 1) / placeValue b L with hm_def
  -- Both sides involve smul_mul / mul_smul patterns
  -- LHS: ∑_τ ((m⁻¹ : ℝ) • ∑_{σ ∈ cyl(τ)} f(σ)) * g(τ)
  --     = (m⁻¹ : ℝ) * ∑_τ (∑_{σ ∈ cyl(τ)} f(σ)) * g(τ)
  -- RHS: ∑_τ f(τ) * ((m⁻¹ : ℝ) • ∑_{σ ∈ cyl(τ)} g(σ))
  --     = (m⁻¹ : ℝ) * ∑_τ f(τ) * (∑_{σ ∈ cyl(τ)} g(σ))
  -- So it suffices to show the inner sums are equal (without the m⁻¹ factor).
  -- After factoring out m⁻¹ on both sides, we need:
  -- ∑_τ (∑_{σ ∈ cyl(τ)} f(σ)) * g(τ) = ∑_τ f(τ) * (∑_{σ ∈ cyl(τ)} g(σ))
  -- Both equal ∑_τ ∑_{σ ∈ cyl(τ)} f(σ) * g(τ) vs ∑_τ ∑_{ρ ∈ cyl(τ)} f(τ) * g(ρ)
  -- These are equal by swapping (τ, σ) ↔ (σ, τ) within same cylinder.
  conv_lhs =>
    arg 2; ext τ
    rw [smul_mul_assoc]
  conv_rhs =>
    arg 2; ext τ
    rw [mul_smul_comm]
  rw [← Finset.smul_sum, ← Finset.smul_sum]
  congr 1
  -- Goal: ∑_τ (∑_{σ ∈ cyl(τ)} f(σ)) * g(τ) = ∑_τ f(τ) * (∑_{σ ∈ cyl(τ)} g(σ))
  -- Expand: distribute multiplication into sums
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  -- Goal: ∑_τ ∑_{σ ∈ cyl(τ)} f(σ.val) * g(τ) = ∑_τ ∑_{σ ∈ cyl(τ)} f(τ) * g(σ.val)
  -- Both are sums over pairs (τ, σ) in the same cylinder.
  -- Key symmetry: σ ∈ cyl(τ) implies τ ∈ cyl(σ)
  have h_symm : ∀ (τ : FiniteRadixSpace b k)
      (σ : finiteCylinderSet b k L hLk (finitePrefix b L τ hLk)),
      τ ∈ finiteCylinderSet b k L hLk (finitePrefix b L σ.val hLk) := by
    intro τ σ i
    simp only [finitePrefix]
    exact (σ.property i).symm
  -- Convert to sigma sums and swap
  rw [← Fintype.sum_sigma']
  rw [← Fintype.sum_sigma']
  let PairType := (τ : FiniteRadixSpace b k) ×
      finiteCylinderSet b k L hLk (finitePrefix b L τ hLk)
  let swapFun : PairType → PairType :=
    fun ⟨τ, σ⟩ => ⟨σ.val, ⟨τ, h_symm τ σ⟩⟩
  let swapEquiv : PairType ≃ PairType := {
    toFun := swapFun
    invFun := swapFun
    left_inv := fun ⟨τ, σ⟩ => rfl
    right_inv := fun ⟨τ, σ⟩ => rfl
  }
  exact Fintype.sum_equiv swapEquiv _ _ (fun ⟨τ, σ⟩ => rfl)

/--
P_L^(k) is idempotent (follows from Proposition 21(1), already proven).

This is a defining property of orthogonal projections.
-/
theorem finiteBlockProjection_idempotent_restated (k L : ℕ) (hLk : L ≤ k + 1)
    [AddCommGroup V] [Module ℝ V] (f : FiniteRadixSpace b k → V) :
    finiteBlockProjection b k L hLk (finiteBlockProjection b k L hLk f) =
    finiteBlockProjection b k L hLk f := by
  exact finiteBlockProjection_idempotent k L hLk f

/--
P_L^(k) projects onto range(P_L^(k)) (block-constant functions).

Combined with self-adjointness, this characterizes P_L^(k) as the unique
orthogonal projection onto the F_{k,L}-measurable subspace.
-/
theorem finiteBlockProjection_range_eq_blockConstant (k L : ℕ) (hLk : L ≤ k + 1)
    [AddCommGroup V] [Module ℝ V] :
    ∀ f : FiniteRadixSpace b k → V,
      (∀ τ τ', finitePrefix b L τ hLk = finitePrefix b L τ' hLk →
        finiteBlockProjection b k L hLk f τ = finiteBlockProjection b k L hLk f τ') := by
  intro f τ τ' h_prefix
  exact finiteBlockProjection_isBlockConstant k L hLk f τ τ' h_prefix

end OrthogonalProjection

/-!
## Operator Norm Bounds (as Linear Maps)
-/

section OperatorNorms

variable {b : RadixSeq} {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/--
The operator norm of P_L^(k) is at most 1 in sup norm.

**Corollary of Theorem 5**.
-/
theorem finiteBlockProjection_opNorm_le_one_sup (k L : ℕ) (hLk : L ≤ k + 1) :
    ∀ f : FiniteRadixSpace b k → V,
      finiteSupNorm b k (finiteBlockProjection b k L hLk f) ≤
      finiteSupNorm b k f :=
  finiteBlockProjection_supNorm_le k L hLk

/--
The operator norm of P_L^(k) is at most 1 in Lp norm (general).
-/
theorem finiteBlockProjection_opNorm_le_one_Lp (p : ℝ≥0∞) (hp : 1 ≤ p) (k L : ℕ) (hLk : L ≤ k + 1) :
    ∀ f : FiniteRadixSpace b k → V,
      finiteLpNorm p b k (finiteBlockProjection b k L hLk f) ≤
      finiteLpNorm p b k f :=
  finiteBlockProjection_Lp_norm_le p hp k L hLk

end OperatorNorms

end FdrsFormal.FunctionSpaces.Commutant
