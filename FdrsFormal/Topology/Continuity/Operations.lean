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

# Ultrametric Continuity and Lipschitz Structure

This file proves that all arithmetic operations are 1-Lipschitz with respect
to the ultrametric distance.

## References

- fdrs.md, Phase 1 Fragment 2, Section 4 (lines 438-499)
- Proposition 12: Tick preserves prefixes
- Corollary 1: Tick is 1-Lipschitz
- Proposition 13: Predecessor is 1-Lipschitz
- Proposition 14: Translation invariance on prefixes
- Corollary 2: Addition is 1-Lipschitz in each input

## Status

SCAFFOLDING ONLY - proofs not yet attempted
-/

import FdrsFormal.Core.Infinite
import FdrsFormal.Operations.Tick
import FdrsFormal.Operations.Predecessor
import FdrsFormal.Operations.Addition
import FdrsFormal.Topology.PrefixCongruence
import FdrsFormal.Topology.Ultrametric

namespace FdrsFormal.Topology.Continuity

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite FdrsFormal.Core.Infinite
open FdrsFormal.Operations.Tick FdrsFormal.Operations.Predecessor FdrsFormal.Operations.Addition
open FdrsFormal.Topology.PrefixCongruence FdrsFormal.Topology.Ultrametric

/-!
## Ultrametric Continuity / Lipschitz Structure

All arithmetic operations are 1-Lipschitz with respect to the ultrametric δ.
-/

/--
**Proposition 12**: Tick preserves prefixes
If π_L(τ) = π_L(σ), then π_L(T(τ)) = π_L(T(σ))
-/
theorem tick_preserves_prefix (b : RadixSeq) (L : ℕ)
    (τ σ : DirectLimitSpace b)
    (h : prefixProjection b L τ = prefixProjection b L σ) :
    prefixProjection b L (tick b τ) = prefixProjection b L (tick b σ) := by
  -- Strategy: Use prefix_congruence_equiv to convert prefix equality to congruence,
  -- then show (n + 1) % B_L = (m + 1) % B_L when n % B_L = m % B_L

  -- Get the congruence from prefix equality
  have h_congr : decode b τ % placeValue b L = decode b σ % placeValue b L := by
    have h1 := (prefix_congruence_equiv b L τ (prefixProjection b L τ)).mp rfl
    have h2 := (prefix_congruence_equiv b L σ (prefixProjection b L τ)).mp h.symm
    calc decode b τ % placeValue b L
        = PrefixCongruence.prefixResidue b L (prefixProjection b L τ) % placeValue b L := h1
      _ = decode b σ % placeValue b L := h2.symm

  -- tick adds 1 to decode
  have h_tick_τ : decode b (tick b τ) = decode b τ + 1 := tick_decode τ
  have h_tick_σ : decode b (tick b σ) = decode b σ + 1 := tick_decode σ

  -- Show (n + 1) % B_L = (m + 1) % B_L when n % B_L = m % B_L
  have h_tick_congr : decode b (tick b τ) % placeValue b L = decode b (tick b σ) % placeValue b L := by
    rw [h_tick_τ, h_tick_σ]
    -- Use Nat.add_mod with shared remainder
    calc (decode b τ + 1) % placeValue b L
        = (decode b τ % placeValue b L + 1 % placeValue b L) % placeValue b L := Nat.add_mod _ _ _
      _ = (decode b σ % placeValue b L + 1 % placeValue b L) % placeValue b L := by rw [h_congr]
      _ = (decode b σ + 1) % placeValue b L := (Nat.add_mod _ _ _).symm

  -- Convert back to prefix equality using the symmetry
  -- tick_prefix is the prefix of tick b τ, show tick b σ has the same prefix
  have h_σ := (prefix_congruence_equiv b L (tick b σ) (prefixProjection b L (tick b τ))).mpr
  have h_result : prefixProjection b L (tick b σ) = prefixProjection b L (tick b τ) := by
    apply h_σ
    have h_τ := (prefix_congruence_equiv b L (tick b τ) (prefixProjection b L (tick b τ))).mp rfl
    rw [← h_tick_congr]
    exact h_τ
  exact h_result.symm

/--
**Corollary 1**: Tick is 1-Lipschitz
δ(T(τ), T(σ)) ≤ δ(τ, σ)
-/
theorem tick_lipschitz (b : RadixSeq) (τ σ : DirectLimitSpace b) :
    ultrametricDist b (DirectLimitSpace.embed b (tick b τ)) (DirectLimitSpace.embed b (tick b σ)) ≤
    ultrametricDist b (DirectLimitSpace.embed b τ) (DirectLimitSpace.embed b σ) := by
  -- Setup: embed τ = τ.digits, prefixProjection b L τ i = τ.digits i
  set x := DirectLimitSpace.embed b τ with hx
  set y := DirectLimitSpace.embed b σ with hy
  set tx := DirectLimitSpace.embed b (tick b τ) with htx
  set ty := DirectLimitSpace.embed b (tick b σ) with hty

  -- Case 1: τ = σ implies tick τ = tick σ, both distances are 0
  by_cases heq : x = y
  · have h_τσ : τ = σ := embed_injective b heq
    subst h_τσ
    -- tx = ty since both based on τ, x = y since both based on τ
    -- ultrametricDist to self is 0
    have h1 : tx = ty := rfl
    have h2 : x = y := rfl
    simp only [ultrametricDist, if_pos h1, if_pos h2, le_refl]

  -- Case 2: τ ≠ σ, need to show firstDiff of ticks ≥ firstDiff of originals
  · -- Let m = firstDiff b x y (where they first differ)
    set m := firstDiff b x y with hm

    -- τ and σ agree on first m digits
    have h_agree : ∀ i : Fin m, τ.digits i = σ.digits i := by
      intro i
      have h := eq_of_lt_firstDiff heq i.isLt
      unfold DirectLimitSpace.embed at hx hy
      calc τ.digits i = x i := by rw [hx]
           _ = y i := h
           _ = σ.digits i := by rw [hy]

    -- Convert to prefixProjection equality
    have h_prefix : prefixProjection b m τ = prefixProjection b m σ := by
      funext i
      exact h_agree i

    -- By tick_preserves_prefix, tick τ and tick σ agree on first m digits
    have h_tick_prefix : prefixProjection b m (tick b τ) = prefixProjection b m (tick b σ) :=
      tick_preserves_prefix b m τ σ h_prefix

    -- Convert back to agreement on embed
    have h_tick_agree : ∀ i : Fin m, tx i = ty i := by
      intro i
      unfold DirectLimitSpace.embed at htx hty
      calc tx i = (tick b τ).digits i := by rw [htx]
           _ = (tick b σ).digits i := congrFun h_tick_prefix i
           _ = ty i := by rw [hty]

    -- So tick τ and tick σ agree on first m digits, meaning firstDiff ≥ m
    have h_firstDiff_ge : m ≤ firstDiff b tx ty ∨ tx = ty := by
      have := (agree_on_prefix_iff m).mp h_tick_agree
      exact this.symm

    -- Case split on whether ticks are equal
    cases h_firstDiff_ge with
    | inl h_ge =>
      -- firstDiff b tx ty ≥ m, so placeValue goes up, distance goes down
      unfold ultrametricDist
      simp only [if_neg heq]
      by_cases htxy : tx = ty
      · simp only [if_pos htxy]
        apply inv_nonneg.mpr
        exact Nat.cast_nonneg _
      · simp only [if_neg htxy]
        -- Need: (placeValue (firstDiff tx ty))⁻¹ ≤ (placeValue m)⁻¹
        have h_place_le : placeValue b m ≤ placeValue b (firstDiff b tx ty) :=
          placeValue.mono h_ge
        have h_pos_m : (0 : ℝ) < placeValue b m := Nat.cast_pos.mpr (placeValue.pos m)
        have h_pos_fd : (0 : ℝ) < placeValue b (firstDiff b tx ty) := Nat.cast_pos.mpr (placeValue.pos _)
        rw [inv_le_inv₀ h_pos_fd h_pos_m]
        exact Nat.cast_le.mpr h_place_le
    | inr htxy =>
      -- tx = ty, distance is 0
      simp only [ultrametricDist, if_neg heq, if_pos htxy]
      apply inv_nonneg.mpr
      exact Nat.cast_nonneg _

/-- Helper: Predecessor preserves prefixes (for nonzero inputs) -/
theorem pred_preserves_prefix (b : RadixSeq) (L : ℕ)
    (τ σ : DirectLimitSpace b)
    (hτ : decode b τ ≠ 0) (hσ : decode b σ ≠ 0)
    (h : prefixProjection b L τ = prefixProjection b L σ) :
    prefixProjection b L (predecessor b τ) = prefixProjection b L (predecessor b σ) := by
  -- Get the congruence from prefix equality
  have h_congr : decode b τ % placeValue b L = decode b σ % placeValue b L := by
    have h1 := (prefix_congruence_equiv b L τ (prefixProjection b L τ)).mp rfl
    have h2 := (prefix_congruence_equiv b L σ (prefixProjection b L τ)).mp h.symm
    calc decode b τ % placeValue b L
        = PrefixCongruence.prefixResidue b L (prefixProjection b L τ) % placeValue b L := h1
      _ = decode b σ % placeValue b L := h2.symm

  -- Use predecessor_preserves_congr_of_ne_zero
  have h_pred_congr : decode b (predecessor b τ) % placeValue b L =
                      decode b (predecessor b σ) % placeValue b L :=
    predecessor_preserves_congr_of_ne_zero L τ σ hτ hσ h_congr

  -- Convert back to prefix equality
  have h_σ := (prefix_congruence_equiv b L (predecessor b σ) (prefixProjection b L (predecessor b τ))).mpr
  have h_result : prefixProjection b L (predecessor b σ) = prefixProjection b L (predecessor b τ) := by
    apply h_σ
    have h_τ := (prefix_congruence_equiv b L (predecessor b τ) (prefixProjection b L (predecessor b τ))).mp rfl
    rw [← h_pred_congr]
    exact h_τ
  exact h_result.symm

/--
**Proposition 13**: Predecessor is 1-Lipschitz
δ(pred(τ), pred(σ)) ≤ δ(τ, σ) on its domain
-/
theorem pred_lipschitz (b : RadixSeq) (τ σ : DirectLimitSpace b)
    (hτ : decode b τ ≠ 0) (hσ : decode b σ ≠ 0) :
    ultrametricDist b (DirectLimitSpace.embed b (predecessor b τ)) (DirectLimitSpace.embed b (predecessor b σ)) ≤
    ultrametricDist b (DirectLimitSpace.embed b τ) (DirectLimitSpace.embed b σ) := by
  -- Same structure as tick_lipschitz
  set x := DirectLimitSpace.embed b τ with hx
  set y := DirectLimitSpace.embed b σ with hy
  set px := DirectLimitSpace.embed b (predecessor b τ) with hpx
  set py := DirectLimitSpace.embed b (predecessor b σ) with hpy

  -- Case 1: τ = σ
  by_cases heq : x = y
  · have h_τσ : τ = σ := embed_injective b heq
    subst h_τσ
    have h1 : px = py := rfl
    have h2 : x = y := rfl
    simp only [ultrametricDist, if_pos h1, if_pos h2, le_refl]

  -- Case 2: τ ≠ σ
  · set m := firstDiff b x y with hm

    -- τ and σ agree on first m digits
    have h_agree : ∀ i : Fin m, τ.digits i = σ.digits i := by
      intro i
      have h := eq_of_lt_firstDiff heq i.isLt
      unfold DirectLimitSpace.embed at hx hy
      calc τ.digits i = x i := by rw [hx]
           _ = y i := h
           _ = σ.digits i := by rw [hy]

    -- Convert to prefixProjection equality
    have h_prefix : prefixProjection b m τ = prefixProjection b m σ := by
      funext i
      exact h_agree i

    -- By pred_preserves_prefix, pred τ and pred σ agree on first m digits
    have h_pred_prefix : prefixProjection b m (predecessor b τ) = prefixProjection b m (predecessor b σ) :=
      pred_preserves_prefix b m τ σ hτ hσ h_prefix

    -- Convert back to agreement on embed
    have h_pred_agree : ∀ i : Fin m, px i = py i := by
      intro i
      unfold DirectLimitSpace.embed at hpx hpy
      calc px i = (predecessor b τ).digits i := by rw [hpx]
           _ = (predecessor b σ).digits i := congrFun h_pred_prefix i
           _ = py i := by rw [hpy]

    -- So pred τ and pred σ agree on first m digits, meaning firstDiff ≥ m
    have h_firstDiff_ge : m ≤ firstDiff b px py ∨ px = py := by
      have := (agree_on_prefix_iff m).mp h_pred_agree
      exact this.symm

    -- Case split on whether preds are equal
    cases h_firstDiff_ge with
    | inl h_ge =>
      unfold ultrametricDist
      simp only [if_neg heq]
      by_cases hpxy : px = py
      · simp only [if_pos hpxy]
        apply inv_nonneg.mpr
        exact Nat.cast_nonneg _
      · simp only [if_neg hpxy]
        have h_place_le : placeValue b m ≤ placeValue b (firstDiff b px py) :=
          placeValue.mono h_ge
        have h_pos_m : (0 : ℝ) < placeValue b m := Nat.cast_pos.mpr (placeValue.pos m)
        have h_pos_fd : (0 : ℝ) < placeValue b (firstDiff b px py) := Nat.cast_pos.mpr (placeValue.pos _)
        rw [inv_le_inv₀ h_pos_fd h_pos_m]
        exact Nat.cast_le.mpr h_place_le
    | inr hpxy =>
      simp only [ultrametricDist, if_neg heq, if_pos hpxy]
      apply inv_nonneg.mpr
      exact Nat.cast_nonneg _

/--
**Proposition 14**: Translation invariance on prefixes
If π_L(τ) = π_L(σ), then π_L(τ ⊕ ρ) = π_L(σ ⊕ ρ)
-/
theorem add_translation_invariance (b : RadixSeq) (L : ℕ)
    (τ σ ρ : DirectLimitSpace b)
    (h : prefixProjection b L τ = prefixProjection b L σ) :
    prefixProjection b L (add b τ ρ) = prefixProjection b L (add b σ ρ) := by
  -- Get the congruence from prefix equality
  have h_congr : decode b τ % placeValue b L = decode b σ % placeValue b L := by
    have h1 := (prefix_congruence_equiv b L τ (prefixProjection b L τ)).mp rfl
    have h2 := (prefix_congruence_equiv b L σ (prefixProjection b L τ)).mp h.symm
    calc decode b τ % placeValue b L
        = PrefixCongruence.prefixResidue b L (prefixProjection b L τ) % placeValue b L := h1
      _ = decode b σ % placeValue b L := h2.symm

  -- Use addition correctness: decode(τ ⊕ ρ) = decode τ + decode ρ
  have h_add_τ : decode b (add b τ ρ) = decode b τ + decode b ρ := add_decode_correct b τ ρ
  have h_add_σ : decode b (add b σ ρ) = decode b σ + decode b ρ := add_decode_correct b σ ρ

  -- Show (decode τ + decode ρ) % B_L = (decode σ + decode ρ) % B_L
  have h_add_congr : decode b (add b τ ρ) % placeValue b L =
                     decode b (add b σ ρ) % placeValue b L := by
    rw [h_add_τ, h_add_σ]
    calc (decode b τ + decode b ρ) % placeValue b L
        = (decode b τ % placeValue b L + decode b ρ % placeValue b L) % placeValue b L := Nat.add_mod _ _ _
      _ = (decode b σ % placeValue b L + decode b ρ % placeValue b L) % placeValue b L := by rw [h_congr]
      _ = (decode b σ + decode b ρ) % placeValue b L := (Nat.add_mod _ _ _).symm

  -- Convert back to prefix equality
  have h_σρ := (prefix_congruence_equiv b L (add b σ ρ) (prefixProjection b L (add b τ ρ))).mpr
  have h_result : prefixProjection b L (add b σ ρ) = prefixProjection b L (add b τ ρ) := by
    apply h_σρ
    have h_τρ := (prefix_congruence_equiv b L (add b τ ρ) (prefixProjection b L (add b τ ρ))).mp rfl
    rw [← h_add_congr]
    exact h_τρ
  exact h_result.symm

/--
**Corollary 2**: Addition is 1-Lipschitz in each input
δ(τ ⊕ ρ, σ ⊕ ρ) ≤ δ(τ, σ) and δ(ρ ⊕ τ, ρ ⊕ σ) ≤ δ(τ, σ)
-/
theorem add_lipschitz_left (b : RadixSeq) (τ σ ρ : DirectLimitSpace b) :
    ultrametricDist b (DirectLimitSpace.embed b (add b τ ρ)) (DirectLimitSpace.embed b (add b σ ρ)) ≤
    ultrametricDist b (DirectLimitSpace.embed b τ) (DirectLimitSpace.embed b σ) := by
  -- Same structure as tick_lipschitz
  set x := DirectLimitSpace.embed b τ with hx
  set y := DirectLimitSpace.embed b σ with hy
  set ax := DirectLimitSpace.embed b (add b τ ρ) with hax
  set ay := DirectLimitSpace.embed b (add b σ ρ) with hay

  -- Case 1: τ = σ
  by_cases heq : x = y
  · have h_τσ : τ = σ := embed_injective b heq
    subst h_τσ
    have h1 : ax = ay := rfl
    have h2 : x = y := rfl
    simp only [ultrametricDist, if_pos h1, if_pos h2, le_refl]

  -- Case 2: τ ≠ σ
  · set m := firstDiff b x y with hm

    -- τ and σ agree on first m digits
    have h_agree : ∀ i : Fin m, τ.digits i = σ.digits i := by
      intro i
      have h := eq_of_lt_firstDiff heq i.isLt
      unfold DirectLimitSpace.embed at hx hy
      calc τ.digits i = x i := by rw [hx]
           _ = y i := h
           _ = σ.digits i := by rw [hy]

    -- Convert to prefixProjection equality
    have h_prefix : prefixProjection b m τ = prefixProjection b m σ := by
      funext i
      exact h_agree i

    -- By add_translation_invariance, (τ ⊕ ρ) and (σ ⊕ ρ) agree on first m digits
    have h_add_prefix : prefixProjection b m (add b τ ρ) = prefixProjection b m (add b σ ρ) :=
      add_translation_invariance b m τ σ ρ h_prefix

    -- Convert back to agreement on embed
    have h_add_agree : ∀ i : Fin m, ax i = ay i := by
      intro i
      unfold DirectLimitSpace.embed at hax hay
      calc ax i = (add b τ ρ).digits i := by rw [hax]
           _ = (add b σ ρ).digits i := congrFun h_add_prefix i
           _ = ay i := by rw [hay]

    -- So (τ ⊕ ρ) and (σ ⊕ ρ) agree on first m digits, meaning firstDiff ≥ m
    have h_firstDiff_ge : m ≤ firstDiff b ax ay ∨ ax = ay := by
      have := (agree_on_prefix_iff m).mp h_add_agree
      exact this.symm

    -- Case split on whether sums are equal
    cases h_firstDiff_ge with
    | inl h_ge =>
      unfold ultrametricDist
      simp only [if_neg heq]
      by_cases haxy : ax = ay
      · simp only [if_pos haxy]
        apply inv_nonneg.mpr
        exact Nat.cast_nonneg _
      · simp only [if_neg haxy]
        have h_place_le : placeValue b m ≤ placeValue b (firstDiff b ax ay) :=
          placeValue.mono h_ge
        have h_pos_m : (0 : ℝ) < placeValue b m := Nat.cast_pos.mpr (placeValue.pos m)
        have h_pos_fd : (0 : ℝ) < placeValue b (firstDiff b ax ay) := Nat.cast_pos.mpr (placeValue.pos _)
        rw [inv_le_inv₀ h_pos_fd h_pos_m]
        exact Nat.cast_le.mpr h_place_le
    | inr haxy =>
      simp only [ultrametricDist, if_neg heq, if_pos haxy]
      apply inv_nonneg.mpr
      exact Nat.cast_nonneg _

theorem add_lipschitz_right (b : RadixSeq) (τ σ ρ : DirectLimitSpace b) :
    ultrametricDist b (DirectLimitSpace.embed b (add b ρ τ)) (DirectLimitSpace.embed b (add b ρ σ)) ≤
    ultrametricDist b (DirectLimitSpace.embed b τ) (DirectLimitSpace.embed b σ) := by
  -- Use commutativity of addition to reduce to add_lipschitz_left
  rw [add_comm b ρ τ, add_comm b ρ σ]
  exact add_lipschitz_left b τ σ ρ

end FdrsFormal.Topology.Continuity
