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

# Locality vs Commutation

Separation theorems showing locality and commutation are distinct properties.

## Mathematical Content (fdrs.md lines 1163-1211)

**Definition 32**: Linear L-locality on R^(k)
**Proposition 28**: Matrix characterization of locality
**Proposition 29**: Commutation is weaker than locality (existence of counterexample)
**Proposition 30**: Locality is weaker than commutation (existence of counterexample)
**Theorem 9**: Intersection = L-local AND commuting with P_L

## References

- fdrs.md, Phase 2 Fragment 3 (lines 1163-1211)
- THEOREM_MAPPING.md
-/

import FdrsFormal.FunctionSpaces.Commutant.BlockDiagonal

namespace FdrsFormal.FunctionSpaces.Commutant

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite
open FdrsFormal.FunctionSpaces.Basic

/-!
## Definition 32: Linear L-Locality
-/

variable (b : RadixSeq) (V : Type*) (k : ℕ)
variable [AddCommGroup V] [Module ℝ V]

/--
**Definition 32**: A linear operator A is L-local if for every τ, (Af)(τ) depends
only on f restricted to the block U_k(π_L(τ)).

Equivalently: f|_{U_k(π_L(τ))} ≡ 0 ⇒ (Af)(τ) = 0
-/
def isLocal (A : (FiniteRadixSpace b k → V) → (FiniteRadixSpace b k → V))
    (L : ℕ) (hLk : L ≤ k + 1) : Prop :=
  ∀ τ : FiniteRadixSpace b k, ∀ f g : FiniteRadixSpace b k → V,
    (∀ σ ∈ finiteCylinderSet b k L hLk (finitePrefix b L τ hLk), f σ = g σ) →
    A f τ = A g τ

/-!
## Propositions 3.3-3.4: Separation Results
-/

/--
**Proposition 29**: Commutation is weaker than locality.

There exist operators commuting with P_L that are not L-local.

**Proof**: Take b = const 2, k = 1, L = 1, A = P_0 (global average).
P_0 commutes with P_1 by `finiteBlockProjection_comm`. P_0 is NOT 1-local:
if it were, applying locality at two cylinder representatives (one per cylinder)
with the constant-1 and constant-0 functions as comparands would force the
globally-constant P_0(g) to equal both 1 and 0, a contradiction.
-/
theorem exists_commutes_not_local :
    ∃ (b : RadixSeq) (k L : ℕ) (hLk : L ≤ k + 1)
      (A : (FiniteRadixSpace b k → ℝ) → (FiniteRadixSpace b k → ℝ)),
      commutesWithProjection A L hLk ∧ ¬ isLocal b ℝ k A L hLk := by
  -- b = const 2, k = 1, L = 1, A = P_0 (global average)
  let b : RadixSeq := ⟨fun _ => 2, fun _ => le_refl 2⟩
  have hb1 : ∀ i : ℕ, 1 < b i := fun i => by have := b.ge_two i; omega
  refine ⟨b, 1, 1, by omega, finiteBlockProjection b 1 0 (by omega), ?_, ?_⟩
  · -- P_0 commutes with P_1 (projection commutativity)
    intro f
    exact finiteBlockProjection_comm 1 0 1 (by omega) (by omega) f
  · -- P_0 is NOT 1-local
    intro hloc
    -- Representatives from each 1-cylinder
    let τ₀ : FiniteRadixSpace b 1 := fun i => ⟨0, b.pos i⟩
    let σ₁ : FiniteRadixSpace b 1 :=
      fun i => if i.val = 0 then ⟨1, hb1 i⟩ else ⟨0, b.pos i⟩
    -- Indicator of the 1-cylinder of τ₀: g(σ) = 1 if σ(0) matches τ₀(0), else 0
    let g : FiniteRadixSpace b 1 → ℝ :=
      fun τ => if τ ⟨0, by omega⟩ = (⟨0, b.pos 0⟩ : Fin (b 0)) then 1 else 0
    -- g agrees with constant-1 on 1-cyl(τ₀)
    have h_agree_1 : ∀ σ ∈ finiteCylinderSet b 1 1 (by omega) (finitePrefix b 1 τ₀ (by omega)),
        g σ = (fun _ => (1 : ℝ)) σ := by
      intro σ hσ
      show (if σ ⟨0, by omega⟩ = (⟨0, b.pos 0⟩ : Fin (b 0)) then 1 else 0) = 1
      rw [if_pos]
      have h0 := hσ ⟨0, by omega⟩
      simp only [finitePrefix, τ₀] at h0
      exact h0
    -- By locality: P_0(g)(τ₀) = P_0(1)(τ₀) = 1
    have h_loc1 := hloc τ₀ g (fun _ => 1) h_agree_1
    have hP1 : finiteBlockProjection b 1 0 (by omega) (fun _ => (1 : ℝ)) τ₀ = 1 :=
      congr_fun (finiteBlockProjection_const 1 0 (by omega) (1 : ℝ)) τ₀
    rw [hP1] at h_loc1
    -- P_0(g) is 0-block-constant (globally constant), so P_0(g)(σ₁) = P_0(g)(τ₀)
    have h_const : finiteBlockProjection b 1 0 (by omega) g τ₀ =
        finiteBlockProjection b 1 0 (by omega) g σ₁ :=
      finiteBlockProjection_isBlockConstant 1 0 (by omega) g τ₀ σ₁
        (by ext i; exact i.elim0)
    -- g agrees with constant-0 on 1-cyl(σ₁)
    have h_agree_0 : ∀ σ ∈ finiteCylinderSet b 1 1 (by omega) (finitePrefix b 1 σ₁ (by omega)),
        g σ = (fun _ => (0 : ℝ)) σ := by
      intro σ hσ
      show (if σ ⟨0, by omega⟩ = (⟨0, b.pos 0⟩ : Fin (b 0)) then 1 else 0) = 0
      rw [if_neg]
      -- σ is in the 1-cylinder of σ₁, so σ(0) = σ₁(0) = ⟨1, _⟩ ≠ ⟨0, _⟩
      have h0 := hσ ⟨0, by omega⟩
      simp only [finitePrefix, σ₁] at h0
      rw [h0]
      simp
    -- By locality: P_0(g)(σ₁) = P_0(0)(σ₁) = 0
    have h_loc0 := hloc σ₁ g (fun _ => 0) h_agree_0
    have hP0 : finiteBlockProjection b 1 0 (by omega) (fun _ => (0 : ℝ)) σ₁ = 0 :=
      congr_fun (finiteBlockProjection_const 1 0 (by omega) (0 : ℝ)) σ₁
    rw [hP0] at h_loc0
    -- P_0(g)(τ₀) = 1  and  P_0(g)(τ₀) = P_0(g)(σ₁) = 0  →  1 = 0
    linarith

/--
**Proposition 30**: Locality is weaker than commutation.

There exist L-local operators that do not commute with P_L.

**Proof**: Take b = const 2, k = 1, L = 0.
A = pointwise multiplication operator: (Af)(τ) = (if digit0 = 0 then 0 else 1) · f(τ).
A is trivially 0-local (the 0-cylinder is the entire space).
If A commuted with P_0, then A(1) = P_0(A(1)) would force A(1) to be globally constant.
But A(1) takes values 0 and 1 at different points — contradiction.
-/
theorem exists_local_not_commutes :
    ∃ (b : RadixSeq) (k L : ℕ) (hLk : L ≤ k + 1)
      (A : (FiniteRadixSpace b k → ℝ) → (FiniteRadixSpace b k → ℝ)),
      isLocal b ℝ k A L hLk ∧ ¬ commutesWithProjection A L hLk := by
  -- b = const 2, k = 1, L = 0
  let b : RadixSeq := ⟨fun _ => 2, fun _ => le_refl 2⟩
  have hb1 : ∀ i : ℕ, 1 < b i := fun i => by have := b.ge_two i; omega
  -- A f τ = (if digit0 = 0 then 0 else 1) * f(τ) — a pointwise multiplication operator
  let A : (FiniteRadixSpace b 1 → ℝ) → (FiniteRadixSpace b 1 → ℝ) :=
    fun f τ => (if τ ⟨0, by omega⟩ = (⟨0, b.pos 0⟩ : Fin (b 0)) then 0 else 1) * f τ
  refine ⟨b, 1, 0, by omega, A, ?_, ?_⟩
  · -- A is 0-local: the 0-cylinder is the entire space, so this is trivial
    intro τ f g hfg
    show (if τ ⟨0, _⟩ = _ then 0 else 1) * f τ = (if τ ⟨0, _⟩ = _ then 0 else 1) * g τ
    congr 1
    exact hfg τ (by intro i; exact i.elim0)
  · -- A does NOT commute with P_0
    intro hcomm
    -- f₁ = constant 1
    let f₁ : FiniteRadixSpace b 1 → ℝ := fun _ => 1
    have h := hcomm f₁
    -- P_0(f₁) = f₁ (constant function is fixed by projection)
    have hPf₁ : finiteBlockProjection b 1 0 (by omega) f₁ = f₁ :=
      finiteBlockProjection_const 1 0 (by omega) (1 : ℝ)
    rw [hPf₁] at h
    -- h : A f₁ = P_0(A f₁), so A f₁ is 0-block-constant (globally constant)
    -- Two elements with different first digits
    let τ₀ : FiniteRadixSpace b 1 := fun i => ⟨0, b.pos i⟩
    let τ₁ : FiniteRadixSpace b 1 :=
      fun i => if i.val = 0 then ⟨1, hb1 i⟩ else ⟨0, b.pos i⟩
    -- P_0(A f₁) is 0-block-constant (globally constant): same value at τ₀ and τ₁
    have h_bc : finiteBlockProjection b 1 0 (by omega) (A f₁) τ₀ =
        finiteBlockProjection b 1 0 (by omega) (A f₁) τ₁ :=
      finiteBlockProjection_isBlockConstant 1 0 (by omega) (A f₁) τ₀ τ₁
        (by ext i; exact i.elim0)
    -- From h: A f₁ = P_0(A f₁), so A f₁ τ₀ = A f₁ τ₁
    have h_eq : A f₁ τ₀ = A f₁ τ₁ := by
      calc A f₁ τ₀ = finiteBlockProjection b 1 0 (by omega) (A f₁) τ₀ := congr_fun h τ₀
        _ = finiteBlockProjection b 1 0 (by omega) (A f₁) τ₁ := h_bc
        _ = A f₁ τ₁ := (congr_fun h τ₁).symm
    -- But A f₁ τ₀ = 0 * 1 = 0 (digit 0 of τ₀ is 0)
    have h0 : A f₁ τ₀ = 0 := by
      show (if τ₀ ⟨0, _⟩ = (⟨0, b.pos 0⟩ : Fin (b 0)) then 0 else 1) * 1 = 0
      simp [τ₀]
    -- And A f₁ τ₁ = 1 * 1 = 1 (digit 0 of τ₁ is 1 ≠ 0)
    have h1 : A f₁ τ₁ = 1 := by
      show (if τ₁ ⟨0, _⟩ = (⟨0, b.pos 0⟩ : Fin (b 0)) then 0 else 1) * 1 = 1
      have : τ₁ ⟨0, by omega⟩ = (⟨1, hb1 0⟩ : Fin (b 0)) := by simp [τ₁]
      rw [show (τ₁ ⟨0, _⟩ : Fin (b 0)) = ⟨1, hb1 0⟩ from this, if_neg]
      · ring
      · simp
    linarith

/-!
## Theorem 9: Intersection Characterization
-/

/--
**Theorem 9**: L-local AND commuting with P_L.

For an additive operator A with A(0) = 0:
  `isLocal A L ∧ commutesWithProjection A L`
  ↔
  `A` is block-preserving (maps cylinder-zero functions to cylinder-zero)
  ∧ `A` commutes with `P_L`

This characterizes the intersection L_L ∩ C_L as block-diagonal operators
commuting with within-block averaging. The block-preserving condition is equivalent
to locality for additive operators, giving the concrete block decomposition.
-/
theorem local_and_commuting_iff_blockwise {b : RadixSeq} {V : Type*} {k : ℕ}
    [AddCommGroup V] [Module ℝ V]
    (A : (FiniteRadixSpace b k → V) → (FiniteRadixSpace b k → V))
    (L : ℕ) (hLk : L ≤ k + 1)
    (h_add : ∀ f g, A (f + g) = A f + A g)
    (h_zero : A 0 = 0) :
    isLocal b V k A L hLk ∧ commutesWithProjection A L hLk ↔
    (∀ f : FiniteRadixSpace b k → V, ∀ τ : FiniteRadixSpace b k,
      (∀ σ ∈ finiteCylinderSet b k L hLk (finitePrefix b L τ hLk), f σ = 0) →
      A f τ = 0) ∧
    commutesWithProjection A L hLk := by
  constructor
  · -- Forward: local → block-preserving (f=0 on cyl(τ) ⟹ Af(τ)=0)
    intro ⟨hloc, hcomm⟩
    exact ⟨fun f τ hf => by
      have := hloc τ f 0 (fun σ hσ => by simp [hf σ hσ])
      rwa [congr_fun h_zero τ] at this, hcomm⟩
  · -- Backward: block-preserving → local
    intro ⟨hblock, hcomm⟩
    refine ⟨fun τ f g hfg => ?_, hcomm⟩
    -- A(f-g)(τ) = 0 since f-g = 0 on cyl(τ), hence Af(τ) = Ag(τ)
    have h_neg : ∀ h : FiniteRadixSpace b k → V, A (-h) = -A h := fun h => by
      have h1 := h_add h (-h)
      simp only [add_neg_cancel, h_zero] at h1
      exact (neg_eq_of_add_eq_zero_right h1.symm).symm
    have h_sub : (A f + (-(A g))) τ = 0 := by
      have := hblock (f + (-g)) τ (fun σ hσ => by simp [hfg σ hσ])
      rwa [h_add, h_neg] at this
    exact add_neg_eq_zero.mp h_sub

end FdrsFormal.FunctionSpaces.Commutant
