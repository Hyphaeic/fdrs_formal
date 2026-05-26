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
import FdrsFormal.FunctionSpaces.Haar.SupportLevel
import FdrsFormal.FunctionSpaces.Commutant

/-!
# Block Projection Action on Haar Atoms

## Main Results

* `haarAtom_preserved_by_projection` - P_L h_α = h_α when ℓ(α) < L
* `haarAtom_annihilated_by_projection` - P_L h_α = 0 when ℓ(α) ≥ L (non-constant)

## References

* fdrs.md, Lines 1366-1391: Proposition 33 and Corollary 8
-/

open FdrsFormal Core.Primitives FunctionSpaces.Commutant
open scoped Classical

variable {b : RadixSeq} {k : ℕ}

namespace FdrsFormal.Haar

theorem haarAtom_preserved_by_projection (α : HaarAtom b k) (L : Fin (k + 1))
    (h : supportLevel α < L) :
    finiteBlockProjection b k L.val (by omega) (haarFunction α) = haarFunction α := by
  apply finiteBlockProjection_fixedPoint
  intro τ τ' hprefix
  simp only [haarFunction]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i.val < L.val
  · have heq := congr_fun hprefix ⟨i.val, hi⟩
    simp only [finitePrefix] at heq
    congr 1
  · have hge : L ≤ i := Fin.mk_le_of_le_val (Nat.le_of_not_lt hi)
    have hzero : α i = 0 := eq_zero_of_gt_supportLevel α i (lt_of_lt_of_le h hge)
    simp [hzero]

/-- Decompose a Fintype sum over α into sum over subtype S + sum over Sᶜ. -/
private lemma sum_subtype_add_sum_compl {α : Type*} [Fintype α] [DecidableEq α]
    (S : Set α) [Fintype ↥S] [Fintype ↥Sᶜ] (f : α → ℝ) :
    (∑ x : ↥S, f x.val) + (∑ x : ↥Sᶜ, f x.val) = ∑ x, f x := by
  set g : ↥S ⊕ ↥Sᶜ → ℝ := Sum.elim (f ·.val) (f ·.val)
  calc (∑ x : ↥S, f x.val) + (∑ x : ↥Sᶜ, f x.val)
      = ∑ x, g x := (Fintype.sum_sum_type g).symm
    _ = ∑ x, f x := Fintype.sum_equiv (Equiv.Set.sumCompl S) g f
          (fun x => by rcases x with ⟨a, _⟩ | ⟨a, _⟩ <;> rfl)

theorem haarAtom_annihilated_by_projection (α : HaarAtom b k) (L : Fin (k + 1))
    (hL : L ≤ supportLevel α) (hnc : ¬ isConstant α) :
    finiteBlockProjection b k L.val (by omega) (haarFunction α) = 0 := by
  have hLk : L.val ≤ k + 1 := by omega
  ext τ
  simp only [Pi.zero_apply, finiteBlockProjection]
  suffices h_cyl_zero : ∑ σ : finiteCylinderSet b k L.val hLk
      (finitePrefix b L.val τ hLk), haarFunction α σ.val = 0 by
    rw [h_cyl_zero, smul_zero]
  set s := finitePrefix b L.val τ hLk
  set cyl := finiteCylinderSet b k L.val hLk s
  -- Indicator-extended function G: matches h_α on cylinder, zero off cylinder
  set G : (i : Fin (k + 1)) → Fin (b i) → ℝ := fun i d =>
    if i.val < L.val then
      if d = τ i then haarComponent i (α i) d else 0
    else haarComponent i (α i) d
  -- Step 1: Full-space sum of ∏ G is 0 (prod_sum + zero factor)
  have h_full_zero : ∑ σ : Core.Finite.FiniteRadixSpace b k, ∏ i, G i (σ i) = 0 := by
    have : ∑ σ : Core.Finite.FiniteRadixSpace b k, ∏ i, G i (σ i) =
        ∏ i, ∑ d, G i d := by
      unfold Core.Finite.FiniteRadixSpace; exact (Fintype.prod_sum G).symm
    rw [this]
    apply Finset.prod_eq_zero (Finset.mem_univ (supportLevel α))
    show ∑ d, G (supportLevel α) d = 0
    simp only [G, if_neg (show ¬ (supportLevel α).val < L.val from not_lt.mpr hL)]
    exact haarComponent_sum_zero _ _ (supportLevel_mem_support α hnc)
  -- Step 2: On-cylinder, ∏ G = h_α
  have h_on : ∀ (σ : ↥cyl), ∏ i, G i (σ.val i) = haarFunction α σ.val := by
    intro ⟨σ, hσ⟩
    simp only [haarFunction]
    apply Finset.prod_congr rfl; intro i _
    show G i (σ i) = haarComponent i (α i) (σ i)
    by_cases hi : i.val < L.val
    · have hmem := hσ ⟨i.val, hi⟩
      simp only [s, finitePrefix] at hmem
      simp only [G, hi, ite_true, hmem, ite_true]
    · simp only [G, hi, ite_false]
  -- Step 3: Off-cylinder, ∏ G = 0
  have h_off : ∀ (σ : ↥(cyl)ᶜ), ∏ i, G i (σ.val i) = 0 := by
    intro ⟨σ, hσ⟩
    simp only [Set.mem_compl_iff, cyl, finiteCylinderSet, Set.mem_setOf_eq, not_forall] at hσ
    obtain ⟨⟨j, hj⟩, hjne⟩ := hσ
    apply Finset.prod_eq_zero (Finset.mem_univ ⟨j, by omega⟩)
    show G ⟨j, by omega⟩ (σ ⟨j, by omega⟩) = 0
    simp only [G, show j < L.val from hj, ite_true]
    rw [if_neg]; simp only [s, finitePrefix] at hjne; exact hjne
  -- Step 4: Combine using decomposition
  have h_decomp := sum_subtype_add_sum_compl cyl
    (fun σ : Core.Finite.FiniteRadixSpace b k => ∏ i, G i (σ i))
  have h_cyl_G : ∑ σ : ↥cyl, ∏ i, G i (σ.val i) =
      ∑ σ : ↥cyl, haarFunction α σ.val := by
    congr 1; ext σ; exact h_on σ
  have h_compl_zero : ∑ σ : ↥(cyl)ᶜ, ∏ i, G i (σ.val i) = 0 :=
    Finset.sum_eq_zero (fun x _ => h_off x)
  linarith

/-- P_L h_α = h_α when ℓ(α) < L. -/
theorem blockProjection_haarAtom (α : HaarAtom b k) (L : ℕ) (hL : L < k + 1) :
    (supportLevel α).val < L →
    finiteBlockProjection b k L (by omega) (haarFunction α) = haarFunction α := by
  intro h; exact haarAtom_preserved_by_projection α ⟨L, hL⟩ h

/-- Subtraction linearity for finiteBlockProjection. -/
private theorem finiteBlockProjection_sub' {V : Type*} [AddCommGroup V] [Module ℝ V]
    (k L : ℕ) (hLk : L ≤ k + 1)
    (f g : Core.Finite.FiniteRadixSpace b k → V) :
    finiteBlockProjection b k L hLk (f - g) =
    finiteBlockProjection b k L hLk f - finiteBlockProjection b k L hLk g := by
  have h : f - g = f + (-1 : ℝ) • g := by ext x; simp [sub_eq_add_neg]
  rw [h, finiteBlockProjection_add, finiteBlockProjection_smul]
  ext x; simp [sub_eq_add_neg]

/--
Detail operator at level L fixes Haar atoms at that level.

Non-constant Haar atoms with support level L are eigenvectors of Δ_L
with eigenvalue 1: Δ_L(h_α) = h_α.

**Proof**: Δ_L = P_{L+1} - P_L. By `haarAtom_preserved_by_projection`,
P_{L+1}(h_α) = h_α since ℓ(α) = L < L+1. By `haarAtom_annihilated_by_projection`,
P_L(h_α) = 0 since L ≤ ℓ(α) and α is non-constant. So Δ_L(h_α) = h_α - 0 = h_α.
-/
theorem detailSubspace_span (L : Fin k) :
    ∀ (α : HaarAtom b k), supportLevel α = ⟨L.val, by omega⟩ → ¬ isConstant α →
      finiteDetailOperator b k L.val (by omega) (haarFunction α) = haarFunction α := by
  intro α hsupp hnc
  simp only [finiteDetailOperator]
  have h_pres := haarAtom_preserved_by_projection α ⟨L.val + 1, by omega⟩
    (by rw [hsupp]; exact Fin.mk_lt_mk.mpr (by omega))
  have h_ann := haarAtom_annihilated_by_projection α ⟨L.val, by omega⟩
    (by rw [hsupp]) hnc
  rw [h_pres, h_ann, sub_zero]

/--
P_L annihilates the detail at level L: P_L ∘ Δ_L = 0.

The detail subspace (image of Δ_L) lies in the kernel of P_L.

**Proof**: P_L(Δ_L f) = P_L(P_{L+1} f - P_L f) = P_L(P_{L+1} f) - P_L(P_L f)
= P_L f - P_L f = 0, using the tower property and idempotency.
-/
theorem detailSubspace_dimension (L : Fin k) :
    ∀ {V : Type*} [AddCommGroup V] [Module ℝ V]
      (f : Core.Finite.FiniteRadixSpace b k → V),
      finiteBlockProjection b k L.val (by omega)
        (finiteDetailOperator b k L.val (by omega) f) = 0 := by
  intro V _ _ f
  simp only [finiteDetailOperator]
  rw [finiteBlockProjection_sub',
      finiteBlockProjection_tower k L.val (L.val + 1) (by omega) (by omega) (by omega),
      finiteBlockProjection_idempotent, sub_self]

end FdrsFormal.Haar
