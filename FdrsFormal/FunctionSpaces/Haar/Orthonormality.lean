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
import FdrsFormal.FunctionSpaces.Haar.Definition
import FdrsFormal.FunctionSpaces.Commutant

/-!
# Orthonormality of Haar Basis

This file proves that the Haar atoms form an orthonormal basis of the mixed-radix
function space H_k under the L² inner product.

## Main Results

* `haarComponent_inner` - Per-digit inner product: ∑_d φ(α,d) φ(β,d) = b·δ_{αβ}
* `haarBasis_orthonormal` - **Theorem 11**: ∑_σ h_α(σ) h_β(σ) = B_{k+1}·δ_{αβ}
* `haarBasis_complete` - Resolution of identity: ∑_α h_α(σ) h_α(τ) = B_{k+1}·δ_{στ}
* `haarAtom_card` - |HaarAtom b k| = ∏ᵢ bᵢ

## References

* fdrs.md, Lines 1346-1350: Theorem 11
-/

open FdrsFormal Core.Primitives Finset
open scoped BigOperators

variable {b : RadixSeq} {k : ℕ}

noncomputable instance : DecidableEq (Core.Finite.FiniteRadixSpace b k) := by
  unfold Core.Finite.FiniteRadixSpace; infer_instance

noncomputable instance : Fintype (Core.Finite.FiniteRadixSpace b k) := by
  unfold Core.Finite.FiniteRadixSpace; infer_instance

namespace FdrsFormal.Haar

/-! ### Per-component inner product -/

/-- Per-digit inner product: ∑_d φ(α,d) φ(β,d) = b·δ_{αβ}. -/
theorem haarComponent_inner (i : Fin (k + 1)) (αᵢ βᵢ : Fin (b i)) :
    ∑ d : Fin (b i), haarComponent i αᵢ d * haarComponent i βᵢ d =
    if αᵢ = βᵢ then (b i : ℝ) else 0 := by
  by_cases hα : αᵢ.val = 0 <;> by_cases hβ : βᵢ.val = 0
  · have hαeq : αᵢ = 0 := Fin.ext hα
    have hβeq : βᵢ = 0 := Fin.ext hβ
    subst hαeq; subst hβeq; simp [nsmul_eq_mul]
  · have hne : αᵢ ≠ βᵢ := by intro h; rw [h] at hα; exact hβ hα
    simp only [hne, ite_false, haarComponent, hα, hβ, ↓reduceDIte, one_mul]
    exact contrastVector_mean_zero (b.ge_two i) _
  · have hne : αᵢ ≠ βᵢ := by intro h; rw [← h] at hβ; exact hα hβ
    simp only [hne, ite_false, haarComponent, hα, hβ, ↓reduceDIte, mul_one]
    exact contrastVector_mean_zero (b.ge_two i) _
  · simp only [haarComponent, hα, hβ, ↓reduceDIte]
    rw [contrastVector_orthonormal]
    by_cases heq : αᵢ = βᵢ
    · subst heq; simp
    · have hne : (⟨αᵢ.val - 1, by omega⟩ : Fin (b i - 1)) ≠
          ⟨βᵢ.val - 1, by omega⟩ := by
        simp only [ne_eq, Fin.ext_iff]; omega
      simp [heq, hne]

/-! ### Helper: product of conditionals -/

private theorem prod_ite_eq_ite_prod {n : ℕ} {b : Fin n → ℕ}
    (α β : (i : Fin n) → Fin (b i)) :
    ∏ i : Fin n, (if α i = β i then (b i : ℝ) else 0) =
    if α = β then ∏ i, (b i : ℝ) else 0 := by
  by_cases h : α = β
  · subst h; simp
  · simp only [h, ite_false]
    obtain ⟨i, hi⟩ : ∃ i, α i ≠ β i := by
      by_contra hall; push_neg at hall; exact h (funext hall)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-! ### Sum-product exchange helper -/

/-- Sum-product exchange after unfolding FiniteRadixSpace. -/
private theorem sum_prod_eq_prod_sum_frs
    (g : (i : Fin (k + 1)) → Fin (b i) → ℝ) :
    ∑ σ : Core.Finite.FiniteRadixSpace b k, ∏ i, g i (σ i) =
    ∏ i, ∑ d, g i d := by
  unfold Core.Finite.FiniteRadixSpace
  exact (Fintype.prod_sum g).symm

/-- Sum-product exchange after unfolding HaarAtom. -/
private theorem sum_prod_eq_prod_sum_ha
    (g : (i : Fin (k + 1)) → Fin (b i) → ℝ) :
    ∑ α : HaarAtom b k, ∏ i, g i (α i) =
    ∏ i, ∑ d, g i d := by
  unfold HaarAtom
  exact (Fintype.prod_sum g).symm

/-! ### Orthonormality (Theorem 11) -/

/--
**Theorem 11** (orthonormality of Haar basis):
∑_σ h_α(σ) h_β(σ) = B_{k+1} · δ_{αβ}
-/
theorem haarBasis_orthonormal (α β : HaarAtom b k) :
    ∑ σ : Core.Finite.FiniteRadixSpace b k,
      haarFunction α σ * haarFunction β σ =
    if α = β then (∏ i : Fin (k + 1), (b i : ℝ)) else 0 := by
  let g : (i : Fin (k + 1)) → Fin (b i) → ℝ :=
    fun i d => haarComponent i (α i) d * haarComponent i (β i) d
  have step1 : ∀ σ : Core.Finite.FiniteRadixSpace b k,
      haarFunction α σ * haarFunction β σ = ∏ i, g i (σ i) :=
    fun _ => Finset.prod_mul_distrib.symm
  simp_rw [step1]
  rw [sum_prod_eq_prod_sum_frs g]
  simp_rw [show ∀ i, ∑ d, g i d = if α i = β i then (b i : ℝ) else 0 from
    fun i => haarComponent_inner i (α i) (β i)]
  exact prod_ite_eq_ite_prod α β

/-! ### Per-component completeness -/

/-- Per-digit completeness: ∑_α φ(α,d) φ(α,d') = b·δ_{d,d'}. -/
theorem haarComponent_complete (i : Fin (k + 1)) (d d' : Fin (b i)) :
    ∑ αᵢ : Fin (b i), haarComponent i αᵢ d * haarComponent i αᵢ d' =
    if d = d' then (b i : ℝ) else 0 := by
  have hbi := b.ge_two i
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (b i)))]
  simp only [haarComponent_constant, one_mul]
  have h_reindex : ∑ x ∈ Finset.univ.erase (0 : Fin (b i)),
      haarComponent i x d * haarComponent i x d' =
      ∑ a : Fin (b i - 1), contrastVector hbi a d * contrastVector hbi a d' := by
    let sd : Fin (b i) → Fin (b i - 1) := fun αᵢ => ⟨αᵢ.val - 1, by omega⟩
    let su : Fin (b i - 1) → Fin (b i) := fun a => ⟨a.val + 1, by omega⟩
    apply Finset.sum_nbij' sd su
    · intro _ _; exact Finset.mem_univ _
    · intro a _
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro h; have hv := Fin.ext_iff.mp h; dsimp [su] at hv; omega
    · intro αᵢ hαᵢ
      have hval : αᵢ.val ≠ 0 := fun h => (Finset.mem_erase.mp hαᵢ).1 (Fin.ext h)
      apply Fin.ext; dsimp [su, sd]; omega
    · intro _ _; rfl
    · intro αᵢ hαᵢ
      have hval : αᵢ.val ≠ 0 := fun h => (Finset.mem_erase.mp hαᵢ).1 (Fin.ext h)
      simp only [sd, haarComponent, hval, ↓reduceDIte]
  rw [h_reindex]
  linarith [contrastVector_complete hbi d d']

/-! ### Completeness (Resolution of identity, Theorem 11) -/

/--
**Theorem 11** (completeness / resolution of identity):
∑_α h_α(σ) h_α(τ) = B_{k+1} · δ_{στ}
-/
theorem haarBasis_complete (σ τ : Core.Finite.FiniteRadixSpace b k) :
    ∑ α : HaarAtom b k,
      haarFunction α σ * haarFunction α τ =
    if σ = τ then (∏ i : Fin (k + 1), (b i : ℝ)) else 0 := by
  let g : (i : Fin (k + 1)) → Fin (b i) → ℝ :=
    fun i αᵢ => haarComponent i αᵢ (σ i) * haarComponent i αᵢ (τ i)
  have step1 : ∀ α : HaarAtom b k,
      haarFunction α σ * haarFunction α τ = ∏ i, g i (α i) :=
    fun _ => Finset.prod_mul_distrib.symm
  simp_rw [step1]
  rw [sum_prod_eq_prod_sum_ha g]
  simp_rw [show ∀ i, ∑ d, g i d = if σ i = τ i then (b i : ℝ) else 0 from
    fun i => haarComponent_complete i (σ i) (τ i)]
  exact prod_ite_eq_ite_prod σ τ

/-! ### Cardinality -/

/-- |HaarAtom b k| = ∏ᵢ bᵢ. -/
theorem haarAtom_card :
    Fintype.card (HaarAtom b k) = ∏ i : Fin (k + 1), b i := by
  unfold HaarAtom; simp [Fintype.card_pi, Fintype.card_fin]

end FdrsFormal.Haar
