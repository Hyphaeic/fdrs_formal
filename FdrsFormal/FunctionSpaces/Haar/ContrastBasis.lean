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
import FdrsFormal.Core
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
# Haar Contrast Basis

This file defines the mean-zero orthonormal contrast basis for digit alphabets.

## Main Definitions

* `onesVec` - The all-ones vector in EuclideanSpace ℝ (Fin b)
* `contrastONB` - Orthonormal basis of the mean-zero subspace (1-vector orthogonal complement)
* `onbVec` - Coercion of ONB vectors to the ambient EuclideanSpace
* `contrastVector` - Scaled contrast vectors ψ^(b)_a satisfying (1/b)∑ ψ_a ψ_{a'} = δ_{aa'}

## Main Results

* `contrastVector_mean_zero` - Each contrast vector has zero mean
* `contrastVector_orthonormal` - The contrast vectors are orthonormal under (1/b)∑
* `contrastVector_complete` - Together with constant vector, they resolve the identity
* `constant_orthogonal_contrasts` - Constant vector is orthogonal to all contrasts

## References

* fdrs.md, Lines 1306-1314: Lemma 3 (existence of contrast basis)
-/

open scoped BigOperators
noncomputable section

variable {b : ℕ}

namespace FdrsFormal.Haar

/-! ### Inner product and ambient space utilities -/

lemma euclidean_inner_eq_sum (x y : EuclideanSpace ℝ (Fin b)) :
    @inner ℝ _ _ x y = ∑ i : Fin b, x i * y i := by
  rw [PiLp.inner_apply]; congr 1; ext i; simp [mul_comm]

/-! ### The all-ones vector and mean-zero subspace -/

/-- The all-ones vector (1, 1, ..., 1) in EuclideanSpace ℝ (Fin b). -/
def onesVec (b : ℕ) : EuclideanSpace ℝ (Fin b) :=
  (EuclideanSpace.equiv (Fin b) ℝ).symm (fun _ => 1)

@[simp] lemma onesVec_apply (i : Fin b) : onesVec b i = 1 := by
  simp [onesVec, EuclideanSpace.equiv]

lemma onesVec_ne_zero (hb : 1 ≤ b) : onesVec b ≠ 0 := by
  intro h
  have : onesVec b ⟨0, by omega⟩ = (0 : EuclideanSpace ℝ (Fin b)) ⟨0, by omega⟩ := by rw [h]
  simp [onesVec, EuclideanSpace.equiv, PiLp.zero_apply] at this

lemma onesVec_inner_self :
    @inner ℝ _ _ (onesVec b) (onesVec b) = (b : ℝ) := by
  rw [euclidean_inner_eq_sum]; simp [Finset.sum_const, nsmul_eq_mul]

/-- The dimension of the mean-zero subspace (orthogonal complement of span{onesVec}) is b - 1. -/
lemma finrank_meanZero (hb : 1 ≤ b) :
    Module.finrank ℝ
      ((ℝ ∙ onesVec b : Submodule ℝ (EuclideanSpace ℝ (Fin b)))ᗮ) = b - 1 := by
  have h1 : Module.finrank ℝ (ℝ ∙ onesVec b : Submodule ℝ (EuclideanSpace ℝ (Fin b))) = 1 :=
    @finrank_span_singleton ℝ (EuclideanSpace ℝ (Fin b)) _ _ _ _ (onesVec_ne_zero hb)
  have h2 := @Submodule.finrank_add_finrank_orthogonal ℝ
    (EuclideanSpace ℝ (Fin b)) _ _ _ _ (ℝ ∙ onesVec b)
  rw [h1, finrank_euclideanSpace_fin] at h2; omega

/-! ### Orthonormal basis of the mean-zero subspace -/

/-- An orthonormal basis of the mean-zero subspace (orthogonal complement of the all-ones vector).
    Constructed from the standard ONB via dimension-based reindexing. -/
def contrastONB (hb : 1 ≤ b) :
    OrthonormalBasis (Fin (b - 1)) ℝ
      ((ℝ ∙ onesVec b : Submodule ℝ (EuclideanSpace ℝ (Fin b)))ᗮ) :=
  (stdOrthonormalBasis ℝ _).reindex (finCongr (finrank_meanZero hb))

/-- The ONB vectors coerced to the ambient EuclideanSpace. -/
def onbVec (hb : 1 ≤ b) (a : Fin (b - 1)) : EuclideanSpace ℝ (Fin b) :=
  ↑(contrastONB hb a :
    (ℝ ∙ onesVec b : Submodule ℝ (EuclideanSpace ℝ (Fin b)))ᗮ)

lemma onbVec_mem (hb : 1 ≤ b) (a : Fin (b - 1)) :
    onbVec hb a ∈
      (ℝ ∙ onesVec b : Submodule ℝ (EuclideanSpace ℝ (Fin b)))ᗮ :=
  Subtype.coe_prop _

/-- Each ONB vector has zero coordinate sum (mean-zero property). -/
lemma onbVec_mean_zero (hb : 1 ≤ b) (a : Fin (b - 1)) :
    ∑ i : Fin b, onbVec hb a i = 0 := by
  have hmem := onbVec_mem hb a
  rw [Submodule.mem_orthogonal'] at hmem
  have h := hmem (onesVec b) (Submodule.mem_span_singleton_self _)
  rw [euclidean_inner_eq_sum] at h; simpa using h

/-- The ONB vectors are orthonormal under the standard inner product. -/
lemma onbVec_orthonormal (hb : 1 ≤ b) (a a' : Fin (b - 1)) :
    ∑ i : Fin b, onbVec hb a i * onbVec hb a' i =
    if a = a' then 1 else 0 := by
  rw [← euclidean_inner_eq_sum]; unfold onbVec; rw [← Submodule.coe_inner]
  exact (orthonormal_iff_ite.mp (contrastONB hb).orthonormal) a a'

/-! ### Full-space ONB construction (for Parseval / completeness) -/

/-- Normalized all-ones vector: (1/√b) · onesVec. Unit vector in the constant direction. -/
private def normalOnes (b : ℕ) : EuclideanSpace ℝ (Fin b) :=
  (1 / Real.sqrt b) • onesVec b

@[simp] private lemma normalOnes_apply (i : Fin b) :
    normalOnes b i = 1 / Real.sqrt b := by
  simp [normalOnes, onesVec_apply]

private lemma onesVec_inner_onbVec (hb : 1 ≤ b) (a : Fin (b - 1)) :
    @inner ℝ _ _ (onesVec b) (onbVec hb a) = 0 := by
  rw [euclidean_inner_eq_sum]; simpa using onbVec_mean_zero hb a

private lemma normalOnes_inner_onbVec (hb : 1 ≤ b) (a : Fin (b - 1)) :
    @inner ℝ _ _ (normalOnes b) (onbVec hb a) = 0 := by
  unfold normalOnes
  rw [inner_smul_left, onesVec_inner_onbVec hb, mul_zero]

private lemma normalOnes_inner_self (hb : 1 ≤ b) :
    @inner ℝ _ _ (normalOnes b) (normalOnes b) = (1 : ℝ) := by
  unfold normalOnes
  rw [inner_smul_left, inner_smul_right, onesVec_inner_self]
  simp only [RCLike.conj_to_real, one_div]
  have hsqrt : Real.sqrt (b : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  field_simp
  exact (Real.sq_sqrt (Nat.cast_nonneg b)).symm

/-- Full-space ONB function: maps `none` to the normalized ones vector,
    and `some a` to the a-th mean-zero ONB vector. -/
private def fullONBVec (hb : 1 ≤ b) : Option (Fin (b - 1)) → EuclideanSpace ℝ (Fin b)
  | none => normalOnes b
  | some a => onbVec hb a

private lemma fullONBVec_orthonormal (hb : 1 ≤ b) :
    Orthonormal ℝ (fullONBVec hb) := by
  refine orthonormal_iff_ite.mpr (fun i j => ?_)
  cases i with
  | none =>
    cases j with
    | none =>
      show @inner ℝ _ _ (normalOnes b) (normalOnes b) = 1
      exact normalOnes_inner_self hb
    | some a =>
      show @inner ℝ _ _ (normalOnes b) (onbVec hb a) = 0
      exact normalOnes_inner_onbVec hb a
  | some a =>
    cases j with
    | none =>
      show @inner ℝ _ _ (onbVec hb a) (normalOnes b) = 0
      rw [real_inner_comm]; exact normalOnes_inner_onbVec hb a
    | some a' =>
      simp only [fullONBVec, Option.some.injEq]
      rw [euclidean_inner_eq_sum]; exact onbVec_orthonormal hb a a'

private lemma option_fin_card (hb : 1 ≤ b) :
    Fintype.card (Option (Fin (b - 1))) = b := by
  simp [Fintype.card_option]; omega

/-- The full orthonormal basis of EuclideanSpace ℝ (Fin b), extending the mean-zero ONB
    with the normalized constant vector. -/
private def fullONB (hb : 1 ≤ b) :
    OrthonormalBasis (Option (Fin (b - 1))) ℝ (EuclideanSpace ℝ (Fin b)) := by
  apply OrthonormalBasis.mk (fullONBVec_orthonormal hb)
  have hli := (fullONBVec_orthonormal hb).linearIndependent
  have hcard : Fintype.card (Option (Fin (b - 1))) = Module.finrank ℝ (EuclideanSpace ℝ (Fin b)) := by
    rw [option_fin_card hb, finrank_euclideanSpace_fin]
  rw [← hli.span_eq_top_of_card_eq_finrank hcard]

private lemma fullONB_coe (hb : 1 ≤ b) :
    ⇑(fullONB hb) = fullONBVec hb := by
  unfold fullONB; exact OrthonormalBasis.coe_mk _ _

/-- **Resolution of identity** for the mean-zero ONB vectors.
    This is the key completeness result: the ONB vectors plus the constant direction
    resolve the identity on EuclideanSpace ℝ (Fin b). -/
theorem onbVec_complete (hb : 1 ≤ b) (d d' : Fin b) :
    ∑ a : Fin (b - 1), onbVec hb a d * onbVec hb a d' =
    (if d = d' then (1 : ℝ) else 0) - 1 / (b : ℝ) := by
  have hP := (fullONB hb).sum_inner_mul_inner
    (EuclideanSpace.single d 1) (EuclideanSpace.single d' 1)
  simp only [fullONB_coe] at hP
  rw [Fintype.sum_option] at hP
  simp only [fullONBVec] at hP
  simp only [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right,
    RCLike.conj_to_real, one_mul] at hP
  change normalOnes b d * normalOnes b d' +
    ∑ x, onbVec hb x d * onbVec hb x d' =
    EuclideanSpace.single d (1 : ℝ) d' at hP
  simp only [normalOnes_apply] at hP
  rw [show (1 : ℝ) / Real.sqrt b * (1 / Real.sqrt b) = 1 / (b : ℝ) from by
    rw [div_mul_div_comm, one_mul]; congr 1; exact Real.mul_self_sqrt (Nat.cast_nonneg b)] at hP
  rw [show EuclideanSpace.single d (1 : ℝ) d' = if d' = d then (1 : ℝ) else 0
    from EuclideanSpace.single_apply d 1 d'] at hP
  rw [show (if d' = d then (1 : ℝ) else 0) = if d = d' then 1 else 0
    from by by_cases h : d = d' <;> simp [h, eq_comm]] at hP
  linarith

/-! ### Contrast vectors (scaled for (1/b)∑ inner product) -/

/--
Contrast vector at index a for base b.
These are mean-zero vectors in ℝ^b that, together with the constant vector,
form an orthonormal basis under the (1/b)∑ inner product.

Satisfies: (1/b) ∑_i ψ_a(i) · ψ_{a'}(i) = δ_{aa'}

**fdrs.md Reference:** Lines 1306-1314, Definition of ψ^(b)_a
-/
def contrastVector (hb : 2 ≤ b) (a : Fin (b - 1)) : Fin b → ℝ :=
  fun i => Real.sqrt b * onbVec (by omega : 1 ≤ b) a i

/--
**Lemma 3** (mean zero property):
Each contrast vector has zero mean: ∑ ψ^(b)_a(i) = 0

**fdrs.md Reference:** Lines 1306-1314, property (1)
-/
theorem contrastVector_mean_zero (hb : 2 ≤ b) (a : Fin (b - 1)) :
    ∑ i : Fin b, contrastVector hb a i = 0 := by
  simp only [contrastVector, ← Finset.mul_sum, onbVec_mean_zero, mul_zero]

private lemma sqrt_mul_sqrt_cancel (x y : ℝ) :
    Real.sqrt (b : ℝ) * x * (Real.sqrt (b : ℝ) * y) = (b : ℝ) * (x * y) := by
  have : Real.sqrt (b : ℝ) * x * (Real.sqrt (b : ℝ) * y) =
    (Real.sqrt (b : ℝ) * Real.sqrt (b : ℝ)) * (x * y) := by ring
  rw [this, Real.mul_self_sqrt (Nat.cast_nonneg b)]

/--
**Lemma 3** (orthonormality):
The contrast vectors form an orthonormal set under (1/b)∑:
∑_i ψ_a(i) · ψ_{a'}(i) = b · δ_{aa'}

Equivalently: (1/b) ∑_i ψ_a(i) · ψ_{a'}(i) = δ_{aa'}

**fdrs.md Reference:** Lines 1306-1314, property (2)
-/
theorem contrastVector_orthonormal (hb : 2 ≤ b) (a a' : Fin (b - 1)) :
    ∑ i : Fin b, contrastVector hb a i * contrastVector hb a' i =
    if a = a' then (b : ℝ) else 0 := by
  simp only [contrastVector, sqrt_mul_sqrt_cancel]
  rw [← Finset.mul_sum, onbVec_orthonormal]; split <;> simp

/--
**Lemma 3** (completeness):
The contrast vectors, together with the constant vector 1, form a complete basis.
Resolution of identity: ∑_a ψ_a(d) · ψ_a(d') = b · δ_{dd'} - 1

**fdrs.md Reference:** Lines 1306-1314, property (3)
-/
theorem contrastVector_complete (hb : 2 ≤ b) (d d' : Fin b) :
    (if d = d' then (b : ℝ) else 0) =
    1 + ∑ a : Fin (b - 1), contrastVector hb a d * contrastVector hb a d' := by
  simp only [contrastVector, sqrt_mul_sqrt_cancel]
  rw [← Finset.mul_sum, onbVec_complete (by omega : 1 ≤ b)]
  have hb_pos : (0 : ℝ) < b := by positivity
  split <;> field_simp <;> linarith

/--
The constant vector (all ones) is orthogonal to all contrast vectors.

**Proof:** Immediate from `contrastVector_mean_zero`.
-/
theorem constant_orthogonal_contrasts (hb : 2 ≤ b) (a : Fin (b - 1)) :
    ∑ i : Fin b, contrastVector hb a i = 0 :=
  contrastVector_mean_zero hb a

end FdrsFormal.Haar

end
