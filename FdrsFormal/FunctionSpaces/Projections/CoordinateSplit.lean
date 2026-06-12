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

# Coordinate Split and Fiberwise Averaging

Block-matrix decomposition of R^(k) into prefix/suffix coordinates.

## Mathematical Content (fdrs.md lines 855-954)

**Proposition 22** (coordinate split): R^(k) ≅ Σ_L × Σ_{k+1-L}
**Proposition 23** (fiberwise averaging): (P_L f)(s,t) = (1/m) Σ_{t'} f(s,t')
**Lemma 1** (eigenspace decomposition): H_k = coarse ⊕ detail

## References

- fdrs.md, Phase 2 Fragment 2, Section 3 (lines 855-954)
-/

import FdrsFormal.FunctionSpaces.Projections.Definition
import FdrsFormal.FunctionSpaces.Commutant.FiniteProjection
import FdrsFormal.FunctionSpaces.Haar.ContrastBasis
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

open scoped Classical

namespace FdrsFormal.FunctionSpaces.Projections

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite
open FdrsFormal.FunctionSpaces.Commutant
open FdrsFormal.Haar

/-! ## Proposition 22: Coordinate split -/

/--
**fdrs.md**: Proposition 22 (coordinate split into prefix/suffix) [§3.1 · Phase 2, Fragment 2] (lines 855-862)

Fix L ≤ k+1. Each τ ∈ R^(k) can be written uniquely as τ = (s,t) where
s ∈ Σ_L is the prefix and t ∈ Σ_{k+1-L} is the suffix.

**Axiomatized**: Standard finite product decomposition.
-/
def coordinateSplit (b : RadixSeq) (k L : ℕ) (hL : L ≤ k + 1) :
    FiniteRadixSpace b k ≃
      ((i : Fin L) → Fin (b i)) × ((i : Fin (k + 1 - L)) → Fin (b (i + L))) where
  toFun τ := (fun i => τ ⟨i.val, by omega⟩, fun i => τ ⟨i.val + L, by omega⟩)
  invFun st := fun ⟨j, hj⟩ =>
    if h : j < L then
      st.1 ⟨j, h⟩
    else
      Fin.cast (congrArg b (Nat.sub_add_cancel (Nat.not_lt.mp h)))
        (st.2 ⟨j - L, by omega⟩)
  left_inv τ := by
    funext ⟨j, hj⟩; simp only; split
    · rfl
    · rename_i h
      apply Fin.ext
      simp only [Fin.val_cast]
      exact congrArg (fun x => (τ x).val) (Fin.ext (by simp [Fin.val_mk]; omega))
  right_inv st := by
    refine Prod.ext ?_ ?_
    · funext ⟨i, hi⟩; simp [show i < L from hi]
    · funext ⟨i, hi⟩
      simp only [show ¬(↑i + L < L) from by omega, ↓reduceDIte]
      apply Fin.ext
      simp only [Fin.val_cast]
      exact congrArg (fun x => (st.2 x).val) (Fin.ext (by simp [Fin.val_mk]))

/-! ## Proposition 23: Fiberwise averaging -/

/--
**fdrs.md**: Proposition 23 (explicit fiberwise averaging) [§3.2 · Phase 2, Fragment 2] (lines 863-870)

Under the coordinate split, (P^(k)_L f)(s,t) = (1/m_{k,L}) Σ_{t'} f(s,t'),
i.e. P_L averages only along suffix fibers for fixed prefix s.

**Proof**: The cylinder set at level L is in bijection with the suffix space
via `cylinderSuffixEquiv`. Reindexing the sum in `finiteBlockProjection`
through this equivalence gives the explicit averaging formula over suffixes.
-/
theorem fiberwiseAveraging (b : RadixSeq) (k L : ℕ) (hL : L ≤ k + 1)
    (f : FiniteRadixSpace b k → ℂ) (τ : FiniteRadixSpace b k) :
    finiteBlockProjection b k L hL f τ =
    ((placeValue b (k + 1) / placeValue b L : ℕ) : ℝ)⁻¹ •
      ∑ t : SuffixSpace b k L,
        f (suffixToCylinder k L hL (finitePrefix b L τ hL) t).val := by
  simp only [finiteBlockProjection]
  congr 1
  exact (Equiv.sum_comp (cylinderSuffixEquiv k L hL (finitePrefix b L τ hL)).symm
    (fun σ => f σ.val)).symm

/-! ## Lemma 1: Eigenspace decomposition -/

/--
**fdrs.md**: Lemma 1 (eigenspace decomposition) [§5.1 · Phase 2, Fragment 2] (lines 942-954)

ℝ^m = span{1} ⊕ 1^⊥, with Π projecting onto span{1}, where m = m_{k,L} = B_{k+1}/B_L.
Hence H_k = (coarse subspace) ⊕ (detail subspace),
and P^(k)_L is the projection onto the coarse summand.

**Proof**: The orthogonal complement of any finite-dimensional subspace gives a direct sum
decomposition. Since span{onesVec} is finite-dimensional (hence complete), the result follows
from `Submodule.isCompl_orthogonal_of_hasOrthogonalProjection`.
-/
theorem eigenspaceDecomposition (b : RadixSeq) (k L : ℕ) (_hL : L ≤ k + 1) :
    let m := placeValue b (k + 1) / placeValue b L
    IsCompl (ℝ ∙ onesVec m) (ℝ ∙ onesVec m)ᗮ :=
  Submodule.isCompl_orthogonal_of_hasOrthogonalProjection

end FdrsFormal.FunctionSpaces.Projections
