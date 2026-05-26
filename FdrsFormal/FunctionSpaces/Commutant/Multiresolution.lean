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

# Multiresolution Subspaces

Defines coarse and detail subspaces in the multiresolution decomposition.

## Mathematical Content (fdrs.md lines 1054-1108)

**Definition 30**: C_L := range(P_L^(k))
**Definition 31**: D_L := range(Δ_L^(k))
**Proposition 27**: Δ_L is orthogonal projection onto D_L
**Corollary 6**: dim D_L = B_L(b_L - 1)

## References

- fdrs.md, Phase 2 Fragment 3 (lines 1054-1108)
- THEOREM_MAPPING.md
-/

import FdrsFormal.FunctionSpaces.Commutant.FiniteProjection
import FdrsFormal.FunctionSpaces.Commutant.Contraction

namespace FdrsFormal.FunctionSpaces.Commutant

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite
open FdrsFormal.FunctionSpaces.Basic

/-!
## Coarse and Detail Subspaces

Definitions of the multiresolution subspaces.
All structural theorems axiomatized - require subspace/dimension theory.
-/

variable (b : RadixSeq) (V : Type*) (k : ℕ)
variable [AddCommGroup V] [Module ℝ V]

/--
**Definition 30**: Coarse subspace C_L = range(P_L^(k)).

Functions that are block-constant at level L.
-/
def coarseSubspace (L : ℕ) (hLk : L ≤ k + 1) : Set (FiniteRadixSpace b k → V) :=
  {f | ∃ g, f = finiteBlockProjection b k L hLk g}

/--
**Definition 31**: Detail subspace D_L = range(Δ_L^(k)).

The orthogonal increment from level L to level L+1.
-/
def detailSubspace (L : ℕ) (hLk : L < k + 1) : Set (FiniteRadixSpace b k → V) :=
  {f | ∃ g, f = finiteDetailOperator b k L hLk g}

/-!
## Structural Properties
-/

/--
Coarse subspaces are nested: C_L ⊆ C_M for L ≤ M.

**Proof**: If f = P_L g, then f is L-block-constant, hence M-block-constant (since L ≤ M),
so P_M f = f by fixedPoint, giving f ∈ range(P_M).
-/
theorem coarseSubspace_mono {b : RadixSeq} {V : Type*} {k : ℕ}
    [AddCommGroup V] [Module ℝ V]
    (L M : ℕ) (hLk : L ≤ k + 1) (hMk : M ≤ k + 1) (hLM : L ≤ M) :
    coarseSubspace b V k L hLk ⊆ coarseSubspace b V k M hMk := by
  intro f ⟨g, hfg⟩
  -- f = P_L g, need ∃ h, f = P_M h. Take h = f.
  use f
  rw [hfg]
  -- Need: P_L g = P_M(P_L g), i.e., P_L g is M-block-constant so P_M fixes it
  symm
  apply finiteBlockProjection_fixedPoint
  -- P_L g is L-block-constant, hence M-block-constant (L ≤ M)
  intro τ τ' h_prefix_M
  apply finiteBlockProjection_isBlockConstant
  funext i
  exact congr_fun h_prefix_M ⟨i.val, Nat.lt_of_lt_of_le i.isLt hLM⟩

/--
**Proposition 27**: Δ_L is self-adjoint (in L²).

⟨Δ_L f, g⟩ = ⟨f, Δ_L g⟩.

**Proof**: Δ_L = P_{L+1} - P_L. Both P_{L+1} and P_L are self-adjoint
(Proposition 25). Self-adjointness distributes over subtraction.
-/
theorem finiteDetailOperator_is_orthogonalProjection {b : RadixSeq} {k : ℕ}
    (L : ℕ) (hLk : L < k + 1)
    (f g : FiniteRadixSpace b k → ℝ) :
    ∑ τ : FiniteRadixSpace b k, (finiteDetailOperator b k L hLk f τ) * (g τ) =
    ∑ τ : FiniteRadixSpace b k, (f τ) * (finiteDetailOperator b k L hLk g τ) := by
  simp only [finiteDetailOperator, Pi.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib]
  have h1 := finiteBlockProjection_isOrthogonalProjection k (L + 1) (by omega) f g
  have h2 := finiteBlockProjection_isOrthogonalProjection k L (by omega) f g
  linarith

/--
Detail subspaces are orthogonal to their corresponding coarse subspaces.

If f ∈ D_L and g ∈ C_L, then ⟨f, g⟩ = 0.

**Proof**: f = Δ_L h = (P_{L+1} - P_L) h and g = P_L g'. By self-adjointness:
⟨f, g⟩ = ⟨P_{L+1} h, P_L g'⟩ - ⟨P_L h, P_L g'⟩
       = ⟨h, P_{L+1}(P_L g')⟩ - ⟨h, P_L(P_L g')⟩
       = ⟨h, P_L g'⟩ - ⟨h, P_L g'⟩ = 0.
Uses tower property P_{L+1}(P_L g') = P_L g' and idempotence P_L² = P_L.
-/
theorem detailSubspace_orthogonal_to_coarse {b : RadixSeq} {k : ℕ}
    (L : ℕ) (hLk : L < k + 1)
    (f : FiniteRadixSpace b k → ℝ) (hf : f ∈ detailSubspace b ℝ k L hLk)
    (g : FiniteRadixSpace b k → ℝ) (hg : g ∈ coarseSubspace b ℝ k L (by omega : L ≤ k + 1)) :
    ∑ τ : FiniteRadixSpace b k, f τ * g τ = 0 := by
  obtain ⟨h1, rfl⟩ := hf
  obtain ⟨h2, rfl⟩ := hg
  -- Unfold Δ_L = P_{L+1} - P_L, distribute
  simp only [finiteDetailOperator, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  -- Self-adjointness of P_{L+1} and P_L
  have hadj1 := finiteBlockProjection_isOrthogonalProjection k (L + 1) (by omega)
    h1 (finiteBlockProjection b k L (by omega) h2)
  have hadj2 := finiteBlockProjection_isOrthogonalProjection k L (by omega)
    h1 (finiteBlockProjection b k L (by omega) h2)
  -- Tower: P_{L+1}(P_L h2) = P_L h2 (P_L h2 is L-bc, hence (L+1)-bc)
  have htower : finiteBlockProjection b k (L + 1) (by omega)
      (finiteBlockProjection b k L (by omega) h2) =
      finiteBlockProjection b k L (by omega) h2 := by
    apply finiteBlockProjection_fixedPoint
    intro τ τ' h_prefix
    apply finiteBlockProjection_isBlockConstant
    funext i
    exact congr_fun h_prefix ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_succ L)⟩
  -- Idempotence: P_L(P_L h2) = P_L h2
  have hidemp : finiteBlockProjection b k L (by omega)
      (finiteBlockProjection b k L (by omega) h2) =
      finiteBlockProjection b k L (by omega) h2 :=
    finiteBlockProjection_idempotent k L (by omega) h2
  rw [hadj1, htower, hadj2, hidemp, sub_self]

end FdrsFormal.FunctionSpaces.Commutant
