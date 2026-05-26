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

# Commutant Structure (Block-Diagonal Operators)

This file characterizes operators commuting with block projections.

## Mathematical Content (fdrs.md lines 955-989)

**Theorem 6 (Commutation ⇔ invariance of coarse/detail subspaces)**:
A linear operator A satisfies [A, P_L^(k)] = 0 iff both subspaces are A-invariant.

**Corollary 5 (block form)**:
In a basis adapted to decomposition range(P) ⊕ ker(P), commuting operators
have block-diagonal form.

## References

- fdrs.md, Phase 2 Fragment 2 (lines 955-989)
- THEOREM_MAPPING.md, Theorem 6
-/

import FdrsFormal.FunctionSpaces.Commutant.FiniteProjection

namespace FdrsFormal.FunctionSpaces.Commutant

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite
open FdrsFormal.FunctionSpaces.Basic

/-!
## Commutation Predicate
-/

section Commutation

variable {b : RadixSeq} {V : Type*} {k : ℕ}
variable [AddCommGroup V] [Module ℝ V]

/--
An operator A commutes with the finite block projection P_L^(k).
-/
def commutesWithProjection
    (A : (FiniteRadixSpace b k → V) → (FiniteRadixSpace b k → V))
    (L : ℕ) (hLk : L ≤ k + 1) : Prop :=
  ∀ f, A (finiteBlockProjection b k L hLk f) = finiteBlockProjection b k L hLk (A f)

end Commutation

/-!
## Range and Kernel
-/

section RangeKernel

variable {b : RadixSeq} {V : Type*} {k : ℕ}
variable [AddCommGroup V] [Module ℝ V]

/--
The range of P_L^(k): block-constant functions at level L.
-/
def projectionRange (L : ℕ) (hLk : L ≤ k + 1) : Set (FiniteRadixSpace b k → V) :=
  {f | ∀ τ τ', finitePrefix b L τ hLk = finitePrefix b L τ' hLk → f τ = f τ'}

/--
The kernel of P_L^(k): functions with zero block-average.
-/
def projectionKernel (L : ℕ) (hLk : L ≤ k + 1) : Set (FiniteRadixSpace b k → V) :=
  {f | finiteBlockProjection b k L hLk f = 0}

end RangeKernel

/-!
## Corollary 5: Block-Diagonal Structure
-/

section BlockDiagonal

variable {b : RadixSeq} {V : Type*} {k : ℕ}
variable [AddCommGroup V] [Module ℝ V]

/--
**Corollary 5**: Commuting operators have block-diagonal structure.

In adapted basis, A ~ diag(A_coarse, A_detail) with no cross-subspace mixing.

**Proof**: Forward direction of Theorem 6.
- Range: if f is block-constant, P f = f, so A f = A(P f) = P(A f), hence A f is block-constant.
- Kernel: if P f = 0, then P(A f) = A(P f) = A 0 = 0, hence A f ∈ ker(P).
-/
theorem commutant_has_blockDiagonal_structure (L : ℕ) (hLk : L ≤ k + 1)
    (A : (FiniteRadixSpace b k → V) → (FiniteRadixSpace b k → V))
    (h_linear : ∀ f g, A (f + g) = A f + A g)
    (hcomm : commutesWithProjection A L hLk) :
    (∀ f ∈ projectionRange (b := b) L hLk, A f ∈ projectionRange (b := b) L hLk) ∧
    (∀ f ∈ projectionKernel (b := b) L hLk, A f ∈ projectionKernel (b := b) L hLk) := by
  -- Derive A 0 = 0 from additivity: A(0+0) = A0 + A0, so A0 = A0 + A0 ⟹ A0 = 0
  have hA0 : A 0 = 0 := by
    have h := h_linear 0 0
    rw [add_zero] at h
    exact (add_left_cancel ((add_zero (A 0)).trans h)).symm
  constructor
  · -- Range preservation: if f is block-constant, then A f is block-constant
    intro f hf τ τ' hpfx
    have hPf : finiteBlockProjection b k L hLk f = f :=
      finiteBlockProjection_fixedPoint k L hLk f hf
    have h_eq := hcomm f
    rw [hPf] at h_eq
    -- h_eq : A f = P(A f), use pointwise
    rw [congr_fun h_eq τ, congr_fun h_eq τ']
    exact finiteBlockProjection_isBlockConstant k L hLk (A f) τ τ' hpfx
  · -- Kernel preservation: if P f = 0, then P(A f) = 0
    intro f hf
    simp only [projectionKernel, Set.mem_setOf_eq] at hf ⊢
    have h_eq := hcomm f
    rw [hf, hA0] at h_eq
    exact h_eq.symm

end BlockDiagonal

/-!
## Theorem 6: Commutation ⇔ Invariance
-/

section CommutationTheorem

variable {b : RadixSeq} {V : Type*} {k : ℕ}
variable [AddCommGroup V] [Module ℝ V]

/--
**Theorem 6 (biconditional)**: Commutation ⇔ range/kernel invariance.

**fdrs.md proof**:
(⇒) If A P_L = P_L A:
  - If x ∈ range(P), then Px = x, so PAx = APx = Ax, hence Ax ∈ range(P)
  - If y ∈ ker(P), then Py = 0, so PAy = APy = 0, hence Ay ∈ ker(P)

(⇐) If A preserves range and kernel:
  - Write v = Pv + (I-P)v with Pv ∈ range(P), (I-P)v ∈ ker(P)
  - Then PA v = P(A Pv + A(I-P)v) = A Pv + 0 = A Pv, so PA = AP
-/
theorem commutation_iff_invariance (L : ℕ) (hLk : L ≤ k + 1)
    (A : (FiniteRadixSpace b k → V) → (FiniteRadixSpace b k → V))
    (h_linear_add : ∀ f g, A (f + g) = A f + A g)
    (_h_linear_zero : A 0 = 0) :
    commutesWithProjection A L hLk ↔
    (∀ f ∈ projectionRange L hLk, A f ∈ projectionRange (b := b) L hLk) ∧
    (∀ f ∈ projectionKernel L hLk, A f ∈ projectionKernel (b := b) L hLk) := by
  constructor
  · -- Forward: commutation → invariance (this is Corollary 5)
    exact commutant_has_blockDiagonal_structure L hLk A h_linear_add
  · -- Backward: invariance → commutation
    intro ⟨h_range, h_kernel⟩ f
    set Pf := finiteBlockProjection b k L hLk f
    -- f - Pf is in the kernel: P(f - Pf) = Pf - P²f = Pf - Pf = 0
    have h_fPf_ker : f - Pf ∈ projectionKernel (b := b) L hLk := by
      simp only [projectionKernel, Set.mem_setOf_eq]
      have h_sub : f - Pf = f + (-1 : ℝ) • Pf := by
        simp [sub_eq_add_neg]
      rw [h_sub, finiteBlockProjection_add, finiteBlockProjection_smul,
          finiteBlockProjection_idempotent]
      simp [add_neg_cancel]
    -- Pf is in the range
    have h_Pf_range : Pf ∈ projectionRange (b := b) L hLk :=
      finiteBlockProjection_isBlockConstant k L hLk f
    -- A(Pf) ∈ range ⟹ P(A(Pf)) = A(Pf); A(f-Pf) ∈ kernel ⟹ P(A(f-Pf)) = 0
    have h_P_APf : finiteBlockProjection b k L hLk (A Pf) = A Pf :=
      finiteBlockProjection_fixedPoint k L hLk (A Pf) (h_range Pf h_Pf_range)
    have h_AfPf_ker : finiteBlockProjection b k L hLk (A (f - Pf)) = 0 :=
      h_kernel (f - Pf) h_fPf_ker
    -- P(A f) = P(A(Pf + (f-Pf))) = P(A Pf) + P(A(f-Pf)) = A Pf + 0 = A Pf
    conv_rhs => rw [show f = Pf + (f - Pf) from by abel]
    rw [h_linear_add, finiteBlockProjection_add, h_P_APf, h_AfPf_ker, add_zero]

end CommutationTheorem

end FdrsFormal.FunctionSpaces.Commutant
