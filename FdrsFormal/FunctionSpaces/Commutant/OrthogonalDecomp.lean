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

# Orthogonal Decomposition

Multiresolution orthogonal direct sum decomposition.

## Mathematical Content (fdrs.md lines 1086-1108)

**Theorem 7 (multiresolution decomposition)**:
There is an orthogonal direct sum decomposition
  H_k = C_0 ⊕ D_0 ⊕ D_1 ⊕ ... ⊕ D_k

and every f ∈ H_k admits the unique expansion
  f = P_0^(k) f + ∑_{L=0}^k Δ_L^(k) f

**Proof**: Telescoping gives P_{k+1}^(k) f = f = P_0 f + ∑ (P_{L+1} - P_L) f.
Orthogonality follows from Proposition 27.

## References

- fdrs.md, Phase 2 Fragment 3 (lines 1086-1108)
- THEOREM_MAPPING.md, Theorem 7
-/

import FdrsFormal.FunctionSpaces.Commutant.Multiresolution

namespace FdrsFormal.FunctionSpaces.Commutant

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite
open FdrsFormal.FunctionSpaces.Basic

/-!
## Theorem 7: Multiresolution Decomposition
-/

variable (b : RadixSeq) (k : ℕ)

/--
P_{k+1} is the identity on FiniteRadixSpace b k, since at level k+1
each cylinder contains exactly one point (the full (k+1)-tuple determines τ).
-/
theorem finiteBlockProjection_fullLevel {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : FiniteRadixSpace b k → V) :
    finiteBlockProjection b k (k + 1) (le_refl _) f = f := by
  apply finiteBlockProjection_fixedPoint
  intro τ τ' h_prefix
  -- If the (k+1)-prefixes agree, all coordinates agree, so τ = τ'
  have : τ = τ' := funext (fun i => congr_fun h_prefix ⟨i.val, i.isLt⟩)
  rw [this]

/--
**Theorem 7**: Multiresolution telescoping decomposition.

Every f ∈ H_k decomposes as:
  f = P_1 f + Δ_1 f + Δ_2 f + ... + Δ_k f

where P_1 is the global-constant projection and Δ_L = P_{L+1} - P_L.

**Proof**: From P_{k+1} = id (fullLevel) and the telescoping identity
P_{k+1} = P_1 + ∑_{L=1}^k Δ_L (finiteBlockProjection_telescoping).
-/
theorem multiresolution_decomposition {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : FiniteRadixSpace b k → V) :
    f = finiteBlockProjection b k 1 (by omega) f +
      ∑ L : Fin k, finiteDetailOperator b k (L.val + 1) (by omega) f :=
  calc f = finiteBlockProjection b k (k + 1) (le_refl _) f :=
        (finiteBlockProjection_fullLevel b k f).symm
    _ = finiteBlockProjection b k 1 (by omega) f +
        ∑ L : Fin k, finiteDetailOperator b k (L.val + 1) (by omega) f :=
        finiteBlockProjection_telescoping k (k + 1) (by omega) (le_refl _) f

/-!
## Linearity Helpers for Uniqueness
-/

/-- P_L sends the zero function to zero. -/
theorem finiteBlockProjection_zero {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : ℕ) (hLk : L ≤ k + 1) :
    finiteBlockProjection b k L hLk (0 : FiniteRadixSpace b k → V) = 0 := by
  have : (0 : FiniteRadixSpace b k → V) = fun _ => (0 : V) := rfl
  rw [this, finiteBlockProjection_const]

/-- P_L distributes over subtraction: P_L(f - g) = P_L f - P_L g. -/
theorem finiteBlockProjection_sub {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : ℕ) (hLk : L ≤ k + 1) (f g : FiniteRadixSpace b k → V) :
    finiteBlockProjection b k L hLk (f - g) =
    finiteBlockProjection b k L hLk f - finiteBlockProjection b k L hLk g := by
  have : f - g = f + ((-1 : ℝ) • g) := by rw [neg_one_smul, sub_eq_add_neg]
  rw [this, finiteBlockProjection_add, finiteBlockProjection_smul, neg_one_smul, ← sub_eq_add_neg]

/-- P_L distributes over finite sums. -/
theorem finiteBlockProjection_finset_sum {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : ℕ) (hLk : L ≤ k + 1) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → (FiniteRadixSpace b k → V)) :
    finiteBlockProjection b k L hLk (∑ i ∈ s, f i) =
    ∑ i ∈ s, finiteBlockProjection b k L hLk (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [finiteBlockProjection_zero b k L hLk]
  | insert a s has ih =>
    rw [Finset.sum_insert has, finiteBlockProjection_add, ih, Finset.sum_insert has]

/-!
## P_1 Kills Detail Components
-/

/--
P_1 annihilates detail at level L+1: P_1 ∘ Δ_{L+1} = 0.

**Proof**: Δ_{L+1} f = P_{L+2} f - P_{L+1} f. By the tower property
(P_1 ∘ P_M = P_1 for M ≥ 1), P_1(P_{L+2} f) = P_1 f = P_1(P_{L+1} f),
so P_1(Δ_{L+1} f) = P_1 f - P_1 f = 0.
-/
theorem finiteBlockProjection_kills_detail {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : ℕ) (hL : L + 1 < k + 1) (f : FiniteRadixSpace b k → V) :
    finiteBlockProjection b k 1 (by omega)
      (finiteDetailOperator b k (L + 1) hL f) = 0 := by
  simp only [finiteDetailOperator]
  rw [finiteBlockProjection_sub b k 1 (by omega)]
  rw [finiteBlockProjection_tower k 1 (L + 2) (by omega) (by omega) (by omega)]
  rw [finiteBlockProjection_tower k 1 (L + 1) (by omega) (by omega) (by omega)]
  exact sub_self _

/-!
## Uniqueness of the Decomposition
-/

/--
**Theorem 7 (uniqueness)**: The multiresolution decomposition is unique.

If f = c + ∑ d_L where c is in the coarse subspace (c = P_1 c, i.e., c is 1-block-constant)
and each d_L is in the detail subspace (d_L = Δ_{L+1} d_L), then
c = P_1 f (the coarse component is uniquely determined).

**Proof**: Apply P_1 to f = c + ∑ d_L. By linearity:
P_1 f = P_1 c + ∑ P_1 d_L = c + ∑ 0 = c,
using P_1 c = c (hypothesis) and P_1(Δ_{L+1} d_L) = 0 (tower property).
-/
-- fdrs.md lines 1086-1098, Theorem 7 (uniqueness)
theorem multiresolution_decomposition_unique {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : FiniteRadixSpace b k → V)
    (c : FiniteRadixSpace b k → V)
    (details : Fin k → (FiniteRadixSpace b k → V))
    (h_decomp : f = c + ∑ L : Fin k, details L)
    (h_coarse : finiteBlockProjection b k 1 (by omega) c = c)
    (h_detail : ∀ L : Fin k,
      finiteDetailOperator b k (L.val + 1) (by omega) (details L) = details L) :
    c = finiteBlockProjection b k 1 (by omega) f := by
  -- Apply P_1 to f = c + ∑ details L
  have h1 : finiteBlockProjection b k 1 (by omega) f =
      finiteBlockProjection b k 1 (by omega) c +
      finiteBlockProjection b k 1 (by omega) (∑ L : Fin k, details L) := by
    conv_lhs => rw [h_decomp]
    exact finiteBlockProjection_add k 1 (by omega) c (∑ L : Fin k, details L)
  -- P_1 c = c
  rw [h_coarse] at h1
  -- P_1(∑ d_L) = ∑ P_1(d_L) = ∑ 0 = 0
  have h2 : finiteBlockProjection b k 1 (by omega) (∑ L : Fin k, details L) = 0 := by
    rw [finiteBlockProjection_finset_sum b k 1 (by omega)]
    apply Finset.sum_eq_zero
    intro L _
    -- P_1(d_L) = P_1(Δ_{L+1} d_L) = 0
    rw [← h_detail L]
    exact finiteBlockProjection_kills_detail b k L.val (by omega) (details L)
  rw [h2, add_zero] at h1
  exact h1.symm

end FdrsFormal.FunctionSpaces.Commutant
