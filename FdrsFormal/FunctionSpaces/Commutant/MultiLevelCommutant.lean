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

# Multi-Level Commutant

Operators commuting with the entire filtration {P_L : 0 ≤ L ≤ k+1}.

## Mathematical Content (fdrs.md lines 1112-1156)

**Theorem 8 (multi-level commutation ⇔ block diagonal)**:
For a linear operator A, the following are equivalent:
1. A commutes with every projection: A P_L = P_L A for all L
2. Each detail subspace D_L is A-invariant
3. Relative to H_k = C_0 ⊕ D_0 ⊕ ... ⊕ D_k, A is block diagonal

**Interpretation**: Commuting with all scales means "no coupling between scales."

## References

- fdrs.md, Phase 2 Fragment 3 (lines 1112-1156)
- THEOREM_MAPPING.md, Theorem 8
-/

import FdrsFormal.FunctionSpaces.Commutant.BlockDiagonal
import FdrsFormal.FunctionSpaces.Commutant.Multiresolution

namespace FdrsFormal.FunctionSpaces.Commutant

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite
open FdrsFormal.FunctionSpaces.Basic

/-!
## Multi-Level Commutant Definition
-/

variable (b : RadixSeq) (V : Type*) (k : ℕ)
variable [AddCommGroup V] [Module ℝ V]

/--
An operator commutes with the entire filtration.
-/
def commutesWithAllProjections
    (A : (FiniteRadixSpace b k → V) → (FiniteRadixSpace b k → V)) : Prop :=
  ∀ L : ℕ, ∀ hLk : L ≤ k + 1, commutesWithProjection A L hLk

/-!
## Theorem 8: Multi-Level Commutation
-/

/--
**Theorem 8**: Commuting with all projections implies preserving each detail subspace.

**fdrs.md lines 1125-1162, Theorem 8**:
(1)⇒(2): If A commutes with P_L and P_{L+1}, it preserves C_L and C_{L+1}, hence
preserves their orthogonal difference D_L = range(Δ_L).

**Proof**: Δ_L = P_{L+1} - P_L. Since A commutes with both, A(Δ_L g) = Δ_L(A g).
-/
theorem multilevel_commutation_iff_blockDiagonal {b : RadixSeq} {V : Type*} {k : ℕ}
    [AddCommGroup V] [Module ℝ V]
    (A : (FiniteRadixSpace b k → V) → (FiniteRadixSpace b k → V))
    (h_add : ∀ f g, A (f + g) = A f + A g)
    (hcomm : commutesWithAllProjections b V k A) :
    ∀ L (hLk : L < k + 1),
      ∀ f ∈ detailSubspace b V k L hLk, A f ∈ detailSubspace b V k L hLk := by
  intro L hLk f ⟨g, hfg⟩
  -- A preserves D_L: if f = Δ_L g, then A f = Δ_L(A g) ∈ D_L
  refine ⟨A g, ?_⟩
  rw [hfg]
  simp only [finiteDetailOperator]
  -- Goal: A(P_{L+1} g - P_L g) = P_{L+1}(A g) - P_L(A g)
  -- Derive A(0) = 0 and A(-f) = -A(f) from additivity
  have hA0 : A 0 = 0 := by
    have h := h_add 0 0; rw [add_zero] at h
    exact (add_left_cancel ((add_zero (A 0)).trans h)).symm
  have hA_neg : ∀ h, A (-h) = -(A h) := by
    intro f'
    have h1 : A f' + A (-f') = 0 := by rw [← h_add, add_neg_cancel]; exact hA0
    exact add_left_cancel (h1.trans (add_neg_cancel (A f')).symm)
  -- Use commutation with P_{L+1} and P_L
  have hc1 := hcomm (L + 1) (by omega) g
  have hc2 := hcomm L (by omega) g
  -- A(a - b) = A(a) - A(b), then substitute commutation
  rw [sub_eq_add_neg, h_add, hA_neg, ← sub_eq_add_neg, hc1, hc2]

end FdrsFormal.FunctionSpaces.Commutant
