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

# Horizon Compatibility (Truncation and Embedding)

This file proves that projections are compatible across different horizons.

## Mathematical Content (fdrs.md lines 1009-1022)

**Definition 29 (truncation / embedding)**:
- Truncation: tr_k : R̂ → R^(k)
- Embedding: ι_k : R^(k) ↪ R^(k+1)

**Proposition 26 (projection compatibility)**:
Projections commute with horizon changes.

## References

- fdrs.md, Phase 2 Fragment 2 (lines 1009-1022)
- THEOREM_MAPPING.md, Proposition 26
-/

import FdrsFormal.FunctionSpaces.Commutant.FiniteProjection
import FdrsFormal.Core.Infinite.DirectLimit

namespace FdrsFormal.FunctionSpaces.Commutant

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite FdrsFormal.Core.Infinite
open FdrsFormal.FunctionSpaces.Basic

/-!
## Truncation and Embedding

Simplified definitions - full implementation deferred.
-/

section TruncationEmbedding

variable {b : RadixSeq} {k : ℕ}

/--
**Definition 29 (embedding)**: Embed R^(k) into R^(k+1) by appending digit 0.

For τ ∈ R^(k), embed(τ) ∈ R^(k+1) has:
- First k+1 digits: same as τ
- Last digit (position k+1): 0
-/
def embedFinite : FiniteRadixSpace b k → FiniteRadixSpace b (k + 1) :=
  fun τ i =>
    if h : i.val < k + 1 then
      τ ⟨i.val, h⟩
    else
      -- i.val ≥ k + 1 and i : Fin (k + 2), so i.val = k + 1
      have hi : i.val = k + 1 := by omega
      ⟨0, by rw [hi]; exact b.pos (k + 1)⟩

end TruncationEmbedding

/-!
## Proposition 26: Projection Compatibility

Axiomatized - requires careful measure-theoretic treatment of horizon limits.
-/

section Compatibility

variable {b : RadixSeq} {V : Type*} {k : ℕ}
variable [AddCommGroup V] [Module ℝ V]

/--
**Proposition 26**: Projections are compatible across horizons.

If P_L^(k) fixes a function f, then P_L^(k+1) fixes the lifted function f ∘ trunc.

**fdrs.md proof**: Averaging over suffix digits at depth L factors as
"average over old suffix" × "average over new last digit"; since lifted functions
are constant in the new digit, the extra averaging does nothing.

**Proof**: If P_L f = f, then f is L-block-constant (by `finiteBlockProjection_isBlockConstant`).
The lifted function f ∘ trunc inherits L-block-constancy since the L-prefix of
trunc(σ) in R^(k) equals the L-prefix of σ in R^(k+1) restricted to the first k+1
digits. By `finiteBlockProjection_fixedPoint`, P_L^(k+1) fixes the lifted function.
-/
theorem projection_compatible_across_horizons (L : ℕ) (hLk : L ≤ k + 1)
    (f : FiniteRadixSpace b k → V) (hf : finiteBlockProjection b k L hLk f = f) :
    finiteBlockProjection b (k + 1) L (by omega)
      (fun σ => f (fun i => σ ⟨i.val, by omega⟩)) =
      fun σ => f (fun i => σ ⟨i.val, by omega⟩) := by
  apply finiteBlockProjection_fixedPoint
  intro τ τ' hprefix
  -- f is L-block-constant since P_L f = f and P_L f is always L-block-constant
  have hbc : ∀ σ σ' : FiniteRadixSpace b k,
      finitePrefix b L σ hLk = finitePrefix b L σ' hLk → f σ = f σ' := by
    intro σ σ' hp
    have := finiteBlockProjection_isBlockConstant k L hLk f σ σ' hp
    rw [hf] at this
    exact this
  -- The L-prefixes of the truncations agree
  apply hbc
  funext ⟨i, hi⟩
  simp only [finitePrefix]
  have := congr_fun hprefix ⟨i, by omega⟩
  simp only [finitePrefix] at this
  exact this

end Compatibility

end FdrsFormal.FunctionSpaces.Commutant
