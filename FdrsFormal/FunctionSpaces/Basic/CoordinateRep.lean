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

# Block Coordinate Representation

This file establishes the canonical isomorphism Φ_L : 𝕋_L(V) ≅ V^{Σ_L} ≅ V^{B_L}.

## Mathematical Content (fdrs.md lines 597-606)

**Proposition 15 (Finite Block Coordinate Representation)**:
There is a canonical isomorphism of vector spaces (and Banach spaces under the sup norm)
  Φ_L : 𝕋_L(V) ≅ V^{Σ_L} ≅ V^{B_L},
given by Φ_L(f) = (f|_{U(s)})_{s ∈ Σ_L} (the value on each block).

**Proof**: If f is constant on each cylinder U(s), it is determined uniquely by the
list of its B_L values. Conversely any assignment a : Σ_L → V defines a block-constant
function f_a(x) = a(π_L(x)). These constructions are mutual inverses.

## Implementation Notes

- This is the finite-dimensional representation at each resolution level
- The isomorphism is both algebraic and (when applicable) isometric
- This is key for computational implementations

## References

- fdrs.md, Section 2, Proposition 15 (lines 597-606)
- THEOREM_MAPPING.md, FunctionSpaces/Basic section
-/

import FdrsFormal.FunctionSpaces.Basic.BlockConstant

namespace FdrsFormal.FunctionSpaces.Basic

open FdrsFormal.Core.Primitives FdrsFormal.Core.Infinite

/-!
## Coordinate Representation Map
-/

variable {b : RadixSeq} {L : ℕ} {V : Type*}

/--
The coordinate representation map Φ_L : 𝕋_L(V) → V^{Σ_L}.

**fdrs.md**: Φ_L(f) = (f|_{U(s)})_{s ∈ Σ_L}

Maps a block-constant tensor to its values on each cylinder.
-/
def blockCoordinate (f : BlockConstantSpace b L V) : PrefixSet b L → V :=
  fun s => f.evalCylinder s

/--
The inverse map: assignment → block-constant tensor.

**fdrs.md**: Any assignment a : Σ_L → V defines a block-constant function f_a(x) = a(π_L(x)).
-/
def fromBlockCoordinate (a : PrefixSet b L → V) : BlockConstantSpace b L V :=
  liftPrefix a

/-!
## The Isomorphism
-/

/--
**Proposition 15**: The block coordinate representation is a bijection.

Φ_L : 𝕋_L(V) ≅ V^{Σ_L}
-/
def blockCoordinateEquiv : BlockConstantSpace b L V ≃ (PrefixSet b L → V) where
  toFun := blockCoordinate
  invFun := fromBlockCoordinate
  left_inv := by
    intro f
    apply Subtype.ext
    funext x
    simp only [fromBlockCoordinate, liftPrefix, blockCoordinate]
    exact (f.evalCylinder_eq (prefixOf b L x) x (mem_cylinderSet_prefixOf b L x)).symm
  right_inv := by
    intro a
    funext s
    simp only [blockCoordinate, fromBlockCoordinate]
    -- Need to show (liftPrefix a).evalCylinder s = a s
    -- evalCylinder evaluates at a representative in the cylinder
    -- That representative has prefixOf b L rep = s, so a (prefixOf b L rep) = a s
    unfold BlockConstantSpace.evalCylinder liftPrefix
    simp only
    -- The representative point has i < L implying s ⟨i, h⟩ is used
    -- So prefixOf b L rep = s
    congr 1
    funext i
    simp only [prefixOf, i.isLt, ↓reduceDIte]

/--
Cardinality: V^{Σ_L} ≅ V^{B_L}.
-/
theorem blockCoordinate_card_domain :
    Fintype.card (PrefixSet b L) = placeValue b L :=
  prefixSet_card b L

/-!
## Algebraic Properties
-/

section Algebraic

variable [AddCommGroup V]

/--
The coordinate map is a group homomorphism.
-/
def blockCoordinateHom : BlockConstantSpace b L V →+ (PrefixSet b L → V) where
  toFun := blockCoordinate
  map_zero' := rfl
  map_add' := fun _ _ => rfl

/--
The coordinate map is a group isomorphism.
-/
def blockCoordinateIso : BlockConstantSpace b L V ≃+ (PrefixSet b L → V) where
  toEquiv := blockCoordinateEquiv
  map_add' := fun _ _ => rfl

end Algebraic

section Module

variable [Semiring R] [AddCommMonoid V] [Module R V]

/--
The coordinate map is R-linear.
-/
def blockCoordinateLinear : BlockConstantSpace b L V →ₗ[R] (PrefixSet b L → V) where
  toFun := blockCoordinate
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

/--
The coordinate map is an R-linear equivalence.
-/
def blockCoordinateLinearEquiv : BlockConstantSpace b L V ≃ₗ[R] (PrefixSet b L → V) :=
  { blockCoordinateEquiv, blockCoordinateLinear with }

end Module

/-!
## Norm Properties (for Banach Spaces)
-/

section Norm

variable [NormedAddCommGroup V]

/--
Under the sup norm, the coordinate representation is an isometry.

‖f‖_∞ = sup_{x ∈ R̂} ‖f(x)‖ = sup_{s ∈ Σ_L} ‖Φ_L(f)(s)‖
-/
theorem blockCoordinate_sup_norm_eq (f : BlockConstantSpace b L V) :
    (⨆ x : CompletedSpace b, ‖f.val x‖) = ⨆ s : PrefixSet b L, ‖blockCoordinate f s‖ := by
  apply le_antisymm
  · -- LHS ≤ RHS: For any x, ‖f.val x‖ ≤ ⨆ s, ‖blockCoordinate f s‖
    apply ciSup_le
    intro x
    -- f.val x = blockCoordinate f (prefixOf b L x)
    have heq : f.val x = blockCoordinate f (prefixOf b L x) := by
      simp only [blockCoordinate]
      exact (f.evalCylinder_eq (prefixOf b L x) x (mem_cylinderSet_prefixOf b L x))
    rw [heq]
    apply le_ciSup_of_le _ (prefixOf b L x)
    · exact le_refl _
    · -- Boundedness: use finite type
      exact Set.finite_range (fun s => ‖blockCoordinate f s‖) |>.bddAbove
  · -- RHS ≤ LHS: For any s, ‖blockCoordinate f s‖ ≤ ⨆ x, ‖f.val x‖
    haveI : Nonempty (PrefixSet b L) := ⟨fun _ => ⟨0, b.pos _⟩⟩
    apply ciSup_le
    intro s
    -- Construct a representative point in the cylinder
    let rep : CompletedSpace b := fun i => if h : i < L then s ⟨i, h⟩ else ⟨0, b.pos i⟩
    have hrep : rep ∈ cylinderSet b L s := fun i => by simp only [rep, i.isLt, ↓reduceDIte]
    have heq : blockCoordinate f s = f.val rep := by
      simp only [blockCoordinate]
      exact f.evalCylinder_eq s rep hrep
    rw [heq]
    apply le_ciSup_of_le _ rep
    · exact le_refl _
    · -- Boundedness: need to show the set is bounded above
      -- This requires that f.val is bounded, which may need additional assumptions
      -- For now, use that the image of f is within the range of blockCoordinate
      have hfin : Set.Finite (Set.range (fun s => ‖blockCoordinate f s‖)) :=
        Set.finite_range _
      use sSup (Set.range (fun s => ‖blockCoordinate f s‖))
      intro y hy
      obtain ⟨x, rfl⟩ := hy
      have heqx : f.val x = blockCoordinate f (prefixOf b L x) := by
        simp only [blockCoordinate]
        exact (f.evalCylinder_eq (prefixOf b L x) x (mem_cylinderSet_prefixOf b L x))
      simp only
      rw [heqx]
      apply le_csSup hfin.bddAbove
      exact Set.mem_range_self _

end Norm

/-!
## Connection to Finite Horizon

On FiniteRadixSpace R^{(k)}, the block coordinate representation gives
an explicit bijection with vectors in V^{B_L} for L ≤ k.
-/

-- For finite horizons, block-constant functions correspond to B_L-dimensional vectors.
-- The cardinality statement |V^{Σ_L}| = |V|^{B_L} requires Fintype V.
-- theorem blockCoordinate_finite_dimension [Fintype V] [DecidableEq V] (L : ℕ) :
--     Fintype.card (PrefixSet b L → V) = Fintype.card V ^ placeValue b L := by
--   rw [Fintype.card_fun, prefixSet_card]

end FdrsFormal.FunctionSpaces.Basic
