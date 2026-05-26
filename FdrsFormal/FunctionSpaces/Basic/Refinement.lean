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

# Refinement Embeddings

This file defines the refinement embeddings ι_{L→L+1} : V^{Σ_L} ↪ V^{Σ_{L+1}}.

## Mathematical Content (fdrs.md lines 607-614)

**Definition 20 (Refinement Embeddings)**:
Define maps ι_{L→L+1} : V^{Σ_L} ↪ V^{Σ_{L+1}} by replication across refined blocks:
  (ι_{L→L+1} a)(s_0, ..., s_L) := a(s_0, ..., s_{L-1}).

Under Φ_L, this is exactly the inclusion 𝕋_L(V) ⊆ 𝕋_{L+1}(V).

## Implementation Notes

- Refinement is achieved by ignoring the last digit
- This creates a directed system V^{Σ_1} → V^{Σ_2} → V^{Σ_3} → ...
- The direct limit of this system would give 𝕋(V) restricted to finite-resolution tensors
- Each embedding is injective but not surjective

## References

- fdrs.md, Section 2, Definition 20 (lines 607-614)
- THEOREM_MAPPING.md, FunctionSpaces/Basic section
-/

import FdrsFormal.FunctionSpaces.Basic.CoordinateRep

namespace FdrsFormal.FunctionSpaces.Basic

open FdrsFormal.Core.Primitives FdrsFormal.Core.Infinite

/-!
## Refinement Embedding Definition
-/

variable {b : RadixSeq} {V : Type*}

/--
Refinement embedding on coordinate vectors: ι_{L→L+1} : V^{Σ_L} ↪ V^{Σ_{L+1}}.

**fdrs.md Definition 20**: (ι_{L→L+1} a)(s_0, ..., s_L) := a(s_0, ..., s_{L-1})

Maps a level-L coordinate vector to level-(L+1) by replicating values across refined blocks.
-/
def refinementEmbedding (L : ℕ) (a : PrefixSet b L → V) : PrefixSet b (L + 1) → V :=
  fun s => a (truncatePrefix s)

-- Alternative notation for refinement embedding (commented - causes issues)
-- notation "ι[" L "→" M "]" => refinementEmbedding (b := _) L

/--
Refinement on BlockConstantSpace: the natural inclusion 𝕋_L(V) ⊆ 𝕋_{L+1}(V).
-/
def refinementInclude (L : ℕ) (f : BlockConstantSpace b L V) : BlockConstantSpace b (L + 1) V :=
  f.coarsenTo

/-!
## Refinement Properties
-/

/--
Refinement embedding is injective.
-/
theorem refinementEmbedding_injective (L : ℕ) :
    Function.Injective (refinementEmbedding (b := b) (V := V) L) := by
  intro a a' h
  funext t
  -- We need to find some s : PrefixSet b (L+1) with truncatePrefix s = t
  -- Use extendPrefix with any digit
  have hpos : 0 < b L := b.pos L
  let s := extendPrefix t ⟨0, hpos⟩
  have hs : truncatePrefix s = t := by
    funext i
    simp only [truncatePrefix, extendPrefix, s]
    rw [Fin.lastCases_castSucc]
  calc a t = a (truncatePrefix s) := by rw [hs]
    _ = refinementEmbedding L a s := rfl
    _ = refinementEmbedding L a' s := by rw [h]
    _ = a' (truncatePrefix s) := rfl
    _ = a' t := by rw [hs]

/--
Refinement commutes with the coordinate representation.

This diagram commutes:
```
  𝕋_L(V) ----Φ_L---→ V^{Σ_L}
     |                  |
  include           ι_{L→L+1}
     ↓                  ↓
  𝕋_{L+1}(V) --Φ_{L+1}→ V^{Σ_{L+1}}
```
-/
theorem refinement_commutes_with_coord (L : ℕ) (f : BlockConstantSpace b L V) :
    blockCoordinate (refinementInclude L f) = refinementEmbedding L (blockCoordinate f) := by
  funext s'
  simp only [blockCoordinate, refinementEmbedding, refinementInclude]
  unfold BlockConstantSpace.evalCylinder BlockConstantSpace.coarsenTo
  simp only
  -- Use block-constancy at level L: both reps agree on first L digits
  apply (isBlockConstant_iff_isBlockConstant' f.val L).mp f.property
  funext i
  simp only [prefixOf]
  -- For i : Fin L, we have i.val < L, so both branches use the positive case
  have hi_lt_L : i.val < L := i.isLt
  have hi_lt_succ : i.val < L + 1 := Nat.lt_succ_of_lt hi_lt_L
  simp only [hi_lt_L, hi_lt_succ, ↓reduceDIte, truncatePrefix, Fin.castSucc]
  congr 1

/-!
## Composition of Refinements
-/

/--
Multi-step refinement: ι_{L→M} for L ≤ M.
-/
def refinementEmbeddingMulti (L M : ℕ) (hLM : L ≤ M) (a : PrefixSet b L → V) :
    PrefixSet b M → V :=
  fun s => a (fun i => s (Fin.castLE hLM i))

/--
Composition of refinement embeddings.

ι_{L→L+1} ∘ ι_{L+1→L+2} = ι_{L→L+2}
-/
theorem refinementEmbedding_comp (L : ℕ) (a : PrefixSet b L → V) :
    refinementEmbedding (L + 1) (refinementEmbedding L a) =
    refinementEmbeddingMulti L (L + 2) (by omega) a := by
  funext s
  simp only [refinementEmbedding, refinementEmbeddingMulti]
  congr 1

/--
Identity refinement: ι_{L→L} = id.
-/
theorem refinementEmbeddingMulti_refl (L : ℕ) (a : PrefixSet b L → V) :
    refinementEmbeddingMulti L L (le_refl L) a = a := by
  funext s
  simp only [refinementEmbeddingMulti]
  congr 1

/--
Transitivity: ι_{L→N} = ι_{M→N} ∘ ι_{L→M} for L ≤ M ≤ N.
-/
theorem refinementEmbeddingMulti_trans (L M N : ℕ) (hLM : L ≤ M) (hMN : M ≤ N)
    (a : PrefixSet b L → V) :
    refinementEmbeddingMulti L N (le_trans hLM hMN) a =
    refinementEmbeddingMulti M N hMN (refinementEmbeddingMulti L M hLM a) := by
  funext s
  simp only [refinementEmbeddingMulti]
  congr 1

/-!
## Algebraic Properties of Refinement
-/

section Algebraic

variable [AddCommGroup V]

/--
Refinement embedding is a group homomorphism.
-/
def refinementEmbeddingHom (L : ℕ) :
    (PrefixSet b L → V) →+ (PrefixSet b (L + 1) → V) where
  toFun := refinementEmbedding L
  map_zero' := by
    ext s
    simp [refinementEmbedding]
  map_add' := by
    intro a c
    ext s
    simp [refinementEmbedding, Pi.add_apply]

end Algebraic

section Module

variable [Semiring R] [AddCommMonoid V] [Module R V]

/--
Refinement embedding is R-linear.
-/
def refinementEmbeddingLinear (L : ℕ) :
    (PrefixSet b L → V) →ₗ[R] (PrefixSet b (L + 1) → V) where
  toFun := refinementEmbedding L
  map_add' := by
    intro a c
    ext s
    simp [refinementEmbedding, Pi.add_apply]
  map_smul' := by
    intro r a
    ext s
    simp [refinementEmbedding, Pi.smul_apply]

end Module

/-!
## Image Characterization
-/

/--
A function at level L+1 is in the image of refinement iff it's constant
on each set of prefixes that share the same truncation.
-/
theorem mem_range_refinementEmbedding_iff (L : ℕ) (f : PrefixSet b (L + 1) → V) :
    (∃ a : PrefixSet b L → V, refinementEmbedding L a = f) ↔
    ∀ s t : PrefixSet b (L + 1), truncatePrefix s = truncatePrefix t → f s = f t := by
  constructor
  · -- Forward: if f = refinementEmbedding L a, then f is constant on truncation fibers
    rintro ⟨a, rfl⟩ s t hst
    simp only [refinementEmbedding, hst]
  · -- Backward: if f is constant on truncation fibers, construct a
    intro hf
    -- Define a by picking a representative for each truncation class
    have hpos : 0 < b L := b.pos L
    use fun t => f (extendPrefix t ⟨0, hpos⟩)
    funext s
    simp only [refinementEmbedding]
    -- Show f (extendPrefix (truncatePrefix s) ⟨0, _⟩) = f s
    apply hf
    -- Need: truncatePrefix (extendPrefix (truncatePrefix s) ⟨0, _⟩) = truncatePrefix s
    funext i
    simp only [truncatePrefix, extendPrefix, Fin.lastCases_castSucc]

/-!
## Connection to Direct Limits

The sequence V^{Σ_1} → V^{Σ_2} → ... forms a directed system.
The block-constant tensors with finite resolution form the direct limit.
-/

/--
The directed system formed by refinement embeddings.

This captures the tower 𝕋_1(V) ⊆ 𝕋_2(V) ⊆ 𝕋_3(V) ⊆ ...
-/
def refinementSystem (b : RadixSeq) (V : Type*) : ℕ → Type _ :=
  fun L => PrefixSet b L → V

/--
The transition maps of the directed system.
-/
def refinementSystemMap (L M : ℕ) (hLM : L ≤ M) :
    refinementSystem b V L → refinementSystem b V M :=
  refinementEmbeddingMulti L M hLM

end FdrsFormal.FunctionSpaces.Basic
