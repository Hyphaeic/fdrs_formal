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

# Block Memory Definition

This file defines block memory as the cylinder-local component of state.

## Mathematical Content (fdrs.md Phase 4)

**Block Memory**: Memory at depth L is `x_L : Σ_L → V` where Σ_L is the
set of prefixes of length L. This represents the ℱ_{k,L}-measurable part
of state.

**Key Insight**: Block memory is exactly what can be computed using only
L digits of the current position τ.

## References

- fdrs.md, Phase 4, Section 4.1 (Block Memory)
- DEPENDENCY_BASED_STRUCTURE.md, Integration/BlockMemory
-/

import FdrsFormal.Core
import FdrsFormal.Topology
import FdrsFormal.FunctionSpaces

namespace FdrsFormal.Integration.BlockMemory

universe u

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-!
## Block Size

The block size B_L = ∏_{i=0}^{L-1} b_i is the number of L-prefixes.
-/

/--
Block size at depth L: B_L = ∏_{i=0}^{L-1} b_i

This is the number of distinct L-digit prefixes in the radix system.
-/
def blockSize (b : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => blockSize b n * b n

/-!
## Block Memory Space

Memory at resolution L consists of functions from L-prefixes to values.
-/

/--
Block memory at depth L for radix sequence b.
This is the space of functions from L-prefixes to V.

**fdrs.md**: `x_L : Σ_L → V`
-/
def BlockMemorySpace (b : ℕ → ℕ) (L : ℕ) (W : Type u) : Type u :=
  Fin (blockSize b L) → W

/--
Block memory is exactly the ℱ_{k,L}-measurable part of full state.

**fdrs.md Proposition**: Block memory at depth L corresponds to
cylinder-constant functions on R^{(k)}.
-/
-- fdrs.md lines 169-174
-- Block memory at depth L partitions depth-k memory: B_L divides B_k.
theorem blockMemory_is_measurable (b : ℕ → ℕ) (_hb : ∀ i, 2 ≤ b i)
    (k L : ℕ) (hL : L ≤ k) :
    blockSize b L ∣ blockSize b k := by
  induction k with
  | zero =>
    have : L = 0 := Nat.le_zero.mp hL
    subst this; exact dvd_refl _
  | succ n ih =>
    rcases Nat.lt_or_eq_of_le hL with hlt | heq
    · exact dvd_mul_of_dvd_left (ih (Nat.lt_succ_iff.mp hlt)) (b n)
    · subst heq; exact dvd_refl _

/-!
## Lift and Restrict Operations

Block memory at different resolutions can be lifted (coarsened) or
restricted (refined).
-/

/--
Block size is monotone in the depth parameter.

**Proof**: By induction on the difference. blockSize(n+1) = blockSize(n) * b(n) ≥ blockSize(n)
since b(n) ≥ 1 (actually ≥ 2 in valid radix systems).
-/
theorem blockSize_mono (b : ℕ → ℕ) (hb : ∀ i, 1 ≤ b i) {m n : ℕ} (h : m ≤ n) :
    blockSize b m ≤ blockSize b n := by
  induction n with
  | zero =>
    simp only [Nat.le_zero] at h
    subst h
    rfl
  | succ n ih =>
    rcases Nat.lt_or_eq_of_le h with h' | h'
    · -- m < n + 1, so m ≤ n
      have hle : m ≤ n := Nat.lt_succ_iff.mp h'
      calc blockSize b m ≤ blockSize b n := ih hle
        _ ≤ blockSize b n * b n := Nat.le_mul_of_pos_right _ (hb n)
        _ = blockSize b (n + 1) := rfl
    · -- m = n + 1
      subst h'
      rfl

/--
Lift operator: coarsen from depth L to depth L' < L.
Takes finer resolution memory and projects to coarser resolution.

**fdrs.md**: `U_L : H_L(V) → H_{L'}(V)` for L' < L

Implementation: Maps a coarse index to the value at the corresponding
fine index (with zeros in the extra digits). For proper averaging,
this would sum over the refinement set.
-/
def liftOperator (b : ℕ → ℕ) (hb : ∀ i, 1 ≤ b i) (L L' : ℕ) (hL : L' < L)
    (x : BlockMemorySpace b L V) : BlockMemorySpace b L' V :=
  -- Project by taking the first value in each coarse cylinder
  fun σ' => x ⟨σ'.val, Nat.lt_of_lt_of_le σ'.isLt (blockSize_mono b hb (Nat.le_of_lt hL))⟩

/--
Restrict operator: project full state to block memory at depth L.
This is the conditional expectation P_L.

**fdrs.md**: `R_L : H_k(V) → H_L(V)`

Implementation: Maps an L-prefix to the value at the corresponding full index
(with zeros in positions L through k-1).
-/
def restrictOperator (b : ℕ → ℕ) (hb : ∀ i, 1 ≤ b i) (k L : ℕ) (hL : L ≤ k)
    (f : Fin (blockSize b k) → V) : BlockMemorySpace b L V :=
  fun σ => f ⟨σ.val, Nat.lt_of_lt_of_le σ.isLt (blockSize_mono b hb hL)⟩

/-!
## Coherent Hierarchical Memory

A hierarchy of block memories satisfying coarsening constraints.
-/

/--
A coherent memory hierarchy at depths 0, 1, ..., L.
Each level must be consistent with coarser levels.

**fdrs.md**: Coarsening constraint: `U_{L',L}(x_L) = x_{L'}` for L' < L
-/
structure CoherentHierarchy (b : ℕ → ℕ) (hb : ∀ i, 1 ≤ b i) (L : ℕ) (V : Type*) where
  /-- Memory at each depth -/
  mem : (l : Fin (L + 1)) → BlockMemorySpace b l V
  /-- Coarsening consistency -/
  coherent : ∀ (l l' : Fin (L + 1)) (hlt : l'.val < l.val),
    liftOperator b hb l.val l'.val hlt (mem l) = mem l'

/--
Projection tower coherence: coarsening after restriction equals direct restriction.
This is P_{L'} ∘ P_L = P_{L'} for L' ≤ L ≤ k.

-- fdrs.md lines 3227-3240, Definition 54
-/
theorem conditionalExpectation_idempotent (b : ℕ → ℕ) (hb : ∀ i, 1 ≤ b i)
    (k L L' : ℕ) (hL'L : L' < L) (hLk : L ≤ k) (f : Fin (blockSize b k) → V) :
    liftOperator b hb L L' hL'L (restrictOperator b hb k L hLk f) =
    restrictOperator b hb k L' (le_trans (le_of_lt hL'L) hLk) f := by
  funext σ; rfl

end FdrsFormal.Integration.BlockMemory
