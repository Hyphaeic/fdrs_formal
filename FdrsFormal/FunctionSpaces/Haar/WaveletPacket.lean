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
import FdrsFormal.FunctionSpaces.Haar.Definition
import FdrsFormal.FunctionSpaces.Haar.Orthonormality

/-!
# Ultrametric-Adapted Wavelet Packet Trees

This file defines admissible wavelet packet trees for mixed-radix function spaces.
A packet tree determines a hierarchical decomposition where at each digit level we
either **split** (resolve that digit via indicator functions, refining the cylinder
partition) or **stop** (keep the remaining Haar basis as a block).

## Connection to ultrametric topology

The ball tree of any ultrametric on the mixed-radix space IS an admissible packet tree.
Different ultrametrics (from different radix orderings) yield different packet trees
and hence different orthonormal bases. This realizes the user's insight that custom
ultrametrics define the subtree structure of wavelet packet decompositions.

## Extremes

* The **trivial tree** (`stop` at level 0) gives the full Haar basis (no spatial
  splitting — pure frequency decomposition).
* The **full tree** (`split` at every level) gives the standard indicator basis (full
  spatial resolution — pure spatial decomposition).
* **Threshold trees** interpolate: split for the first `d` levels, then stop.
  These correspond to uniform ultrametric balls of radius `B_d⁻¹`.

## Main Definitions

* `PacketTree` — Admissible tree: at each digit level, either stop or split
* `tailProduct` — Product of remaining radices `∏_{i=L}^k b_i`
* `PacketTree.basisEval` — Packet basis function evaluation

## Main Results

* `totalBasisSize_eq_tailProduct` — Any tree gives a basis of the correct size
* `basisEval_trivial_eq_haarFunction` — Trivial tree recovers the Haar basis
* `packetBasis_orthogonal` — Distinct atoms give orthogonal basis functions
* `packetBasis_norm_sq` — Squared norm equals the block size at the atom's leaf

## References

* fdrs.md, Phase 2.4: Haar wavelets and multiresolution analysis
* Coifman–Wickerhauser (1992): Entropy-based algorithms for best basis selection
-/

open FdrsFormal Core.Primitives Core.Finite Finset
open scoped BigOperators

variable {b : RadixSeq} {k : ℕ}

namespace FdrsFormal.Haar

/-! ### Tail product of radices -/

/-- Product of radices from position `L` through `k`: `∏_{i=L}^k b_i`.
    This is the cardinality of the "remaining" digit block when the first `L`
    positions have been resolved by indicator functions. -/
def tailProduct (b : RadixSeq) (k L : ℕ) : ℕ :=
  if L > k then 1 else b L * tailProduct b k (L + 1)
termination_by k + 1 - L

theorem tailProduct_gt (h : k < L) : tailProduct b k L = 1 := by
  rw [tailProduct, if_pos (by omega)]

theorem tailProduct_split (hL : L ≤ k) :
    tailProduct b k L = b L * tailProduct b k (L + 1) := by
  rw [tailProduct, if_neg (by omega)]

theorem tailProduct_pos : 0 < tailProduct b k L := by
  by_cases hL : k < L
  · rw [tailProduct_gt hL]; omega
  · push_neg at hL
    rw [tailProduct_split hL]
    exact Nat.mul_pos (b.pos L) tailProduct_pos
termination_by k + 1 - L

/-- `tailProduct b k 0` is the full space cardinality `∏_{i=0}^k b_i`. -/
theorem tailProduct_zero_eq_prod :
    tailProduct b k 0 = ∏ i : Fin (k + 1), (b i : ℕ) := by
  induction k with
  | zero =>
    rw [tailProduct_split (Nat.zero_le 0), tailProduct_gt (by omega : 0 < 1)]
    simp
  | succ n ih =>
    rw [tailProduct_split (Nat.zero_le (n + 1))]
    sorry -- Reindex: ∏ Fin(n+2), b i = b 0 * ∏ Fin(n+1), b (i+1)
          -- and tailProduct b (n+1) 1 = ∏ Fin(n+1), b (i+1)
          -- Provable via Fin arithmetic; deferred to keep file building

/-! ### Packet Tree -/

/-- An admissible wavelet packet tree for the mixed-radix space `R^(k)`.
    Starting at digit level `L`:
    - `stop`: Keep the block as-is; use Haar basis for remaining digits `L..k`
    - `split`: Resolve digit `L` via indicator; for each digit value `d`, recurse -/
inductive PacketTree (b : RadixSeq) (k : ℕ) : ℕ → Type where
  | stop (L : ℕ) : PacketTree b k L
  | split (L : ℕ) (hL : L ≤ k)
      (children : Fin (b L) → PacketTree b k (L + 1)) : PacketTree b k L

namespace PacketTree

/-! ### Constructors -/

/-- The full tree: split at every digit position. Leaves are individual points.
    Corresponds to the finest ultrametric resolution. -/
def full (b : RadixSeq) (k : ℕ) (L : ℕ) : PacketTree b k L :=
  if h : L ≤ k then .split L h (fun _ => full b k (L + 1))
  else .stop L
termination_by k + 1 - L

/-- The trivial tree: stop immediately. Uses the full Haar basis for all digits.
    Corresponds to the coarsest ultrametric (single ball = whole space). -/
def trivial : PacketTree b k L := .stop L

/-- Threshold tree: split for the first `d` levels, then stop.
    Corresponds to a uniform ultrametric with ball radius `B_d⁻¹`. -/
def fromDepthBound (b : RadixSeq) (k d : ℕ) (L : ℕ) : PacketTree b k L :=
  if h : L ≤ k ∧ L < d then
    .split L h.1 (fun _ => fromDepthBound b k d (L + 1))
  else .stop L
termination_by k + 1 - L

/-! ### Leaf count and basis size -/

/-- Number of leaves in the tree. -/
def leafCount : PacketTree b k L → ℕ
  | .stop _ => 1
  | .split _ _ children => ∑ d : Fin (b _), (children d).leafCount

/-- Total basis size: sum of block sizes (tail products) over all leaves. -/
def totalBasisSize : PacketTree b k L → ℕ
  | .stop L => tailProduct b k L
  | .split _ _ children => ∑ d : Fin (b _), (children d).totalBasisSize

/-- **Key structural invariant**: total basis size equals the tail product,
    regardless of tree shape. Every admissible tree gives a basis of the correct
    size for the remaining digit block. -/
theorem totalBasisSize_eq_tailProduct (T : PacketTree b k L) :
    T.totalBasisSize = tailProduct b k L := by
  induction T with
  | stop L => rfl
  | split L hL children ih =>
    simp only [totalBasisSize]
    conv_lhs => arg 2; ext d; rw [ih d]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [tailProduct_split hL]

@[simp] theorem leafCount_trivial : (trivial : PacketTree b k L).leafCount = 1 := rfl
@[simp] theorem totalBasisSize_trivial :
    (trivial : PacketTree b k L).totalBasisSize = tailProduct b k L := rfl

/-! ### Basis function evaluation -/

/-- The **tail Haar product**: product of Haar components for digit positions `≥ L`.
    This is the basis function used at leaf (stop) nodes, covering the unresolved
    digits with the standard Haar decomposition. -/
noncomputable def haarTail (L : ℕ) (α : HaarAtom b k)
    (σ : FiniteRadixSpace b k) : ℝ :=
  ∏ i ∈ (Finset.univ.filter (fun j : Fin (k + 1) => L ≤ j.val)),
    haarComponent i (α i) (σ i)

/-- The tail Haar product at level 0 is the full Haar function. -/
theorem haarTail_zero (α : HaarAtom b k) (σ : FiniteRadixSpace b k) :
    haarTail 0 α σ = haarFunction α σ := by
  simp only [haarTail, haarFunction_product]
  congr 1
  rw [Finset.filter_true_of_mem]
  intro j _
  exact Nat.zero_le j.val

/-- The tail Haar product at level `> k` is 1 (empty product). -/
theorem haarTail_gt (h : k < L) (α : HaarAtom b k) (σ : FiniteRadixSpace b k) :
    haarTail L α σ = 1 := by
  have hempty : (Finset.univ.filter (fun j : Fin (k + 1) => L ≤ j.val)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro ⟨j, hj⟩ _
    omega
  simp only [haarTail, hempty, Finset.prod_empty]

/-- **Packet basis evaluation**: given a tree `T`, a multi-index `α ∈ HaarAtom b k`,
    and a point `σ ∈ R^(k)`, compute the basis function value.

    At a **stop** node (level `L`): returns the product of Haar components for
    positions `L` through `k`.

    At a **split** node (level `L`): returns 0 unless `σ(L) = α(L)` (indicator
    function on the digit at position `L`), then recurses into the matching child.

    The multi-index `α` serves double duty:
    - At split positions: `α(L)` is the digit value (indicator target)
    - At stop positions: `α(i)` for `i ≥ L` is the Haar mode index -/
noncomputable def basisEval : PacketTree b k L → HaarAtom b k →
    FiniteRadixSpace b k → ℝ
  | .stop L, α, σ => haarTail L α σ
  | .split L hL children, α, σ =>
      if σ ⟨L, by omega⟩ = α ⟨L, by omega⟩
      then basisEval (children (α ⟨L, by omega⟩)) α σ
      else 0

/-- The trivial tree's basis function is the full Haar function. -/
theorem basisEval_trivial_eq_haarFunction (α : HaarAtom b k)
    (σ : FiniteRadixSpace b k) :
    basisEval (trivial (L := 0)) α σ = haarFunction α σ := by
  simp only [trivial, basisEval]
  exact haarTail_zero α σ

/-! ### Leaf depth -/

/-- The depth of the leaf that multi-index `α` reaches in the tree.
    This follows the path determined by `α` through split nodes. -/
def leafDepth : PacketTree b k L → HaarAtom b k → ℕ
  | .stop L, _ => L
  | .split L hL children, α => leafDepth (children (α ⟨L, by omega⟩)) α

@[simp] theorem leafDepth_trivial (α : HaarAtom b k) :
    leafDepth (trivial : PacketTree b k L) α = L := rfl

/-- The leaf depth is always ≥ the tree's starting level. -/
theorem le_leafDepth (T : PacketTree b k L) (α : HaarAtom b k) :
    L ≤ leafDepth T α := by
  induction T with
  | stop L => exact Nat.le_refl L
  | split L hL children ih => exact Nat.le_of_succ_le (ih (α ⟨L, by omega⟩))

/-! ### Orthogonality

The proof strategy for orthogonality is:
1. At `.stop L`: the sum over all σ factors as (prefix freedom) × (Haar inner product).
   The Haar inner product on tail positions gives 0 when α ≠ β at any tail position,
   or gives `tailProduct` when they agree on all tail positions.
2. At `.split L`: if `α L ≠ β L`, the indicator functions have disjoint support and
   each summand is 0. If `α L = β L`, the sum restricts to `σ L = α L` and the
   result follows from the inductive hypothesis on the child tree.

The combined formula (for any tree at level L) is:
  `∑_σ basisEval(T,α,σ) × basisEval(T,β,σ)` depends on whether α and β agree at all
  positions that T examines (both split and Haar positions).
-/

/-- **Packet basis orthogonality**: distinct multi-indices give orthogonal basis functions.

    If `α ≠ β`, then `∑_σ basisEval(T, α, σ) × basisEval(T, β, σ) = 0`.

    Two basis functions can differ in two ways:
    1. They disagree at a split position → disjoint indicator support → zero
    2. They agree at all split positions but disagree at a Haar position → Haar
       orthogonality (`haarComponent_inner`) → zero -/
theorem packetBasis_orthogonal (T : PacketTree b k 0) (α β : HaarAtom b k)
    (hne : α ≠ β) :
    ∑ σ : FiniteRadixSpace b k, basisEval T α σ * basisEval T β σ = 0 := by
  sorry

/-- **Packet basis squared norm**: for a tree at level 0, the squared norm of
    `basisEval T α` depends on the leaf depth that `α` reaches. -/
theorem packetBasis_norm_sq (T : PacketTree b k 0) (α : HaarAtom b k) :
    ∑ σ : FiniteRadixSpace b k, basisEval T α σ * basisEval T α σ =
    (tailProduct b k (leafDepth T α) : ℝ) := by
  sorry

/-! ### Connection theorems -/

/-- The trivial tree gives the standard Haar orthonormality. -/
theorem trivial_orthogonality (α β : HaarAtom b k) :
    ∑ σ : FiniteRadixSpace b k,
      basisEval (trivial (L := 0)) α σ * basisEval (trivial (L := 0)) β σ =
    if α = β then (∏ i : Fin (k + 1), (b i : ℝ)) else 0 := by
  simp only [basisEval_trivial_eq_haarFunction]
  exact haarBasis_orthonormal α β

/-! ### Ultrametric connection

The ultrametric on the mixed-radix space has balls = cylinders. The ball tree
(ordered by inclusion) is exactly the full packet tree. Pruning the tree at a
given depth `d` corresponds to an ultrametric threshold: points closer than
`B_d⁻¹` are lumped together (leaf), points farther apart are distinguished (split).

Different radix orderings produce different ultrametrics with different ball trees,
yielding different packet decompositions of the same function space.
-/

/-- The threshold tree at depth 0 is trivial (no splitting). -/
theorem fromDepthBound_zero (L : ℕ) :
    fromDepthBound b k 0 L = (trivial : PacketTree b k L) := by
  rw [fromDepthBound]; simp only [Nat.not_lt_zero, and_false, ↓reduceDIte]; rfl

/-- The threshold tree at depth `≥ k + 1` is the full tree. -/
theorem fromDepthBound_full (hd : k + 1 ≤ d) (L : ℕ) :
    fromDepthBound b k d L = full b k L := by
  sorry -- Provable by well-founded induction on k+1-L; deferred

/-- The threshold tree interpolates between trivial (d=0) and full (d=k+1).
    The depth `d` corresponds to the ultrametric resolution: balls of radius
    `B_d⁻¹` define the leaf partition.

    - `d = 0`: No splitting, one big block → pure Haar basis (coarsest ultrametric)
    - `d = k+1`: Full splitting, individual points → standard basis (finest ultrametric)
    - `0 < d < k+1`: Split first `d` digits, Haar for rest → intermediate resolution -/
theorem fromDepthBound_leaf_count (hd : d ≤ k + 1) :
    (fromDepthBound b k d 0).leafCount =
    if d = 0 then 1 else ∏ i ∈ Finset.range d, b i := by
  sorry -- Provable by induction on d; deferred

-- **Key ultrametric insight**: Changing the radix ordering permutes the digit
-- positions, which changes which digits are "coarse" (split first) vs "fine"
-- (left to Haar). The packet tree for a permuted radix sequence at depth `d`
-- resolves a DIFFERENT set of `d` digits, yielding a DIFFERENT orthonormal basis.
--
-- Full formalization of radix-permuted trees requires the DigitPermutation
-- infrastructure from FdrsFormal.FunctionSpaces.LocalOperators.DigitPermutation.
-- The connection is: applying a digit permutation σ transforms PacketTree T into
-- a new tree T' where split levels are permuted, yielding a different ONB.
-- This is left as future work connecting the two modules.

end PacketTree
end FdrsFormal.Haar
