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

/-- `tailProduct b k L = ∏_{i=L}^{k} b_i` as a `Finset.Ico` product. -/
theorem tailProduct_eq_prod_Ico (b : RadixSeq) (k L : ℕ) :
    tailProduct b k L = ∏ i ∈ Finset.Ico L (k + 1), b i := by
  by_cases hL : k < L
  · rw [tailProduct_gt hL, Finset.Ico_eq_empty (by omega), Finset.prod_empty]
  · push_neg at hL
    rw [tailProduct_split hL, tailProduct_eq_prod_Ico b k (L + 1)]
    have hsplit : Finset.Ico L (k + 1) = insert L (Finset.Ico (L + 1) (k + 1)) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    rw [hsplit, Finset.prod_insert (by simp only [Finset.mem_Ico]; omega)]
  termination_by k + 1 - L

/-- `tailProduct b k 0` is the full space cardinality `∏_{i=0}^k b_i`. -/
theorem tailProduct_zero_eq_prod :
    tailProduct b k 0 = ∏ i : Fin (k + 1), (b i : ℕ) := by
  rw [tailProduct_eq_prod_Ico b k 0, ← Finset.range_eq_Ico]
  exact (Fin.prod_univ_eq_prod_range (fun i => (b i : ℕ)) (k + 1)).symm

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

/-! ### Closed-form factorization

We give a per-position closed form for `basisEval`. The basis function factors as
a product over digit positions, with position-`i` contribution `1` below the
start level `L`, an indicator `𝟙[d = α i]` at split positions
`i ∈ [L, leafDepth T α)`, and the Haar component for `i ≥ leafDepth T α`. This
unifies the orthogonality and norm proofs: both follow by `Fintype.prod_sum` on
the closed form.
-/

/-- Per-position factor of the packet basis function. -/
private noncomputable def pCompAt (L D : ℕ) (α : HaarAtom b k)
    (i : Fin (k + 1)) (d : Fin (b i)) : ℝ :=
  if i.val < L then 1
  else if i.val < D then (if d = α i then 1 else 0)
  else haarComponent i (α i) d

/-- **Closed form** for the packet basis function: factors as a product over
positions, with `1` below the start level, an indicator at split positions, and
the Haar component for positions beyond the leaf. -/
theorem basisEval_eq_prod {L : ℕ} (T : PacketTree b k L) (α : HaarAtom b k)
    (σ : FiniteRadixSpace b k) :
    basisEval T α σ = ∏ i : Fin (k + 1), pCompAt L (leafDepth T α) α i (σ i) := by
  induction T with
  | stop M =>
    show haarTail M α σ = _
    rw [haarTail, Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro i _
    simp only [leafDepth, pCompAt]
    by_cases h : i.val < M
    · rw [if_neg (Nat.not_le_of_lt h), if_pos h]
    · rw [if_pos (Nat.not_lt.mp h), if_neg h, if_neg h]
  | split M hM children ih =>
    have hM1 : M < k + 1 := Nat.lt_succ_of_le hM
    show (if σ ⟨M, hM1⟩ = α ⟨M, hM1⟩ then basisEval (children (α ⟨M, hM1⟩)) α σ else 0)
        = ∏ i : Fin (k + 1), pCompAt M (leafDepth (children (α ⟨M, hM1⟩)) α) α i (σ i)
    rw [ih (α ⟨M, hM1⟩)]
    have hMD : M < leafDepth (children (α ⟨M, hM1⟩)) α :=
      Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (le_leafDepth _ _)
    -- Peel position ⟨M, hM1⟩ from both products
    rw [show (∏ i : Fin (k+1), pCompAt M (leafDepth (children (α ⟨M, hM1⟩)) α) α i (σ i))
            = pCompAt M (leafDepth (children (α ⟨M, hM1⟩)) α) α ⟨M, hM1⟩ (σ ⟨M, hM1⟩)
              * ∏ i ∈ Finset.univ.erase ⟨M, hM1⟩,
                pCompAt M (leafDepth (children (α ⟨M, hM1⟩)) α) α i (σ i)
          from (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ _)).symm]
    rw [show (∏ i : Fin (k+1), pCompAt (M+1) (leafDepth (children (α ⟨M, hM1⟩)) α) α i (σ i))
            = pCompAt (M+1) (leafDepth (children (α ⟨M, hM1⟩)) α) α ⟨M, hM1⟩ (σ ⟨M, hM1⟩)
              * ∏ i ∈ Finset.univ.erase ⟨M, hM1⟩,
                pCompAt (M+1) (leafDepth (children (α ⟨M, hM1⟩)) α) α i (σ i)
          from (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ _)).symm]
    have pM : pCompAt M (leafDepth (children (α ⟨M, hM1⟩)) α) α ⟨M, hM1⟩ (σ ⟨M, hM1⟩)
        = if σ ⟨M, hM1⟩ = α ⟨M, hM1⟩ then (1 : ℝ) else 0 := by
      simp only [pCompAt]
      rw [if_neg (Nat.lt_irrefl M), if_pos hMD]
    have pM1 : pCompAt (M+1) (leafDepth (children (α ⟨M, hM1⟩)) α) α ⟨M, hM1⟩ (σ ⟨M, hM1⟩) = 1 := by
      simp only [pCompAt]
      rw [if_pos (Nat.lt_succ_self M)]
    rw [pM, pM1, one_mul]
    have heq : ∀ i ∈ (Finset.univ : Finset (Fin (k+1))).erase ⟨M, hM1⟩,
        pCompAt M (leafDepth (children (α ⟨M, hM1⟩)) α) α i (σ i)
        = pCompAt (M+1) (leafDepth (children (α ⟨M, hM1⟩)) α) α i (σ i) := by
      intro i hi
      rw [Finset.mem_erase] at hi
      have hival : i.val ≠ M := fun h => hi.1 (Fin.ext h)
      simp only [pCompAt]
      by_cases h : i.val < M
      · rw [if_pos h, if_pos (Nat.lt_succ_of_lt h)]
      · have hnot : ¬ i.val < M + 1 := by omega
        rw [if_neg h, if_neg hnot]
    rw [Finset.prod_congr rfl heq]
    by_cases h : σ ⟨M, hM1⟩ = α ⟨M, hM1⟩
    · simp [h]
    · simp [h]

/-- Fin-filter to Ico reindex: `Fin (k+1)` filtered by `D ≤ ·.val` is in
bijection with `Ico D (k+1)` via `Fin.val`. -/
private theorem prod_fin_filter_ge_eq_Ico (D : ℕ) (g : ℕ → ℝ) :
    ∏ i ∈ (Finset.univ : Finset (Fin (k + 1))).filter (fun i => D ≤ i.val), g i.val
    = ∏ j ∈ Finset.Ico D (k + 1), g j := by
  refine Finset.prod_bij (fun (a : Fin (k + 1)) _ => a.val) ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_filter] at ha
    rw [Finset.mem_Ico]
    exact ⟨ha.2, a.isLt⟩
  · intro a₁ _ a₂ _ heq
    exact Fin.ext heq
  · intro j hj
    rw [Finset.mem_Ico] at hj
    refine ⟨⟨j, hj.2⟩, ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hj.1⟩
  · intros; rfl

/-- `tailProduct b k D` as a `Fin`-indexed product with a guard. -/
private theorem tailProduct_eq_prod_fin (D : ℕ) :
    (tailProduct b k D : ℝ) = ∏ i : Fin (k + 1), if D ≤ i.val then (b i : ℝ) else 1 := by
  rw [tailProduct_eq_prod_Ico]
  push_cast
  symm
  rw [← Finset.prod_filter]
  exact prod_fin_filter_ge_eq_Ico D (fun j => (b j : ℝ))

/-- **First-difference with mode-match**: if `α, β` differ at some position `≥ L`
in a tree `T : PacketTree b k L`, there is a position `j ≥ L` where they differ
*and* both leaf depths are simultaneously above or simultaneously at-most `j`
(so the per-position factor in the closed form vanishes). -/
private theorem firstDiffMode_gen (α β : HaarAtom b k) :
    ∀ {L : ℕ} (T : PacketTree b k L),
      (∃ i : Fin (k + 1), L ≤ i.val ∧ α i ≠ β i) →
      ∃ j : Fin (k + 1), L ≤ j.val ∧ α j ≠ β j ∧
        ((j.val < leafDepth T α ∧ j.val < leafDepth T β) ∨
         (leafDepth T α ≤ j.val ∧ leafDepth T β ≤ j.val)) := by
  intro L T
  induction T with
  | stop M =>
    intro ⟨j, hLj, hne_j⟩
    refine ⟨j, hLj, hne_j, Or.inr ?_⟩
    show leafDepth (PacketTree.stop M) α ≤ j.val ∧ leafDepth (PacketTree.stop M) β ≤ j.val
    simp only [leafDepth]
    exact ⟨hLj, hLj⟩
  | split M hM children ih =>
    intro ⟨i, hMi, hne_i⟩
    have hM1 : M < k + 1 := Nat.lt_succ_of_le hM
    by_cases hαβ : α ⟨M, hM1⟩ = β ⟨M, hM1⟩
    · -- Same value at M; recurse on the child
      have hMi' : M + 1 ≤ i.val := by
        rcases Nat.lt_or_eq_of_le hMi with h | h
        · exact h
        · exfalso
          apply hne_i
          have : i = ⟨M, hM1⟩ := Fin.ext h.symm
          rw [this]; exact hαβ
      obtain ⟨j, hMj, hne_j, hmode⟩ := ih (α ⟨M, hM1⟩) ⟨i, hMi', hne_i⟩
      refine ⟨j, by omega, hne_j, ?_⟩
      show (j.val < leafDepth (children (α ⟨M, hM1⟩)) α
              ∧ j.val < leafDepth (children (β ⟨M, hM1⟩)) β)
           ∨ (leafDepth (children (α ⟨M, hM1⟩)) α ≤ j.val
              ∧ leafDepth (children (β ⟨M, hM1⟩)) β ≤ j.val)
      rw [show children (β ⟨M, hM1⟩) = children (α ⟨M, hM1⟩) by rw [hαβ]]
      exact hmode
    · -- Different at M; take j = ⟨M, hM1⟩, both leaf depths > M
      refine ⟨⟨M, hM1⟩, Nat.le_refl _, hαβ, Or.inl ⟨?_, ?_⟩⟩
      · show M < leafDepth (children (α ⟨M, hM1⟩)) α
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (le_leafDepth _ _)
      · show M < leafDepth (children (β ⟨M, hM1⟩)) β
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (le_leafDepth _ _)

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
  set Dα := leafDepth T α with hDα
  set Dβ := leafDepth T β with hDβ
  -- Step 1: factor each `basisEval` via the closed form and combine the products.
  have step1 : ∀ σ : FiniteRadixSpace b k,
      basisEval T α σ * basisEval T β σ
      = ∏ i : Fin (k+1), pCompAt 0 Dα α i (σ i) * pCompAt 0 Dβ β i (σ i) := by
    intro σ
    rw [basisEval_eq_prod T α σ, basisEval_eq_prod T β σ, ← Finset.prod_mul_distrib]
  simp_rw [step1]
  -- Step 2: sum-product exchange `∑ σ ∏ i = ∏ i ∑ d`.
  rw [show (∑ σ : FiniteRadixSpace b k,
            ∏ i : Fin (k+1), pCompAt 0 Dα α i (σ i) * pCompAt 0 Dβ β i (σ i))
        = ∏ i : Fin (k+1), ∑ d : Fin (b i), pCompAt 0 Dα α i d * pCompAt 0 Dβ β i d from ?_]
  · -- Step 3: at the first-difference position `j`, the factor `∑ d` is `0`.
    have hex : ∃ i : Fin (k + 1), (0 : ℕ) ≤ i.val ∧ α i ≠ β i := by
      by_contra hall
      push_neg at hall
      exact hne (funext fun i => hall i (Nat.zero_le _))
    obtain ⟨j, _, hne_j, hmode⟩ := firstDiffMode_gen α β T hex
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rcases hmode with ⟨hjα, hjβ⟩ | ⟨hjα, hjβ⟩
    · -- both in the split-indicator mode: factor `= ∑ d 𝟙[d=α j]·𝟙[d=β j] = 0` (`α j ≠ β j`)
      have hfact : ∀ d : Fin (b j), pCompAt 0 Dα α j d * pCompAt 0 Dβ β j d
            = (if d = α j then (1:ℝ) else 0) * (if d = β j then (1:ℝ) else 0) := by
        intro d
        simp only [pCompAt]
        rw [if_neg (Nat.not_lt_zero _), if_pos hjα,
            if_neg (Nat.not_lt_zero _), if_pos hjβ]
      simp_rw [hfact]
      apply Finset.sum_eq_zero
      intro d _
      by_cases hd : d = α j
      · have hd' : d ≠ β j := fun h => hne_j (hd ▸ h)
        rw [if_pos hd, if_neg hd']
        ring
      · rw [if_neg hd]
        ring
    · -- both in the Haar mode: factor `= ∑ d hc(α j,d)·hc(β j,d) = 0` (`haarComponent_inner`)
      have hfact : ∀ d : Fin (b j), pCompAt 0 Dα α j d * pCompAt 0 Dβ β j d
            = haarComponent j (α j) d * haarComponent j (β j) d := by
        intro d
        simp only [pCompAt]
        rw [if_neg (Nat.not_lt_zero _), if_neg (Nat.not_lt.mpr hjα),
            if_neg (Nat.not_lt_zero _), if_neg (Nat.not_lt.mpr hjβ)]
      simp_rw [hfact]
      rw [haarComponent_inner j (α j) (β j), if_neg hne_j]
  · show ∑ σ : ((i : Fin (k+1)) → Fin (b i)), _ = _
    exact (Fintype.prod_sum (fun i d => pCompAt 0 Dα α i d * pCompAt 0 Dβ β i d)).symm

/-- **Packet basis squared norm**: for a tree at level 0, the squared norm of
    `basisEval T α` depends on the leaf depth that `α` reaches. -/
theorem packetBasis_norm_sq (T : PacketTree b k 0) (α : HaarAtom b k) :
    ∑ σ : FiniteRadixSpace b k, basisEval T α σ * basisEval T α σ =
    (tailProduct b k (leafDepth T α) : ℝ) := by
  set D := leafDepth T α with hD
  -- Step 1: factor each `basisEval` via the closed form and combine.
  have step1 : ∀ σ : FiniteRadixSpace b k,
      basisEval T α σ * basisEval T α σ
      = ∏ i : Fin (k+1), pCompAt 0 D α i (σ i) * pCompAt 0 D α i (σ i) := by
    intro σ
    rw [basisEval_eq_prod T α σ, ← Finset.prod_mul_distrib]
  simp_rw [step1]
  -- Step 2: sum-product exchange.
  rw [show (∑ σ : FiniteRadixSpace b k,
            ∏ i : Fin (k+1), pCompAt 0 D α i (σ i) * pCompAt 0 D α i (σ i))
        = ∏ i : Fin (k+1), ∑ d : Fin (b i), pCompAt 0 D α i d * pCompAt 0 D α i d from ?_]
  · -- Step 3: per-position sum: `1` for split levels, `b i` for Haar levels.
    have hperi : ∀ i : Fin (k+1),
        (∑ d : Fin (b i), pCompAt 0 D α i d * pCompAt 0 D α i d)
        = if D ≤ i.val then (b i : ℝ) else 1 := by
      intro i
      by_cases h : i.val < D
      · -- split-indicator mode: ∑_d 𝟙[d=α i]² = 1
        rw [if_neg (Nat.not_le_of_lt h)]
        have hfact : ∀ d : Fin (b i), pCompAt 0 D α i d * pCompAt 0 D α i d
              = if d = α i then (1:ℝ) else 0 := by
          intro d
          simp only [pCompAt]
          rw [if_neg (Nat.not_lt_zero _), if_pos h]
          by_cases hd : d = α i
          · simp [hd]
          · simp [hd]
        simp_rw [hfact]
        rw [Finset.sum_ite_eq']
        simp
      · -- Haar mode: ∑_d hc(α i,d)² = b i  (`haarComponent_inner i (α i) (α i)`)
        rw [if_pos (Nat.not_lt.mp h)]
        have hfact : ∀ d : Fin (b i), pCompAt 0 D α i d * pCompAt 0 D α i d
              = haarComponent i (α i) d * haarComponent i (α i) d := by
          intro d
          simp only [pCompAt]
          rw [if_neg (Nat.not_lt_zero _), if_neg h]
        simp_rw [hfact]
        rw [haarComponent_inner i (α i) (α i)]
        simp
    simp_rw [hperi]
    -- Step 4: the resulting product is `tailProduct b k D`.
    exact (tailProduct_eq_prod_fin D).symm
  · show ∑ σ : ((i : Fin (k+1)) → Fin (b i)), _ = _
    exact (Fintype.prod_sum (fun i d => pCompAt 0 D α i d * pCompAt 0 D α i d)).symm

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
  rw [fromDepthBound, full]
  by_cases h : L ≤ k
  · rw [dif_pos ⟨h, by omega⟩, dif_pos h]
    congr 1
    funext _
    exact fromDepthBound_full hd (L + 1)
  · rw [dif_neg (fun hc => h hc.1), dif_neg h]
  termination_by k + 1 - L

/-- Leaf count of the threshold tree from level `L`: `∏_{i=L}^{d-1} b_i`. -/
theorem fromDepthBound_leafCount_aux (hd : d ≤ k + 1) (L : ℕ) :
    (fromDepthBound b k d L).leafCount = ∏ i ∈ Finset.Ico L d, b i := by
  rw [fromDepthBound]
  by_cases h : L ≤ k ∧ L < d
  · rw [dif_pos h]
    simp only [leafCount]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
        fromDepthBound_leafCount_aux hd (L + 1)]
    have hsplit : Finset.Ico L d = insert L (Finset.Ico (L + 1) d) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    rw [hsplit, Finset.prod_insert (by simp only [Finset.mem_Ico]; omega)]
  · rw [dif_neg h]
    simp only [leafCount]
    rw [Finset.Ico_eq_empty (by omega), Finset.prod_empty]
  termination_by k + 1 - L

theorem fromDepthBound_leaf_count (hd : d ≤ k + 1) :
    (fromDepthBound b k d 0).leafCount =
    if d = 0 then 1 else ∏ i ∈ Finset.range d, b i := by
  rw [fromDepthBound_leafCount_aux hd 0, ← Finset.range_eq_Ico]
  by_cases hd0 : d = 0
  · subst hd0; simp
  · rw [if_neg hd0]

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
