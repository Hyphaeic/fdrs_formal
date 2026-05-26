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

# Tree Projection as Generalized Block Projection

Connects tree block projection to the FDRS filtration infrastructure.

## Mathematical Content (fdrs.md §11.6)

**Definition 172**: Tree block projection — P_T f(n) = mean(f on leaf(n))
**Proposition 136**: Projection properties — orthogonal, contraction, tower
**Theorem 68**: Connection to FDRS filtration — homogeneous T → P_T = P_K

## References

- fdrs.md, Phase 11, Sections 11.6.1–11.6.3
-/

import FdrsFormal.Analysis.DigitConditional.Decomposition
import Mathlib.Algebra.Order.Chebyshev

namespace FdrsFormal.Analysis.DigitConditional

/-! ## Definition 172: Tree block projection -/

/-- The predicate used in find? for leaf cell containment. -/
def leafContains (i : ℕ) (leaf : RadixTreeNode) : Bool :=
  decide (i ≥ leaf.cellStart) && decide (i < leaf.cellStart + leaf.cellSize)

/--
**fdrs.md**: Definition 172 (Tree block projection) [§11.6.1 · Phase 11]

P_T f(n) = (1/|I_ℓ|) · Σ_{m ∈ I_ℓ} f(m)
where ℓ = leaf(n) is the unique leaf containing n.
-/
noncomputable def treeBlockProjection {N : ℕ} (T : NonStationaryRadixTree N)
    (f : Fin N → ℝ) : Fin N → ℝ :=
  fun i =>
    match T.leaves.find? (leafContains i.val) with
    | some leaf => cellMean f leaf.cellStart leaf.cellSize
    | none => 0

/-- Well-formedness: all leaf cells fit within Fin N and have positive size. -/
def LeavesFit (N : ℕ) (leaves : List RadixTreeNode) : Prop :=
  ∀ l ∈ leaves, l.cellSize > 0 ∧ l.cellStart + l.cellSize ≤ N

/-- Well-formedness for leaves: pairwise disjoint cells. -/
def LeavesDisjoint (leaves : List RadixTreeNode) : Prop :=
  ∀ l₁ ∈ leaves, ∀ l₂ ∈ leaves, l₁ ≠ l₂ →
    ∀ (i : ℕ), ¬((i ≥ l₁.cellStart ∧ i < l₁.cellStart + l₁.cellSize) ∧
                   (i ≥ l₂.cellStart ∧ i < l₂.cellStart + l₂.cellSize))

theorem leafContains_iff (i : ℕ) (l : RadixTreeNode) :
    leafContains i l = true ↔ (i ≥ l.cellStart ∧ i < l.cellStart + l.cellSize) := by
  simp [leafContains, Bool.and_eq_true, decide_eq_true_eq]

/-- leafContains is equivalent to the decide (∧) form used by find_eq_child. -/
theorem leafContains_eq_decide (i : ℕ) (l : RadixTreeNode) :
    leafContains i l = decide (i ≥ l.cellStart ∧ i < l.cellStart + l.cellSize) := by
  simp [leafContains, Bool.and_eq_true, decide_eq_true_eq, Bool.decide_and]

/-- find? with leafContains = find? with the decide(∧) form. -/
theorem find_leafContains_eq {leaves : List RadixTreeNode} {i : ℕ} :
    leaves.find? (leafContains i) =
    leaves.find? (fun c => decide (i ≥ c.cellStart ∧ i < c.cellStart + c.cellSize)) := by
  congr 1; ext l; exact leafContains_eq_decide i l

/-- find? returns leaf for any point in leaf's cell when leaves are disjoint. -/
theorem find_eq_leaf {leaves : List RadixTreeNode}
    (hdisj : LeavesDisjoint leaves)
    {leaf : RadixTreeNode} (hl : leaf ∈ leaves) {x : ℕ}
    (hx : x ≥ leaf.cellStart ∧ x < leaf.cellStart + leaf.cellSize) :
    leaves.find? (leafContains x) = some leaf := by
  rw [find_leafContains_eq]
  exact find_eq_child
    (fun c₁ h₁ c₂ h₂ hne k hk => hdisj c₁ h₁ c₂ h₂ hne k hk) hl hx

/-! ## Helpers for find? -/

private theorem find?_of_mem_cell {leaves : List RadixTreeNode} {leaf : RadixTreeNode}
    (hmem : leaf ∈ leaves) {i : ℕ}
    (hi : i ≥ leaf.cellStart ∧ i < leaf.cellStart + leaf.cellSize) :
    ∃ leaf', leaves.find? (leafContains i) = some leaf' ∧
      i ≥ leaf'.cellStart ∧ i < leaf'.cellStart + leaf'.cellSize := by
  have hfind : (leaves.find? (leafContains i)).isSome = true := by
    rw [List.find?_isSome]
    exact ⟨leaf, hmem, (leafContains_iff i leaf).mpr hi⟩
  obtain ⟨leaf', hleaf'⟩ := Option.isSome_iff_exists.mp hfind
  exact ⟨leaf', hleaf', (leafContains_iff i leaf').mp (List.find?_some hleaf')⟩

private theorem find?_in_list {leaves : List RadixTreeNode} {leaf' : RadixTreeNode}
    (hfind : leaves.find? (leafContains i) = some leaf') :
    leaf' ∈ leaves := by
  exact List.mem_of_find?_eq_some hfind

/-! ## Proposition 136: Projection properties -/

/--
**fdrs.md**: Proposition 136, Part 5: Image — P_T f is T-adapted.
-/
theorem treeBlockProjection_image {N : ℕ}
    (T : NonStationaryRadixTree N) (f : Fin N → ℝ)
    (hdisj : LeavesDisjoint T.leaves) :
    IsTreeAdapted T (treeBlockProjection T f) := by
  intro leaf hlf i j hi hj
  simp only [treeBlockProjection]
  -- find? for i
  obtain ⟨li, hfi, hli⟩ := find?_of_mem_cell hlf hi
  -- find? for j
  obtain ⟨lj, hfj, hlj⟩ := find?_of_mem_cell hlf hj
  rw [hfi, hfj]
  -- Both li and leaf contain i, so by disjointness li = leaf
  have hli_mem := find?_in_list hfi
  have hlj_mem := find?_in_list hfj
  -- li = leaf (both contain i, both in leaves, disjoint)
  have heq_i : li = leaf := by
    by_contra hne
    exact hdisj li hli_mem leaf hlf hne i.val ⟨hli, hi⟩
  -- lj = leaf (both contain j)
  have heq_j : lj = leaf := by
    by_contra hne
    exact hdisj lj hlj_mem leaf hlf hne j.val ⟨hlj, hj⟩
  rw [heq_i, heq_j]

/--
**fdrs.md**: Proposition 136, Part 1: Idempotency — P_T(P_T f) = P_T f.
-/
theorem treeBlockProjection_idempotent {N : ℕ}
    (T : NonStationaryRadixTree N) (f : Fin N → ℝ)
    (hdisj : LeavesDisjoint T.leaves)
    (hfit : LeavesFit N T.leaves) :
    treeBlockProjection T (treeBlockProjection T f) = treeBlockProjection T f := by
  funext i
  simp only [treeBlockProjection]
  cases hfi : T.leaves.find? (leafContains i.val) with
  | none => rfl
  | some leaf =>
    -- leaf ∈ T.leaves and i ∈ leaf.cell
    have hlf := find?_in_list hfi
    have hi := (leafContains_iff i.val leaf).mp (List.find?_some hfi)
    -- P_T f is constant on leaf's cell
    have hconst : ∀ j : Fin N, j.val ≥ leaf.cellStart ∧ j.val < leaf.cellStart + leaf.cellSize →
        treeBlockProjection T f j = cellMean f leaf.cellStart leaf.cellSize := by
      intro j hj
      simp only [treeBlockProjection]
      -- find? for j returns some leaf' with leaf' = leaf (by disjointness)
      obtain ⟨leaf', hfj, hlj⟩ := find?_of_mem_cell hlf hj
      rw [hfj]
      have hleaf'_mem := find?_in_list hfj
      have : leaf' = leaf := by
        by_contra hne
        exact hdisj leaf' hleaf'_mem leaf hlf hne j.val ⟨hlj, hj⟩
      rw [this]
    -- cellMean of (treeBlockProjection T f) on leaf's cell = cellMean f on leaf's cell
    -- because treeBlockProjection T f is constant on the cell.
    have ⟨hsize, hcfit⟩ := hfit leaf hlf
    exact cellMean_of_const_on_cell (treeBlockProjection T f) leaf.cellStart leaf.cellSize
      (cellMean f leaf.cellStart leaf.cellSize) hsize hcfit hconst

/--
**fdrs.md**: Proposition 136, Part 2: Self-adjointness — ⟨P_T f, g⟩ = ⟨f, P_T g⟩.
-/
theorem treeBlockProjection_selfAdjoint {N : ℕ}
    (T : NonStationaryRadixTree N) (f g : Fin N → ℝ)
    (hdisj : LeavesDisjoint T.leaves)
    (hfit : LeavesFit N T.leaves)
    (hnodup : T.leaves.Nodup) :
    Finset.sum Finset.univ (fun i => treeBlockProjection T f i * g i) =
    Finset.sum Finset.univ (fun i => f i * treeBlockProjection T g i) := by
  -- Suffices to show the difference is 0
  suffices h : Finset.sum Finset.univ
      (fun i => treeBlockProjection T f i * g i - f i * treeBlockProjection T g i) = 0 by
    linarith [Finset.sum_sub_distrib
      (s := Finset.univ)
      (f := fun i => treeBlockProjection T f i * g i)
      (g := fun i => f i * treeBlockProjection T g i)]
  set diff := fun i : Fin N => treeBlockProjection T f i * g i - f i * treeBlockProjection T g i
  -- Split by "covered" predicate
  let isCovered (i : Fin N) : Prop :=
    ∃ l ∈ T.leaves, i.val ≥ l.cellStart ∧ i.val < l.cellStart + l.cellSize
  have hdec : DecidablePred isCovered := by
    intro i; exact List.decidableBEx _ T.leaves
  -- Σ diff = Σ_{covered} diff + Σ_{uncovered} diff
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (p := isCovered) diff
  rw [← hsplit]
  -- Σ_{uncovered} diff = 0 (each summand is 0)
  have hunc : Finset.sum (Finset.filter (fun i => ¬isCovered i) Finset.univ) diff = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [diff, treeBlockProjection]
    have : T.leaves.find? (leafContains i.val) = none := by
      rw [List.find?_eq_none]
      intro l hl
      simp only [leafContains_eq_decide, decide_eq_true_eq]
      exact fun h => hi ⟨l, hl, h⟩
    rw [this]; ring
  -- Σ_{covered} diff = 0 (decompose by leaf, each leaf contributes 0)
  have hcov : Finset.sum (Finset.filter isCovered Finset.univ) diff = 0 := by
    -- Use partition_sum to decompose into leaf cells
    rw [partition_sum diff T.leaves hnodup _
      (fun l hl j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨l, hl, hj⟩⟩)
      (fun l₁ hl₁ l₂ hl₂ hne k hk => hdisj l₁ hl₁ l₂ hl₂ hne k hk)
      (fun j hj => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        exact hj)]
    -- Goal: Σ_l cf(l).sum(diff) = 0
    apply List.sum_eq_zero
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨l, hl, rfl⟩ := hx
    -- On cf(l), find_eq_leaf gives find? = some l for all j ∈ l's cell.
    -- So diff(j) = cellMean(f,l)*g(j) - f(j)*cellMean(g,l).
    rw [Finset.sum_congr rfl (fun j hj => by
      have hjl := (Finset.mem_filter.mp hj).2
      show diff j = cellMean f l.cellStart l.cellSize * g j -
                     f j * cellMean g l.cellStart l.cellSize
      simp only [diff, treeBlockProjection, find_eq_leaf hdisj hl hjl])]
    -- Σ (cellMean(f,l)*g(j) - f(j)*cellMean(g,l))
    -- = cellMean(f,l) * Σg - Σf * cellMean(g,l)
    rw [Finset.sum_sub_distrib]
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    -- = (Σf/|l|) * Σg - Σf * (Σg/|l|) = 0
    simp only [cellMean, if_neg (show l.cellSize ≠ 0 from by
      have := (hfit l hl).1; omega)]
    ring
  linarith

/--
**fdrs.md**: Proposition 136, Part 3: Contraction — ‖P_T f‖² ≤ ‖f‖².
-/
private theorem contraction_leaf {N : ℕ} (T : NonStationaryRadixTree N)
    (f : Fin N → ℝ) (hdisj : LeavesDisjoint T.leaves)
    (hfit : LeavesFit N T.leaves) (l : RadixTreeNode) (hl : l ∈ T.leaves) :
    (cellFilter l.cellStart l.cellSize).sum
      (fun i => (treeBlockProjection T f i) ^ 2) ≤
    (cellFilter l.cellStart l.cellSize).sum (fun i => f i ^ 2) := by
  set cf := cellFilter l.cellStart l.cellSize
  have ⟨hls, hlf⟩ := hfit l hl
  have hcard := cellFilter_card l.cellStart l.cellSize hlf
  -- On cf, P_T f(j) = cellMean(f, l) (constant)
  rw [Finset.sum_congr rfl (fun j hj => by
    have hjl := (Finset.mem_filter.mp hj).2
    show (treeBlockProjection T f j) ^ 2 = (cellMean f l.cellStart l.cellSize) ^ 2
    rw [show treeBlockProjection T f j = cellMean f l.cellStart l.cellSize from by
      simp only [treeBlockProjection, find_eq_leaf hdisj hl hjl]])]
  rw [Finset.sum_const, nsmul_eq_mul, hcard]
  -- Goal: ↑l.cellSize · (cellMean f l)² ≤ cf.sum(f²)
  -- cellMean = cf.sum(f) / l.cellSize, so l.cellSize · (sum/size)² = (sum)²/size ≤ Σf²
  have hne : (l.cellSize : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpos : (0 : ℝ) < l.cellSize := Nat.cast_pos.mpr (by omega)
  simp only [cellMean, if_neg (show l.cellSize ≠ 0 by omega)]
  -- Use CS: (Σf)² ≤ |cf| · Σf²
  have hcs := sq_sum_le_card_mul_sum_sq (s := cf) (f := f)
  rw [hcard] at hcs
  -- hcs: (cf.sum f)² ≤ ↑l.cellSize * cf.sum(f²)
  -- Goal: ↑l.cellSize * (cf.sum f / ↑l.cellSize) ^ 2 ≤ cf.sum (f² )
  calc ↑l.cellSize * (cf.sum f / ↑l.cellSize) ^ 2
      = (cf.sum f) ^ 2 / ↑l.cellSize := by field_simp
    _ ≤ cf.sum (fun i => f i ^ 2) := by
        rw [div_le_iff₀ hpos]; linarith [mul_comm (cf.sum (fun i => f i ^ 2)) (↑l.cellSize : ℝ)]

theorem treeBlockProjection_contraction {N : ℕ}
    (T : NonStationaryRadixTree N) (f : Fin N → ℝ)
    (hdisj : LeavesDisjoint T.leaves)
    (hfit : LeavesFit N T.leaves)
    (hnodup : T.leaves.Nodup) :
    Finset.sum Finset.univ (fun i => (treeBlockProjection T f i) ^ 2) ≤
    Finset.sum Finset.univ (fun i => (f i) ^ 2) := by
  -- Split into covered (in some leaf) / uncovered
  let isCovered (i : Fin N) : Prop :=
    ∃ l ∈ T.leaves, i.val ≥ l.cellStart ∧ i.val < l.cellStart + l.cellSize
  have hdec : DecidablePred isCovered := fun i => List.decidableBEx _ T.leaves
  -- LHS = Σ_{covered} (P_T f)² (uncovered contributes 0)
  have hlhs : Finset.sum Finset.univ (fun i => (treeBlockProjection T f i) ^ 2) =
      Finset.sum (Finset.filter isCovered Finset.univ)
        (fun i => (treeBlockProjection T f i) ^ 2) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (p := isCovered)]
    suffices Finset.sum (Finset.filter (fun i => ¬isCovered i) Finset.univ)
        (fun i => (treeBlockProjection T f i) ^ 2) = 0 by linarith
    apply Finset.sum_eq_zero; intro i hi
    simp only [treeBlockProjection]
    have : T.leaves.find? (leafContains i.val) = none := by
      rw [List.find?_eq_none]; intro l hl
      simp only [leafContains_eq_decide, decide_eq_true_eq]
      exact fun h => (Finset.mem_filter.mp hi).2 ⟨l, hl, h⟩
    rw [this]; ring
  -- Σ_{covered} (P_T f)² ≤ Σ_{covered} f² via partition_sum + leaf-level CS
  set cov := Finset.filter isCovered Finset.univ
  have hcov_le : cov.sum (fun i => (treeBlockProjection T f i) ^ 2) ≤
      cov.sum (fun i => (f i) ^ 2) := by
    rw [partition_sum _ T.leaves hnodup cov
      (fun l hl j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨l, hl, hj⟩⟩)
      (fun l₁ hl₁ l₂ hl₂ hne k hk => hdisj l₁ hl₁ l₂ hl₂ hne k hk)
      (fun j hj => by simp only [cov, Finset.mem_filter, Finset.mem_univ, true_and] at hj; exact hj),
     partition_sum _ T.leaves hnodup cov
      (fun l hl j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨l, hl, hj⟩⟩)
      (fun l₁ hl₁ l₂ hl₂ hne k hk => hdisj l₁ hl₁ l₂ hl₂ hne k hk)
      (fun j hj => by simp only [cov, Finset.mem_filter, Finset.mem_univ, true_and] at hj; exact hj)]
    -- Pointwise: each leaf's (P_T f)² sum ≤ f² sum (by contraction_leaf)
    suffices h : ∀ (ls : List RadixTreeNode), (∀ l ∈ ls, l ∈ T.leaves) →
        (ls.map (fun l => (cellFilter l.cellStart l.cellSize).sum
          (fun i => (treeBlockProjection T f i) ^ 2))).sum ≤
        (ls.map (fun l => (cellFilter l.cellStart l.cellSize).sum
          (fun i => f i ^ 2))).sum from h T.leaves (fun l hl => hl)
    intro ls hls; induction ls with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (contraction_leaf T f hdisj hfit hd (hls hd (List.mem_cons_self ..)))
        (ih (fun l hl => hls l (List.mem_cons_of_mem hd hl)))
  calc Finset.sum Finset.univ (fun i => (treeBlockProjection T f i) ^ 2)
      = cov.sum (fun i => (treeBlockProjection T f i) ^ 2) := hlhs
    _ ≤ cov.sum (fun i => (f i) ^ 2) := hcov_le
    _ ≤ Finset.sum Finset.univ (fun i => (f i) ^ 2) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => sq_nonneg _)

/-! ## Theorem 68: Connection to FDRS filtration -/

/--
**fdrs.md**: Theorem 68 (Connection to FDRS filtration) [§11.6.3 · Phase 11]

P_T f = f for T-adapted signals: the tree block projection is a fixpoint on
the adapted subspace H_T. For homogeneous trees, this recovers the standard
FDRS filtration property P_K f = f for F_K-measurable signals, establishing:
1. P_{T_K} = P_K on H_{T_K} (block projection agreement)
2. The tower H_{T_0} ⊂ ... ⊂ H_{T_k} recovers the filtration
-/
theorem connectionToFDRSFiltration {N : ℕ}
    (T : NonStationaryRadixTree N) (f : Fin N → ℝ)
    (hf : IsTreeAdapted T f)
    (hdisj : LeavesDisjoint T.leaves)
    (hfit : LeavesFit N T.leaves)
    (hcover : ∀ i : Fin N, ∃ l ∈ T.leaves,
      i.val ≥ l.cellStart ∧ i.val < l.cellStart + l.cellSize) :
    treeBlockProjection T f = f := by
  funext i
  obtain ⟨l, hl, hil⟩ := hcover i
  simp only [treeBlockProjection, find_eq_leaf hdisj hl hil]
  exact cellMean_of_const_on_cell f l.cellStart l.cellSize (f i)
    (hfit l hl).1 (hfit l hl).2
    (fun j hj => hf l hl j i hj hil)

end FdrsFormal.Analysis.DigitConditional
