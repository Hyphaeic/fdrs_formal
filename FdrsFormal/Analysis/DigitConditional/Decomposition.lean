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

# Orthogonal Layer Decomposition

Orthogonal decomposition of tree-adapted signals into mean + node layers.

## Mathematical Content (fdrs.md §11.2)

**Definition 166**: Tree-adapted signal — f constant on each leaf cell
**Definition 167**: Node projection and layer — P_v averaging, g_v = child means - parent mean
**Lemma 5**: Within-node layer properties — mean-zero, block-constant, supported on I_v
**Theorem 65**: Orthogonal decomposition — f = μ + Σg_v, orthogonality, Parseval
**Corollary 30**: Exact adapted signals — f ∈ H_T implies exact reconstruction

## References

- fdrs.md, Phase 11, Sections 11.2.1–11.2.5
-/

import FdrsFormal.Analysis.DigitConditional.Tree

namespace FdrsFormal.Analysis.DigitConditional

/-! ## Definition 166: Tree-adapted signal -/

/--
**fdrs.md**: Definition 166 (Tree-adapted signal) [§11.2.1 · Phase 11]

A signal f : Fin N → ℝ is T-adapted if it is constant on each leaf cell of T.
The space H_T has dimension |Leaves(T)|.
-/
def IsTreeAdapted {N : ℕ} (T : NonStationaryRadixTree N) (f : Fin N → ℝ) : Prop :=
  ∀ leaf ∈ T.leaves, ∀ (i j : Fin N),
    (i.val ≥ leaf.cellStart ∧ i.val < leaf.cellStart + leaf.cellSize) →
    (j.val ≥ leaf.cellStart ∧ j.val < leaf.cellStart + leaf.cellSize) →
    f i = f j

/-- The subspace of T-adapted signals. -/
def treeAdaptedSubspace {N : ℕ} (T : NonStationaryRadixTree N) :
    Set (Fin N → ℝ) :=
  {f | IsTreeAdapted T f}

/-! ## Definition 167: Node projection and layer -/

/-- The mean of f over indices in the range [start, start + size). -/
noncomputable def cellMean {N : ℕ} (f : Fin N → ℝ) (start size : ℕ) : ℝ :=
  if size = 0 then 0
  else (Finset.sum (Finset.filter
    (fun j : Fin N => j.val ≥ start ∧ j.val < start + size)
    Finset.univ) f) / size

/-! ### CellMean infrastructure -/

/-- The cell filter for [start, start+size) in Fin N. -/
abbrev cellFilter {N : ℕ} (start size : ℕ) : Finset (Fin N) :=
  Finset.filter (fun j : Fin N => j.val ≥ start ∧ j.val < start + size) Finset.univ

/-- Cardinality of cellFilter when the cell fits within Fin N. -/
theorem cellFilter_card {N : ℕ} (start size : ℕ)
    (hfit : start + size ≤ N) :
    (cellFilter (N := N) start size).card = size := by
  -- Build an explicit bijection between cellFilter and Fin size
  let f : Fin size → Fin N := fun k => ⟨start + k.val, by omega⟩
  have hinj : Function.Injective f :=
    fun a b h => Fin.ext (by simp [f, Fin.val_mk] at h; omega)
  -- Show card ≥ size (injection from Fin size)
  have hge : size ≤ (cellFilter (N := N) start size).card := by
    calc size = (Finset.univ : Finset (Fin size)).card := by simp
      _ ≤ (Finset.image f Finset.univ).card :=
          le_of_eq (Finset.card_image_of_injective _ hinj).symm
      _ ≤ (cellFilter (N := N) start size).card := by
          apply Finset.card_le_card
          intro j hj
          simp only [Finset.mem_image, Finset.mem_univ, true_and] at hj
          obtain ⟨k, rfl⟩ := hj
          simp only [cellFilter, Finset.mem_filter, Finset.mem_univ, true_and, f, Fin.val_mk]
          omega
  -- Show card ≤ size (surjection back)
  have hle : (cellFilter (N := N) start size).card ≤ size := by
    calc (cellFilter (N := N) start size).card
        ≤ (Finset.image f Finset.univ).card := by
          apply Finset.card_le_card
          intro ⟨j, hj⟩ hmem
          simp only [cellFilter, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
          simp only [Finset.mem_image, Finset.mem_univ, true_and]
          exact ⟨⟨j - start, by omega⟩, Fin.ext (by simp [f]; omega)⟩
      _ = size := by rw [Finset.card_image_of_injective _ hinj]; simp
  omega

/-- cellMean of a constant function equals the constant (when cell fits in Fin N). -/
theorem cellMean_const {N : ℕ} (c : ℝ) (start size : ℕ)
    (hsize : size > 0) (hfit : start + size ≤ N) :
    cellMean (N := N) (fun _ => c) start size = c := by
  simp only [cellMean, if_neg (by omega : size ≠ 0)]
  rw [Finset.sum_const, cellFilter_card start size hfit, nsmul_eq_mul]
  have : (size : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

/-- cellMean when f is constant with value c on the cell. -/
theorem cellMean_of_const_on_cell {N : ℕ} (f : Fin N → ℝ) (start size : ℕ) (c : ℝ)
    (hsize : size > 0) (hfit : start + size ≤ N)
    (hconst : ∀ j : Fin N, j.val ≥ start ∧ j.val < start + size → f j = c) :
    cellMean f start size = c := by
  have : cellMean f start size = cellMean (N := N) (fun _ => c) start size := by
    simp only [cellMean, if_neg (by omega : size ≠ 0)]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    exact hconst j (Finset.mem_filter.mp hj).2
  rw [this, cellMean_const (N := N) c start size hsize hfit]

/-! ### Partition sum decomposition -/

/-- Key partition lemma: the sum of f over a parent cell equals the sum of
    sums of f over child cells, when children form a partition of the parent. -/
theorem partition_sum {N : ℕ} (f : Fin N → ℝ) (children : List RadixTreeNode)
    (hnodup : children.Nodup)
    (S : Finset (Fin N))
    (hsub : ∀ c ∈ children, ∀ j : Fin N,
      j.val ≥ c.cellStart ∧ j.val < c.cellStart + c.cellSize → j ∈ S)
    (hdisj : ∀ c₁ ∈ children, ∀ c₂ ∈ children, c₁ ≠ c₂ →
      ∀ (k : ℕ), ¬((k ≥ c₁.cellStart ∧ k < c₁.cellStart + c₁.cellSize) ∧
                     (k ≥ c₂.cellStart ∧ k < c₂.cellStart + c₂.cellSize)))
    (hcover : ∀ j ∈ S,
      ∃ c ∈ children, j.val ≥ c.cellStart ∧ j.val < c.cellStart + c.cellSize) :
    S.sum f = (children.map (fun c =>
      (Finset.filter (fun j : Fin N =>
        j.val ≥ c.cellStart ∧ j.val < c.cellStart + c.cellSize) Finset.univ).sum f)).sum := by
  -- Generalize over S so the IH is universally quantified
  suffices h : ∀ (S : Finset (Fin N)),
    (∀ c ∈ children, ∀ j : Fin N,
      j.val ≥ c.cellStart ∧ j.val < c.cellStart + c.cellSize → j ∈ S) →
    (∀ c₁ ∈ children, ∀ c₂ ∈ children, c₁ ≠ c₂ →
      ∀ (k : ℕ), ¬((k ≥ c₁.cellStart ∧ k < c₁.cellStart + c₁.cellSize) ∧
                     (k ≥ c₂.cellStart ∧ k < c₂.cellStart + c₂.cellSize))) →
    (∀ j ∈ S, ∃ c ∈ children, j.val ≥ c.cellStart ∧ j.val < c.cellStart + c.cellSize) →
    S.sum f = (children.map (fun c =>
      (Finset.filter (fun j : Fin N =>
        j.val ≥ c.cellStart ∧ j.val < c.cellStart + c.cellSize) Finset.univ).sum f)).sum from
    h S hsub hdisj hcover
  clear hsub hdisj hcover S
  induction children with
  | nil =>
    intro S hsub hdisj hcover
    simp only [List.map_nil, List.sum_nil]
    apply Finset.sum_eq_zero
    intro j hj
    obtain ⟨c, hc, _⟩ := hcover j hj
    simp at hc
  | cons c cs ih =>
    intro S hsub hdisj hcover
    simp only [List.map_cons, List.sum_cons]
    let cf := Finset.filter (fun j : Fin N =>
      j.val ≥ c.cellStart ∧ j.val < c.cellStart + c.cellSize) Finset.univ
    have hcf_sub : cf ⊆ S := by
      intro j hj
      exact hsub c (List.mem_cons_self ..) j (Finset.mem_filter.mp hj).2
    have hunion : S = cf ∪ (S \ cf) := by
      ext j; simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · intro hj; by_cases hjc : j ∈ cf
        · left; exact hjc
        · right; exact ⟨hj, hjc⟩
      · rintro (hj | ⟨hj, _⟩) <;> [exact hcf_sub hj; exact hj]
    rw [hunion, Finset.sum_union disjoint_sdiff_self_right]
    congr 1
    apply ih (List.nodup_cons.mp hnodup).2
    · intro c' hc' j hj
      have hj_S : j ∈ S := hsub c' (List.mem_cons_of_mem c hc') j hj
      refine Finset.mem_sdiff.mpr ⟨hj_S, ?_⟩
      simp only [cf, Finset.mem_filter, Finset.mem_univ, true_and]
      intro hjc
      have hne : c' ≠ c := by
        intro heq; subst heq
        exact (List.nodup_cons.mp hnodup).1 hc'
      exact hdisj c (List.mem_cons_self ..) c' (List.mem_cons_of_mem c hc')
        (Ne.symm hne) j.val ⟨hjc, hj⟩
    · intro c₁ hc₁ c₂ hc₂ hne k
      exact hdisj c₁ (List.mem_cons_of_mem c hc₁) c₂ (List.mem_cons_of_mem c hc₂) hne k
    · intro j hj
      obtain ⟨hj_S, hj_ncf⟩ := Finset.mem_sdiff.mp hj
      obtain ⟨c', hc', hjc'⟩ := hcover j hj_S
      cases hc' with
      | head =>
        exfalso; apply hj_ncf
        simp only [cf, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hjc'
      | tail _ hc'_cs =>
        exact ⟨c', hc'_cs, hjc'⟩

-- tower_property removed — proved inline in withinNodeLayer_meanZero via partition_sum

/--
**fdrs.md**: Definition 167 (Node projection and layer) [§11.2.2 · Phase 11]

Node projection P_v averages f over the cell I_v.
-/
noncomputable def nodeProjection {N : ℕ} (node : RadixTreeNode) (f : Fin N → ℝ) :
    Fin N → ℝ :=
  fun i =>
    if i.val ≥ node.cellStart ∧ i.val < node.cellStart + node.cellSize then
      cellMean f node.cellStart node.cellSize
    else 0

/-- Node layer: the within-node variation at the child level.
    For i in child c_j: g_v(f)(i) = mean(f on c_j) - mean(f on v).
    For i outside all children: g_v(f)(i) = 0. -/
noncomputable def nodeLayer {N : ℕ} (parent : RadixTreeNode)
    (children : List RadixTreeNode) (f : Fin N → ℝ) : Fin N → ℝ :=
  fun i =>
    let parentMean := cellMean f parent.cellStart parent.cellSize
    match children.find? (fun c =>
      decide (i.val ≥ c.cellStart ∧ i.val < c.cellStart + c.cellSize)) with
    | some child => cellMean f child.cellStart child.cellSize - parentMean
    | none => 0

/-! ## Lemma 5: Within-node layer properties -/

/--
**fdrs.md**: Lemma 5 (Within-node layer properties) [§11.2.3 · Phase 11]

Part 3: Supported on I_v — g_v(f)(i) = 0 for i outside the parent cell.
Requires: children cells are subsets of the parent cell.
-/
theorem withinNodeLayer_supported {N : ℕ} (parent : RadixTreeNode)
    (children : List RadixTreeNode) (f : Fin N → ℝ)
    (hsub : ∀ c ∈ children, c.cellStart ≥ parent.cellStart ∧
      c.cellStart + c.cellSize ≤ parent.cellStart + parent.cellSize) :
    ∀ (i : Fin N), ¬(i.val ≥ parent.cellStart ∧ i.val < parent.cellStart + parent.cellSize) →
      nodeLayer parent children f i = 0 := by
  intro i hi
  simp only [nodeLayer]
  -- If i is outside the parent, it's outside every child (by hsub)
  suffices hfind : children.find? (fun c =>
      decide (i.val ≥ c.cellStart ∧ i.val < c.cellStart + c.cellSize)) = none by
    rw [hfind]
  rw [List.find?_eq_none]
  intro c hc
  simp only [decide_eq_true_eq]
  intro ⟨hge, hlt⟩
  have ⟨hcs, hce⟩ := hsub c hc
  exact hi ⟨by omega, by omega⟩

/-- Helper: find? returns `child` for any point in `child`'s cell when children are disjoint. -/
theorem find_eq_child {children : List RadixTreeNode}
    (hdisj : ∀ c₁ ∈ children, ∀ c₂ ∈ children, c₁ ≠ c₂ →
      ∀ (k : ℕ), ¬((k ≥ c₁.cellStart ∧ k < c₁.cellStart + c₁.cellSize) ∧
                     (k ≥ c₂.cellStart ∧ k < c₂.cellStart + c₂.cellSize)))
    {child : RadixTreeNode} (hc : child ∈ children) {x : ℕ}
    (hx : x ≥ child.cellStart ∧ x < child.cellStart + child.cellSize) :
    children.find? (fun c => decide (x ≥ c.cellStart ∧ x < c.cellStart + c.cellSize)) = some child := by
  induction children with
  | nil => simp at hc
  | cons hd tl ih =>
    simp only [List.find?_cons]
    split
    next hpred =>
      -- hd satisfies the predicate for x
      have hpred_val : x ≥ hd.cellStart ∧ x < hd.cellStart + hd.cellSize := by
        rwa [decide_eq_true_eq] at hpred
      -- child also contains x (by hx) and child ∈ hd :: tl
      -- So hd and child both contain x; by disjointness hd = child
      congr
      cases hc with
      | head => rfl
      | tail _ hc_tl =>
        by_contra hne
        exact hdisj hd (List.mem_cons_self ..) child (List.mem_cons_of_mem _ hc_tl)
          hne x ⟨hpred_val, hx⟩
    next hpred =>
      -- hd does NOT contain x, so child ≠ hd
      cases hc with
      | head =>
        -- child = hd, but hd doesn't contain x, contradicting hx
        exfalso
        rw [decide_eq_false_iff_not] at hpred
        exact hpred hx
      | tail _ hc_tl =>
        exact ih (fun c₁ h₁ c₂ h₂ hne k =>
          hdisj c₁ (List.mem_cons_of_mem _ h₁) c₂ (List.mem_cons_of_mem _ h₂) hne k) hc_tl

theorem withinNodeLayer_blockConstant {N : ℕ} (parent : RadixTreeNode)
    (children : List RadixTreeNode) (f : Fin N → ℝ)
    (hdisj : ∀ c₁ ∈ children, ∀ c₂ ∈ children, c₁ ≠ c₂ →
      ∀ (k : ℕ), ¬((k ≥ c₁.cellStart ∧ k < c₁.cellStart + c₁.cellSize) ∧
                     (k ≥ c₂.cellStart ∧ k < c₂.cellStart + c₂.cellSize)))
    (child : RadixTreeNode) (hc : child ∈ children) :
    ∀ (i j : Fin N),
      (i.val ≥ child.cellStart ∧ i.val < child.cellStart + child.cellSize) →
      (j.val ≥ child.cellStart ∧ j.val < child.cellStart + child.cellSize) →
      nodeLayer parent children f i = nodeLayer parent children f j := by
  intro i j hi hj
  simp only [nodeLayer, find_eq_child hdisj hc hi, find_eq_child hdisj hc hj]

/--
**fdrs.md**: Lemma 5, Part 1: Mean-zero on I_v.
The sum of g_v(f) over the parent cell is zero.
-/
theorem withinNodeLayer_meanZero {N : ℕ} (hN : N > 0) (parent : RadixTreeNode)
    (children : List RadixTreeNode) (f : Fin N → ℝ)
    (hpart : (children.map RadixTreeNode.cellSize).sum = parent.cellSize)
    (hsub : ∀ c ∈ children, c.cellStart ≥ parent.cellStart ∧
      c.cellStart + c.cellSize ≤ parent.cellStart + parent.cellSize)
    (hdisj : ∀ c₁ ∈ children, ∀ c₂ ∈ children, c₁ ≠ c₂ →
      ∀ (k : ℕ), ¬((k ≥ c₁.cellStart ∧ k < c₁.cellStart + c₁.cellSize) ∧
                     (k ≥ c₂.cellStart ∧ k < c₂.cellStart + c₂.cellSize)))
    (hcover : ∀ (j : Fin N), j.val ≥ parent.cellStart ∧ j.val < parent.cellStart + parent.cellSize →
      ∃ c ∈ children, j.val ≥ c.cellStart ∧ j.val < c.cellStart + c.cellSize)
    (hnodup : children.Nodup)
    (hpfit : parent.cellStart + parent.cellSize ≤ N)
    (hpsize : parent.cellSize > 0)
    (hcfit : ∀ c ∈ children, c.cellSize > 0 ∧ c.cellStart + c.cellSize ≤ N) :
    Finset.sum (Finset.filter
      (fun j : Fin N => j.val ≥ parent.cellStart ∧ j.val < parent.cellStart + parent.cellSize)
      Finset.univ)
      (nodeLayer parent children f) = 0 := by
  set pf := cellFilter (N := N) parent.cellStart parent.cellSize with hpf_def
  set μ := cellMean f parent.cellStart parent.cellSize with hμ_def
  -- Step 1: Rewrite each summand.
  -- For j ∈ pf, hcover gives child c with j ∈ c's cell.
  -- find_eq_child gives find? = some c.
  -- So nodeLayer = cellMean(f,c) - μ.
  -- The key: nodeLayer is constant on each child cell (= cellMean(f,c) - μ for all j in c).
  -- So: Σ_{j ∈ pf} nodeLayer(j) = Σ_c (|cf(c)| · (cellMean(f,c) - μ))
  --                               = Σ_c |cf(c)| · cellMean(f,c) - (Σ_c |cf(c)|) · μ

  -- Key partition hypothesis for partition_sum
  have hpsub : ∀ c ∈ children, ∀ j : Fin N,
      j.val ≥ c.cellStart ∧ j.val < c.cellStart + c.cellSize → j ∈ pf := by
    intro c hc j hj
    simp only [pf, cellFilter, Finset.mem_filter, Finset.mem_univ, true_and]
    have ⟨hcs, hce⟩ := hsub c hc; omega
  have hpcover : ∀ j ∈ pf,
      ∃ c ∈ children, j.val ≥ c.cellStart ∧ j.val < c.cellStart + c.cellSize := by
    intro j hj
    simp only [pf, cellFilter, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact hcover j hj
  -- Step 2: Decompose pf.sum(nodeLayer) using partition_sum
  rw [partition_sum _ children hnodup pf hpsub hdisj hpcover]
  -- Goal: Σ_c cf(c).sum(nodeLayer) = 0
  -- For each child c, nodeLayer is constant on cf(c) with value cellMean(f,c) - μ.
  -- So cf(c).sum(nodeLayer) = cf(c).sum(f) - |cf(c)| * μ.
  -- Summing over all children: Σ cf(c).sum(f) - (Σ |cf(c)|) * μ.
  -- By partition_sum for f: Σ cf(c).sum(f) = pf.sum(f).
  -- By cellFilter_card: |cf(c)| = c.cellSize when c fits in Fin N.
  -- Σ c.cellSize = parent.cellSize (hpart).
  -- parent.cellSize * μ = parent.cellSize * (pf.sum(f) / parent.cellSize) = pf.sum(f).
  -- So the difference = 0.

  -- Helper: on each child's cell, nodeLayer = cellMean(f,c) - μ
  have hchild_sum : ∀ c ∈ children,
      (cellFilter (N := N) c.cellStart c.cellSize).sum (nodeLayer parent children f) =
      (cellFilter (N := N) c.cellStart c.cellSize).sum f -
      ↑(cellFilter (N := N) c.cellStart c.cellSize).card * μ := by
    intro c hc
    -- nodeLayer is constant on c's cell
    have hconst : ∀ j ∈ cellFilter (N := N) c.cellStart c.cellSize,
        nodeLayer parent children f j = cellMean f c.cellStart c.cellSize - μ := by
      intro j hj
      unfold nodeLayer
      rw [find_eq_child hdisj hc (Finset.mem_filter.mp hj).2]
    -- Σ (cellMean(f,c) - μ) = |cf| * (cellMean(f,c) - μ) [constant]
    --                        = |cf| * cellMean(f,c) - |cf| * μ
    --                        = cf.sum(f) - |cf| * μ
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    -- Goal: ↑|cf| * (cellMean(f,c) - μ) = cf.sum(f) - ↑|cf| * μ
    have ⟨hcs, hcf⟩ := hcfit c hc
    rw [cellFilter_card c.cellStart c.cellSize hcf]
    -- Goal: ↑c.cellSize * (cellMean(f,c) - μ) = cf.sum(f) - ↑c.cellSize * μ
    simp only [cellMean, if_neg (show c.cellSize ≠ 0 by omega)]
    have hne : (c.cellSize : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp

  -- Use hchild_sum to rewrite each child's contribution
  -- First, show the map of nodeLayer sums = map of (f sums - card * μ)
  have hmap_eq : children.map (fun c =>
      (cellFilter (N := N) c.cellStart c.cellSize).sum (nodeLayer parent children f)) =
    children.map (fun c =>
      (cellFilter (N := N) c.cellStart c.cellSize).sum f -
      ↑(cellFilter (N := N) c.cellStart c.cellSize).card * μ) := by
    exact List.map_congr_left (fun c hc => hchild_sum c hc)
  rw [hmap_eq]
  -- Goal: Σ_c (cf(c).sum(f) - |cf(c)| * μ) = 0
  -- = Σ_c cf(c).sum(f) - Σ_c |cf(c)| * μ
  -- = pf.sum(f) - parent.cellSize * μ
  -- = 0

  -- Factor out: Σ (a_c - b_c) = Σ a_c - Σ b_c
  have key1 : (children.map (fun c =>
      (cellFilter (N := N) c.cellStart c.cellSize).sum f -
      ↑(cellFilter (N := N) c.cellStart c.cellSize).card * μ)).sum =
    (children.map (fun c =>
      (cellFilter (N := N) c.cellStart c.cellSize).sum f)).sum -
    (children.map (fun c =>
      ↑(cellFilter (N := N) c.cellStart c.cellSize).card * μ)).sum := by
    -- This is a general algebraic fact: for any list, Σ(a-b) = Σa - Σb
    suffices h : ∀ (l : List RadixTreeNode),
      (l.map (fun c =>
        (cellFilter (N := N) c.cellStart c.cellSize).sum f -
        ↑(cellFilter (N := N) c.cellStart c.cellSize).card * μ)).sum =
      (l.map (fun c => (cellFilter (N := N) c.cellStart c.cellSize).sum f)).sum -
      (l.map (fun c => ↑(cellFilter (N := N) c.cellStart c.cellSize).card * μ)).sum from
      h children
    intro l
    induction l with
    | nil => simp
    | cons hd tl ihtl => simp only [List.map_cons, List.sum_cons]; rw [ihtl]; ring
  rw [key1]

  -- LHS term 1: Σ cf(c).sum(f) = pf.sum(f) (by partition_sum)
  rw [← partition_sum f children hnodup pf hpsub hdisj hpcover]

  -- LHS term 2: Σ (|cf(c)| * μ) = (Σ |cf(c)|) * μ = parent.cellSize * μ
  have key2 : (children.map (fun c =>
      ↑(cellFilter (N := N) c.cellStart c.cellSize).card * μ)).sum =
      ↑parent.cellSize * μ := by
    -- Factor out μ: Σ (card_c * μ) = (Σ card_c) * μ
    have factored : ∀ (l : List RadixTreeNode),
        (l.map (fun c => ↑(cellFilter (N := N) c.cellStart c.cellSize).card * μ)).sum =
        (l.map (fun c => (↑(cellFilter (N := N) c.cellStart c.cellSize).card : ℝ))).sum * μ := by
      intro l; induction l with
      | nil => simp
      | cons hd tl ihtl => simp only [List.map_cons, List.sum_cons]; rw [ihtl]; ring
    rw [factored]
    congr 1
    -- Σ |cf(c)| = Σ c.cellSize = parent.cellSize (using cellFilter_card + hpart)
    have cards_eq : ∀ (l : List RadixTreeNode),
        (∀ c ∈ l, c.cellSize > 0 ∧ c.cellStart + c.cellSize ≤ N) →
        (l.map (fun c => (↑(cellFilter (N := N) c.cellStart c.cellSize).card : ℝ))).sum =
        ↑(l.map RadixTreeNode.cellSize).sum := by
      intro l hl; induction l with
      | nil => simp
      | cons hd tl ihtl =>
        simp only [List.map_cons, List.sum_cons, Nat.cast_add]
        rw [ihtl (fun c hc => hl c (List.mem_cons_of_mem hd hc)),
            cellFilter_card hd.cellStart hd.cellSize (hl hd (List.mem_cons_self ..)).2]
    rw [cards_eq children hcfit, hpart]
  rw [key2]

  -- Goal: pf.sum(f) - parent.cellSize * μ = 0
  -- μ = pf.sum(f) / parent.cellSize
  simp only [μ, cellMean, if_neg (show parent.cellSize ≠ 0 by omega)]
  rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (show parent.cellSize ≠ 0 by omega))]
  ring

/-! ## Theorem 65: Orthogonal decomposition -/

/--
**fdrs.md**: Theorem 65 (Orthogonal decomposition) [§11.2.4 · Phase 11]

For a T-adapted signal f:
1. f = μ·1 + Σ_{v internal} g_v(f)
2. ⟨g_v, g_w⟩ = 0 for v ≠ w
3. ‖f - μ‖² = Σ ‖g_v‖² (Parseval)
-/
noncomputable def globalMean {N : ℕ} (f : Fin N → ℝ) : ℝ :=
  if N = 0 then 0 else (Finset.sum Finset.univ f) / N

/-- Orthogonal decomposition: the node layers are pairwise orthogonal.
    For nodes with disjoint support, orthogonality is immediate.
    For ancestor-descendant pairs, it follows from the mean-zero property. -/
theorem orthogonalDecomposition_disjointSupport {N : ℕ}
    (parent₁ parent₂ : RadixTreeNode)
    (children₁ children₂ : List RadixTreeNode) (f : Fin N → ℝ)
    (hdisj : ∀ (i : Fin N),
      ¬((i.val ≥ parent₁.cellStart ∧ i.val < parent₁.cellStart + parent₁.cellSize) ∧
        (i.val ≥ parent₂.cellStart ∧ i.val < parent₂.cellStart + parent₂.cellSize)))
    (hsub₁ : ∀ c ∈ children₁, c.cellStart ≥ parent₁.cellStart ∧
      c.cellStart + c.cellSize ≤ parent₁.cellStart + parent₁.cellSize)
    (hsub₂ : ∀ c ∈ children₂, c.cellStart ≥ parent₂.cellStart ∧
      c.cellStart + c.cellSize ≤ parent₂.cellStart + parent₂.cellSize) :
    Finset.sum Finset.univ (fun i =>
      nodeLayer parent₁ children₁ f i * nodeLayer parent₂ children₂ f i) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  -- At least one of the layers is 0 at i (disjoint supports)
  by_cases h₁ : i.val ≥ parent₁.cellStart ∧ i.val < parent₁.cellStart + parent₁.cellSize
  · -- i is in parent₁'s cell, so i is NOT in parent₂'s cell
    have h₂ : ¬(i.val ≥ parent₂.cellStart ∧ i.val < parent₂.cellStart + parent₂.cellSize) := by
      intro h₂; exact hdisj i ⟨h₁, h₂⟩
    rw [withinNodeLayer_supported parent₂ children₂ f hsub₂ i h₂]
    ring
  · rw [withinNodeLayer_supported parent₁ children₁ f hsub₁ i h₁]
    ring

/--
**fdrs.md**: Theorem 65, Part 3: One-level Parseval / ANOVA identity.

For a parent node with disjoint children that cover it, the node layer
(between-group component) is orthogonal to the within-child deviations.
This is the building block for the full Parseval identity ‖f - μ‖² = Σ ‖g_v‖²,
which follows by induction on the tree structure.

Concretely: Σ_{i∈P} nodeLayer(i) · (f(i) - cellMean(f, child(i))) = 0,
because nodeLayer is constant on each child cell and within-child deviations
sum to zero.
-/
theorem orthogonalDecomposition_parseval {N : ℕ} (hN : N > 0)
    (parent : RadixTreeNode) (children : List RadixTreeNode) (f : Fin N → ℝ)
    (hnodup : children.Nodup)
    (hdisj : ∀ c₁ ∈ children, ∀ c₂ ∈ children, c₁ ≠ c₂ →
      ∀ (k : ℕ), ¬((k ≥ c₁.cellStart ∧ k < c₁.cellStart + c₁.cellSize) ∧
                     (k ≥ c₂.cellStart ∧ k < c₂.cellStart + c₂.cellSize)))
    (hsub : ∀ c ∈ children, c.cellStart ≥ parent.cellStart ∧
      c.cellStart + c.cellSize ≤ parent.cellStart + parent.cellSize)
    (hcover : ∀ j : Fin N, j.val ≥ parent.cellStart ∧ j.val < parent.cellStart + parent.cellSize →
      ∃ c ∈ children, j.val ≥ c.cellStart ∧ j.val < c.cellStart + c.cellSize)
    (hpfit : parent.cellStart + parent.cellSize ≤ N)
    (hcfit : ∀ c ∈ children, c.cellSize > 0 ∧ c.cellStart + c.cellSize ≤ N) :
    -- The node layer is orthogonal to within-child deviations on the parent cell
    Finset.sum (cellFilter (N := N) parent.cellStart parent.cellSize)
      (fun i => nodeLayer parent children f i *
        (f i - match children.find? (fun c =>
          decide (i.val ≥ c.cellStart ∧ i.val < c.cellStart + c.cellSize))
        with | some child => cellMean f child.cellStart child.cellSize | none => f i)) = 0 := by
  -- Decompose the sum over the parent cell into child cells
  set pf := cellFilter (N := N) parent.cellStart parent.cellSize
  have hpsub : ∀ c ∈ children, ∀ j : Fin N,
      j.val ≥ c.cellStart ∧ j.val < c.cellStart + c.cellSize → j ∈ pf := by
    intro c hc j hj
    simp only [pf, cellFilter, Finset.mem_filter, Finset.mem_univ, true_and]
    have ⟨hcs, hce⟩ := hsub c hc; omega
  have hpcover : ∀ j ∈ pf,
      ∃ c ∈ children, j.val ≥ c.cellStart ∧ j.val < c.cellStart + c.cellSize := by
    intro j hj
    simp only [pf, cellFilter, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact hcover j hj
  rw [partition_sum _ children hnodup pf hpsub hdisj hpcover]
  -- For each child c, show the child's contribution is 0
  apply List.sum_eq_zero
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨c, hc, rfl⟩ := hx
  -- On child c's cell, nodeLayer is constant and deviations are from child mean
  set cf := cellFilter (N := N) c.cellStart c.cellSize
  -- Rewrite summands: on c's cell, find? returns c and nodeLayer = childMean - parentMean
  rw [Finset.sum_congr rfl (fun j hj => by
    have hjc := (Finset.mem_filter.mp hj).2
    -- find? returns c for j in c's cell
    show nodeLayer parent children f j *
      (f j - match children.find? (fun c' =>
        decide (j.val ≥ c'.cellStart ∧ j.val < c'.cellStart + c'.cellSize))
      with | some child => cellMean f child.cellStart child.cellSize | none => f j) =
      (cellMean f c.cellStart c.cellSize - cellMean f parent.cellStart parent.cellSize) *
      (f j - cellMean f c.cellStart c.cellSize)
    simp only [nodeLayer, find_eq_child hdisj hc hjc])]
  -- Factor out the constant (childMean - parentMean)
  rw [← Finset.mul_sum]
  -- Goal: (childMean - parentMean) * Σ_{j∈cf}(f(j) - childMean) = 0
  -- Σ_{j∈cf}(f(j) - childMean) = cf.sum(f) - |cf| * childMean = 0
  suffices h : cf.sum (fun j => f j - cellMean f c.cellStart c.cellSize) = 0 by
    rw [h, mul_zero]
  have hcne : c.cellSize ≠ 0 := by have := (hcfit c hc).1; omega
  have hne : (c.cellSize : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hcne
  have hcard := cellFilter_card c.cellStart c.cellSize (hcfit c hc).2
  -- cellMean = cf.sum f / c.cellSize
  have hcm : cellMean f c.cellStart c.cellSize = cf.sum f / ↑c.cellSize := by
    simp only [cellMean, if_neg hcne, cf, cellFilter]
  -- Σ (f(j) - μ_c) = cf.sum f - |cf| · μ_c = cf.sum f - cf.sum f = 0
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard, hcm,
      mul_div_cancel₀ _ hne, sub_self]

/-! ## Corollary 30: Exact adapted signals -/

/--
**fdrs.md**: Corollary 30 (Exact adapted signals) [§11.2.5 · Phase 11]

For a T-adapted signal, f(i) equals the cell mean on each leaf cell.
This is the pointwise reconstruction: P_T f(i) = f(i).
The full reconstruction P_T f = f is proved as connectionToFDRSFiltration
in Projection.lean.
-/
theorem exactAdaptedReconstruction {N : ℕ} (hN : N > 0)
    (T : NonStationaryRadixTree N) (f : Fin N → ℝ) (hf : IsTreeAdapted T f)
    (leaf : RadixTreeNode) (hl : leaf ∈ T.leaves)
    (hfit : leaf.cellSize > 0 ∧ leaf.cellStart + leaf.cellSize ≤ N)
    {i : Fin N} (hi : i.val ≥ leaf.cellStart ∧ i.val < leaf.cellStart + leaf.cellSize) :
    cellMean f leaf.cellStart leaf.cellSize = f i :=
  cellMean_of_const_on_cell f leaf.cellStart leaf.cellSize (f i)
    hfit.1 hfit.2 (fun j hj => hf leaf hl j i hj hi)

end FdrsFormal.Analysis.DigitConditional
