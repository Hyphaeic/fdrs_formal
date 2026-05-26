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

# Non-Stationary Radix Trees

Foundational types for Phase 11 — digit-conditional signal analysis.

## Mathematical Content (fdrs.md §11.1)

**Definition 164**: Non-stationary radix tree — rooted tree on finite I with position-modular grouping
**Definition 165**: Depth and heterogeneity — homogeneous vs heterogeneous classification
**Proposition 131**: Leaf count identity — |Leaves| = 1 + Σ(r(v)-1)
**Proposition 132**: Homogeneous recovery — homogeneous T ↔ standard cylinder partition

## References

- fdrs.md, Phase 11, Sections 11.1.1–11.1.4
-/

import FdrsFormal.Core

namespace FdrsFormal.Analysis.DigitConditional

/-! ## Definition 164: Non-stationary radix tree -/

/--
**fdrs.md**: Definition 164 (Non-stationary radix tree) [§11.1.1 · Phase 11]

A non-stationary radix tree. Each node is either a leaf (carrying its cell
size and start offset) or an internal node with a list of children.
-/
inductive RadixTree where
  /-- A leaf node with cell size and start offset -/
  | leaf (cellSize : ℕ) (cellStart : ℕ) : RadixTree
  /-- An internal node with children -/
  | node (children : List RadixTree) : RadixTree
  deriving Repr

namespace RadixTree

/-- Number of children: 0 for leaves, n for internal nodes. -/
def childCount : RadixTree → ℕ
  | .leaf _ _ => 0
  | .node cs => cs.length

/-! ### Leaf count and internal branch sum via mutual recursion -/

mutual
  def leafCount : RadixTree → ℕ
    | .leaf _ _ => 1
    | .node children => leafCountList children

  def leafCountList : List RadixTree → ℕ
    | [] => 0
    | t :: ts => t.leafCount + leafCountList ts
end

mutual
  def internalBranchSum : RadixTree → ℕ
    | .leaf _ _ => 0
    | .node children => (children.length - 1) + ibsList children

  def ibsList : List RadixTree → ℕ
    | [] => 0
    | t :: ts => t.internalBranchSum + ibsList ts
end

/-- The depth (longest root-to-leaf path). -/
def depth : RadixTree → ℕ
  | .leaf _ _ => 0
  | .node [] => 1
  | .node (c :: _) => 1 + c.depth

/-! ### Definition 165: Depth and heterogeneity -/

/--
**fdrs.md**: Definition 165 (Depth and heterogeneity) [§11.1.2 · Phase 11]
-/
def isHomogeneous : RadixTree → Prop
  | .leaf _ _ => True
  | .node children =>
    (∀ c₁ ∈ children, ∀ c₂ ∈ children, c₁.childCount = c₂.childCount) ∧
    (∀ c₁ ∈ children, ∀ c₂ ∈ children, c₁.leafCount = c₂.leafCount) ∧
    (∀ c ∈ children, c.isHomogeneous)

def isHeterogeneous (t : RadixTree) : Prop := ¬t.isHomogeneous

/-! ### Simp lemmas for mutual defs -/

@[simp] theorem leafCount_leaf (s o : ℕ) : (leaf s o).leafCount = 1 := rfl
@[simp] theorem leafCount_node (cs : List RadixTree) :
    (node cs).leafCount = leafCountList cs := rfl
@[simp] theorem leafCountList_nil : leafCountList ([] : List RadixTree) = 0 := rfl
@[simp] theorem leafCountList_cons (t : RadixTree) (ts : List RadixTree) :
    leafCountList (t :: ts) = t.leafCount + leafCountList ts := rfl

@[simp] theorem ibs_leaf (s o : ℕ) : (leaf s o).internalBranchSum = 0 := rfl
@[simp] theorem ibs_node (cs : List RadixTree) :
    (node cs).internalBranchSum = (cs.length - 1) + ibsList cs := rfl
@[simp] theorem ibsList_nil : ibsList ([] : List RadixTree) = 0 := rfl
@[simp] theorem ibsList_cons (t : RadixTree) (ts : List RadixTree) :
    ibsList (t :: ts) = t.internalBranchSum + ibsList ts := rfl

/-! ### Well-formedness: all internal nodes have ≥ 1 child -/

/-- An internal node is well-formed if it has ≥ 1 child and all children are well-formed.
    Leaves are always well-formed. -/
def WellFormed : RadixTree → Prop
  | .leaf _ _ => True
  | .node children => children.length ≥ 1 ∧ ∀ c ∈ children, c.WellFormed

/-! ### Proposition 131: Leaf count identity

The identity leafCount = 1 + Σ(r(v)-1) holds for well-formed trees. -/

/-- List sub-identity with tree identity available for smaller trees. -/
private theorem leafCountList_of_ih (children : List RadixTree)
    (hwf : ∀ c ∈ children, c.WellFormed)
    (ih : ∀ c ∈ children, c.leafCount = 1 + c.internalBranchSum) :
    leafCountList children = children.length + ibsList children := by
  induction children with
  | nil => rfl
  | cons c cs ihcs =>
    simp only [leafCountList_cons, ibsList_cons, List.length_cons]
    have hc := ih c (by simp)
    have hcs := ihcs
      (fun c' hc' => hwf c' (List.mem_cons_of_mem c hc'))
      (fun c' hc' => ih c' (List.mem_cons_of_mem c hc'))
    linarith

/--
**fdrs.md**: Proposition 131 (Leaf count identity) [§11.1.3 · Phase 11]

For any well-formed radix tree T: leafCount(T) = 1 + internalBranchSum(T).
-/
theorem leafCount_eq_one_add_internalBranchSum (t : RadixTree) (hwf : t.WellFormed) :
    t.leafCount = 1 + t.internalBranchSum := by
  match t with
  | .leaf _ _ => rfl
  | .node children =>
    simp only [leafCount_node, ibs_node, WellFormed] at hwf ⊢
    obtain ⟨hlen, hchildren⟩ := hwf
    have h := leafCountList_of_ih children hchildren
      (fun c hc => leafCount_eq_one_add_internalBranchSum c (hchildren c hc))
    omega
termination_by sizeOf t
decreasing_by
  simp_wf
  have hmem : c ∈ children := hc
  have : sizeOf c < sizeOf children := List.sizeOf_lt_of_mem hmem
  simp_wf; omega

/-! ### Proposition 132: Homogeneous recovery -/

/-- Branching factors from root downward, following the first child. -/
def branchingFactors : RadixTree → List ℕ
  | .leaf _ _ => []
  | .node [] => [0]
  | .node (c :: cs) => (c :: cs).length :: c.branchingFactors

/-- leafCountList when all elements have the same leafCount. -/
private theorem leafCountList_const (ts : List RadixTree) (k : ℕ)
    (h : ∀ t, t ∈ ts → t.leafCount = k) :
    leafCountList ts = ts.length * k := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [leafCountList_cons, List.length_cons]
    rw [h t (by simp), ih (fun t' ht' => h t' (by simp [ht']))]
    ring

/-- Within a homogeneous tree, all siblings have the same leafCount. -/
private theorem homogeneous_siblings_same_leafCount
    (cs : List RadixTree)
    (hbranch : ∀ c₁ ∈ cs, ∀ c₂ ∈ cs, c₁.childCount = c₂.childCount)
    (hleaf : ∀ c₁ ∈ cs, ∀ c₂ ∈ cs, c₁.leafCount = c₂.leafCount)
    (hhom : ∀ c ∈ cs, c.isHomogeneous)
    (c₁ : RadixTree) (hc₁ : c₁ ∈ cs) (c₂ : RadixTree) (hc₂ : c₂ ∈ cs) :
    c₁.leafCount = c₂.leafCount :=
  hleaf c₁ hc₁ c₂ hc₂

/--
**fdrs.md**: Proposition 132 (Homogeneous recovery) [§11.1.4 · Phase 11]

For a homogeneous tree, the leaf count equals the product of branching factors.
-/
theorem homogeneous_leafCount_eq_prod (t : RadixTree) (hom : t.isHomogeneous) :
    t.leafCount = t.branchingFactors.prod := by
  match t with
  | .leaf _ _ => rfl
  | .node [] => rfl
  | .node (c :: cs) =>
    simp only [leafCount_node, branchingFactors, List.prod_cons]
    simp only [isHomogeneous] at hom
    obtain ⟨hbranch, hleaf, hhom⟩ := hom
    have hc_hom : c.isHomogeneous := hhom c (by simp)
    have hc_ih : c.leafCount = c.branchingFactors.prod :=
      homogeneous_leafCount_eq_prod c hc_hom
    have hall : ∀ t, t ∈ (c :: cs) → t.leafCount = c.leafCount :=
      fun t ht => homogeneous_siblings_same_leafCount (c :: cs) hbranch hleaf hhom t ht c (by simp)
    rw [leafCountList_const _ c.leafCount hall, hc_ih]

end RadixTree

/-! ## Level-based representation for downstream compatibility -/

/-- Node metadata for the level-based representation. -/
structure RadixTreeNode where
  /-- Number of children (branching factor); 0 for leaves -/
  branching : ℕ
  /-- Cell size: number of elements in I_v -/
  cellSize : ℕ
  /-- Cell start: offset in the canonical ordering of I -/
  cellStart : ℕ
  deriving DecidableEq, Repr

/-- A non-stationary radix tree on `Fin N`, wrapping the inductive `RadixTree`. -/
structure NonStationaryRadixTree (N : ℕ) where
  /-- The underlying inductive tree -/
  tree : RadixTree
  deriving Repr

namespace NonStationaryRadixTree

/-- Extract leaf nodes from the inductive tree. -/
def extractLeaves : RadixTree → List RadixTreeNode
  | .leaf s o => [⟨0, s, o⟩]
  | .node children => children.flatMap extractLeaves

/-- The leaves of a radix tree. -/
def leaves {N : ℕ} (T : NonStationaryRadixTree N) : List RadixTreeNode :=
  extractLeaves T.tree

/-- The number of leaves. -/
def leafCount {N : ℕ} (T : NonStationaryRadixTree N) : ℕ :=
  T.tree.leafCount

/-- The depth of the tree. -/
def depth {N : ℕ} (T : NonStationaryRadixTree N) : ℕ :=
  T.tree.depth

/-- A tree is homogeneous if all nodes at the same depth have the same branching. -/
def isHomogeneous {N : ℕ} (T : NonStationaryRadixTree N) : Prop :=
  T.tree.isHomogeneous

/-- A tree is heterogeneous if it is not homogeneous. -/
def isHeterogeneous {N : ℕ} (T : NonStationaryRadixTree N) : Prop :=
  ¬T.isHomogeneous

end NonStationaryRadixTree

/-! ## Propositions via NonStationaryRadixTree API -/

def internalBranchingSum {N : ℕ} (T : NonStationaryRadixTree N) : ℕ :=
  T.tree.internalBranchSum

/--
**fdrs.md**: Proposition 131 (Leaf count identity) [§11.1.3 · Phase 11]
-/
theorem leafCountIdentity {N : ℕ} (T : NonStationaryRadixTree N) (hwf : T.tree.WellFormed) :
    T.leafCount = 1 + internalBranchingSum T :=
  RadixTree.leafCount_eq_one_add_internalBranchSum T.tree hwf

/--
**fdrs.md**: Proposition 132 (Homogeneous recovery) [§11.1.4 · Phase 11]
-/
theorem homogeneousRecovery {N : ℕ} (T : NonStationaryRadixTree N)
    (hom : T.isHomogeneous) :
    T.leafCount = T.tree.branchingFactors.prod :=
  RadixTree.homogeneous_leafCount_eq_prod T.tree hom

end FdrsFormal.Analysis.DigitConditional
