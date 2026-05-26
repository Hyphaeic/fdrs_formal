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

# Fourier Ceiling Theorem

Proves that no single Fourier mode can capture more than fraction α of
a digit-conditional signal's energy.

## Mathematical Content (fdrs.md §11.4)

**Definition 169**: Root-periodic energy fraction — α(f,T) = ‖g_root‖²/‖f-μ‖²
**Theorem 66**: Fourier ceiling — max Fourier correlation ≤ √α
**Proposition 134**: Homogeneous ceiling trivial — α = 1 for Vilenkin signals

## References

- fdrs.md, Phase 11, Sections 11.4.1–11.4.3
-/

import FdrsFormal.Analysis.DigitConditional.SignalClass
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace FdrsFormal.Analysis.DigitConditional

open Finset

/-! ## Definition 169: Root-periodic energy fraction -/

/--
**fdrs.md**: Definition 169 (Root-periodic energy fraction) [§11.4.1 · Phase 11]

α(f, T) = ‖g_root(f)‖² / ‖f - μ‖²

The fraction of signal energy in the root (depth-1) layer — the only layer
visible to standard Fourier/Vilenkin analysis.
-/
noncomputable def rootPeriodicEnergyFraction {N : ℕ} (T : NonStationaryRadixTree N)
    (f : Fin N → ℝ) : ℝ :=
  let μ := globalMean f
  let totalVar := Finset.sum Finset.univ (fun i => (f i - μ) ^ 2)
  if totalVar = 0 then 1  -- Convention: α = 1 for constant signals
  else
    -- Root layer energy: between-group variance at the first level
    let rootNode : RadixTreeNode := ⟨T.tree.childCount, N, 0⟩
    let children : List RadixTreeNode := T.leaves
    let rootLayerEnergy := Finset.sum Finset.univ
      (fun i => (nodeLayer rootNode children f i) ^ 2)
    rootLayerEnergy / totalVar

/-! ## Theorem 66: Fourier ceiling -/

/--
**fdrs.md**: Theorem 66 (Fourier ceiling) [§11.4.2 · Phase 11]

Partition-level Fourier ceiling: for any partition of [0, N) into disjoint
children cells, any signal f, and any function φ that is constant on each
child cell, the inner product ⟨f − μ, φ⟩ is controlled by the root layer:

  (Σ (f(i) − μ) · φ(i))² ≤ (Σ nodeLayer(i)²) · (Σ φ(i)²)

The proof decomposes f − μ = nodeLayer + residual, shows the residual is
orthogonal to φ (since φ is child-constant and residual is child-mean-zero),
and applies Cauchy–Schwarz to the remaining ⟨nodeLayer, φ⟩ term.

This is the weakest correct statement: it takes the alignment condition
(φ constant on children) as a hypothesis rather than deriving it from a
position-modular predicate. For Vilenkin characters χ that are constant on
depth-1 cylinders, this gives |⟨f−μ, χ⟩|² ≤ α · ‖f−μ‖² · ‖χ‖².
-/
theorem fourierCeiling {N : ℕ} (hN : N > 0)
    (rootNode : RadixTreeNode) (children : List RadixTreeNode)
    (f φ : Fin N → ℝ)
    -- children partition [0, N) with standard well-formedness
    (hnodup : children.Nodup)
    (hdisj : ∀ c₁ ∈ children, ∀ c₂ ∈ children, c₁ ≠ c₂ →
      ∀ (k : ℕ), ¬((k ≥ c₁.cellStart ∧ k < c₁.cellStart + c₁.cellSize) ∧
                     (k ≥ c₂.cellStart ∧ k < c₂.cellStart + c₂.cellSize)))
    (hsub : ∀ c ∈ children, c.cellStart ≥ rootNode.cellStart ∧
      c.cellStart + c.cellSize ≤ rootNode.cellStart + rootNode.cellSize)
    (hcover : ∀ i : Fin N, ∃ c ∈ children, i.val ≥ c.cellStart ∧
      i.val < c.cellStart + c.cellSize)
    (hroot : rootNode.cellStart = 0 ∧ rootNode.cellSize = N)
    (hcfit : ∀ c ∈ children, c.cellSize > 0 ∧ c.cellStart + c.cellSize ≤ N)
    (hpart : (children.map RadixTreeNode.cellSize).sum = rootNode.cellSize)
    -- φ is constant on each child cell (the alignment hypothesis)
    (hφconst : ∀ c ∈ children, ∀ (i j : Fin N),
      (i.val ≥ c.cellStart ∧ i.val < c.cellStart + c.cellSize) →
      (j.val ≥ c.cellStart ∧ j.val < c.cellStart + c.cellSize) →
      φ i = φ j) :
    -- ⟨f − μ, φ⟩² ≤ ‖g_root(f)‖² · ‖φ‖²
    (Finset.sum Finset.univ (fun i =>
      (f i - globalMean f) * φ i)) ^ 2 ≤
    (Finset.sum Finset.univ (fun i =>
      (nodeLayer rootNode children f i) ^ 2)) *
    (Finset.sum Finset.univ (fun i => (φ i) ^ 2)) := by
  -- Step 1: Decompose f(i) − μ = nodeLayer(i) + residual(i)
  -- where residual(i) = f(i) − cellMean(f, child(i))
  -- Step 2: ⟨f−μ, φ⟩ = ⟨nodeLayer, φ⟩ + ⟨residual, φ⟩ = ⟨nodeLayer, φ⟩
  --   because ⟨residual, φ⟩ = 0 (φ child-constant, residual child-mean-zero)
  -- Step 3: Cauchy–Schwarz on ⟨nodeLayer, φ⟩

  -- Rewrite each (f i - μ) * φ i = nodeLayer(i) * φ(i) + residual(i) * φ(i)
  -- and show the residual cross-term vanishes.

  -- First show: Σ (f(i) - μ) * φ(i) = Σ nodeLayer(i) * φ(i)
  suffices hinner : Finset.sum Finset.univ (fun i => (f i - globalMean f) * φ i) =
      Finset.sum Finset.univ (fun i => nodeLayer rootNode children f i * φ i) by
    rw [hinner]
    -- Step 3: Cauchy–Schwarz
    exact sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i => nodeLayer rootNode children f i) (fun i => φ i)

  -- Prove the inner product equality:
  -- Σ (f(i) - μ) * φ(i) = Σ nodeLayer(i) * φ(i)
  -- i.e., Σ (f(i) - μ - nodeLayer(i)) * φ(i) = 0
  -- where f(i) - μ - nodeLayer(i) = f(i) - cellMean(f, child(i)) (the residual)
  suffices hcross : Finset.sum Finset.univ
      (fun i => (f i - globalMean f - nodeLayer rootNode children f i) * φ i) = 0 by
    have := Finset.sum_sub_distrib (s := Finset.univ)
      (f := fun i => (f i - globalMean f) * φ i)
      (g := fun i => nodeLayer rootNode children f i * φ i)
    linarith [Finset.sum_congr (show Finset.univ = Finset.univ from rfl)
      (fun i _ => show (f i - globalMean f) * φ i -
        nodeLayer rootNode children f i * φ i =
        (f i - globalMean f - nodeLayer rootNode children f i) * φ i by ring)]

  -- The residual at i (in child c) is f(i) - cellMean(f, c).
  -- φ is constant on c. Residual sums to 0 on c. So the cross-term = 0.
  -- Decompose the sum over children using partition_sum.
  have hfit : rootNode.cellStart + rootNode.cellSize ≤ N := by omega
  set pf := cellFilter (N := N) rootNode.cellStart rootNode.cellSize
  have hpf_univ : pf = Finset.univ := by
    simp only [pf, cellFilter]
    rw [Finset.filter_true_of_mem (fun j _ => by
      obtain ⟨h1, h2⟩ := hroot; omega)]
  rw [← hpf_univ]
  have hpsub : ∀ c ∈ children, ∀ j : Fin N,
      j.val ≥ c.cellStart ∧ j.val < c.cellStart + c.cellSize → j ∈ pf := by
    intro c hc j hj; rw [hpf_univ]; exact Finset.mem_univ j
  have hpcover : ∀ j ∈ pf,
      ∃ c ∈ children, j.val ≥ c.cellStart ∧ j.val < c.cellStart + c.cellSize := by
    intro j _; exact hcover j
  rw [partition_sum _ children hnodup pf hpsub hdisj hpcover]
  -- Goal: Σ_c cf(c).sum((f(i)-μ-nodeLayer(i)) * φ(i)) = 0
  apply List.sum_eq_zero
  intro x hx; rw [List.mem_map] at hx; obtain ⟨c, hc, rfl⟩ := hx
  set cf := cellFilter (N := N) c.cellStart c.cellSize
  -- On child c: nodeLayer(i) = cellMean(f,c) - cellMean(f,root) = cellMean(f,c) - μ
  -- So f(i) - μ - nodeLayer(i) = f(i) - cellMean(f,c)
  -- And φ is constant on c with value φ_c
  rw [Finset.sum_congr rfl (fun j hj => by
    have hjc := (Finset.mem_filter.mp hj).2
    -- Rewrite nodeLayer
    show (f j - globalMean f - nodeLayer rootNode children f j) * φ j =
      (f j - cellMean f c.cellStart c.cellSize) * φ j
    congr 1
    simp only [nodeLayer, find_eq_child hdisj hc hjc]
    -- nodeLayer = cellMean(f,c) - cellMean(f,root)
    -- cellMean(f, root) = globalMean f  (since root covers all of [0,N))
    have hroot_mean : cellMean f rootNode.cellStart rootNode.cellSize = globalMean f := by
      simp only [globalMean, if_neg (by omega : N ≠ 0), cellMean,
        if_neg (show rootNode.cellSize ≠ 0 by omega)]
      rw [hroot.1, hroot.2]
      congr 1
      · congr 1; rw [Finset.filter_true_of_mem (fun j _ => by simp)]
    linarith [hroot_mean])]
  -- Goal: cf.sum(fun j => (f j - cellMean(f,c)) * φ(j)) = 0
  -- φ is constant on c, so factor it out
  -- Get the constant value of φ on c
  have ⟨hcsize, hcle⟩ := hcfit c hc
  -- pick a witness point in c
  have hwit : ∃ w : Fin N, w.val ≥ c.cellStart ∧ w.val < c.cellStart + c.cellSize := by
    exact ⟨⟨c.cellStart, by omega⟩, by simp; omega⟩
  obtain ⟨w, hw⟩ := hwit
  -- φ is constant on c with value φ w
  rw [Finset.sum_congr rfl (fun j hj => by
    have hjc := (Finset.mem_filter.mp hj).2
    show (f j - cellMean f c.cellStart c.cellSize) * φ j =
      (f j - cellMean f c.cellStart c.cellSize) * φ w
    congr 1; exact hφconst c hc j w hjc hw)]
  -- Factor out φ w: Σ (f(j) - μ_c) * φ_w = φ_w * Σ(f(j) - μ_c) = φ_w * 0 = 0
  rw [← Finset.sum_mul]
  -- Σ_{j∈cf}(f(j) - cellMean(f,c)) = 0  (definition of cellMean)
  have hcne : c.cellSize ≠ 0 := by omega
  have hne : (c.cellSize : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hcne
  have hcard := cellFilter_card c.cellStart c.cellSize hcle
  have hzero : cf.sum (fun j => f j - cellMean f c.cellStart c.cellSize) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard]
    have hcm : cellMean f c.cellStart c.cellSize = cf.sum f / ↑c.cellSize := by
      simp only [cellMean, if_neg hcne, cf, cellFilter]
    rw [hcm, mul_div_cancel₀ _ hne, sub_self]
  rw [hzero, zero_mul]

/-! ## Energy fraction (corrected definition) -/

/-- Root-layer energy fraction, parameterized by explicit root children.
    Unlike `rootPeriodicEnergyFraction` (which uses T.leaves and is correct
    only for depth-1 trees), this definition takes the root's direct children
    as a parameter, making it correct for arbitrary tree depth.

    α(f, root, children) = ‖g_root(f)‖² / ‖f − μ‖²
-/
noncomputable def energyFraction {N : ℕ}
    (rootNode : RadixTreeNode) (children : List RadixTreeNode)
    (f : Fin N → ℝ) : ℝ :=
  let μ := globalMean f
  let totalVar := Finset.sum Finset.univ (fun i => (f i - μ) ^ 2)
  if totalVar = 0 then 1
  else
    let rootLayerEnergy := Finset.sum Finset.univ
      (fun i => (nodeLayer rootNode children f i) ^ 2)
    rootLayerEnergy / totalVar

/-- Fourier ceiling in energy-fraction form: for φ constant on root children,
    |⟨f−μ, φ⟩|² / (‖f−μ‖² · ‖φ‖²) ≤ α(f, root, children).

    This restates `fourierCeiling` using the energy fraction α, dividing
    both sides by ‖f−μ‖² · ‖φ‖² (when both are nonzero).
-/
theorem fourierCeiling_energyFraction {N : ℕ} (hN : N > 0)
    (rootNode : RadixTreeNode) (children : List RadixTreeNode)
    (f φ : Fin N → ℝ)
    (hnodup : children.Nodup)
    (hdisj : ∀ c₁ ∈ children, ∀ c₂ ∈ children, c₁ ≠ c₂ →
      ∀ (k : ℕ), ¬((k ≥ c₁.cellStart ∧ k < c₁.cellStart + c₁.cellSize) ∧
                     (k ≥ c₂.cellStart ∧ k < c₂.cellStart + c₂.cellSize)))
    (hsub : ∀ c ∈ children, c.cellStart ≥ rootNode.cellStart ∧
      c.cellStart + c.cellSize ≤ rootNode.cellStart + rootNode.cellSize)
    (hcover : ∀ i : Fin N, ∃ c ∈ children, i.val ≥ c.cellStart ∧
      i.val < c.cellStart + c.cellSize)
    (hroot : rootNode.cellStart = 0 ∧ rootNode.cellSize = N)
    (hcfit : ∀ c ∈ children, c.cellSize > 0 ∧ c.cellStart + c.cellSize ≤ N)
    (hpart : (children.map RadixTreeNode.cellSize).sum = rootNode.cellSize)
    (hφconst : ∀ c ∈ children, ∀ (i j : Fin N),
      (i.val ≥ c.cellStart ∧ i.val < c.cellStart + c.cellSize) →
      (j.val ≥ c.cellStart ∧ j.val < c.cellStart + c.cellSize) →
      φ i = φ j)
    (hfnc : Finset.sum Finset.univ (fun i => (f i - globalMean f) ^ 2) ≠ 0)
    (hφnz : Finset.sum Finset.univ (fun i => (φ i) ^ 2) ≠ 0) :
    (Finset.sum Finset.univ (fun i => (f i - globalMean f) * φ i)) ^ 2 /
      ((Finset.sum Finset.univ (fun i => (f i - globalMean f) ^ 2)) *
       (Finset.sum Finset.univ (fun i => (φ i) ^ 2))) ≤
    energyFraction rootNode children f := by
  simp only [energyFraction, if_neg hfnc]
  -- LHS = ⟨f-μ, φ⟩² / (‖f-μ‖² · ‖φ‖²)
  -- RHS = ‖g_root‖² / ‖f-μ‖²
  -- Suffices: ⟨f-μ, φ⟩² / (‖f-μ‖² · ‖φ‖²) ≤ ‖g_root‖² / ‖f-μ‖²
  -- i.e., ⟨f-μ, φ⟩² / ‖φ‖² ≤ ‖g_root‖² (after canceling ‖f-μ‖²)
  -- which follows from fourierCeiling: ⟨f-μ, φ⟩² ≤ ‖g_root‖² · ‖φ‖²
  have htv_pos : 0 < Finset.sum Finset.univ (fun i => (f i - globalMean f) ^ 2) :=
    lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (Ne.symm hfnc)
  have hφ_pos : 0 < Finset.sum Finset.univ (fun i => (φ i) ^ 2) :=
    lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (Ne.symm hφnz)
  have hprod_pos : 0 < (Finset.sum Finset.univ (fun i => (f i - globalMean f) ^ 2)) *
      (Finset.sum Finset.univ (fun i => (φ i) ^ 2)) := mul_pos htv_pos hφ_pos
  rw [div_le_div_iff₀ hprod_pos htv_pos]
  -- Goal: ⟨f-μ,φ⟩² * totalVar ≤ rootLayerEnergy * (totalVar * ‖φ‖²)
  -- = rootLayerEnergy * ‖φ‖² * totalVar
  -- Suffices: ⟨f-μ,φ⟩² ≤ rootLayerEnergy * ‖φ‖² (then multiply both sides by totalVar)
  have hceiling := fourierCeiling hN rootNode children f φ
    hnodup hdisj hsub hcover hroot hcfit hpart hφconst
  -- hceiling : ⟨f-μ,φ⟩² ≤ ‖g_root‖² · ‖φ‖²
  calc (Finset.sum Finset.univ (fun i => (f i - globalMean f) * φ i)) ^ 2 *
        Finset.sum Finset.univ (fun i => (f i - globalMean f) ^ 2)
      ≤ (Finset.sum Finset.univ (fun i => (nodeLayer rootNode children f i) ^ 2) *
         Finset.sum Finset.univ (fun i => (φ i) ^ 2)) *
        Finset.sum Finset.univ (fun i => (f i - globalMean f) ^ 2) := by
          exact mul_le_mul_of_nonneg_right hceiling (le_of_lt htv_pos)
    _ = Finset.sum Finset.univ (fun i => (nodeLayer rootNode children f i) ^ 2) *
        (Finset.sum Finset.univ (fun i => (f i - globalMean f) ^ 2) *
         Finset.sum Finset.univ (fun i => (φ i) ^ 2)) := by ring

/-! ## Proposition 134: Homogeneous ceiling trivial -/

/--
**fdrs.md**: Proposition 134 (Homogeneous ceiling trivial) [§11.4.3 · Phase 11]

If T is homogeneous, α = 1 for signals whose energy lies entirely in the
root layer. For periodic signals, the Fourier ceiling is tight.
-/
theorem homogeneousCeilingTrivial {N : ℕ} (hN : N > 0)
    (T : NonStationaryRadixTree N) (hom : T.isHomogeneous)
    (f : Fin N → ℝ) (hf : IsTreeAdapted T f) (hdepth1 : T.depth = 1)
    (hdisj : ∀ l₁ ∈ T.leaves, ∀ l₂ ∈ T.leaves, l₁ ≠ l₂ →
      ∀ k, ¬((k ≥ l₁.cellStart ∧ k < l₁.cellStart + l₁.cellSize) ∧
              (k ≥ l₂.cellStart ∧ k < l₂.cellStart + l₂.cellSize)))
    (hfit : ∀ l ∈ T.leaves, l.cellSize > 0 ∧ l.cellStart + l.cellSize ≤ N)
    (hcover : ∀ i : Fin N, ∃ l ∈ T.leaves,
      i.val ≥ l.cellStart ∧ i.val < l.cellStart + l.cellSize) :
    rootPeriodicEnergyFraction T f = 1 := by
  simp only [rootPeriodicEnergyFraction, NonStationaryRadixTree.depth] at hdepth1 ⊢
  -- Case split on totalVar
  by_cases htv : Finset.sum Finset.univ (fun i => (f i - globalMean f) ^ 2) = 0
  · -- Constant signal: α = 1 by convention
    simp [htv]
  · -- Non-constant: show rootLayerEnergy = totalVar
    rw [if_neg htv]
    -- rootLayerEnergy = Σ (nodeLayer root (T.leaves) f i)²
    -- For T-adapted f: f is constant on each leaf cell.
    -- nodeLayer at i = cellMean(f, leaf(i)) - globalMean f
    -- Since f constant on leaf(i): cellMean(f, leaf) = f(i).
    -- So nodeLayer(i) = f(i) - globalMean f.
    -- rootLayerEnergy = Σ (f(i) - globalMean f)² = totalVar.
    -- So α = totalVar / totalVar = 1.
    -- Show rootLayerEnergy = totalVar
    -- nodeLayer at i = cellMean(f, leaf(i)) - globalMean f
    -- For T-adapted f: f constant on leaf cell, so cellMean = f(i).
    -- Thus nodeLayer(i) = f(i) - μ, and rootLayerEnergy = Σ(f(i)-μ)² = totalVar.
    suffices heq : Finset.sum Finset.univ
        (fun i => (nodeLayer ⟨T.tree.childCount, N, 0⟩ T.leaves f i) ^ 2) =
        Finset.sum Finset.univ (fun i => (f i - globalMean f) ^ 2) by
      rw [heq]; field_simp
    apply Finset.sum_congr rfl
    intro i _
    -- Show nodeLayer root leaves f i = f(i) - globalMean f
    congr 1
    -- nodeLayer uses find? on T.leaves
    obtain ⟨l, hl, hil⟩ := hcover i
    simp only [nodeLayer]
    -- find? returns l for i (by disjointness)
    rw [find_eq_child (fun c₁ h₁ c₂ h₂ hne k hk => hdisj c₁ h₁ c₂ h₂ hne k hk) hl hil]
    dsimp only []
    -- Goal: cellMean f l.cellStart l.cellSize - cellMean f 0 N = f i - globalMean f
    -- cellMean f 0 N = globalMean f (same sum, same size)
    -- cellMean f l = f(i) (f constant on l's cell)
    have hcm_fi : cellMean f l.cellStart l.cellSize = f i := by
      apply cellMean_of_const_on_cell f l.cellStart l.cellSize (f i)
        (hfit l hl).1 (hfit l hl).2
      intro j hj; exact hf l hl j i hj hil
    rw [hcm_fi]
    -- cellMean f 0 N = globalMean f
    simp only [globalMean, if_neg (by omega : N ≠ 0)]
    -- cellMean f 0 N vs (Σ f) / N
    simp only [cellMean, if_neg (by omega : N ≠ 0)]
    congr 1
    rw [Finset.filter_true_of_mem (fun j _ => by simp)]

end FdrsFormal.Analysis.DigitConditional
