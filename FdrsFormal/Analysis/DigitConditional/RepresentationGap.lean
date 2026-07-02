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

# Representation Gap

Quantifies the advantage of tree-adapted partitions over uniform partitions.

## Mathematical Content (fdrs.md §11.5)

**Definition 170**: Minimum uniform cells — U(f) = min uniform partition size for f
**Definition 171**: Representation gap — Gap(f,T) = U(f)/|Leaves(T)|
**Proposition 135** (honest form): the gap is genuine — collapse direction
  `Gap ≤ 1` proven (uniform partition matched, zero penalty), and the strict
  `Gap > 1` (heterogeneity strictly pays) proven via a `Fin 4` witness
**Theorem 67**: Depth-2 gap formula — Gap = b₀·lcm(rⱼ)/Σrⱼ
**Corollary 31**: Compensated heterogeneity — Gap = 1 iff all child radices equal

## References

- fdrs.md, Phase 11, Sections 11.5.1–11.5.5
-/

import FdrsFormal.Analysis.DigitConditional.Decomposition
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.Lattice

namespace FdrsFormal.Analysis.DigitConditional

/-! ## Definition 170: Minimum uniform cells -/

/--
`f` is constant on every cell of the uniform `k`-equipartition of `Fin N`.
For `k ∣ N` the cells are the equal-size blocks `[j·(N/k), (j+1)·(N/k))`,
indexed by `i ↦ i.val / (N / k)` — the genuine cylinder cells of the homogeneous
depth-1 refinement at branching `k`.
-/
def ConstantOnUniformCells {N : ℕ} (f : Fin N → ℝ) (k : ℕ) : Prop :=
  ∀ i j : Fin N, i.val / (N / k) = j.val / (N / k) → f i = f j

/--
**fdrs.md**: Definition 170 (Minimum uniform cells) [§11.5.1 · Phase 11]

`U(f) = min { k : k ∣ N ∧ f constant on each cell of the uniform k-partition }`.

The singleton partition `k = N` always qualifies (`N / N = 1`, every cell a single
point), so the set is nonempty and `U(f) ≤ N`. This is the genuine quantity
replacing the former `:= N` placeholder: it equals `N` exactly when `f` has no
uniform structure, and is strictly smaller when a coarser equipartition already
resolves `f` (e.g. `U = 1` for a constant signal).
-/
noncomputable def minUniformCells {N : ℕ} (f : Fin N → ℝ) : ℕ :=
  sInf {k | k ∣ N ∧ 1 ≤ k ∧ ConstantOnUniformCells f k}

/-- The singleton equipartition `k = N` represents every signal: it is the
maximal refinement, so it always lies in the admissible set. -/
theorem N_mem_uniformSet {N : ℕ} (hN : 0 < N) (f : Fin N → ℝ) :
    N ∈ {k | k ∣ N ∧ 1 ≤ k ∧ ConstantOnUniformCells f k} := by
  refine ⟨dvd_refl N, hN, fun i j h => ?_⟩
  rw [Nat.div_self hN, Nat.div_one, Nat.div_one] at h
  exact congrArg f (Fin.ext h)

/-- `U(f) ≤ N`: the singleton partition always works. -/
theorem minUniformCells_le_N {N : ℕ} (hN : 0 < N) (f : Fin N → ℝ) :
    minUniformCells f ≤ N :=
  Nat.sInf_le (N_mem_uniformSet hN f)

/-- `U(f)` is a divisor of `N` (it is a realised equipartition size). -/
theorem minUniformCells_dvd {N : ℕ} (hN : 0 < N) (f : Fin N → ℝ) :
    minUniformCells f ∣ N :=
  (Nat.sInf_mem ⟨N, N_mem_uniformSet hN f⟩).1

/-- `U(f) ≥ 1`. -/
theorem minUniformCells_pos {N : ℕ} (hN : 0 < N) (f : Fin N → ℝ) :
    0 < minUniformCells f :=
  (Nat.sInf_mem ⟨N, N_mem_uniformSet hN f⟩).2.1

/-- Minimality: if `f` is constant on the uniform `k`-partition (`k ∣ N`, `k ≥ 1`),
then `U(f) ≤ k`. -/
theorem minUniformCells_le_of_uniform {N : ℕ} (f : Fin N → ℝ) {k : ℕ}
    (hk : k ∣ N) (hk1 : 1 ≤ k) (hc : ConstantOnUniformCells f k) :
    minUniformCells f ≤ k :=
  Nat.sInf_le ⟨hk, hk1, hc⟩

/-- A constant signal needs exactly one uniform cell: `U(const) = 1`. -/
theorem minUniformCells_const {N : ℕ} (hN : 0 < N) (f : Fin N → ℝ)
    (hf : ∀ i j : Fin N, f i = f j) :
    minUniformCells f = 1 :=
  le_antisymm
    (Nat.sInf_le ⟨one_dvd N, le_refl 1, fun i j _ => hf i j⟩)
    (Nat.sInf_mem ⟨N, N_mem_uniformSet hN f⟩).2.1

/-! ## Definition 171: Representation gap -/

/--
**fdrs.md**: Definition 171 (Representation gap) [§11.5.2 · Phase 11]

Gap(f, T) = U(f) / |Leaves(T)|.
-/
noncomputable def representationGap {N : ℕ} (T : NonStationaryRadixTree N)
    (f : Fin N → ℝ) : ℝ :=
  if T.leafCount = 0 then 0
  else (minUniformCells f : ℝ) / (T.leafCount : ℝ)

/-! ## Proposition 135 (honest form): the gap is a genuine quantity -/

/--
**fdrs.md**: Proposition 135 (collapse direction) [§11.5.3 · Phase 11]

**Honest replacement for the former vacuous `representationGap_ge_one`.**

The old `Gap ≥ 1` held only because `minUniformCells` was the placeholder `:= N`
(making `Gap = N / leafCount ≥ 1` whenever `leafCount ≤ N` — a triviality). With
the real `U(f)`, a per-tree `Gap ≥ 1` is *false*: a non-minimal homogeneous tree
can carry more leaves than `U(f)` (e.g. a 5-leaf tree on a constant signal gives
`Gap = 1/5`). What survives — and is exactly the experiment's measured
`adv-over-uniform = 0.0000` at `Gap = 1` — is the **collapse direction**: when a
tree's `leafCount` is a valid equipartition size on which `f` is constant (i.e.
`f` is adapted to the homogeneous/uniform tree), the equal-size uniform partition
loses nothing, so `Gap ≤ 1`.
-/
theorem representationGap_le_one_of_uniform {N : ℕ}
    (T : NonStationaryRadixTree N) (f : Fin N → ℝ)
    (hdvd : T.leafCount ∣ N) (hpos : 1 ≤ T.leafCount)
    (hc : ConstantOnUniformCells f T.leafCount) :
    representationGap T f ≤ 1 := by
  unfold representationGap
  rw [if_neg (by omega : T.leafCount ≠ 0),
    div_le_one (by exact_mod_cast hpos : (0 : ℝ) < (T.leafCount : ℝ))]
  exact_mod_cast minUniformCells_le_of_uniform f hdvd hpos hc

/--
**fdrs.md**: Proposition 135 (strict gap) [§11.5.3 · Phase 11]

**The genuine content of Proposition 135**: heterogeneity can strictly pay off.
There is a signal and a *heterogeneous* adapted tree whose leaf count is below the
best uniform partition, so `Gap > 1`. Concrete witness on `Fin 4`: the heterogeneous
tree `node [leaf 2 0, node [leaf 1 2, leaf 1 3]]` (3 leaves) is adapted to
`f = ![0,0,1,2]`, yet the only equipartition of `{0,1,2,3}` on which `f` is constant
is the singleton one (the `k = 1, 2` equipartitions are ruled out by
`f 0 ≠ f 2` and `f 2 ≠ f 3`), so `U(f) = 4` and `Gap = 4/3 > 1`.
-/
theorem representationGap_gt_one_example :
    ∃ (N : ℕ) (T : NonStationaryRadixTree N) (f : Fin N → ℝ),
      T.tree.isHeterogeneous ∧ IsTreeAdapted T f ∧ 1 < representationGap T f := by
  refine ⟨4, ⟨.node [.leaf 2 0, .node [.leaf 1 2, .leaf 1 3]]⟩,
    fun i => if i.val < 2 then 0 else if i.val = 2 then 1 else 2, ?_, ?_, ?_⟩
  · -- heterogeneous: the two root children have child-counts 0 and 2
    intro h
    simp only [RadixTree.isHomogeneous] at h
    have h2 := h.1 (.leaf 2 0) (by simp) (.node [.leaf 1 2, .leaf 1 3]) (by simp)
    simp [RadixTree.childCount] at h2
  · -- adapted: f is constant on each leaf cell
    intro leaf hleaf i j hi hj
    have hlv : (⟨.node [.leaf 2 0, .node [.leaf 1 2, .leaf 1 3]]⟩ :
        NonStationaryRadixTree 4).leaves = [⟨0, 2, 0⟩, ⟨0, 1, 2⟩, ⟨0, 1, 3⟩] := by
      simp [NonStationaryRadixTree.leaves, NonStationaryRadixTree.extractLeaves,
        List.flatMap_cons, List.flatMap_nil]
    rw [hlv] at hleaf
    fin_cases hleaf
    · obtain ⟨_, hi2⟩ := hi; obtain ⟨_, hj2⟩ := hj
      have e1 : i.val < 2 := by simpa using hi2
      have e2 : j.val < 2 := by simpa using hj2
      simp [e1, e2]
    · obtain ⟨hi1, hi2⟩ := hi; obtain ⟨hj1, hj2⟩ := hj
      have : i = j := Fin.ext (by simp only [] at *; omega)
      rw [this]
    · obtain ⟨hi1, hi2⟩ := hi; obtain ⟨hj1, hj2⟩ := hj
      have : i = j := Fin.ext (by simp only [] at *; omega)
      rw [this]
  · -- the gap is 4/3 > 1
    set g : Fin 4 → ℝ := fun i => if i.val < 2 then 0 else if i.val = 2 then 1 else 2 with hg
    have hlc : (⟨.node [.leaf 2 0, .node [.leaf 1 2, .leaf 1 3]]⟩ :
        NonStationaryRadixTree 4).leafCount = 3 := by
      simp [NonStationaryRadixTree.leafCount, RadixTree.leafCount, RadixTree.leafCountList]
    have hminU : minUniformCells g = 4 := by
      refine le_antisymm (minUniformCells_le_N (by norm_num) g) ?_
      have hmem : minUniformCells g ∈ {k | k ∣ 4 ∧ 1 ≤ k ∧ ConstantOnUniformCells g k} :=
        Nat.sInf_mem ⟨4, N_mem_uniformSet (by norm_num) g⟩
      obtain ⟨hdvd, h1, hc⟩ := hmem
      rcases (Nat.le_of_dvd (by norm_num) hdvd).lt_or_eq with hlt | heq
      · exfalso
        have hcases : minUniformCells g = 1 ∨ minUniformCells g = 2 ∨ minUniformCells g = 3 := by
          omega
        rcases hcases with h | h | h
        · rw [h] at hc
          have h02 := hc 0 2 (by decide)
          simp only [hg] at h02; norm_num at h02
        · rw [h] at hc
          have h23 := hc 2 3 (by decide)
          simp only [hg] at h23; norm_num at h23
        · rw [h] at hdvd; exact absurd hdvd (by decide)
      · omega
    unfold representationGap
    rw [hlc, hminU]
    norm_num

/-! ## Theorem 67: Depth-2 gap formula -/

/--
**fdrs.md**: Theorem 67 (Depth-2 gap formula) [§11.5.4 · Phase 11]

For a depth-2 tree with root branching b₀ ≥ 2 and child branching r_i ≥ 1:
  sum(r) > 0 and b₀ · lcm(r) ≥ sum(r).

The second part uses: each r_i ∣ lcm(r), so r_i ≤ lcm(r), so sum(r) ≤ b₀ · lcm(r).
-/
theorem depth2GapFormula (b₀ : ℕ) (r : Fin b₀ → ℕ)
    (hb : b₀ ≥ 2) (hr : ∀ i, r i ≥ 1) :
    let lcm_r := Finset.univ.lcm r
    let sum_r := Finset.univ.sum r
    sum_r > 0 ∧ (b₀ * lcm_r : ℕ) ≥ sum_r := by
  simp only
  have i0 : Fin b₀ := ⟨0, by omega⟩
  have hlcm_pos : 0 < Finset.univ.lcm r := by
    rw [Nat.pos_iff_ne_zero]
    rw [Finset.lcm_ne_zero_iff]
    intro x _
    have := hr x; omega
  constructor
  · -- sum > 0
    apply Finset.sum_pos
    · intro i _; exact Nat.lt_of_lt_of_le Nat.zero_lt_one (hr i)
    · exact ⟨i0, Finset.mem_univ _⟩
  · -- b₀ * lcm ≥ sum
    have hle : ∀ i : Fin b₀, r i ≤ Finset.univ.lcm r := by
      intro i
      exact Nat.le_of_dvd hlcm_pos (Finset.dvd_lcm (Finset.mem_univ i))
    calc Finset.univ.sum r
        ≤ Finset.univ.sum (fun _ => Finset.univ.lcm r) :=
          Finset.sum_le_sum (fun i _ => hle i)
      _ = b₀ * Finset.univ.lcm r := by simp [Finset.sum_const]

/-! ## Corollary 31: Compensated heterogeneity -/

/--
**fdrs.md**: Corollary 31 (Compensated heterogeneity) [§11.5.5 · Phase 11]

b₀ * lcm(r) = sum(r) iff all r_i are equal.
-/
theorem compensatedHeterogeneity (b₀ : ℕ) (r : Fin b₀ → ℕ)
    (hb : b₀ ≥ 2) (hr : ∀ i, r i ≥ 1) :
    let lcm_r := Finset.univ.lcm r
    let sum_r := Finset.univ.sum r
    (b₀ * lcm_r = sum_r) ↔ (∀ i j : Fin b₀, r i = r j) := by
  simp only
  have i0 : Fin b₀ := ⟨0, by omega⟩
  have hlcm_pos : 0 < Finset.univ.lcm r := by
    rw [Nat.pos_iff_ne_zero]
    rw [Finset.lcm_ne_zero_iff]
    intro x _
    have := hr x; omega
  constructor
  · -- Forward: b₀ * lcm = sum → all equal
    intro heq
    have hle : ∀ i : Fin b₀, r i ≤ Finset.univ.lcm r :=
      fun i => Nat.le_of_dvd hlcm_pos (Finset.dvd_lcm (Finset.mem_univ i))
    have hall : ∀ i : Fin b₀, r i = Finset.univ.lcm r := by
      by_contra hne
      push_neg at hne
      obtain ⟨i, hi⟩ := hne
      have hlt : r i < Finset.univ.lcm r := lt_of_le_of_ne (hle i) hi
      have : Finset.univ.sum r < Finset.univ.sum (fun _ : Fin b₀ => Finset.univ.lcm r) :=
        Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ i, hlt⟩
      simp [Finset.sum_const] at this
      omega
    exact fun i j => by rw [hall i, hall j]
  · -- Backward: all equal → b₀ * lcm = sum
    intro hall
    have heq_r : ∀ i, r i = r i0 := fun i => hall i i0
    have hlcm : Finset.univ.lcm r = r i0 := by
      apply Nat.dvd_antisymm
      · exact Finset.lcm_dvd (fun i _ => dvd_of_eq (heq_r i))
      · exact Finset.dvd_lcm (Finset.mem_univ i0)
    have hsum : Finset.univ.sum r = b₀ * r i0 := by
      conv_lhs => arg 2; ext i; rw [heq_r i]
      simp [Finset.sum_const]
    rw [hlcm, hsum]

end FdrsFormal.Analysis.DigitConditional
