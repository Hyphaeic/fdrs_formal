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
Authors: [Your Name]

# Ultrametric Topology on Mixed-Radix Spaces

This file defines the ultrametric topology on mixed-radix spaces via cylinder sets.

## References

- fdrs.md, Phase 1 Fragment 1, Section 5 (Definitions 5.1-5.3, Propositions 5.4-5.6)
-/

import FdrsFormal.Core.Infinite
import FdrsFormal.Topology.PrefixCongruence
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Topology.MetricSpace.Basic

namespace FdrsFormal.Topology.Ultrametric

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite FdrsFormal.Core.Infinite
open FdrsFormal.Topology.PrefixCongruence

variable {b : RadixSeq}

/-! ## Definition 8: Cylinder sets -/

/-- Cylinder set U(s) = {x : x_i = s_i for all i < L} -/
def cylinder (b : RadixSeq) (L : ℕ) (s : (i : Fin L) → Fin (b i)) : Set (CompletedSpace b) :=
  {x | ∀ i : Fin L, x i = s i}

/-- The residue of a prefix: r(s) = ∑_{i<L} s_i * B_i -/
def prefixResidue (b : RadixSeq) (L : ℕ) (s : (i : Fin L) → Fin (b i)) : ℕ :=
  ∑ i : Fin L, (s i : ℕ) * placeValue b i

/-! ## Definition 9: Ultrametric distance -/

open Classical in
/-- Find the first index where two sequences differ -/
noncomputable def firstDiff (b : RadixSeq) (x y : CompletedSpace b) : ℕ :=
  if h : x ≠ y then Nat.find (Function.ne_iff.mp h) else 0

open Classical in
/-- The ultrametric distance: δ(x,y) = B_m^{-1} where m is the first differing index -/
noncomputable def ultrametricDist (b : RadixSeq) (x y : CompletedSpace b) : ℝ :=
  if x = y then 0 else (placeValue b (firstDiff b x y) : ℝ)⁻¹

/-! ## Proposition 3: Ultrametric axioms

**fdrs.md**: Proposition 3 (δ is an ultrametric) [§5.4 · Phase 1, Fragment 1] (lines 188-210) -/

/-- Helper: firstDiff is well-defined when sequences differ -/
theorem firstDiff_spec {x y : CompletedSpace b} (h : x ≠ y) :
    x (firstDiff b x y) ≠ y (firstDiff b x y) := by
  unfold firstDiff
  have hex : ∃ i, x i ≠ y i := Function.ne_iff.mp h
  rw [dif_pos h]
  exact Nat.find_spec hex

/-- Helper: indices below firstDiff have equal values -/
theorem eq_of_lt_firstDiff {x y : CompletedSpace b} (h : x ≠ y) {i : ℕ} (hi : i < firstDiff b x y) :
    x i = y i := by
  unfold firstDiff at hi
  have hex : ∃ j, x j ≠ y j := Function.ne_iff.mp h
  rw [dif_pos h] at hi
  by_contra h_ne
  exact Nat.find_min hex hi h_ne

theorem ultrametricDist_self_iff (x y : CompletedSpace b) :
    ultrametricDist b x y = 0 ↔ x = y := by
  constructor
  · intro h
    unfold ultrametricDist at h
    split_ifs at h with heq
    · exact heq
    · -- If x ≠ y, then δ = B_m^{-1} > 0, contradiction
      exfalso
      have hpos : 0 < (placeValue b (firstDiff b x y) : ℝ)⁻¹ := by
        apply inv_pos.mpr
        exact Nat.cast_pos.mpr (placeValue.pos _)
      linarith
  · intro h
    rw [h]
    unfold ultrametricDist
    simp

theorem ultrametricDist_comm (x y : CompletedSpace b) :
    ultrametricDist b x y = ultrametricDist b y x := by
  unfold ultrametricDist
  by_cases hxy : x = y
  · simp [hxy]
  · by_cases hyx : y = x
    · simp [hyx]
    · -- Both x ≠ y and y ≠ x, show firstDiff b x y = firstDiff b y x
      simp only [if_neg hxy, if_neg hyx]
      congr 1
      unfold firstDiff
      have hx : ∃ i, x i ≠ y i := Function.ne_iff.mp hxy
      have hy : ∃ i, y i ≠ x i := Function.ne_iff.mp hyx
      rw [dif_pos hxy, dif_pos hyx]
      -- Both Nat.find are searching for the same property (swapped equality)
      -- The predicates are equivalent by ne_comm
      congr
      funext m
      simp only [ne_comm]

theorem ultrametricDist_nonneg (x y : CompletedSpace b) :
    0 ≤ ultrametricDist b x y := by
  unfold ultrametricDist
  split_ifs
  · rfl
  · apply inv_nonneg.mpr
    exact Nat.cast_nonneg _

/-- **Proposition 3**: Strong triangle inequality -/
theorem ultrametricDist_triangle (x y z : CompletedSpace b) :
    ultrametricDist b x z ≤ max (ultrametricDist b x y) (ultrametricDist b y z) := by
  unfold ultrametricDist
  by_cases hxz : x = z
  · -- Case: x = z, distance is 0
    subst hxz
    simp
    left
    exact ultrametricDist_nonneg _ _
  · by_cases hxy : x = y
    · -- Case: x ≠ z, x = y
      subst hxy
      simp [hxz]
    · by_cases hyz : y = z
      · -- Case: x ≠ z, x ≠ y, y = z
        subst hyz
        simp [hxz, hxy]
      · -- Case: x ≠ z, x ≠ y, y ≠ z - the main case
        simp only [if_neg hxz, if_neg hxy, if_neg hyz]
        -- Prove: B_{m_xz}^{-1} ≤ max(B_{m_xy}^{-1}, B_{m_yz}^{-1})
        -- Strategy: show firstDiff x z ≥ min(firstDiff x y, firstDiff y z)
        set m_xy := firstDiff b x y
        set m_yz := firstDiff b y z
        set m_xz := firstDiff b x z
        set m := min m_xy m_yz

        -- Show that x and z agree on all indices < m
        have h_agree : ∀ i < m, x i = z i := by
          intro i hi
          have hi_xy : i < m_xy := Nat.lt_of_lt_of_le hi (Nat.min_le_left _ _)
          have hi_yz : i < m_yz := Nat.lt_of_lt_of_le hi (Nat.min_le_right _ _)
          calc x i = y i := eq_of_lt_firstDiff hxy hi_xy
               _ = z i := eq_of_lt_firstDiff hyz hi_yz

        -- Therefore firstDiff x z ≥ m
        have h_ge : m ≤ m_xz := by
          by_contra h_not
          push_neg at h_not
          -- If m_xz < m, then x and z agree at m_xz
          have : x m_xz = z m_xz := h_agree m_xz h_not
          -- But they differ at m_xz by definition of firstDiff
          have : x m_xz ≠ z m_xz := firstDiff_spec hxz
          contradiction

        -- Since placeValue is strictly monotone, B_m ≤ B_{m_xz}, so B_{m_xz}^{-1} ≤ B_m^{-1}
        have h_place_le : placeValue b m ≤ placeValue b m_xz :=
          placeValue.mono h_ge
        have h_inv_le : (placeValue b m_xz : ℝ)⁻¹ ≤ (placeValue b m : ℝ)⁻¹ := by
          have h_pos_m : (0 : ℝ) < placeValue b m := Nat.cast_pos.mpr (placeValue.pos m)
          have h_pos_mxz : (0 : ℝ) < placeValue b m_xz := Nat.cast_pos.mpr (placeValue.pos m_xz)
          rw [inv_le_inv₀ h_pos_mxz h_pos_m]
          exact Nat.cast_le.mpr h_place_le

        -- And B_m^{-1} = max(B_{m_xy}^{-1}, B_{m_yz}^{-1})
        have h_max : (placeValue b m : ℝ)⁻¹ = max (placeValue b m_xy : ℝ)⁻¹ (placeValue b m_yz : ℝ)⁻¹ := by
          show (placeValue b (min m_xy m_yz) : ℝ)⁻¹ = max (placeValue b m_xy : ℝ)⁻¹ (placeValue b m_yz : ℝ)⁻¹
          by_cases h_comp : m_yz < m_xy
          · -- m_yz < m_xy, so min = m_yz and max of inverses = inverse of min
            rw [min_eq_right (Nat.le_of_lt h_comp)]
            have h_lt : (placeValue b m_yz : ℝ) < placeValue b m_xy := Nat.cast_lt.mpr (placeValue.strictMono h_comp)
            have h_pos_xy : (0 : ℝ) < placeValue b m_xy := Nat.cast_pos.mpr (placeValue.pos m_xy)
            have h_pos_yz : (0 : ℝ) < placeValue b m_yz := Nat.cast_pos.mpr (placeValue.pos m_yz)
            have h_inv_lt : (placeValue b m_xy : ℝ)⁻¹ < (placeValue b m_yz : ℝ)⁻¹ := by
              rw [inv_lt_inv₀ h_pos_xy h_pos_yz]
              exact h_lt
            rw [max_eq_right_of_lt h_inv_lt]
          · -- m_xy ≤ m_yz, so min = m_xy and max of inverses = inverse of min
            push_neg at h_comp
            have h_le : m_xy ≤ m_yz := h_comp
            rw [min_eq_left h_le]
            by_cases h_eq : m_xy = m_yz
            · rw [h_eq]; simp [max_self]
            · have h_lt : m_xy < m_yz := Nat.lt_of_le_of_ne h_le h_eq
              have h_lt_cast : (placeValue b m_xy : ℝ) < placeValue b m_yz := Nat.cast_lt.mpr (placeValue.strictMono h_lt)
              have h_pos_xy : (0 : ℝ) < placeValue b m_xy := Nat.cast_pos.mpr (placeValue.pos m_xy)
              have h_pos_yz : (0 : ℝ) < placeValue b m_yz := Nat.cast_pos.mpr (placeValue.pos m_yz)
              have h_inv_lt : (placeValue b m_yz : ℝ)⁻¹ < (placeValue b m_xy : ℝ)⁻¹ := by
                rw [inv_lt_inv₀ h_pos_yz h_pos_xy]
                exact h_lt_cast
              rw [max_eq_left_of_lt h_inv_lt]

        calc (placeValue b m_xz : ℝ)⁻¹
            ≤ (placeValue b m : ℝ)⁻¹ := h_inv_le
          _ = max (placeValue b m_xy : ℝ)⁻¹ (placeValue b m_yz : ℝ)⁻¹ := h_max

/-! ## Metric space instance -/

/-- The regular triangle inequality follows from the ultrametric inequality -/
theorem ultrametricDist_triangle_regular (x y z : CompletedSpace b) :
    ultrametricDist b x z ≤ ultrametricDist b x y + ultrametricDist b y z := by
  calc ultrametricDist b x z
      ≤ max (ultrametricDist b x y) (ultrametricDist b y z) := ultrametricDist_triangle x y z
    _ ≤ ultrametricDist b x y + ultrametricDist b y z := max_le_add_of_nonneg
        (ultrametricDist_nonneg x y) (ultrametricDist_nonneg y z)

noncomputable instance : MetricSpace (CompletedSpace b) where
  dist := ultrametricDist b
  dist_self := fun x => by unfold ultrametricDist; simp
  dist_comm := ultrametricDist_comm
  dist_triangle := ultrametricDist_triangle_regular
  eq_of_dist_eq_zero := fun h => (ultrametricDist_self_iff _ _).mp h

noncomputable instance : IsUltrametricDist (CompletedSpace b) where
  dist_triangle_max := ultrametricDist_triangle

/-! ## Propositions 5.5-5.6 -/

/-- Helper: characterize when distance is less than B_L^{-1} -/
theorem ultrametricDist_lt_placeValue_inv_iff {x y : CompletedSpace b} (L : ℕ) :
    ultrametricDist b x y < (placeValue b L : ℝ)⁻¹ ↔
    (x = y ∨ L < firstDiff b x y) := by
  constructor
  · intro h
    unfold ultrametricDist at h
    split_ifs at h with heq
    · left; exact heq
    · right
      -- h : (placeValue b (firstDiff b x y))⁻¹ < (placeValue b L)⁻¹
      -- Since inv is order-reversing on positive reals, this means placeValue b L < placeValue b (firstDiff b x y)
      -- And since placeValue is strictly monotone, this means L < firstDiff b x y
      have h_pos_L : (0 : ℝ) < placeValue b L := Nat.cast_pos.mpr (placeValue.pos L)
      have h_pos_fd : (0 : ℝ) < placeValue b (firstDiff b x y) := Nat.cast_pos.mpr (placeValue.pos _)
      have h_inv : (placeValue b L : ℝ) < placeValue b (firstDiff b x y) := by
        rw [inv_lt_inv₀ h_pos_fd h_pos_L] at h
        exact h
      have h_nat : placeValue b L < placeValue b (firstDiff b x y) := by
        exact Nat.cast_lt.mp h_inv
      exact placeValue.strictMono.lt_iff_lt.mp h_nat
  · intro h
    cases h with
    | inl heq =>
      rw [heq]
      unfold ultrametricDist
      simp only [if_true]
      have h_pos : (0 : ℝ) < placeValue b L := Nat.cast_pos.mpr (placeValue.pos L)
      exact inv_pos.mpr h_pos
    | inr hlt =>
      unfold ultrametricDist
      split_ifs with heq
      · have h_pos : (0 : ℝ) < placeValue b L := Nat.cast_pos.mpr (placeValue.pos L)
        exact inv_pos.mpr h_pos
      · -- Need to show (placeValue b (firstDiff b x y))⁻¹ < (placeValue b L)⁻¹
        have h_nat : placeValue b L < placeValue b (firstDiff b x y) :=
          placeValue.strictMono hlt
        have h_cast : (placeValue b L : ℝ) < placeValue b (firstDiff b x y) :=
          Nat.cast_lt.mpr h_nat
        have h_pos_fd : (0 : ℝ) < placeValue b (firstDiff b x y) := Nat.cast_pos.mpr (placeValue.pos (firstDiff b x y))
        have h_pos_L : (0 : ℝ) < placeValue b L := Nat.cast_pos.mpr (placeValue.pos L)
        rw [inv_lt_inv₀ h_pos_fd h_pos_L]
        exact h_cast

/-- Helper: characterize when distance is at most B_L^{-1} -/
theorem ultrametricDist_le_placeValue_inv_iff {x y : CompletedSpace b} (L : ℕ) :
    ultrametricDist b x y ≤ (placeValue b L : ℝ)⁻¹ ↔
    (x = y ∨ L ≤ firstDiff b x y) := by
  constructor
  · intro h
    unfold ultrametricDist at h
    split_ifs at h with heq
    · left; exact heq
    · right
      -- h : (placeValue b (firstDiff b x y))⁻¹ ≤ (placeValue b L)⁻¹
      have h_pos_L : (0 : ℝ) < placeValue b L := Nat.cast_pos.mpr (placeValue.pos L)
      have h_pos_fd : (0 : ℝ) < placeValue b (firstDiff b x y) := Nat.cast_pos.mpr (placeValue.pos _)
      have h_inv : (placeValue b L : ℝ) ≤ placeValue b (firstDiff b x y) := by
        rw [inv_le_inv₀ h_pos_fd h_pos_L] at h
        exact h
      have h_nat : placeValue b L ≤ placeValue b (firstDiff b x y) :=
        Nat.cast_le.mp h_inv
      exact placeValue.strictMono.le_iff_le.mp h_nat
  · intro h
    cases h with
    | inl heq =>
      rw [heq]
      unfold ultrametricDist
      simp only [if_true]
      have h_pos : (0 : ℝ) < placeValue b L := Nat.cast_pos.mpr (placeValue.pos L)
      exact le_of_lt (inv_pos.mpr h_pos)
    | inr hle =>
      unfold ultrametricDist
      split_ifs with heq
      · have h_pos : (0 : ℝ) < placeValue b L := Nat.cast_pos.mpr (placeValue.pos L)
        exact le_of_lt (inv_pos.mpr h_pos)
      · have h_nat : placeValue b L ≤ placeValue b (firstDiff b x y) :=
          placeValue.mono hle
        have h_cast : (placeValue b L : ℝ) ≤ placeValue b (firstDiff b x y) :=
          Nat.cast_le.mpr h_nat
        have h_pos_fd : (0 : ℝ) < placeValue b (firstDiff b x y) := Nat.cast_pos.mpr (placeValue.pos (firstDiff b x y))
        have h_pos_L : (0 : ℝ) < placeValue b L := Nat.cast_pos.mpr (placeValue.pos L)
        rw [inv_le_inv₀ h_pos_fd h_pos_L]
        exact h_cast

/-- Helper: sequences agree on first L digits iff they're equal or differ beyond L -/
theorem agree_on_prefix_iff {x y : CompletedSpace b} (L : ℕ) :
    (∀ i : Fin L, x i = y i) ↔ (x = y ∨ L ≤ firstDiff b x y) := by
  constructor
  · intro h_agree
    by_cases heq : x = y
    · left; exact heq
    · right
      -- If x ≠ y but they agree on first L digits, then firstDiff b x y ≥ L
      by_contra h_not
      push_neg at h_not
      -- h_not : firstDiff b x y < L
      -- But then x and y differ at firstDiff b x y < L, contradicting h_agree
      have h_diff : x (firstDiff b x y) ≠ y (firstDiff b x y) := firstDiff_spec heq
      have : firstDiff b x y < L := h_not
      have h_fd_fin : (⟨firstDiff b x y, this⟩ : Fin L) ∈ Finset.univ := Finset.mem_univ _
      have h_agree_fd := h_agree ⟨firstDiff b x y, this⟩
      contradiction
  · intro h
    cases h with
    | inl heq => intro i; rw [heq]
    | inr hle =>
      intro i
      by_cases heq : x = y
      · rw [heq]
      · -- x ≠ y and firstDiff b x y ≥ L, so for i < L, x i = y i
        have : i.val < L := i.isLt
        have : i.val < firstDiff b x y := Nat.lt_of_lt_of_le this hle
        exact eq_of_lt_firstDiff heq this

/-- **Proposition 4**: Closed balls equal cylinders.
    Metric.closedBall x B_L^{-1} = cylinder b L (take x L) -/
theorem closedBall_eq_cylinder (L : ℕ) (x : CompletedSpace b) :
    Metric.closedBall x ((placeValue b L : ℝ)⁻¹) = cylinder b L (CompletedSpace.take x L) := by
  ext y
  simp only [Metric.mem_closedBall, cylinder, Set.mem_setOf_eq]
  constructor
  · intro h
    -- h : dist x y ≤ (placeValue b L)⁻¹
    have := (ultrametricDist_le_placeValue_inv_iff L).mp h
    have h_agree := (agree_on_prefix_iff L).mpr this
    intro i
    exact h_agree i
  · intro h
    -- h : ∀ i : Fin L, y i = (CompletedSpace.take x L) i
    have h_agree : ∀ i : Fin L, x i = y i := by
      intro i
      have := h i
      unfold CompletedSpace.take at this
      exact this.symm
    have := (agree_on_prefix_iff L).mp h_agree
    rw [dist_comm]
    exact (ultrametricDist_le_placeValue_inv_iff L).mpr this

/-- Open ball is contained in cylinder (one direction of the attempted ball_eq_cylinder) -/
theorem ball_subset_cylinder (L : ℕ) (x : CompletedSpace b) :
    Metric.ball x ((placeValue b L : ℝ)⁻¹) ⊆ cylinder b L (CompletedSpace.take x L) := by
  intro y hy
  have hle : y ∈ Metric.closedBall x ((placeValue b L : ℝ)⁻¹) := Metric.ball_subset_closedBall hy
  rw [closedBall_eq_cylinder] at hle
  exact hle

theorem cylinder_isClopen (L : ℕ) (s : (i : Fin L) → Fin (b i)) :
    IsClopen (cylinder b L s) := by
  constructor
  · -- Cylinder is closed: show complement is open
    rw [← isOpen_compl_iff]
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    -- hx : x ∈ (cylinder b L s)ᶜ, i.e., x ∉ cylinder b L s
    simp only [Set.mem_compl_iff, cylinder, Set.mem_setOf_eq] at hx
    push_neg at hx
    obtain ⟨i, hi⟩ := hx
    -- The cylinder containing x with prefix (take x L) is disjoint from cylinder b L s
    rw [mem_nhds_iff]
    use cylinder b L (CompletedSpace.take x L)
    constructor
    · -- Show it's a subset of the complement
      intro y hy
      simp only [Set.mem_compl_iff, cylinder, Set.mem_setOf_eq] at hy ⊢
      push_neg
      use i
      intro hy_s
      -- y ∈ cylinder with x's prefix means y i = x i
      unfold CompletedSpace.take at hy
      have h_yi_eq_xi : y i = x i := hy i
      -- But hi says x i ≠ s i, and hy_s says y i = s i
      have h_xi_eq_si : x i = s i := calc
        x i = y i := h_yi_eq_xi.symm
        _ = s i := hy_s
      exact hi h_xi_eq_si
    · refine ⟨?_, ?_⟩
      · -- Show it's open (it's a closed ball, which is open in ultrametric spaces)
        rw [← closedBall_eq_cylinder L x]
        have hr : ((placeValue b L : ℝ)⁻¹ : ℝ) ≠ 0 := by
          apply ne_of_gt
          exact inv_pos.mpr (Nat.cast_pos.mpr (placeValue.pos L))
        exact IsUltrametricDist.isOpen_closedBall x hr
      · -- x is in it
        intro j
        rfl
  · -- Cylinder is open: closed balls are open in ultrametric spaces
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    -- hx : x ∈ cylinder b L s, i.e., ∀ i : Fin L, x i = s i
    rw [mem_nhds_iff]
    use cylinder b L s
    refine ⟨Set.Subset.refl _, ?_, hx⟩
    -- Show cylinder is open by showing it equals a closed ball centered at x
    have h_eq : cylinder b L s = cylinder b L (CompletedSpace.take x L) := by
      ext y
      simp only [cylinder, Set.mem_setOf_eq]
      constructor
      · intro hy i
        unfold CompletedSpace.take
        calc y i = s i := hy i
             _ = x i := (hx i).symm
      · intro hy i
        unfold CompletedSpace.take at hy
        calc y i = x i := hy i
             _ = s i := hx i
    rw [h_eq, ← closedBall_eq_cylinder L x]
    have hr : ((placeValue b L : ℝ)⁻¹ : ℝ) ≠ 0 := by
      apply ne_of_gt
      exact inv_pos.mpr (Nat.cast_pos.mpr (placeValue.pos L))
    exact IsUltrametricDist.isOpen_closedBall x hr

/-- Helper: decode can be split by prefix -/
theorem decode_split_prefix (τ : DirectLimitSpace b) (L : ℕ) :
    ∃ q : ℕ, decode b τ = (∑ i : Fin L, (τ.digits i : ℕ) * placeValue b i) + q * placeValue b L := by
  -- Use the congruence result: decode τ ≡ prefix_sum (mod B_L)
  have h_mod := decode_mod_eq_prefix_mod b τ L
  -- This means decode τ = prefix_sum + (some multiple of B_L)
  set prefix_sum := ∑ i : Fin L, (τ.digits i : ℕ) * placeValue b i with hps
  set n := decode b τ with hn
  -- n % B_L = prefix_sum % B_L, and we know prefix_sum < B_L
  have h_prefix_lt : prefix_sum < placeValue b L := prefix_sum_lt_placeValue b L (fun i => τ.digits i)
  have h_prefix_mod : prefix_sum % placeValue b L = prefix_sum := Nat.mod_eq_of_lt h_prefix_lt
  rw [h_prefix_mod] at h_mod
  -- Use n / B_L as our q
  use n / placeValue b L
  -- n = B_L * (n / B_L) + (n % B_L) = B_L * q + prefix_sum
  have h_div_mod := Nat.div_add_mod n (placeValue b L)
  rw [h_mod] at h_div_mod
  -- h_div_mod : B_L * (n / B_L) + prefix_sum = n
  -- We need: n = prefix_sum + (n / B_L) * B_L
  rw [mul_comm, add_comm]
  exact h_div_mod.symm

/-- Helper: Extract digit i from a sum using modular arithmetic -/
theorem extract_digit_from_decode {L : ℕ} (τ : DirectLimitSpace b) (i : Fin L) :
    ((decode b τ) / placeValue b i) % b i = (τ.digits i : ℕ) := by
  -- Use encode_decode: encode b (decode b τ) = τ
  -- The encode function extracts digits via (n / B_i) % b_i
  have h_enc_dec := encode_decode τ
  set n := decode b τ with hn
  set σ := encode b n with hσ
  -- From h_enc_dec, we have σ = τ, so σ.digits i = τ.digits i
  have h_digits_eq : σ.digits i = τ.digits i := by rw [h_enc_dec]
  -- We need to show (n / B_i) % b_i = (τ.digits i : ℕ)
  conv_rhs => rw [← h_digits_eq]
  -- Now show (n / B_i) % b_i = (σ.digits i : ℕ)
  set K := findHorizon b n with hK
  have h_bound := findHorizon_bound b n
  -- σ.digits i is defined by: if i ≤ K then encodeFinite else 0
  have σ_digits_def : σ.digits i = if h : i.val ≤ K
      then encodeFinite b K ⟨n, h_bound⟩ ⟨i, Nat.lt_succ_of_le h⟩
      else ⟨0, b.pos i⟩ := rfl
  rw [σ_digits_def]
  -- Case split on i ≤ K
  split_ifs with h_le
  · -- Case: i ≤ K, encodeFinite extracts (n / B_i) % b_i
    simp only [encodeFinite]
  · -- Case: i > K, so σ.digits i = 0 and n / B_i = 0
    have h_lt : K < i := Nat.lt_of_not_le h_le
    have h_n_lt_BK1 : n < placeValue b (K + 1) := h_bound
    have h_BK1_le_Bi : placeValue b (K + 1) ≤ placeValue b i := placeValue.mono (Nat.succ_le_of_lt h_lt)
    have h_n_lt_Bi : n < placeValue b i := Nat.lt_of_lt_of_le h_n_lt_BK1 h_BK1_le_Bi
    have h_div_zero : n / placeValue b i = 0 := Nat.div_eq_zero_iff.mpr (Or.inr h_n_lt_Bi)
    simp [h_div_zero]

/-- **Proposition 5**: Cylinders are congruence classes -/
theorem cylinder_iff_congruence (L : ℕ) (s : (i : Fin L) → Fin (b i)) (τ : DirectLimitSpace b) :
    DirectLimitSpace.embed b τ ∈ cylinder b L s ↔ decode b τ ≡ prefixResidue b L s [MOD placeValue b L] := by
  unfold DirectLimitSpace.embed cylinder prefixResidue
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h
    -- h : ∀ i : Fin L, τ.digits i = s i
    -- Need to show: decode τ ≡ ∑ i<L, s_i * B_i (mod B_L)
    show (decode b τ) % placeValue b L = (∑ i : Fin L, (s i : ℕ) * placeValue b i) % placeValue b L
    -- Key: decode τ = ∑_{i<L} τ_i * B_i + (higher terms divisible by B_L)
    obtain ⟨q, hq⟩ := decode_split_prefix τ L
    rw [hq]
    -- Substitute τ_i = s_i for i < L
    have h_sum_eq : ∑ i : Fin L, (τ.digits i : ℕ) * placeValue b i =
                    ∑ i : Fin L, (s i : ℕ) * placeValue b i := by
      congr 1
      ext i
      congr 1
      exact congrArg Fin.val (h i)
    rw [h_sum_eq]
    simp [Nat.add_mul_mod_self_right]
  · intro h
    -- h : decode τ ≡ ∑ s_j * B_j (mod B_L)
    -- Need to show: ∀ i : Fin L, τ_i = s_i
    intro i
    apply Fin.ext
    -- Use decode_mod_eq_prefix_mod: decode τ % B_L = (∑ τ.digits j * B_j) % B_L
    have h_decode_mod := decode_mod_eq_prefix_mod b τ L
    set τ_sum := ∑ j : Fin L, (τ.digits j : ℕ) * placeValue b j with h_τ_sum
    set s_sum := ∑ j : Fin L, (s j : ℕ) * placeValue b j with h_s_sum
    have h_τ_sum_lt : τ_sum < placeValue b L := prefix_sum_lt_placeValue b L (fun j => τ.digits j)
    have h_τ_sum_mod : τ_sum % placeValue b L = τ_sum := Nat.mod_eq_of_lt h_τ_sum_lt
    have h_s_sum_lt : s_sum < placeValue b L := prefix_sum_lt_placeValue b L s
    have h_s_sum_mod : s_sum % placeValue b L = s_sum := Nat.mod_eq_of_lt h_s_sum_lt
    -- h_decode_mod: decode τ % B_L = τ_sum % B_L = τ_sum
    rw [h_τ_sum_mod] at h_decode_mod
    -- h (as modular congruence): decode τ % B_L = s_sum % B_L = s_sum
    have h_eq : decode b τ % placeValue b L = s_sum % placeValue b L := h
    rw [h_s_sum_mod] at h_eq
    -- So decode τ % B_L = τ_sum and decode τ % B_L = s_sum
    -- Therefore τ_sum = s_sum
    have h_sums_eq : τ_sum = s_sum := h_decode_mod.symm.trans h_eq
    -- By uniqueness of mixed-radix representation, τ.digits i = s i
    -- Use digits_unique for finite sums
    cases L with
    | zero => exact i.elim0
    | succ L' =>
      -- Both τ_sum and s_sum are < B_{L'+1}
      -- By digits_unique: encodeFinite (decodeFinite d) = d
      -- Restrict τ.digits to Fin (L' + 1)
      set τ_digits : FiniteRadixSpace b L' := fun j => τ.digits j with h_τ_digits
      set s_digits : FiniteRadixSpace b L' := s with h_s_digits
      -- The sums are exactly decodeFinite applied to these restricted functions
      have h_τ_sum_eq : τ_sum = decodeFinite b L' τ_digits := rfl
      have h_s_sum_eq : s_sum = decodeFinite b L' s_digits := rfl
      -- By encodeFinite_decodeFinite
      have h_enc_τ : encodeFinite b L' ⟨τ_sum, h_τ_sum_lt⟩ = τ_digits :=
        encodeFinite_decodeFinite L' τ_digits
      have h_enc_s : encodeFinite b L' ⟨s_sum, h_s_sum_lt⟩ = s_digits :=
        encodeFinite_decodeFinite L' s_digits
      -- Since τ_sum = s_sum, their encodeFinite outputs are equal
      -- Directly prove τ_digits = s_digits using encodeFinite definition
      have h_digits_eq : τ_digits = s_digits := by
        rw [← h_enc_τ, ← h_enc_s]
        funext j
        simp only [encodeFinite]
        apply Fin.ext
        simp only [Fin.val_mk]
        rw [h_sums_eq]
      exact congrArg Fin.val (congrFun h_digits_eq i)

end FdrsFormal.Topology.Ultrametric
