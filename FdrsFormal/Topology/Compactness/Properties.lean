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

# Compactness and Topological Properties

This file formalizes compactness, total disconnectedness, and density properties
of the completed mixed-radix space.

## References

- fdrs.md, Phase 1 Fragment 3
- Compactness from Tychonoff's theorem
- Total disconnectedness from clopen basis
- Density of eventually-zero sequences
-/

import FdrsFormal.Topology.Ultrametric
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Data.Nat.Nth

namespace FdrsFormal.Topology.Compactness

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite FdrsFormal.Core.Infinite
open FdrsFormal.Topology.Ultrametric

/-!
## Compactness and Total Disconnectedness

The completed space ℛ̂ = ∏_{i≥0} D_i is a compact, totally disconnected ultrametric space.
-/

/-- Helper: given an infinite set of natural numbers and a finite type,
some value appears infinitely often. -/
lemma exists_infinite_fiber {n : ℕ} (hn : n > 0) (f : ℕ → Fin n) :
    ∃ d : Fin n, Set.Infinite {k | f k = d} := by
  by_contra h
  push_neg at h
  -- All fibers are finite, so their union is finite
  have h_union : Set.univ = ⋃ d : Fin n, {k | f k = d} := by
    ext k
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_setOf_eq, exists_eq']
  have h_finite : Set.Finite (⋃ d : Fin n, {k | f k = d}) := by
    apply Set.finite_iUnion
    intro d
    exact h d
  rw [← h_union] at h_finite
  exact Set.not_infinite.mpr h_finite Set.infinite_univ

/-- Given an infinite set S and a map to a finite type, some fiber is infinite -/
lemma exists_infinite_fiber_on_set {n : ℕ} (hn : n > 0) (S : Set ℕ) (hS : S.Infinite)
    (f : ℕ → Fin n) : ∃ d : Fin n, Set.Infinite {k ∈ S | f k = d} := by
  by_contra h
  push_neg at h
  have h_union : S = ⋃ d : Fin n, {k ∈ S | f k = d} := by
    ext k
    simp only [Set.mem_iUnion, Set.mem_sep_iff]
    constructor
    · intro hk; exact ⟨f k, hk, rfl⟩
    · intro ⟨_, hk, _⟩; exact hk
  have h_finite : Set.Finite (⋃ d : Fin n, {k ∈ S | f k = d}) := by
    apply Set.finite_iUnion
    intro d
    exact h d
  rw [← h_union] at h_finite
  exact Set.not_infinite.mpr h_finite hS

/-- Extract a strictly increasing subsequence hitting an infinite set -/
noncomputable def extractSubseq (S : Set ℕ) (hS : Set.Infinite S) : ℕ → ℕ :=
  Nat.nth (· ∈ S)

lemma extractSubseq_mem (S : Set ℕ) (hS : Set.Infinite S) (n : ℕ) :
    extractSubseq S hS n ∈ S := by
  unfold extractSubseq
  have : (setOf (· ∈ S)).Infinite := by
    simp only [Set.setOf_mem_eq]
    exact hS
  exact Nat.nth_mem_of_infinite this n

lemma extractSubseq_strictMono (S : Set ℕ) (hS : Set.Infinite S) :
    StrictMono (extractSubseq S hS) := by
  unfold extractSubseq
  have : (setOf (· ∈ S)).Infinite := by
    simp only [Set.setOf_mem_eq]
    exact hS
  exact Nat.nth_strictMono this

/-- placeValue grows without bound: for any M, there exists L with B_L > M -/
theorem placeValue_unbounded (b : RadixSeq) (M : ℕ) : ∃ L, M < placeValue b L := by
  -- placeValue b L ≥ 2^L (since each b_i ≥ 2), and 2^L grows faster than L
  use M + 1
  -- Each radix is at least 2, so placeValue b (M+1) ≥ 2^(M+1)
  have h_ge_pow : 2 ^ (M + 1) ≤ placeValue b (M + 1) := by
    induction M with
    | zero =>
      simp only [Nat.zero_add, pow_one, placeValue.succ, placeValue.zero, one_mul]
      exact b.ge_two 0
    | succ n ih =>
      rw [placeValue.succ]
      calc 2 ^ (n + 1 + 1)
          = 2 ^ (n + 1) * 2 := by ring
        _ ≤ placeValue b (n + 1) * 2 := Nat.mul_le_mul_right 2 ih
        _ ≤ placeValue b (n + 1) * b (n + 1) := Nat.mul_le_mul_left _ (b.ge_two (n + 1))
  calc M < 2 ^ M := M.lt_two_pow_self
    _ ≤ 2 ^ (M + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ M)
    _ ≤ placeValue b (M + 1) := h_ge_pow

/-- The cylinders (sets of sequences with fixed prefix) are finite for any given length L -/
lemma finite_cylinder_representatives (b : RadixSeq) (L : ℕ) :
    Finite ((i : Fin L) → Fin (b i)) := Pi.finite

/-- Cylinders form a finite cover at each level L -/
lemma cylinder_finite_cover (b : RadixSeq) (L : ℕ) :
    Set.univ = ⋃ (s : (i : Fin L) → Fin (b i)), cylinder b L (fun i => s ⟨i, i.2⟩) := by
  ext x
  simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
  -- Every x belongs to the cylinder determined by its first L coordinates
  use fun i => x i
  simp only [cylinder, Set.mem_setOf_eq]
  intro _
  trivial

/-- **ℛ̂ is totally bounded**: for any ε > 0, finitely many balls of radius ε cover the space -/
theorem completed_space_totallyBounded (b : RadixSeq) :
    TotallyBounded (Set.univ : Set (CompletedSpace b)) := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  -- Find L such that B_L^{-1} < ε
  obtain ⟨L, hL⟩ := placeValue_unbounded b (Nat.ceil ε⁻¹)
  have hL_inv : (placeValue b L : ℝ)⁻¹ < ε := by
    have h_pos_L : (0 : ℝ) < placeValue b L := Nat.cast_pos.mpr (placeValue.pos L)
    rw [inv_lt_comm₀ h_pos_L hε]
    calc ε⁻¹ ≤ Nat.ceil ε⁻¹ := Nat.le_ceil _
      _ < placeValue b L := Nat.cast_lt.mpr hL
  -- Use cylinders at level L as centers; there are finitely many (B_L of them)
  -- Each cylinder has diameter ≤ 2 * B_L^{-1} < 2ε, so ε-balls at centers cover
  -- Actually, cylinders = balls of radius B_L^{-1}, so we need to pick one point per cylinder

  -- Define a function to construct a center for a given prefix
  let mkCenter (s : (i : Fin L) → Fin (b i)) : CompletedSpace b :=
    fun i => if h : i < L then s ⟨i, h⟩ else ⟨0, b.pos i⟩

  let centers : Set (CompletedSpace b) := Set.range mkCenter
  use centers
  constructor
  · -- centers is finite (since the index set is finite)
    apply Set.finite_range
  · -- centers cover Set.univ within ε-balls
    intro x _
    -- Goal: x ∈ ⋃ y ∈ centers, ball y ε
    -- The center for x is mkCenter (x restricted to Fin L)
    let xPrefix : (i : Fin L) → Fin (b i) := fun i => x i
    simp only [Set.mem_iUnion, Metric.mem_ball]
    refine ⟨mkCenter xPrefix, ?_, ?_⟩
    · -- mkCenter xPrefix ∈ centers
      exact Set.mem_range.mpr ⟨xPrefix, rfl⟩
    · -- dist from x to center is < ε
      -- The center agrees with x on first L positions (by construction)
      -- So dist ≤ B_L^{-1} < ε
      have h_center : ∀ i < L, mkCenter xPrefix i = x i := by
        intro i hi
        simp only [mkCenter, xPrefix, hi, dite_true]
      calc dist x (mkCenter xPrefix)
          = dist (mkCenter xPrefix) x := dist_comm _ _
        _ ≤ (placeValue b L : ℝ)⁻¹ := by
            rw [show dist _ x = ultrametricDist b _ x from rfl]
            rw [ultrametricDist_le_placeValue_inv_iff]
            by_cases heq : mkCenter xPrefix = x
            · left; exact heq
            · right
              -- firstDiff ≥ L because they agree on first L positions
              by_contra h_lt
              push_neg at h_lt
              have := h_center (firstDiff b _ x) h_lt
              exact firstDiff_spec heq this
        _ < ε := hL_inv

/-- **ℛ̂ is complete**: every Cauchy sequence converges -/
instance completed_space_completeSpace (b : RadixSeq) : CompleteSpace (CompletedSpace b) := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hcauchy
  -- u is Cauchy: for every ε > 0, eventually |u_n - u_m| < ε
  -- In our ultrametric, this means: for every L, eventually u_n agrees on first L coords
  -- Define limit by: for each coord i, take the eventual common value

  -- For each coordinate i, the sequence u_n(i) is eventually constant
  have h_eventually_const : ∀ i, ∃ N, ∀ n ≥ N, u n i = u N i := by
    intro i
    -- Use Cauchy property with ε = B_{i+1}^{-1}
    rw [Metric.cauchySeq_iff] at hcauchy
    have h_pos : (0 : ℝ) < (placeValue b (i + 1) : ℝ)⁻¹ :=
      inv_pos.mpr (Nat.cast_pos.mpr (placeValue.pos _))
    obtain ⟨N, hN⟩ := hcauchy _ h_pos
    use N
    intro n hn
    -- dist (u n) (u N) < B_{i+1}^{-1} means they agree on first i+1 coords
    have hdist := hN n hn N (le_refl N)
    rw [show dist (u n) (u N) = ultrametricDist b (u n) (u N) from rfl] at hdist
    have h_or := (ultrametricDist_lt_placeValue_inv_iff (i + 1)).mp hdist
    cases h_or with
    | inl heq => exact congrFun heq i
    | inr hlt =>
      -- firstDiff > i+1, so they agree at position i
      have h_i_lt : i < firstDiff b (u n) (u N) := Nat.lt_of_succ_lt hlt
      by_cases heq : u n = u N
      · exact congrFun heq i
      · exact eq_of_lt_firstDiff heq h_i_lt

  -- Define the limit using choice
  let limit : CompletedSpace b := fun i => u (h_eventually_const i).choose i

  use limit
  -- Show u converges to limit
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Find L such that B_L^{-1} < ε
  obtain ⟨L, hL⟩ := placeValue_unbounded b (Nat.ceil ε⁻¹)
  have hL_inv : (placeValue b L : ℝ)⁻¹ < ε := by
    have h_pos_L : (0 : ℝ) < placeValue b L := Nat.cast_pos.mpr (placeValue.pos L)
    rw [inv_lt_comm₀ h_pos_L hε]
    calc ε⁻¹ ≤ Nat.ceil ε⁻¹ := Nat.le_ceil _
      _ < placeValue b L := Nat.cast_lt.mpr hL
  -- Find N large enough that u_n stabilizes on first L coordinates
  -- N = max of the N_i for i < L
  let N_max := Finset.sup (Finset.range L) (fun i => (h_eventually_const i).choose)
  use N_max
  intro n hn
  calc dist (u n) limit ≤ (placeValue b L : ℝ)⁻¹ := by
        rw [show dist (u n) limit = ultrametricDist b (u n) limit from rfl]
        rw [ultrametricDist_le_placeValue_inv_iff]
        by_cases heq : u n = limit
        · left; exact heq
        · right
          -- Show u n and limit agree on first L coords, so firstDiff ≥ L
          by_contra h_lt
          push_neg at h_lt
          -- They differ at position (firstDiff ...) < L
          let j := firstDiff b (u n) limit
          have hj_lt : j < L := h_lt
          -- But u n j = limit j for n ≥ N_max
          have h_agree : u n j = limit j := by
            simp only [limit]
            let N_j := (h_eventually_const j).choose
            have hN_j := (h_eventually_const j).choose_spec
            have h_j_mem : j ∈ Finset.range L := Finset.mem_range.mpr hj_lt
            have h_Nmax_ge : N_j ≤ N_max := by
              simp only [N_max]
              exact Finset.le_sup (f := fun i => (h_eventually_const i).choose) h_j_mem
            have h_n_ge : n ≥ N_j := Nat.le_trans h_Nmax_ge hn
            exact hN_j n h_n_ge
          exact firstDiff_spec heq h_agree
    _ < ε := hL_inv

/-- **ℛ̂ is compact** (Tychonoff's theorem applied to finite discrete spaces)

CompletedSpace b = (i : ℕ) → Fin (b i) is a product of finite discrete spaces.
Each Fin (b i) is finite, hence compact. By Tychonoff's theorem, the product is compact.

We prove this using the characterization: a metric space is compact iff it is complete and totally bounded. -/
instance completed_space_compactSpace (b : RadixSeq) : CompactSpace (CompletedSpace b) := by
  -- Compact ↔ complete + totally bounded (for metric spaces)
  rw [← isCompact_univ_iff, isCompact_iff_totallyBounded_isComplete]
  constructor
  · exact completed_space_totallyBounded b
  · -- Set.univ is complete because CompletedSpace b is a CompleteSpace
    exact IsClosed.isComplete isClosed_univ

/-- **ℛ̂ is totally disconnected** (ultrametric spaces are totally disconnected)

Ultrametric spaces have the property that all balls are clopen, which implies
they are totally separated, hence totally disconnected. -/
instance completed_space_totallyDisconnectedSpace (b : RadixSeq) :
    TotallyDisconnectedSpace (CompletedSpace b) :=
  -- IsUltrametricDist implies TotallySeparatedSpace (from Mathlib)
  -- TotallySeparatedSpace implies TotallyDisconnectedSpace (priority 100 instance)
  inferInstance

/-- **ℛ is countable** (bijective with ℕ) -/
theorem direct_limit_countable (b : RadixSeq) :
    Countable (DirectLimitSpace b) :=
  Countable.of_equiv ℕ (decodeEquiv b).symm

/-- Truncate a completed space element at level L, giving an element of DirectLimitSpace -/
def truncateAt (b : RadixSeq) (x : CompletedSpace b) (L : ℕ) : DirectLimitSpace b where
  digits := fun i => if i < L then x i else ⟨0, b.pos i⟩
  eventually_zero := ⟨L, fun i hi => by simp [Nat.not_lt.mpr (Nat.le_of_succ_le hi)]⟩

/-- Truncation agrees with x on the first L positions -/
theorem truncateAt_agree (b : RadixSeq) (x : CompletedSpace b) (L : ℕ) :
    ∀ i < L, (truncateAt b x L).digits i = x i := by
  intro i hi
  simp only [truncateAt, hi, ↓reduceIte]

/-- Distance between x and its truncation is at most B_L^{-1} -/
theorem dist_truncateAt_le (b : RadixSeq) (x : CompletedSpace b) (L : ℕ) :
    dist (DirectLimitSpace.embed b (truncateAt b x L)) x ≤ (placeValue b L : ℝ)⁻¹ := by
  -- dist in our MetricSpace is ultrametricDist
  show ultrametricDist b _ x ≤ _
  rw [ultrametricDist_le_placeValue_inv_iff]
  -- Either x = truncateAt, or L ≤ firstDiff
  by_cases heq : DirectLimitSpace.embed b (truncateAt b x L) = x
  · left; exact heq
  · right
    -- Show that x and truncateAt agree on first L positions, so firstDiff ≥ L
    by_contra h_not
    push_neg at h_not
    -- firstDiff < L, so they differ at some i < L
    have h_lt : firstDiff b (DirectLimitSpace.embed b (truncateAt b x L)) x < L := h_not
    have h_agree := truncateAt_agree b x L (firstDiff b _ x) h_lt
    -- But they should differ at firstDiff by definition
    have h_diff := firstDiff_spec heq
    simp only [DirectLimitSpace.embed] at h_agree h_diff
    exact h_diff h_agree

/-- **ℛ is dense in ℛ̂** (eventually-zero sequences are dense in all sequences)

For any x : CompletedSpace b and ε > 0, we can find an eventually-zero sequence
within distance ε of x by truncating x at a sufficiently large level. -/
theorem direct_limit_dense_in_completed (b : RadixSeq) :
    Dense (Set.range (DirectLimitSpace.embed b)) := by
  rw [Metric.dense_iff]
  intro x ε hε
  -- Find L such that (placeValue b L)⁻¹ < ε
  -- Equivalently, placeValue b L > ε⁻¹
  have h_arch : ∃ L, (placeValue b L : ℝ)⁻¹ < ε := by
    obtain ⟨L, hL⟩ := placeValue_unbounded b (Nat.ceil ε⁻¹)
    use L
    have h_pos_L : (0 : ℝ) < placeValue b L := Nat.cast_pos.mpr (placeValue.pos L)
    rw [inv_lt_comm₀ h_pos_L hε]
    calc ε⁻¹ ≤ Nat.ceil ε⁻¹ := Nat.le_ceil _
      _ < placeValue b L := Nat.cast_lt.mpr hL
  obtain ⟨L, hL⟩ := h_arch
  -- Use truncateAt x L
  -- Goal: (ball x ε ∩ Set.range (DirectLimitSpace.embed b)).Nonempty
  refine ⟨DirectLimitSpace.embed b (truncateAt b x L), ?_, ⟨truncateAt b x L, rfl⟩⟩
  -- Need: dist (truncateAt x L) x < ε
  rw [Metric.mem_ball]
  calc dist (DirectLimitSpace.embed b (truncateAt b x L)) x
      ≤ (placeValue b L : ℝ)⁻¹ := dist_truncateAt_le b x L
    _ < ε := hL

end FdrsFormal.Topology.Compactness
