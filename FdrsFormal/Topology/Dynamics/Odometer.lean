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

# Odometer Dynamics

This file formalizes the Tick operator as a continuous dynamical system
on the completed space.

## References

- fdrs.md, Phase 1 Fragment 3
- Tick extends to ℛ̂ continuously
- Minimality and aperiodicity conditions
- Orbit structure
-/

import FdrsFormal.Core.Infinite
import FdrsFormal.Core.PrefixValue
import FdrsFormal.Operations.Tick
import FdrsFormal.Topology.Ultrametric
import FdrsFormal.Topology.Compactness

namespace FdrsFormal.Topology.Dynamics

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite FdrsFormal.Core.Infinite
open FdrsFormal.Operations.Tick
open FdrsFormal.Topology.Ultrametric
open FdrsFormal.Topology.Compactness
open scoped Classical

/-!
## Odometer Dynamics

The Tick operator extends to a continuous map on the completed space ℛ̂,
forming an odometer (adding machine) dynamical system.
-/

/-- Carry predicate: true if all digits before position i are maximal -/
def allMaxBefore (b : RadixSeq) (x : CompletedSpace b) : ℕ → Prop
  | 0 => True
  | i + 1 => allMaxBefore b x i ∧ x i = ⟨b i - 1, Nat.sub_lt (b.pos i) Nat.one_pos⟩

/-- **Tick extends continuously to ℛ̂**
Defined by digit-wise addition with carry propagation. -/
noncomputable def tickCompleted (b : RadixSeq) : CompletedSpace b → CompletedSpace b :=
  fun x i =>
    if allMaxBefore b x i then
      if h : (x i).val + 1 < b i then
        ⟨(x i).val + 1, h⟩
      else
        ⟨0, b.pos i⟩  -- Wrap around (x i was maximal)
    else
      x i  -- No carry reaches this position

/-- allMaxBefore depends only on coordinates before i -/
theorem allMaxBefore_of_agree {b : RadixSeq} {x y : CompletedSpace b} {i : ℕ}
    (h : ∀ j < i, x j = y j) : allMaxBefore b x i = allMaxBefore b y i := by
  induction i with
  | zero => rfl
  | succ n ih =>
    simp only [allMaxBefore]
    have hih : allMaxBefore b x n = allMaxBefore b y n := ih (fun j hj => h j (Nat.lt_succ_of_lt hj))
    have hn : x n = y n := h n (Nat.lt_succ_self n)
    rw [hih, hn]

/-- tickCompleted preserves agreement on prefixes -/
theorem tickCompleted_agree_on_prefix {b : RadixSeq} {x y : CompletedSpace b} {L : ℕ}
    (h : ∀ j < L, x j = y j) : ∀ j < L, tickCompleted b x j = tickCompleted b y j := by
  intro j hj
  simp only [tickCompleted]
  -- allMaxBefore depends only on coordinates before j, which agree
  have hmax : allMaxBefore b x j = allMaxBefore b y j :=
    allMaxBefore_of_agree (fun k hk => h k (Nat.lt_trans hk hj))
  rw [hmax]
  -- x j = y j by assumption
  have hxj : x j = y j := h j hj
  rw [hxj]

/-- **Tick on ℛ̂ is continuous**

Continuity follows from the fact that tickCompleted only depends on finitely many
coordinates: if x and y agree on the first L positions, then so do tick(x) and tick(y). -/
theorem tick_completed_continuous (b : RadixSeq) : Continuous (tickCompleted b) := by
  rw [Metric.continuous_iff]
  intro x ε hε
  -- Step 1: Find L such that B_L^{-1} < ε (use placeValue_unbounded)
  have h_arch : ∃ L, (placeValue b L : ℝ)⁻¹ < ε := by
    obtain ⟨L, hL⟩ := placeValue_unbounded b (Nat.ceil ε⁻¹)
    use L
    have h_pos_L : (0 : ℝ) < placeValue b L := Nat.cast_pos.mpr (placeValue.pos L)
    rw [inv_lt_comm₀ h_pos_L hε]
    calc ε⁻¹ ≤ Nat.ceil ε⁻¹ := Nat.le_ceil _
      _ < placeValue b L := Nat.cast_lt.mpr hL
  obtain ⟨L, hL⟩ := h_arch
  -- Step 2: Use δ = B_L^{-1}
  use (placeValue b L : ℝ)⁻¹
  constructor
  · exact inv_pos.mpr (Nat.cast_pos.mpr (placeValue.pos L))
  · intro y hy
    -- hy : dist y x < B_L^{-1} (note: Metric.continuous_iff uses dist y x)
    -- Goal: dist (tickCompleted b y) (tickCompleted b x) < ε
    -- Use symmetry: dist y x = dist x y (ultrametricDist_comm)
    rw [dist_comm] at hy
    -- Now hy : dist x y < B_L^{-1}
    -- This means x and y agree on first L digits (by ultrametric characterization)
    have h_agree : ∀ j < L, x j = y j := by
      -- dist = ultrametricDist b for our MetricSpace instance
      have h_or := (ultrametricDist_lt_placeValue_inv_iff L).mp hy
      cases h_or with
      | inl heq => intro j _; exact congrFun heq j
      | inr hlt =>
        intro j hj
        -- hlt : L < firstDiff b x y, hj : j < L
        -- Need to show x j = y j
        -- Since L < firstDiff, we have j < firstDiff, so x j = y j by eq_of_lt_firstDiff
        have h_ne : x ≠ y := by
          intro heq
          -- If x = y, then firstDiff b x y = 0 by definition
          simp only [heq, firstDiff, dif_neg (not_not.mpr rfl)] at hlt
          -- hlt : L < 0 is impossible
          exact Nat.not_lt_zero L hlt
        exact eq_of_lt_firstDiff h_ne (Nat.lt_trans hj hlt)
    -- Apply tickCompleted_agree_on_prefix
    have h_tick_agree := tickCompleted_agree_on_prefix h_agree
    -- Goal: dist (tickCompleted b y) (tickCompleted b x) < ε
    -- Use dist_comm to swap to dist (tickCompleted b x) (tickCompleted b y)
    rw [dist_comm]
    -- Now goal: dist (tickCompleted b x) (tickCompleted b y) < ε
    -- dist = ultrametricDist b in our instance
    calc ultrametricDist b (tickCompleted b x) (tickCompleted b y)
        ≤ (placeValue b L : ℝ)⁻¹ := by
          rw [ultrametricDist_le_placeValue_inv_iff]
          by_cases heq : tickCompleted b x = tickCompleted b y
          · left; exact heq
          · right
            -- firstDiff ≥ L because they agree on first L positions
            by_contra h_not
            push_neg at h_not
            have := h_tick_agree (firstDiff b _ _) h_not
            exact firstDiff_spec heq this
      _ < ε := hL

-- tick_minimal is proved at the end of the file (after its dependencies)

/-- Helper: if not eventually all-maximal, there exists a smallest non-maximal position -/
lemma exists_first_nonmax {b : RadixSeq} {x : CompletedSpace b}
    (h : ¬∃ K, ∀ i ≥ K, x i = ⟨b i - 1, Nat.sub_lt (b.pos i) Nat.one_pos⟩) :
    ∃ m, (∀ j < m, x j = ⟨b j - 1, Nat.sub_lt (b.pos j) Nat.one_pos⟩) ∧
         x m ≠ ⟨b m - 1, Nat.sub_lt (b.pos m) Nat.one_pos⟩ := by
  -- h says: for every K, there exists i ≥ K such that x i ≠ max
  push_neg at h
  -- h : ∀ K, ∃ i ≥ K, x i ≠ ⟨b i - 1, _⟩
  by_contra h_no_first
  push_neg at h_no_first
  -- h_no_first : ∀ m, (∀ j < m, x j = max) → x m = max
  -- By strong induction, all positions are maximal
  have h_all_max : ∀ i, x i = ⟨b i - 1, Nat.sub_lt (b.pos i) Nat.one_pos⟩ := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      apply h_no_first i
      intro j hj
      exact ih j hj
  -- But h says there's always a non-max position ≥ K
  specialize h 0
  obtain ⟨i, _, hi_ne⟩ := h
  exact hi_ne (h_all_max i)

/-- allMaxBefore follows from all positions before being maximal -/
lemma allMaxBefore_of_all_max {b : RadixSeq} {x : CompletedSpace b} {m : ℕ}
    (h : ∀ j < m, x j = ⟨b j - 1, Nat.sub_lt (b.pos j) Nat.one_pos⟩) :
    allMaxBefore b x m := by
  induction m with
  | zero => exact trivial
  | succ n ih =>
    simp only [allMaxBefore]
    constructor
    · exact ih (fun j hj => h j (Nat.lt_succ_of_lt hj))
    · exact h n (Nat.lt_succ_self n)

/-- Helper: tick at the first non-maximal position increments it -/
lemma tickCompleted_at_first_nonmax {b : RadixSeq} {x : CompletedSpace b} {m : ℕ}
    (h_before : ∀ j < m, x j = ⟨b j - 1, Nat.sub_lt (b.pos j) Nat.one_pos⟩)
    (h_at : x m ≠ ⟨b m - 1, Nat.sub_lt (b.pos m) Nat.one_pos⟩) :
    (tickCompleted b x m).val = (x m).val + 1 := by
  simp only [tickCompleted]
  have h_allmax : allMaxBefore b x m := allMaxBefore_of_all_max h_before
  rw [if_pos h_allmax]
  -- Now show x m is not maximal, so we don't wrap
  have h_not_max : (x m).val + 1 < b m := by
    by_contra h_ge
    push_neg at h_ge
    -- (x m).val + 1 ≥ b m, but (x m).val < b m, so (x m).val = b m - 1
    have h_eq : (x m).val = b m - 1 := by
      have h_lt : (x m).val < b m := (x m).isLt
      omega
    -- This means x m = ⟨b m - 1, _⟩
    have : x m = ⟨b m - 1, Nat.sub_lt (b.pos m) Nat.one_pos⟩ := by
      apply Fin.ext
      exact h_eq
    exact h_at this
  rw [dif_pos h_not_max]

/-- Helper: tick zeros all positions before the first non-maximal position -/
lemma tickCompleted_before_first_nonmax {b : RadixSeq} {x : CompletedSpace b} {m : ℕ}
    (h_before : ∀ j < m, x j = ⟨b j - 1, Nat.sub_lt (b.pos j) Nat.one_pos⟩) :
    ∀ j < m, tickCompleted b x j = ⟨0, b.pos j⟩ := by
  intro j hj
  simp only [tickCompleted]
  -- allMaxBefore b x j is true (all positions before j are maximal)
  have h_allmax : allMaxBefore b x j :=
    allMaxBefore_of_all_max (fun k hk => h_before k (Nat.lt_trans hk hj))
  rw [if_pos h_allmax]
  -- x j is maximal, so we wrap to 0
  have h_max : x j = ⟨b j - 1, Nat.sub_lt (b.pos j) Nat.one_pos⟩ := h_before j hj
  have h_wrap : ¬ (x j).val + 1 < b j := by
    rw [h_max]
    simp only [Fin.val_mk]
    omega
  rw [dif_neg h_wrap]

/-- tick is injective: if tick(x) = tick(y) then x = y -/
theorem tickCompleted_injective (b : RadixSeq) : Function.Injective (tickCompleted b) := by
  intro x y h
  -- If tick(x) = tick(y), then x and y agree at all positions
  funext i
  -- Prove by strong induction on i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    -- allMaxBefore depends only on earlier coordinates, which agree by IH
    have h_max_eq : allMaxBefore b x i = allMaxBefore b y i :=
      allMaxBefore_of_agree (fun j hj => ih j hj)
    -- At position i, tick(x) i = tick(y) i
    have hi : tickCompleted b x i = tickCompleted b y i := congrFun h i
    simp only [tickCompleted] at hi
    rw [h_max_eq] at hi
    -- Now both sides have the same if-condition
    by_cases hmax : allMaxBefore b y i
    · -- allMaxBefore is true
      simp only [if_pos hmax] at hi
      -- Now we have: if cond1 then val1 else val2 = if cond2 then val3 else val4
      -- where cond1 = (x i).val + 1 < b i, cond2 = (y i).val + 1 < b i
      by_cases hx : (x i).val + 1 < b i
      · by_cases hy : (y i).val + 1 < b i
        · -- Both don't wrap
          simp only [dif_pos hx, dif_pos hy, Fin.ext_iff, Fin.val_mk] at hi
          exact Fin.ext (by omega)
        · -- x doesn't wrap but y wraps: tick(x) i = x i + 1, tick(y) i = 0
          simp only [dif_pos hx, dif_neg hy, Fin.ext_iff, Fin.val_mk] at hi
          -- hi : (x i).val + 1 = 0, impossible since (x i).val + 1 ≥ 1
          omega
      · by_cases hy : (y i).val + 1 < b i
        · -- x wraps but y doesn't
          simp only [dif_neg hx, dif_pos hy, Fin.ext_iff, Fin.val_mk] at hi
          omega
        · -- Both wrap to 0, so x i and y i are both maximal
          push_neg at hx hy
          have hx_max : (x i).val = b i - 1 := by omega
          have hy_max : (y i).val = b i - 1 := by omega
          exact Fin.ext (by omega)
    · -- allMaxBefore is false: x i = tick(x) i and y i = tick(y) i
      simp only [if_neg hmax] at hi
      exact hi

/-! ### Helpers for aperiodicity proof -/

/-- allMaxBefore for smaller indices follows from allMaxBefore for larger indices -/
lemma allMaxBefore_of_succ {b : RadixSeq} {x : CompletedSpace b} {j : ℕ}
    (h : allMaxBefore b x (j + 1)) : allMaxBefore b x j := by
  simp only [allMaxBefore] at h
  exact h.1

/-- allMaxBefore is monotonic: if all positions < j are max, then all positions < i are max for i ≤ j -/
lemma allMaxBefore_of_le' {b : RadixSeq} {x : CompletedSpace b} {i j : ℕ}
    (h : allMaxBefore b x j) (hij : i ≤ j) : allMaxBefore b x i := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hij
  rw [hk] at h
  clear hk hij j
  induction k with
  | zero => exact h
  | succ k' ih =>
    apply ih
    exact allMaxBefore_of_succ h

/-- tick preserves the "not eventually all-max" property -/
lemma tickCompleted_preserves_not_eventually_all_max {b : RadixSeq} {x : CompletedSpace b}
    (h : ¬∃ K, ∀ i ≥ K, x i = ⟨b i - 1, Nat.sub_lt (b.pos i) Nat.one_pos⟩) :
    ¬∃ K, ∀ i ≥ K, tickCompleted b x i = ⟨b i - 1, Nat.sub_lt (b.pos i) Nat.one_pos⟩ := by
  intro ⟨K, hK⟩
  -- tick(x) at large positions equals x at those positions (beyond first non-max)
  have h_orig := h
  obtain ⟨m, h_before, h_at_m⟩ := exists_first_nonmax h
  -- For i > m, tick(x) i = x i
  -- Since x is not eventually all-max, exists i ≥ max(K, m+1) with x i ≠ max
  push_neg at h
  specialize h (max K (m + 1))
  obtain ⟨i, hi_ge, hi_ne⟩ := h
  have hi_gt_m : m < i := Nat.lt_of_succ_le (le_of_max_le_right hi_ge)
  have tick_i : tickCompleted b x i = x i := by
    simp only [tickCompleted]
    have h_not_allmax : ¬allMaxBefore b x i := by
      intro hall
      have : allMaxBefore b x (m + 1) := allMaxBefore_of_le' hall (Nat.succ_le_of_lt hi_gt_m)
      simp only [allMaxBefore] at this
      exact h_at_m this.2
    rw [if_neg h_not_allmax]
  have hi_ge_K : K ≤ i := le_of_max_le_left hi_ge
  specialize hK i hi_ge_K
  rw [tick_i] at hK
  exact hi_ne hK

/-- Iterate of tick preserves "not eventually all-max" -/
lemma tickCompleted_iterate_preserves_not_eventually_all_max {b : RadixSeq} {x : CompletedSpace b} (n : ℕ)
    (h : ¬∃ K, ∀ i ≥ K, x i = ⟨b i - 1, Nat.sub_lt (b.pos i) Nat.one_pos⟩) :
    ¬∃ K, ∀ i ≥ K, (tickCompleted b)^[n] x i = ⟨b i - 1, Nat.sub_lt (b.pos i) Nat.one_pos⟩ := by
  induction n with
  | zero => simp only [Function.iterate_zero, id_eq]; exact h
  | succ n' ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    exact tickCompleted_preserves_not_eventually_all_max ih

/-! ### Tick and prefix value relationship

These theorems establish that tick increments the prefix value by 1 modulo B_L.
-/

/-- When allMaxBefore holds up to L, tick zeros all first L positions,
    so the prefix value becomes 0. -/
private theorem prefixValue_tickCompleted_of_allMax {L : ℕ} {x : CompletedSpace b}
    (h : allMaxBefore b x L) :
    Core.prefixValue b L (tickCompleted b x) = 0 := by
  simp only [Core.prefixValue]
  apply Finset.sum_eq_zero
  intro ⟨i, hi⟩ _
  suffices (tickCompleted b x i : ℕ) = 0 by simp [this]
  simp only [tickCompleted]
  have h_i1 : allMaxBefore b x (i + 1) := allMaxBefore_of_le' h (Nat.succ_le_of_lt hi)
  rw [if_pos h_i1.1]
  have h_max : x i = ⟨b i - 1, Nat.sub_lt (b.pos i) Nat.one_pos⟩ := h_i1.2
  have : ¬((x i).val + 1 < b i) := by rw [h_max]; simp; omega
  rw [dif_neg this]

/-- When allMaxBefore holds up to L, the prefix value equals B_L - 1. -/
private theorem prefixValue_of_allMax {L : ℕ} {x : CompletedSpace b}
    (h : allMaxBefore b x L) :
    Core.prefixValue b L x = placeValue b L - 1 := by
  cases L with
  | zero => simp [Core.prefixValue, placeValue]
  | succ K =>
    simp only [Core.prefixValue]
    have h_max : ∀ i : Fin (K + 1), (x i.val : ℕ) = b i.val - 1 := by
      intro ⟨i, hi⟩
      have h_i1 := allMaxBefore_of_le' h (Nat.succ_le_of_lt hi)
      simp [h_i1.2]
    calc ∑ i : Fin (K + 1), (x i.val : ℕ) * placeValue b i.val
        = ∑ i : Fin (K + 1), (b i.val - 1) * placeValue b i.val := by
          apply Finset.sum_congr rfl; intro i _; rw [h_max i]
      _ = placeValue b (K + 1) - 1 := placeValue.sum_max_digits K

/-- When ¬allMaxBefore, tick increments the prefix value by exactly 1. -/
private theorem prefixValue_tickCompleted_succ {L : ℕ} {x : CompletedSpace b}
    (h : ¬allMaxBefore b x L) :
    Core.prefixValue b L (tickCompleted b x) = Core.prefixValue b L x + 1 := by
  induction L with
  | zero => exact absurd trivial h
  | succ L ih =>
    rw [Core.prefixValue_succ, Core.prefixValue_succ]
    by_cases h_all_L : allMaxBefore b x L
    · -- allMaxBefore L holds, so x L must not be maximal
      have h_not_max : x L ≠ ⟨b L - 1, Nat.sub_lt (b.pos L) Nat.one_pos⟩ := by
        intro hmax; exact h ⟨h_all_L, hmax⟩
      have h_pv_zero := prefixValue_tickCompleted_of_allMax h_all_L
      have h_pv_max := prefixValue_of_allMax h_all_L
      have h_tick_L : (tickCompleted b x L : ℕ) = (x L : ℕ) + 1 := by
        simp only [tickCompleted, if_pos h_all_L]
        have h_lt : (x L).val + 1 < b L := by
          have := (x L).isLt
          have : (x L).val ≠ b L - 1 := fun heq => h_not_max (Fin.ext heq)
          omega
        rw [dif_pos h_lt]
      rw [h_pv_zero, h_pv_max, h_tick_L]
      -- Goal: 0 + ((x L : ℕ) + 1) * B_L = (B_L - 1) + (x L : ℕ) * B_L + 1
      have hB := placeValue.one_le L (b := b)
      rw [Nat.zero_add, Nat.add_one_mul]
      omega
    · -- ¬allMaxBefore L: tick doesn't change position L
      have h_tick_L : tickCompleted b x L = x L := by
        simp only [tickCompleted, if_neg h_all_L]
      rw [h_tick_L, ih h_all_L]
      omega

/-- **Tick increments prefix value by 1 modulo B_L.**
    Replaces the axiom `tick_prefixValue_succ` from Core/PrefixValue.lean. -/
theorem tickCompleted_prefixValue_succ (L : ℕ) (x : CompletedSpace b) :
    (Core.prefixValue b L (tickCompleted b x) : ℤ) ≡
    (Core.prefixValue b L x : ℤ) + 1 [ZMOD (placeValue b L : ℤ)] := by
  by_cases h : allMaxBefore b x L
  · -- All first L maximal: tick wraps to 0
    rw [prefixValue_tickCompleted_of_allMax h, prefixValue_of_allMax h]
    show (0 : ℤ) ≡ ↑(placeValue b L - 1) + 1 [ZMOD ↑(placeValue b L)]
    have h_pos := placeValue.one_le L (b := b)
    have : (↑(placeValue b L - 1) : ℤ) + 1 = ↑(placeValue b L) := by
      rw [Nat.cast_sub h_pos]; omega
    rw [this]
    exact (Int.modEq_zero_iff_dvd.mpr dvd_rfl).symm
  · -- Not all maximal: exact +1
    rw [prefixValue_tickCompleted_succ h, Nat.cast_add, Nat.cast_one]

/-- Prefix value after n ticks increases by n modulo B_L. -/
theorem tickCompleted_iterate_prefixValue (L n : ℕ) (x : CompletedSpace b) :
    (Core.prefixValue b L ((tickCompleted b)^[n] x) : ℤ) ≡
    (Core.prefixValue b L x : ℤ) + (n : ℤ) [ZMOD (placeValue b L : ℤ)] := by
  induction n with
  | zero =>
    simp only [Function.iterate_zero, id_eq, Nat.cast_zero, add_zero]
    exact Int.ModEq.refl _
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp_apply]
    have h := (tickCompleted_prefixValue_succ L ((tickCompleted b)^[n] x)).trans (ih.add_right 1)
    have : (↑(n + 1) : ℤ) = (↑n : ℤ) + 1 := by push_cast; ring
    rw [this, ← add_assoc]
    exact h

/-- **Period divisibility**: if tick^n(x) = x, then B_L divides n.
    Replaces the axiom `tick_period_divisibility` from Core/PrefixValue.lean. -/
theorem tickCompleted_period_divisibility (L n : ℕ) (x : CompletedSpace b)
    (hperiod : (tickCompleted b)^[n] x = x) :
    (n : ℤ) ≡ 0 [ZMOD (placeValue b L : ℤ)] := by
  have h := tickCompleted_iterate_prefixValue L n x
  rw [hperiod] at h
  have h2 : (Core.prefixValue b L x : ℤ) + 0 ≡
      (Core.prefixValue b L x : ℤ) + (n : ℤ) [ZMOD (placeValue b L : ℤ)] := by rwa [add_zero]
  exact (Int.ModEq.add_left_cancel (Int.ModEq.refl _) h2).symm

/-- **Aperiodicity**: for non-eventually-constant sequences, orbits are infinite

A point has a finite orbit iff it is eventually all-maximal (the "infinity" point). -/
theorem tick_aperiodic (b : RadixSeq) (x : CompletedSpace b)
    (h : ¬∃ K, ∀ i ≥ K, x i = ⟨b i - 1, Nat.sub_lt (b.pos i) Nat.one_pos⟩) :
    ∀ n > 0, (tickCompleted b)^[n] x ≠ x := by
  intro n hn
  -- Key insight: tick acts like adding 1 in mixed-radix representation
  -- If x is not eventually all-max, tick changes x in a detectable way
  -- After n ticks, we've "added n" which is non-zero

  -- Find the first non-maximal position
  obtain ⟨m, h_before, h_at⟩ := exists_first_nonmax h

  -- Strategy: show that (tick^n x) differs from x at some position
  -- For n = 1, tick(x) differs from x at position m (it's incremented)
  -- For general n, we track the "carry" propagation

  -- For simplicity, prove for n = 1 first, then generalize
  induction n with
  | zero => omega
  | succ k ih =>
    intro heq
    cases k with
    | zero =>
      -- n = 1 case: tick x = x is impossible
      rw [Nat.zero_add, Function.iterate_one] at heq
      -- tick x at position m has value (x m).val + 1
      have h1 := tickCompleted_at_first_nonmax h_before h_at
      -- But heq says tick x = x, so (tick x m) = x m
      have h2 : tickCompleted b x m = x m := congrFun heq m
      -- This gives (x m).val + 1 = (x m).val, contradiction
      have h3 : (tickCompleted b x m).val = (x m).val := congrArg Fin.val h2
      omega
    | succ k' =>
      -- n = k' + 2 case: tick^{k'+2}(x) = x is impossible
      -- Key insight: tick^{k'+1}(x) is also not eventually all-max,
      -- so applying the base case to it shows tick^{k'+2}(x) ≠ tick^{k'+1}(x).
      -- Combined with injectivity, this leads to a contradiction.

      -- Simplify: tick^{k+1}(x) = tick^{k'+2}(x) = tick(tick^{k'+1}(x))
      -- heq currently says tick^{k'+2}(x) = x

      -- Let y = tick^{k'+1}(x)
      let y := (tickCompleted b)^[k' + 1] x

      -- y is not eventually all-max (tick preserves this property)
      have hy_not_ev_max : ¬∃ K, ∀ i ≥ K, y i = ⟨b i - 1, Nat.sub_lt (b.pos i) Nat.one_pos⟩ := by
        exact tickCompleted_iterate_preserves_not_eventually_all_max (k' + 1) h

      -- Apply base case to y: tick(y) ≠ y
      obtain ⟨m_y, h_before_y, h_at_y⟩ := exists_first_nonmax hy_not_ev_max
      have h_tick_y_ne_y : tickCompleted b y ≠ y := by
        intro heq_y
        have h1 := tickCompleted_at_first_nonmax h_before_y h_at_y
        have h2 : tickCompleted b y m_y = y m_y := congrFun heq_y m_y
        have h3 : (tickCompleted b y m_y).val = (y m_y).val := congrArg Fin.val h2
        omega

      -- heq says tick^{k'+2}(x) = x, which is tick(y) = x
      -- y = tick^{k'+1}(x) = tickCompleted b (tick^{k'}(x))
      -- So tickCompleted b y = tickCompleted b (tickCompleted b (tick^{k'}(x))) = tick^{k'+2}(x) = x
      have heq' : tickCompleted b y = x := by
        simp only [Function.iterate_succ', Function.comp_apply] at heq
        -- heq : tickCompleted b (tickCompleted b ((tickCompleted b)^[k'] x)) = x
        -- y = (tickCompleted b)^[k' + 1] x = tickCompleted b ((tickCompleted b)^[k'] x)
        -- So tickCompleted b y = tickCompleted b (tickCompleted b ((tickCompleted b)^[k'] x))
        show tickCompleted b ((tickCompleted b)^[k' + 1] x) = x
        simp only [Function.iterate_succ', Function.comp_apply]
        exact heq

      -- x ≠ y follows because tick(y) = x and tick(y) ≠ y
      have hx_ne_y : x ≠ y := by
        intro hxy
        rw [hxy] at heq'
        exact h_tick_y_ne_y heq'

      -- Now use injectivity argument.
      -- If tick^{k'+2}(x) = x, and all tick^m(x) ≠ x for 0 < m < k'+2,
      -- then we have a cycle of length exactly k'+2.
      -- For placeValue b L > k'+2, the L-truncated "value" increases by 1
      -- each tick, so after k'+2 ticks it increases by k'+2, not 0.
      -- This contradicts tick^{k'+2}(x) = x.

      -- Use that tick(y) = x but y ≠ x and y = tick^{k'+1}(x)
      -- means we have exactly a cycle: x → tick(x) → ... → y → x
      -- By IH, no intermediate element equals x.
      -- So all k'+2 elements are distinct in the sequence.

      -- The contradiction: tick(y) = x means the cycle closes,
      -- but for x not eventually all-max, the "mixed-radix value"
      -- strictly increases by 1 mod B_L for each tick.
      -- After k'+2 ticks, value increases by k'+2 (mod B_L).
      -- If tick^{k'+2}(x) = x, then k'+2 ≡ 0 (mod B_L) for all L.
      -- But B_L grows unboundedly (B_L ≥ 2^L), so for L large enough,
      -- B_L > k'+2, making k'+2 ≡ 0 (mod B_L) impossible.

      -- For now, we observe: the sequence has all distinct elements (by IH),
      -- and closes back to x. The only way for this to happen is if
      -- the dynamics "wrap around", which requires the element to be
      -- eventually all-max. But x is not eventually all-max.
      -- Since y = tick^{k'+1}(x) is also not eventually all-max,
      -- tick(y) moves "forward" in the odometer ordering.
      -- The only element whose tick can equal x is the "predecessor" of x,
      -- but x is not eventually all-max, so such predecessor exists uniquely
      -- (if at all), and it's determined by x.

      -- Actually, use this: y = tick^{k'+1}(x) ≠ x (by IH).
      -- So y ≠ x.
      -- tick(y) = x (by heq).
      -- If z = tick(y) = x for y ≠ x, then y is the "predecessor" of x.
      -- But then tick(y) = x means y = tick^{-1}(x) (the unique preimage).
      -- So tick^{k'+1}(x) = tick^{-1}(x).
      -- Applying tick: tick^{k'+2}(x) = x. ✓ (this is heq, so consistent)
      -- But also: tick^{k'+1}(x) = tick^{-1}(x) means tick^{k'+2}(x) = x.
      -- And: tick^{k'}(x) = tick^{-2}(x) (applying tick^{-1} to both sides)
      -- Continuing: x = tick^{-(k'+1)}(x).
      -- So x = tick^{-(k'+1)}(x) = tick^{-(k'+1)+k'+2}(x) = tick(x).
      -- But tick(x) ≠ x by base case. Contradiction!

      -- Formalize: heq gives tick(y) = x where y = tick^{k'+1}(x).
      -- By injectivity: if tick(a) = tick(b) then a = b.
      -- tick(y) = x and tick(tick^{-1}(x)) = x (if preimage exists).
      -- So y = tick^{-1}(x) (unique preimage).

      -- Simpler: use that tick^{k'+2}(x) = tick^0(x) = x.
      -- So in the orbit, position k'+2 equals position 0.
      -- But tick^1(x) ≠ x, tick^2(x) ≠ x, ..., tick^{k'+1}(x) ≠ x (by IH).
      -- So the orbit has period exactly k'+2.

      -- For x not eventually all-max, the orbit is aperiodic.
      -- This follows from the odometer structure, but we need to prove it.

      -- Use: tick(y) = x and y ≠ x.
      -- tick is injective, so tick(y) = x means y is THE preimage of x.
      -- Now, tick(tick^{k'}(x)) = tick^{k'+1}(x) = y.
      -- So tick^{k'}(x) is the preimage of y.

      -- Let w = tick^{k'}(x). Then tick(w) = y and tick(y) = x.
      -- So tick(tick(w)) = x, i.e., tick²(w) = x.
      -- Also w = tick^{k'}(x).
      -- So tick²(tick^{k'}(x)) = x, i.e., tick^{k'+2}(x) = x. ✓ (heq)

      -- The key: apply IH to y instead of x.
      -- y is not eventually all-max.
      -- By IH for y: tick^m(y) ≠ y for 0 < m ≤ k'+1. But wait, our IH is for x, not y.

      -- Different approach: the theorem says "for all x not ev-max, tick^n(x) ≠ x".
      -- So we can apply it to any not-ev-max element.
      -- y = tick^{k'+1}(x) is not ev-max.
      -- Apply theorem to y with n=1: tick(y) ≠ y.
      -- We have tick(y) = x (from heq).
      -- So x ≠ y.
      -- This is hy_ne_x, which we already have. Not a contradiction yet.

      -- Apply theorem to y with n = k'+2:
      -- tick^{k'+2}(y) ≠ y.
      -- tick^{k'+2}(y) = tick^{k'+2}(tick^{k'+1}(x)) = tick^{2k'+3}(x).

      -- OK this is getting circular. Let me use a direct argument.

      -- Since y = tick^{k'+1}(x) and tick(y) = x (heq),
      -- the sequence x, tick(x), tick²(x), ..., tick^{k'+1}(x) = y, tick(y) = x
      -- forms a cycle. By IH, all elements except the last (= first) are ≠ x.
      -- So the orbit has period k'+2.

      -- Claim: for x not ev-max, the orbit under tick is infinite (no period).
      -- This is equivalent to our theorem.

      -- To prove the claim: use that tick acts like +1 on the mixed-radix value.
      -- If orbit has period n, then +n ≡ 0 (mod B_L) for all L.
      -- This is impossible since B_L → ∞.

      -- For now, we use a more direct argument:
      -- Iterate the base case: tick^{k'+1}(x) ≠ tick^{k'}(x) ≠ ... ≠ tick(x) ≠ x.
      -- So all elements x, tick(x), ..., tick^{k'+1}(x) are distinct.
      -- If tick^{k'+2}(x) = x, this means the (k'+2)th element equals the 0th.
      -- The orbit is {x, tick(x), ..., tick^{k'+1}(x)} with |orbit| = k'+2.

      -- But by the preservation lemma, all elements are not ev-max.
      -- The base case says tick(z) ≠ z for any z not ev-max.
      -- So tick^{k'+2}(x) ≠ tick^{k'+1}(x).
      -- But heq says tick^{k'+2}(x) = x.
      -- So x ≠ tick^{k'+1}(x). ✓ (this is hy_ne_x)

      -- The missing piece: we need tick^{k'+2}(x) ≠ x, not tick^{k'+2}(x) ≠ tick^{k'+1}(x).

      -- Use injectivity of tick^{k'+1}:
      -- If tick^{k'+2}(x) = x = tick^0(x), apply tick^{-1} (k'+1) times:
      -- tick(x) = tick^{-(k')}(x).
      -- But this requires surjectivity/inverse, which we haven't proved.

      -- Alternative: we have a cycle x → tick(x) → ... → tick^{k'+1}(x) → x.
      -- All k'+2 elements are in the orbit. By IH, none except possibly x = tick^{k'+2}(x)
      -- are equal to x. But tick^{k'+2}(x) = x by heq.
      -- So the cycle is valid, with k'+2 distinct elements.

      -- But: x not ev-max means there are infinitely many non-max positions.
      -- After each tick, we "add 1" to the mixed-radix representation.
      -- After k'+2 ticks, we've added k'+2.
      -- For the L-prefix (L large enough that B_L > k'+2), the value mod B_L
      -- has increased by k'+2, not returned to original.
      -- So tick^{k'+2}(x) ≠ x. Contradiction!

      -- Let's use placeValue_unbounded to find such L.
      obtain ⟨L, hL⟩ := placeValue_unbounded b (k' + 2)
      -- hL : k' + 2 < placeValue b L
      -- So B_L > k' + 2 ≥ 1.
      -- The L-truncated value of x, call it v, satisfies:
      -- L-truncated value of tick^{k'+2}(x) ≡ v + (k'+2) (mod B_L)
      -- If tick^{k'+2}(x) = x, then v ≡ v + (k'+2) (mod B_L)
      -- So k'+2 ≡ 0 (mod B_L), i.e., B_L | (k'+2).
      -- But B_L > k'+2 > 0, so B_L cannot divide k'+2. Contradiction!

      have h_not_div : ¬(placeValue b L ∣ (k' + 2)) := by
        intro hdiv
        have h1 : k' + 2 ≥ placeValue b L := Nat.le_of_dvd (by omega) hdiv
        omega
      -- We need to show that tick^{k'+2}(x) = x implies placeValue b L | (k'+2).
      -- This requires the prefixValue lemma. Let's add it.
      -- For now, use a placeholder that captures the mathematical argument.

      -- Actually, let's prove it directly by tracking what tick does.
      -- tick(z) differs from z at the first non-max position.
      -- After k'+2 ticks starting from x, if we return to x,
      -- we must have "wrapped around" B_L times at the L-truncation level.
      -- But B_L > k'+2, so we can't wrap even once in k'+2 steps.

      -- The L-truncated sequence evolves as:
      -- x|_L, tick(x)|_L, tick²(x)|_L, ..., tick^{k'+2}(x)|_L
      -- Each step increases the L-prefix value by 1 (with wrap at B_L).
      -- After k'+2 steps, value increases by k'+2 (mod B_L).
      -- If tick^{k'+2}(x) = x, then (k'+2) mod B_L = 0.
      -- But k'+2 < B_L, so k'+2 mod B_L = k'+2 ≠ 0.
      -- Contradiction!

      exfalso

      -- Key insight: We use the relationship between tick^{k'+2}(x) and tick^{k'+1}(x).
      -- From heq': tick(y) = x where y = tick^{k'+1}(x).
      -- From h_tick_y_ne_y: tick(y) ≠ y.
      -- So x ≠ y, meaning x ≠ tick^{k'+1}(x).

      -- We already have this as hx_ne_y. The contradiction comes from:
      -- heq (original): tick^{k'+2}(x) = x
      -- But tick^{k'+2}(x) = tick(tick^{k'+1}(x)) = tick(y) = x. ✓

      -- The issue is that this is consistent, not contradictory!
      -- We need the modular arithmetic argument.

      -- Since B_L > k'+2, the L-truncated value increases by k'+2 after k'+2 ticks.
      -- This is < B_L, so no wraparound, meaning tick^{k'+2}(x)|_L ≠ x|_L.
      -- Hence tick^{k'+2}(x) ≠ x, contradicting heq.

      -- To prove this formally, we track the digit at the first non-max position.
      -- After each tick, this position's value increases by 1 (with carry propagation).
      -- After k'+2 ticks from x, we've "added" k'+2 to the mixed-radix number.
      -- Since B_L > k'+2, the L-prefix has genuinely increased, not wrapped around.

      -- Direct approach: For L > m (first non-max position of x), look at prefix.
      -- tick(x) at position m has value (x m).val + 1.
      -- Since B_L > k'+2 and m < L, after k'+2 ticks, position m has changed.

      -- Actually, the cleanest is to observe that:
      -- tick^{k'+2}(x) at position m is NOT equal to x at position m (in general).
      -- Specifically, tracking the value at position m through k'+2 iterations.

      -- However, this requires careful tracking because carries can propagate.
      -- The modular arithmetic of the L-prefix is the correct abstraction.

      -- For now, we use that h_not_div combined with the modular arithmetic
      -- of prefix values gives the contradiction.

      -- Since tick acts as +1 in mixed-radix, tick^{k'+2} acts as +(k'+2).
      -- If tick^{k'+2}(x) = x, then (k'+2) ≡ 0 (mod B_L) for all L (prefix perspective).
      -- But B_L > k'+2 for our chosen L, so this is impossible.

      apply h_not_div

      -- We need to show placeValue b L ∣ (k' + 2) from heq (tick^{k'+2}(x) = x).
      -- This follows from Core.PrefixValue.tick_period_divisibility:
      -- If tick^n(x) = x, then n ≡ 0 (mod B_L)
      have h_mod : ((k' + 2) : ℤ) ≡ 0 [ZMOD (placeValue b L : ℤ)] :=
        tickCompleted_period_divisibility L (k' + 2) x heq
      -- Convert modular equivalence to divisibility
      rw [Int.modEq_zero_iff_dvd] at h_mod
      -- Now have: (placeValue b L : ℤ) ∣ (k' + 2 : ℤ)
      -- Since both are positive natural numbers, this implies Nat divisibility
      obtain ⟨c, hc⟩ := h_mod
      -- hc: (k' + 2 : ℤ) = (placeValue b L : ℤ) * c
      -- Since k' + 2 > 0 and placeValue b L > 0, we must have c > 0
      have hc_nonneg : 0 ≤ c := by
        by_contra h_neg
        push_neg at h_neg
        have : (placeValue b L : ℤ) * c < 0 := by
          apply Int.mul_neg_of_pos_of_neg
          · exact Nat.cast_pos.mpr (placeValue.pos L)
          · exact h_neg
        rw [← hc] at this
        omega
      -- Convert using natAbs: since (a : ℤ) ∣ (b : ℤ) and both are Nat, then a ∣ b in Nat
      have : (k' + 2 : ℕ) = placeValue b L * c.natAbs := by
        -- Normalize hc to use ↑(k' + 2) instead of ↑k' + ↑2
        have hc' : ((k' + 2 : ℕ) : ℤ) = ((placeValue b L : ℕ) : ℤ) * c := by
          convert hc using 1 <;> norm_cast
        -- Apply natAbs to both sides and simplify
        calc (k' + 2 : ℕ)
            = ((k' + 2 : ℕ) : ℤ).natAbs := (Int.natAbs_natCast _).symm
          _ = (((placeValue b L : ℕ) : ℤ) * c).natAbs := by rw [hc']
          _ = ((placeValue b L : ℕ) : ℤ).natAbs * c.natAbs := Int.natAbs_mul _ _
          _ = (placeValue b L : ℕ) * c.natAbs := by rw [Int.natAbs_natCast]
      rw [this]
      exact dvd_mul_right (placeValue b L) c.natAbs

/-! ### Orbit density (Minimality) -/

/-- If two completed-space elements have the same prefix value at depth L,
    they agree on the first L digits. Converse of `prefixValue_eq_of_prefix_eq`. -/
private theorem prefix_eq_of_prefixValue_eq {L : ℕ} {x y : CompletedSpace b}
    (h : Core.prefixValue b L x = Core.prefixValue b L y) :
    ∀ i : Fin L, x (i : ℕ) = y (i : ℕ) := by
  cases L with
  | zero => intro i; exact i.elim0
  | succ k =>
    -- prefixValue b (k+1) and decodeFinite b k are definitionally equal on
    -- the restricted digit functions, so h serves as the injectivity input
    have h' : decodeFinite b k (fun (i : Fin (k + 1)) => x ↑i) =
              decodeFinite b k (fun (i : Fin (k + 1)) => y ↑i) := h
    have h_eq := decodeFinite_injective k h'
    intro i
    exact congrFun h_eq i

/-- ℤ-congruence of ℕ casts with compatible bounds implies equality. -/
private lemma eq_of_natCast_modEq {a b m : ℕ}
    (h : (a : ℤ) ≡ (b : ℤ) [ZMOD (m : ℤ)]) (ha : a < m) (hb : b < m) : a = b := by
  have h1 : (↑a : ℤ) % ↑m = ↑a :=
    Int.emod_eq_of_lt (Nat.cast_nonneg a) (by exact_mod_cast ha)
  have h2 : (↑b : ℤ) % ↑m = ↑b :=
    Int.emod_eq_of_lt (Nat.cast_nonneg b) (by exact_mod_cast hb)
  have h3 : (↑a : ℤ) = ↑b := by rw [← h1, ← h2]; exact h
  exact_mod_cast h3

/-- **Minimality**: every orbit of tick is dense in the completed space ℛ̂.

The proof uses:
1. Tick increments prefix values by 1 modulo B_L (`tickCompleted_iterate_prefixValue`)
2. Any target prefix value is reachable by an appropriate iterate
3. Equal prefix values at depth L imply agreement on first L digits (injectivity of decoding)
4. Prefix agreement implies small ultrametric distance -/
theorem tick_minimal (b : RadixSeq) (_h : ∃ M, ∀ i, b i ≤ M) :
    ∀ x : CompletedSpace b, Dense (Set.range (fun n => (tickCompleted b)^[n] x)) := by
  intro x y
  rw [Metric.mem_closure_iff]
  intro ε hε
  -- Step 1: Find L such that B_L⁻¹ < ε
  obtain ⟨L, hL⟩ : ∃ L, (placeValue b L : ℝ)⁻¹ < ε := by
    obtain ⟨L, hL⟩ := placeValue_unbounded b (Nat.ceil ε⁻¹)
    exact ⟨L, by
      rw [inv_lt_comm₀ (Nat.cast_pos.mpr (placeValue.pos L)) hε]
      calc ε⁻¹ ≤ ↑⌈ε⁻¹⌉₊ := Nat.le_ceil _
        _ < ↑(placeValue b L) := Nat.cast_lt.mpr hL⟩
  -- Step 2: Choose n := vy + B - vx so that tick^n(x) has the same L-prefix as y
  set B := placeValue b L
  set vx := Core.prefixValue b L x
  set vy := Core.prefixValue b L y
  have hvx_lt := Core.prefixValue_lt (b := b) L x
  have hvy_lt := Core.prefixValue_lt (b := b) L y
  have hvx_le : vx ≤ vy + B := (le_of_lt hvx_lt).trans (Nat.le_add_left B vy)
  set n := vy + B - vx
  -- Step 3: Prove prefix values match via modular arithmetic
  have h_pv_eq : Core.prefixValue b L ((tickCompleted b)^[n] x) = vy := by
    apply eq_of_natCast_modEq _ (Core.prefixValue_lt L _) hvy_lt
    -- (↑pv_tick : ℤ) ≡ ↑vx + ↑n [ZMOD ↑B]
    have h1 := tickCompleted_iterate_prefixValue L n x
    -- ↑vx + ↑n = ↑(vx + n) = ↑(vy + B) = ↑vy + ↑B
    have h2 : (↑vx : ℤ) + ↑n = ↑vy + ↑B := by exact_mod_cast Nat.add_sub_cancel' hvx_le
    -- Rewrite and chain: ↑pv_tick ≡ ↑vy + ↑B ≡ ↑vy [ZMOD ↑B]
    rw [h2] at h1
    exact h1.trans (Int.modEq_iff_dvd.mpr ⟨-1, by ring⟩)
  -- Step 4: Equal prefix values → prefix agreement → small distance
  have h_agree := prefix_eq_of_prefixValue_eq h_pv_eq
  refine ⟨(tickCompleted b)^[n] x, ⟨n, rfl⟩, ?_⟩
  rw [dist_comm]
  calc dist ((tickCompleted b)^[n] x) y
      = ultrametricDist b ((tickCompleted b)^[n] x) y := rfl
    _ ≤ (↑B)⁻¹ := by
        rw [ultrametricDist_le_placeValue_inv_iff]
        exact (agree_on_prefix_iff L).mp h_agree
    _ < ε := hL

end FdrsFormal.Topology.Dynamics
