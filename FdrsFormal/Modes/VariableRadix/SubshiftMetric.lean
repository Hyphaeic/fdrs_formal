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

# Subshift metric space — Chunk 1: the gauge as a function of depth

The generated (continued-fraction) timeline: a point is an infinite sequence of
partial quotients `x : ℕ → ℕ`, all `≥ 1` (`Admissible`). Its length-`n` prefix is
`pre x n`, and the **gauge at depth `n`** is the convergent denominator
`gaugeAt x n = qₙ` from the `RemainderState` ledger.

This chunk establishes the three properties of `gaugeAt` that the eventual
ultrametric needs:
* `gaugeAt_pos`        — `0 < qₙ` (positive denominator),
* `gaugeAt_monotone`   — `qₙ` non-decreasing in depth (the strong-triangle prereq),
* `gaugeAt_inv_lt`     — `1/qₙ → 0` (cylinders shrink), the depth form of `gauge_inv_lt`.

Built on the committed `SubshiftWeight` (engine + shrink); imports nothing from the
topology layer.
-/
import FdrsFormal.Modes.VariableRadix.SubshiftWeight

namespace FdrsFormal.Modes.VariableRadix.Subshift

open RemainderState

/-- A point of the generated timeline: an infinite quotient sequence, all `≥ 1`. -/
def Admissible (x : ℕ → ℕ) : Prop := ∀ i, 1 ≤ x i

/-- The length-`n` quotient prefix `[x 0, x 1, …, x (n-1)]`. -/
def pre (x : ℕ → ℕ) (n : ℕ) : List ℕ := (List.range n).map x

@[simp] theorem pre_zero (x : ℕ → ℕ) : pre x 0 = [] := by simp [pre]

theorem pre_succ (x : ℕ → ℕ) (n : ℕ) : pre x (n + 1) = pre x n ++ [x n] := by
  simp [pre, List.range_succ]

@[simp] theorem pre_length (x : ℕ → ℕ) (n : ℕ) : (pre x n).length = n := by simp [pre]

theorem pre_admissible {x : ℕ → ℕ} (hx : Admissible x) (n : ℕ) :
    ∀ a ∈ pre x n, 1 ≤ a := by
  intro a ha
  simp only [pre, List.mem_map, List.mem_range] at ha
  obtain ⟨i, _, rfl⟩ := ha
  exact hx i

/-- The gauge at depth `n`: the convergent denominator `qₙ` of `x`'s quotient prefix. -/
def gaugeAt (x : ℕ → ℕ) (n : ℕ) : ℤ := (steps init (pre x n)).qCur

/-- **Positivity.** `qₙ > 0` — a safe metric denominator. -/
theorem gaugeAt_pos {x : ℕ → ℕ} (hx : Admissible x) (n : ℕ) : 0 < gaugeAt x n :=
  steps_qCur_pos (pre_admissible hx n)

/-- One-step monotonicity of the gauge in depth. -/
theorem gaugeAt_le_succ {x : ℕ → ℕ} (hx : Admissible x) (n : ℕ) :
    gaugeAt x n ≤ gaugeAt x (n + 1) := by
  have hstep : steps init (pre x (n + 1)) = (steps init (pre x n)).step (x n) := by
    rw [pre_succ]; simp only [steps, List.foldl_append, List.foldl_cons, List.foldl_nil]
  obtain ⟨hp, hpc, _, _⟩ := steps_invariant (pre_admissible hx n)
  have hxn : (1 : ℤ) ≤ (x n : ℤ) := by exact_mod_cast hx n
  have hqp : (0 : ℤ) ≤ (steps init (pre x n)).qCur := le_trans hp hpc
  unfold gaugeAt
  rw [hstep]
  simp only [step]
  nlinarith [mul_nonneg (sub_nonneg.mpr hxn) hqp, hp]

/-- **Monotonicity.** `qₙ` is non-decreasing in depth — the prerequisite for the
ultrametric strong triangle inequality. -/
theorem gaugeAt_monotone {x : ℕ → ℕ} (hx : Admissible x) : Monotone (gaugeAt x) :=
  monotone_nat_of_le_succ (gaugeAt_le_succ hx)

/-- **Cylinder diameter → 0 (depth form).** For every `ε > 0`, beyond some depth `N`
the cylinder radius `1/qₙ < ε` — even for φ, where the base product would not shrink. -/
theorem gaugeAt_inv_lt {x : ℕ → ℕ} (hx : Admissible x) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n → ((gaugeAt x n : ℝ))⁻¹ < ε := by
  obtain ⟨N, hN⟩ := gauge_inv_lt ε hε
  exact ⟨N, fun n hn => hN (pre x n) (pre_admissible hx n) (by rw [pre_length]; exact hn)⟩

/-! ## Chunk 2 — the gauge-induced ultrametric distance -/

open Classical

/-- Longest-common-prefix length: the first index where `x` and `y` differ (`0` if equal). -/
noncomputable def lcpLen (x y : ℕ → ℕ) : ℕ := if h : ∃ i, x i ≠ y i then Nat.find h else 0

/-- The gauge-induced distance: `1/qₗ` at the common-prefix depth `ℓ`, and `0` if equal.
This is the subshift analogue of `ultrametricDist`, with the `qₖ` gauge in place of `β`. -/
noncomputable def cfDist (x y : ℕ → ℕ) : ℝ :=
  if h : ∃ i, x i ≠ y i then ((gaugeAt x (lcpLen x y) : ℝ))⁻¹ else 0

theorem lcpLen_eq_find {x y : ℕ → ℕ} (h : ∃ i, x i ≠ y i) : lcpLen x y = Nat.find h := by
  rw [lcpLen, dif_pos h]

theorem cfDist_of_ne {x y : ℕ → ℕ} (h : ∃ i, x i ≠ y i) :
    cfDist x y = ((gaugeAt x (lcpLen x y) : ℝ))⁻¹ := by rw [cfDist, dif_pos h]

theorem cfDist_of_eq {x y : ℕ → ℕ} (h : ¬ ∃ i, x i ≠ y i) : cfDist x y = 0 := by
  rw [cfDist, dif_neg h]

theorem eq_of_not_exists_ne {x y : ℕ → ℕ} (h : ¬ ∃ i, x i ≠ y i) : x = y := by
  funext i; by_contra hne; exact h ⟨i, hne⟩

theorem exists_ne_symm {x y : ℕ → ℕ} (h : ∃ i, x i ≠ y i) : ∃ i, y i ≠ x i := by
  obtain ⟨i, hi⟩ := h; exact ⟨i, fun e => hi e.symm⟩

/-- Below the lcp, the two sequences agree. -/
theorem agree_below_lcp {x y : ℕ → ℕ} (h : ∃ i, x i ≠ y i) {i : ℕ} (hi : i < lcpLen x y) :
    x i = y i := by
  rw [lcpLen_eq_find h] at hi
  exact not_not.mp (Nat.find_min h hi)

/-- The length-`n` prefixes agree for any depth `n ≤ lcp`. -/
theorem pre_eq_of_le_lcp {x y : ℕ → ℕ} (h : ∃ i, x i ≠ y i) {n : ℕ} (hn : n ≤ lcpLen x y) :
    pre x n = pre y n := by
  simp only [pre]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  exact agree_below_lcp h (lt_of_lt_of_le hi hn)

theorem gaugeAt_eq_of_pre_eq {x y : ℕ → ℕ} {n : ℕ} (hpre : pre x n = pre y n) :
    gaugeAt x n = gaugeAt y n := by rw [gaugeAt, gaugeAt, hpre]

theorem lcpLen_comm (x y : ℕ → ℕ) : lcpLen x y = lcpLen y x := by
  by_cases h : ∃ i, x i ≠ y i
  · have h' : ∃ i, y i ≠ x i := exists_ne_symm h
    rw [lcpLen_eq_find h, lcpLen_eq_find h']
    refine le_antisymm (Nat.find_le ?_) (Nat.find_le ?_)
    · exact fun e => (Nat.find_spec h') e.symm
    · exact fun e => (Nat.find_spec h) e.symm
  · have h' : ¬ ∃ i, y i ≠ x i := fun he => h (exists_ne_symm he)
    rw [lcpLen, lcpLen, dif_neg h, dif_neg h']

/-- **Self-distance is zero.** -/
theorem cfDist_self (x : ℕ → ℕ) : cfDist x x = 0 := by
  apply cfDist_of_eq; rintro ⟨i, hi⟩; exact hi rfl

/-- **Non-negativity.** -/
theorem cfDist_nonneg {x : ℕ → ℕ} (hx : Admissible x) (y : ℕ → ℕ) : 0 ≤ cfDist x y := by
  unfold cfDist
  split
  · have : (0 : ℝ) < (gaugeAt x (lcpLen x y) : ℝ) := by exact_mod_cast gaugeAt_pos hx (lcpLen x y)
    exact inv_nonneg.mpr this.le
  · exact le_refl 0

/-- **Symmetry.** Both endpoints see the same gauge at the common prefix. -/
theorem cfDist_comm (x y : ℕ → ℕ) : cfDist x y = cfDist y x := by
  by_cases h : ∃ i, x i ≠ y i
  · have h' : ∃ i, y i ≠ x i := exists_ne_symm h
    have hpre : pre x (lcpLen x y) = pre y (lcpLen x y) := pre_eq_of_le_lcp h (le_refl _)
    rw [cfDist_of_ne h, cfDist_of_ne h', ← lcpLen_comm x y, gaugeAt_eq_of_pre_eq hpre]
  · have h' : ¬ ∃ i, y i ≠ x i := fun he => h (exists_ne_symm he)
    rw [cfDist_of_eq h, cfDist_of_eq h']

/-- **Identity of indiscernibles** (for admissible points). -/
theorem cfDist_eq_zero_iff {x : ℕ → ℕ} (hx : Admissible x) (y : ℕ → ℕ) :
    cfDist x y = 0 ↔ x = y := by
  constructor
  · intro hd
    by_contra hne
    have h : ∃ i, x i ≠ y i := by
      by_contra h'; exact hne (eq_of_not_exists_ne h')
    rw [cfDist_of_ne h] at hd
    have hpos : (0 : ℝ) < (gaugeAt x (lcpLen x y) : ℝ) := by exact_mod_cast gaugeAt_pos hx _
    exact (inv_ne_zero (ne_of_gt hpos)) hd
  · rintro rfl; exact cfDist_self x

/-- **Strong triangle inequality** — completing the genuine ULTRAMETRIC.
`cfDist x z ≤ max (cfDist x y) (cfDist y z)`: a longer shared prefix
(`lcpLen x z ≥ min(lcpLen x y, lcpLen y z)`) gives, via `gaugeAt_monotone`, the
smaller `1/q`. -/
theorem cfDist_triangle {x : ℕ → ℕ} (hx : Admissible x) (y z : ℕ → ℕ) :
    cfDist x z ≤ max (cfDist x y) (cfDist y z) := by
  by_cases hxz : ∃ i, x i ≠ z i
  · by_cases hxy : ∃ i, x i ≠ y i
    · by_cases hyz : ∃ i, y i ≠ z i
      · -- main case: x, y, z pairwise distinct on the relevant prefixes
        rw [cfDist_of_ne hxz, cfDist_of_ne hxy, cfDist_of_ne hyz]
        have hmin : min (lcpLen x y) (lcpLen y z) ≤ lcpLen x z := by
          rw [lcpLen_eq_find hxz, Nat.le_find_iff]
          intro i hi
          rw [lt_min_iff] at hi
          exact fun hne => hne ((agree_below_lcp hxy hi.1).trans (agree_below_lcp hyz hi.2))
        have hxpos : (0 : ℝ) < (gaugeAt x (lcpLen x z) : ℝ) := by exact_mod_cast gaugeAt_pos hx _
        have hminpos : (0 : ℝ) < (gaugeAt x (min (lcpLen x y) (lcpLen y z)) : ℝ) := by
          exact_mod_cast gaugeAt_pos hx _
        have hmono : gaugeAt x (min (lcpLen x y) (lcpLen y z)) ≤ gaugeAt x (lcpLen x z) :=
          gaugeAt_monotone hx hmin
        have hinv : ((gaugeAt x (lcpLen x z) : ℝ))⁻¹
            ≤ ((gaugeAt x (min (lcpLen x y) (lcpLen y z)) : ℝ))⁻¹ :=
          (inv_le_inv₀ hxpos hminpos).mpr (by exact_mod_cast hmono)
        rcases le_total (lcpLen x y) (lcpLen y z) with hab | hba
        · rw [min_eq_left hab] at hinv
          exact le_trans hinv (le_max_left _ _)
        · rw [min_eq_right hba] at hinv
          rw [gaugeAt_eq_of_pre_eq (pre_eq_of_le_lcp hxy hba)] at hinv
          exact le_trans hinv (le_max_right _ _)
      · have he : y = z := eq_of_not_exists_ne hyz
        rw [← he]; exact le_max_left _ _
    · have he : x = y := eq_of_not_exists_ne hxy
      rw [← he]; exact le_max_right _ _
  · rw [cfDist_of_eq hxz]
    exact le_max_of_le_left (cfDist_nonneg hx y)

/-! ## Chunk 3b — `ball = cylinder` (the analytic ↔ combinatorial translation) -/

/-- Equal length-`n` prefixes ⇒ pointwise agreement below `n`. -/
theorem agree_of_pre_eq {x y : ℕ → ℕ} {n i : ℕ} (h : pre x n = pre y n) (hi : i < n) :
    x i = y i := by
  have hcongr := congrArg (fun l => l[i]?) h
  simpa [pre, List.getElem?_map, List.getElem?_range, hi] using hcongr

/-- **`ball = cylinder`.** Every open ball around an admissible point is exactly a
combinatorial cylinder: choosing `n` minimal with radius `1/qₙ < r`,
`{y | cfDist x y < r} = {y | pre y n = pre x n}`. This is the translation layer
between the analytic metric (limits, continuity) and the combinatorial cylinders
(Haar/Parry measure, routing). -/
theorem ball_eq_cylinder {x : ℕ → ℕ} (hx : Admissible x) (r : ℝ) (hr : 0 < r) :
    ∃ n : ℕ, {y | cfDist x y < r} = {y | pre y n = pre x n} := by
  have hex : ∃ k, ((gaugeAt x k : ℝ))⁻¹ < r := by
    obtain ⟨N, hN⟩ := gaugeAt_inv_lt hx r hr
    exact ⟨N, hN N (le_refl N)⟩
  refine ⟨Nat.find hex, ?_⟩
  have hspec : ((gaugeAt x (Nat.find hex) : ℝ))⁻¹ < r := Nat.find_spec hex
  ext y
  simp only [Set.mem_setOf_eq]
  constructor
  · -- analytic → combinatorial
    intro hd
    by_cases hxy : ∃ i, x i ≠ y i
    · rw [cfDist_of_ne hxy] at hd
      have hle : Nat.find hex ≤ lcpLen x y := by
        by_contra hlt
        push_neg at hlt
        exact (Nat.find_min hex hlt) hd
      exact (pre_eq_of_le_lcp hxy hle).symm
    · have he : x = y := eq_of_not_exists_ne hxy
      rw [← he]
  · -- combinatorial → analytic
    intro hpre
    by_cases hxy : ∃ i, x i ≠ y i
    · rw [cfDist_of_ne hxy]
      have hle : Nat.find hex ≤ lcpLen x y := by
        rw [lcpLen_eq_find hxy, Nat.le_find_iff]
        exact fun i hi hne => hne (agree_of_pre_eq hpre.symm hi)
      have hnpos : (0 : ℝ) < (gaugeAt x (Nat.find hex) : ℝ) := by exact_mod_cast gaugeAt_pos hx _
      have hlcppos : (0 : ℝ) < (gaugeAt x (lcpLen x y) : ℝ) := by exact_mod_cast gaugeAt_pos hx _
      calc ((gaugeAt x (lcpLen x y) : ℝ))⁻¹
          ≤ ((gaugeAt x (Nat.find hex) : ℝ))⁻¹ :=
            (inv_le_inv₀ hlcppos hnpos).mpr (by exact_mod_cast gaugeAt_monotone hx hle)
        _ < r := hspec
    · rw [cfDist_of_eq hxy]; exact hr

end FdrsFormal.Modes.VariableRadix.Subshift
