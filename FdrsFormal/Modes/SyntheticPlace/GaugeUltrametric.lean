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

# Synthetic place complex SU0 — the gauge→ultrametric keystone

The first stone of the Synthetic Place System (design: `docs/synthetic-place/00-thesis.md`,
roadmap: `docs/synthetic-place/01-build-roadmap.md`). A **prefix gauge** is the minimal
structure a "designed ultrametric basis" needs: a resolution weight on finite words,
positive and non-decreasing along admissible extensions. The keystone:

> **Any positive, extension-monotone prefix gauge induces a genuine ultrametric on
> digit streams, with `ball = cylinder`** (the latter at every radius when the gauge is
> unbounded along the centre).

This makes "ultrametric defined by arbitrary structure" a first-class object and
*unifies the corpus's two instances*:

* the **product gauge** `β_ω = prefixWeight ω` (every radix law; the induced distance
  carries Definition 79's `β_ω(lcp)⁻¹` formula) — `productGauge`;
* the **generated CF gauge** `qₙ` (`SubshiftMetric.gaugeAt`) — `cfGauge`, with
  `gaugeDist cfGauge = cfDist` proven on admissible points, so `cfDist` literally
  becomes an instance of this file.

Design decisions D1–D4 (roadmap): generic digit type `D`, predicate admissibility
(`Adm`, prefix-closed) rather than dependent fibers, the distance *derived* rather than
carried as a field, and two-tier hypotheses (positivity+monotonicity give the
ultrametric; unboundedness is asked separately, only for the all-radii ball=cylinder).

**Honest scope.** No claim `gaugeDist (productGauge ω) = δ_ω` as defined on
`InfiniteVariableSpace` — that type alignment is the same outstanding infrastructure as
Theorem 43 step 4 (thesis ledger item 2); what is proven is the defining formula on raw
streams. Bounded gauges are legal: they yield the ultrametric but not arbitrarily fine
cylinders. Leaf module. No `sorry`; axiom-clean.
-/
import FdrsFormal.Modes.VariableRadix.SubshiftMetric

namespace FdrsFormal.Modes.SyntheticPlace

open Classical FdrsFormal.Modes.VariableRadix

variable {D : Type*} [DecidableEq D]

/-! ## 1. Streams, prefixes, longest common prefix (generic digit type) -/

/-- The length-`n` prefix of a digit stream. -/
def pre (x : ℕ → D) (n : ℕ) : List D := (List.range n).map x

@[simp] theorem pre_zero (x : ℕ → D) : pre x 0 = [] := by simp [pre]

theorem pre_succ (x : ℕ → D) (n : ℕ) : pre x (n + 1) = pre x n ++ [x n] := by
  simp [pre, List.range_succ]

@[simp] theorem pre_length (x : ℕ → D) (n : ℕ) : (pre x n).length = n := by simp [pre]

/-- Longest-common-prefix length: the first index where `x` and `y` differ (`0` if equal). -/
noncomputable def lcpLen (x y : ℕ → D) : ℕ :=
  if h : ∃ i, x i ≠ y i then Nat.find h else 0

theorem lcpLen_eq_find {x y : ℕ → D} (h : ∃ i, x i ≠ y i) :
    lcpLen x y = Nat.find h := by rw [lcpLen, dif_pos h]

theorem eq_of_not_exists_ne {x y : ℕ → D} (h : ¬ ∃ i, x i ≠ y i) : x = y := by
  funext i; by_contra hne; exact h ⟨i, hne⟩

theorem exists_ne_symm {x y : ℕ → D} (h : ∃ i, x i ≠ y i) : ∃ i, y i ≠ x i := by
  obtain ⟨i, hi⟩ := h; exact ⟨i, fun e => hi e.symm⟩

/-- Below the lcp, the two streams agree. -/
theorem agree_below_lcp {x y : ℕ → D} (h : ∃ i, x i ≠ y i) {i : ℕ}
    (hi : i < lcpLen x y) : x i = y i := by
  rw [lcpLen_eq_find h] at hi
  exact not_not.mp (Nat.find_min h hi)

/-- The length-`n` prefixes agree for any depth `n ≤ lcp`. -/
theorem pre_eq_of_le_lcp {x y : ℕ → D} (h : ∃ i, x i ≠ y i) {n : ℕ}
    (hn : n ≤ lcpLen x y) : pre x n = pre y n := by
  simp only [pre]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  exact agree_below_lcp h (lt_of_lt_of_le hi hn)

theorem lcpLen_comm (x y : ℕ → D) : lcpLen x y = lcpLen y x := by
  by_cases h : ∃ i, x i ≠ y i
  · have h' : ∃ i, y i ≠ x i := exists_ne_symm h
    rw [lcpLen_eq_find h, lcpLen_eq_find h']
    refine le_antisymm (Nat.find_le ?_) (Nat.find_le ?_)
    · exact fun e => (Nat.find_spec h') e.symm
    · exact fun e => (Nat.find_spec h) e.symm
  · have h' : ¬ ∃ i, y i ≠ x i := fun he => h (exists_ne_symm he)
    rw [lcpLen, lcpLen, dif_neg h, dif_neg h']

/-- Equal length-`n` prefixes ⇒ pointwise agreement below `n`. -/
theorem agree_of_pre_eq {x y : ℕ → D} {n i : ℕ} (h : pre x n = pre y n) (hi : i < n) :
    x i = y i := by
  have hcongr := congrArg (fun l => l[i]?) h
  simpa [pre, List.getElem?_map, List.getElem?_range, hi] using hcongr

/-! ## 2. The prefix gauge (the designed ultrametric basis, D2/D3/D4) -/

/-- **A prefix gauge**: a resolution weight on finite words, positive and
non-decreasing along admissible one-step extensions, over a prefix-closed set of
admissible words. This is the minimal data of a *designed ultrametric basis* — no
primes, no ring, no order on values; the structure (subshift, completion counts,
nested chains, …) enters only through `gauge` and `Adm`. -/
structure PrefixGauge (D : Type*) where
  /-- admissible finite words (the grammar of the substrate). -/
  Adm : List D → Prop
  /-- the resolution weight of a word (place value / admissible-completion count / …). -/
  gauge : List D → ℕ
  /-- admissibility is prefix-closed. -/
  adm_append : ∀ s t, Adm (s ++ t) → Adm s
  /-- the gauge is positive on admissible words. -/
  pos : ∀ s, Adm s → 0 < gauge s
  /-- the gauge is non-decreasing along admissible one-step extensions. -/
  mono_append : ∀ s d, Adm (s ++ [d]) → gauge s ≤ gauge (s ++ [d])

namespace PrefixGauge

variable (G : PrefixGauge D)

/-- Prefix-monotonicity, derived from the one-step law (D4). -/
theorem mono_of_append (s u : List D) (h : G.Adm (s ++ u)) :
    G.gauge s ≤ G.gauge (s ++ u) := by
  induction u using List.reverseRecOn with
  | nil => simp
  | append_singleton bs d ih =>
    have h1 : G.Adm ((s ++ bs) ++ [d]) := by
      rw [List.append_assoc]; exact h
    have h2 : G.Adm (s ++ bs) := G.adm_append _ _ h1
    calc G.gauge s ≤ G.gauge (s ++ bs) := ih h2
      _ ≤ G.gauge ((s ++ bs) ++ [d]) := G.mono_append _ _ h1
      _ = G.gauge (s ++ (bs ++ [d])) := by rw [List.append_assoc]

end PrefixGauge

/-- An admissible point: every prefix is an admissible word. -/
def AdmissiblePoint (G : PrefixGauge D) (x : ℕ → D) : Prop := ∀ n, G.Adm (pre x n)

/-- The gauge along a point's prefixes. -/
def gaugeAt (G : PrefixGauge D) (x : ℕ → D) (n : ℕ) : ℕ := G.gauge (pre x n)

theorem gaugeAt_pos (G : PrefixGauge D) {x : ℕ → D} (hx : AdmissiblePoint G x) (n : ℕ) :
    0 < gaugeAt G x n := G.pos _ (hx n)

theorem gaugeAt_monotone (G : PrefixGauge D) {x : ℕ → D} (hx : AdmissiblePoint G x) :
    Monotone (gaugeAt G x) := by
  apply monotone_nat_of_le_succ
  intro n
  have h := G.mono_append (pre x n) (x n) (by rw [← pre_succ]; exact hx (n + 1))
  simpa [gaugeAt, pre_succ] using h

theorem gaugeAt_eq_of_pre_eq (G : PrefixGauge D) {x y : ℕ → D} {n : ℕ}
    (hpre : pre x n = pre y n) : gaugeAt G x n = gaugeAt G y n := by
  rw [gaugeAt, gaugeAt, hpre]

/-! ## 3. The induced distance (derived, not carried — D3) -/

/-- **The gauge-induced distance**: the reciprocal gauge at the longest common prefix
(`0` for equal streams). The first-disagreement metric of the designed basis. -/
noncomputable def gaugeDist (G : PrefixGauge D) (x y : ℕ → D) : ℝ :=
  if h : ∃ i, x i ≠ y i then ((G.gauge (pre x (lcpLen x y)) : ℝ))⁻¹ else 0

theorem gaugeDist_of_ne (G : PrefixGauge D) {x y : ℕ → D} (h : ∃ i, x i ≠ y i) :
    gaugeDist G x y = ((G.gauge (pre x (lcpLen x y)) : ℝ))⁻¹ := by
  rw [gaugeDist, dif_pos h]

theorem gaugeDist_of_eq (G : PrefixGauge D) {x y : ℕ → D} (h : ¬ ∃ i, x i ≠ y i) :
    gaugeDist G x y = 0 := by rw [gaugeDist, dif_neg h]

/-- **Self-distance is zero.** -/
theorem gaugeDist_self (G : PrefixGauge D) (x : ℕ → D) : gaugeDist G x x = 0 := by
  apply gaugeDist_of_eq; rintro ⟨i, hi⟩; exact hi rfl

/-- **Non-negativity** (admissible centre). -/
theorem gaugeDist_nonneg (G : PrefixGauge D) {x : ℕ → D} (hx : AdmissiblePoint G x)
    (y : ℕ → D) : 0 ≤ gaugeDist G x y := by
  unfold gaugeDist
  split
  · have : (0 : ℝ) < (G.gauge (pre x (lcpLen x y)) : ℝ) := by
      exact_mod_cast G.pos _ (hx (lcpLen x y))
    exact inv_nonneg.mpr this.le
  · exact le_refl 0

/-- **Symmetry.** Both endpoints read the same gauge on their common prefix. -/
theorem gaugeDist_comm (G : PrefixGauge D) (x y : ℕ → D) :
    gaugeDist G x y = gaugeDist G y x := by
  by_cases h : ∃ i, x i ≠ y i
  · have h' : ∃ i, y i ≠ x i := exists_ne_symm h
    have hpre : pre x (lcpLen x y) = pre y (lcpLen x y) := pre_eq_of_le_lcp h (le_refl _)
    rw [gaugeDist_of_ne G h, gaugeDist_of_ne G h', ← lcpLen_comm x y, hpre]
  · have h' : ¬ ∃ i, y i ≠ x i := fun he => h (exists_ne_symm he)
    rw [gaugeDist_of_eq G h, gaugeDist_of_eq G h']

/-- **Identity of indiscernibles** (admissible centre). -/
theorem gaugeDist_eq_zero_iff (G : PrefixGauge D) {x : ℕ → D}
    (hx : AdmissiblePoint G x) (y : ℕ → D) : gaugeDist G x y = 0 ↔ x = y := by
  constructor
  · intro hd
    by_contra hne
    have h : ∃ i, x i ≠ y i := by
      by_contra h'; exact hne (eq_of_not_exists_ne h')
    rw [gaugeDist_of_ne G h] at hd
    have hpos : (0 : ℝ) < (G.gauge (pre x (lcpLen x y)) : ℝ) := by
      exact_mod_cast G.pos _ (hx (lcpLen x y))
    exact (inv_ne_zero (ne_of_gt hpos)) hd
  · rintro rfl; exact gaugeDist_self G x

/-- **SU0 — THE KEYSTONE (strong triangle inequality).** Any positive,
extension-monotone prefix gauge induces a genuine ULTRAMETRIC: a longer shared prefix
(`lcp x z ≥ min (lcp x y) (lcp y z)`) gives, via gauge monotonicity, the smaller
reciprocal. The `cfDist_triangle` proof, gauge-generic — the structure (subshift,
completion count, nested chain) enters only through the `PrefixGauge` laws. -/
theorem gaugeDist_triangle (G : PrefixGauge D) {x : ℕ → D}
    (hx : AdmissiblePoint G x) (y z : ℕ → D) :
    gaugeDist G x z ≤ max (gaugeDist G x y) (gaugeDist G y z) := by
  by_cases hxz : ∃ i, x i ≠ z i
  · by_cases hxy : ∃ i, x i ≠ y i
    · by_cases hyz : ∃ i, y i ≠ z i
      · -- main case: pairwise distinct on the relevant prefixes
        rw [gaugeDist_of_ne G hxz, gaugeDist_of_ne G hxy, gaugeDist_of_ne G hyz]
        have hmin : min (lcpLen x y) (lcpLen y z) ≤ lcpLen x z := by
          rw [lcpLen_eq_find hxz, Nat.le_find_iff]
          intro i hi
          rw [lt_min_iff] at hi
          exact fun hne => hne ((agree_below_lcp hxy hi.1).trans (agree_below_lcp hyz hi.2))
        have hxpos : (0 : ℝ) < (G.gauge (pre x (lcpLen x z)) : ℝ) := by
          exact_mod_cast G.pos _ (hx (lcpLen x z))
        have hminpos : (0 : ℝ) < (G.gauge (pre x (min (lcpLen x y) (lcpLen y z))) : ℝ) := by
          exact_mod_cast G.pos _ (hx (min (lcpLen x y) (lcpLen y z)))
        have hmono : G.gauge (pre x (min (lcpLen x y) (lcpLen y z)))
            ≤ G.gauge (pre x (lcpLen x z)) := gaugeAt_monotone G hx hmin
        have hinv : ((G.gauge (pre x (lcpLen x z)) : ℝ))⁻¹
            ≤ ((G.gauge (pre x (min (lcpLen x y) (lcpLen y z))) : ℝ))⁻¹ :=
          (inv_le_inv₀ hxpos hminpos).mpr (by exact_mod_cast hmono)
        rcases le_total (lcpLen x y) (lcpLen y z) with hab | hba
        · rw [min_eq_left hab] at hinv
          exact le_trans hinv (le_max_left _ _)
        · rw [min_eq_right hba] at hinv
          have hpre : pre x (lcpLen y z) = pre y (lcpLen y z) := pre_eq_of_le_lcp hxy hba
          rw [hpre] at hinv
          exact le_trans hinv (le_max_right _ _)
      · have he : y = z := eq_of_not_exists_ne hyz
        rw [← he]; exact le_max_left _ _
    · have he : x = y := eq_of_not_exists_ne hxy
      rw [← he]; exact le_max_right _ _
  · rw [gaugeDist_of_eq G hxz]
    exact le_max_of_le_left (gaugeDist_nonneg G hx y)

/-! ## 4. Unbounded gauges: cylinders shrink, `ball = cylinder` at every radius -/

/-- The gauge is unbounded along a point: resolution grows without bound (D4's
second tier; automatic for product gauges, the CF gauge, and coupled gauges). -/
def GaugeUnbounded (G : PrefixGauge D) (x : ℕ → D) : Prop :=
  ∀ M : ℕ, ∃ n, M ≤ gaugeAt G x n

/-- Cylinder radius `1/gaugeAt` eventually drops below any `ε > 0`. -/
theorem gaugeAt_inv_lt (G : PrefixGauge D) {x : ℕ → D} (hx : AdmissiblePoint G x)
    (hu : GaugeUnbounded G x) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n → ((gaugeAt G x n : ℝ))⁻¹ < ε := by
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / ε)
  obtain ⟨N, hN⟩ := hu (M + 1)
  refine ⟨N, fun n hn => ?_⟩
  have hmono : gaugeAt G x N ≤ gaugeAt G x n := gaugeAt_monotone G hx hn
  have h1 : (M : ℝ) < (gaugeAt G x n : ℝ) := by
    have : M + 1 ≤ gaugeAt G x n := le_trans hN hmono
    exact_mod_cast Nat.lt_of_lt_of_le (Nat.lt_succ_self M) this
  have hq : 1 / ε < (gaugeAt G x n : ℝ) := lt_trans hM h1
  have hpos : (0 : ℝ) < (gaugeAt G x n : ℝ) := by exact_mod_cast gaugeAt_pos G hx n
  have h2 : (0 : ℝ) < 1 / ε := one_div_pos.mpr hε
  have hlt := (inv_lt_inv₀ hpos h2).mpr hq
  rwa [one_div, inv_inv] at hlt

/-- **`ball = cylinder`.** For an unbounded gauge, every open ball about an admissible
point is exactly a combinatorial cylinder — the translation layer between the analytic
metric and the combinatorial refinement domains, now for ANY designed gauge. -/
theorem ball_eq_cylinder (G : PrefixGauge D) {x : ℕ → D} (hx : AdmissiblePoint G x)
    (hu : GaugeUnbounded G x) (r : ℝ) (hr : 0 < r) :
    ∃ n : ℕ, {y | gaugeDist G x y < r} = {y | pre y n = pre x n} := by
  have hex : ∃ k, ((gaugeAt G x k : ℝ))⁻¹ < r := by
    obtain ⟨N, hN⟩ := gaugeAt_inv_lt G hx hu r hr
    exact ⟨N, hN N (le_refl N)⟩
  refine ⟨Nat.find hex, ?_⟩
  have hspec : ((gaugeAt G x (Nat.find hex) : ℝ))⁻¹ < r := Nat.find_spec hex
  ext y
  simp only [Set.mem_setOf_eq]
  constructor
  · -- analytic → combinatorial
    intro hd
    by_cases hxy : ∃ i, x i ≠ y i
    · rw [gaugeDist_of_ne G hxy] at hd
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
    · rw [gaugeDist_of_ne G hxy]
      have hle : Nat.find hex ≤ lcpLen x y := by
        rw [lcpLen_eq_find hxy, Nat.le_find_iff]
        exact fun i hi hne => hne (agree_of_pre_eq hpre.symm hi)
      have hnpos : (0 : ℝ) < (gaugeAt G x (Nat.find hex) : ℝ) := by
        exact_mod_cast gaugeAt_pos G hx _
      have hlcppos : (0 : ℝ) < (G.gauge (pre x (lcpLen x y)) : ℝ) := by
        exact_mod_cast G.pos _ (hx _)
      calc ((G.gauge (pre x (lcpLen x y)) : ℝ))⁻¹
          ≤ ((gaugeAt G x (Nat.find hex) : ℝ))⁻¹ :=
            (inv_le_inv₀ hlcppos hnpos).mpr
              (by exact_mod_cast gaugeAt_monotone G hx hle)
        _ < r := hspec
    · rw [gaugeDist_of_eq G hxy]; exact hr

/-! ## 5. Bridge I — the product gauge (every radix law; Definition 79's formula) -/

/-- **The product gauge** of a radix law: `gauge = β_ω = prefixWeight ω`, no
admissibility constraint. Phase 6's designed ultrametric, as a `PrefixGauge`. -/
def productGauge (ω : RadixLaw) : PrefixGauge ℕ where
  Adm _ := True
  gauge := prefixWeight ω
  adm_append _ _ _ := trivial
  pos s _ := prefixWeight_pos ω s
  mono_append s d _ := by
    rw [prefixWeight_append]
    exact Nat.le_mul_of_pos_right _ (ω.radix_pos s)

theorem productGauge_admissible (ω : RadixLaw) (x : ℕ → ℕ) :
    AdmissiblePoint (productGauge ω) x := fun _ => trivial

/-- The product gauge dominates `2^depth` (radices are ≥ 2). -/
theorem two_pow_length_le_prefixWeight (ω : RadixLaw) (s : PrefixWord) :
    2 ^ s.length ≤ prefixWeight ω s := by
  induction s using List.reverseRecOn with
  | nil => simp
  | append_singleton bs d ih =>
    rw [prefixWeight_append, List.length_append, List.length_singleton, pow_succ]
    calc 2 ^ bs.length * 2 ≤ prefixWeight ω bs * 2 := Nat.mul_le_mul_right 2 ih
      _ ≤ prefixWeight ω bs * ω.radix bs := Nat.mul_le_mul_left _ (ω.radix_ge_two bs)

/-- Product gauges are unbounded along every point. -/
theorem productGauge_unbounded (ω : RadixLaw) (x : ℕ → ℕ) :
    GaugeUnbounded (productGauge ω) x := by
  intro M
  refine ⟨M, ?_⟩
  show M ≤ prefixWeight ω (pre x M)
  calc M ≤ 2 ^ M := Nat.le_of_lt M.lt_two_pow_self
    _ ≤ prefixWeight ω (pre x M) := by
        have h := two_pow_length_le_prefixWeight ω (pre x M)
        rwa [pre_length] at h

/-- The induced distance carries **Definition 79's formula** `β_ω(lcp)⁻¹` on streams.
(The alignment with `δ_ω` on `InfiniteVariableSpace` is deliberately not claimed —
thesis ledger item 2.) -/
theorem gaugeDist_productGauge (ω : RadixLaw) {x y : ℕ → ℕ} (h : ∃ i, x i ≠ y i) :
    gaugeDist (productGauge ω) x y = ((prefixWeight ω (pre x (lcpLen x y)) : ℝ))⁻¹ :=
  gaugeDist_of_ne _ h

/-! ## 6. Bridge II — the CF gauge: `cfDist` is an instance of SU0 -/

/-- **The generated (continued-fraction) gauge** as a `PrefixGauge`: admissible words
have all quotients ≥ 1, and the gauge is the convergent denominator `qₙ` of the
`RemainderState` ledger. -/
def cfGauge : PrefixGauge ℕ where
  Adm s := ∀ a ∈ s, 1 ≤ a
  gauge s := ((RemainderState.init.steps s).qCur).toNat
  adm_append s t h a ha := h a (List.mem_append_left _ ha)
  pos s hs := by
    have h := RemainderState.steps_qCur_pos hs
    omega
  mono_append s d h := by
    have hs : ∀ a ∈ s, 1 ≤ a := fun a ha => h a (List.mem_append_left _ ha)
    have hd : 1 ≤ d := h d (List.mem_append_right _ (List.mem_singleton_self d))
    have hstep : RemainderState.init.steps (s ++ [d])
        = (RemainderState.init.steps s).step d := by
      simp [RemainderState.steps, List.foldl_append]
    obtain ⟨hp, hpc, hq, _⟩ := RemainderState.steps_invariant hs
    have hd' : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    have hqp : (0 : ℤ) ≤ (RemainderState.init.steps s).qCur := le_trans hp hpc
    have hkey : (RemainderState.init.steps s).qCur
        ≤ (d : ℤ) * (RemainderState.init.steps s).qCur
          + (RemainderState.init.steps s).qPrev := by nlinarith
    show ((RemainderState.init.steps s).qCur).toNat
        ≤ ((RemainderState.init.steps (s ++ [d])).qCur).toNat
    rw [hstep]
    simp only [RemainderState.step]
    omega

/-- A stream is `cfGauge`-admissible iff it is `Subshift.Admissible` (all quotients ≥ 1). -/
theorem cfGauge_admissiblePoint_iff (x : ℕ → ℕ) :
    AdmissiblePoint cfGauge x ↔ Subshift.Admissible x := by
  constructor
  · intro h i
    have hmem : x i ∈ pre x (i + 1) := by
      simp only [pre, List.mem_map]
      exact ⟨i, by simp [List.mem_range], rfl⟩
    exact h (i + 1) (x i) hmem
  · intro h n a ha
    simp only [pre, List.mem_map] at ha
    obtain ⟨j, _, rfl⟩ := ha
    exact h j

/-- The two prefix extractors agree definitionally. -/
theorem pre_eq_subshift (x : ℕ → ℕ) (n : ℕ) : pre x n = Subshift.pre x n := rfl

/-- The two lcp lengths agree (instance-independent `Nat.find`). -/
theorem lcpLen_eq_subshift {x y : ℕ → ℕ} (h : ∃ i, x i ≠ y i) :
    lcpLen x y = Subshift.lcpLen x y := by
  rw [lcpLen_eq_find h, Subshift.lcpLen_eq_find h]

/-- **`cfDist` is an instance of SU0.** On admissible points, the gauge-induced
distance of `cfGauge` is exactly the Phase 13 continued-fraction ultrametric. The two
existing corpus ultrametrics (product δ and CF δ) are now both instances of one
keystone. -/
theorem gaugeDist_cfGauge {x : ℕ → ℕ} (hx : Subshift.Admissible x) (y : ℕ → ℕ) :
    gaugeDist cfGauge x y = Subshift.cfDist x y := by
  by_cases h : ∃ i, x i ≠ y i
  · rw [gaugeDist_of_ne _ h, Subshift.cfDist_of_ne h, lcpLen_eq_subshift h]
    have hq : 0 < Subshift.gaugeAt x (Subshift.lcpLen x y) :=
      Subshift.gaugeAt_pos hx (Subshift.lcpLen x y)
    congr 1
    show (((RemainderState.init.steps (pre x (Subshift.lcpLen x y))).qCur).toNat : ℝ)
        = ((Subshift.gaugeAt x (Subshift.lcpLen x y) : ℤ) : ℝ)
    rw [pre_eq_subshift]
    have htoNat : (((RemainderState.init.steps
        (Subshift.pre x (Subshift.lcpLen x y))).qCur).toNat : ℤ)
        = (RemainderState.init.steps (Subshift.pre x (Subshift.lcpLen x y))).qCur :=
      Int.toNat_of_nonneg (le_of_lt hq)
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) htoNat
  · rw [gaugeDist_of_eq _ h, Subshift.cfDist_of_eq h]

end FdrsFormal.Modes.SyntheticPlace
