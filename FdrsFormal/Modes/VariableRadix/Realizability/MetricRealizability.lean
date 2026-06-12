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

# Theorem 43, solved — the corrected metric realizability characterization

This file closes the metric half of Theorem 43 that `Sufficiency.lean` honestly
deferred, in the **corrected** form recorded by the Phase-14 erratum (fdrs.md
§6.6.1): the original conditions are insufficient — witnessed here — and the right
characterization is:

> **Theorem 43 (corrected).** For an abstract ultrametric `δ` on `∏ᵢ Dᵢ` (each
> `Dᵢ` finite with ≥ 2 elements), `δ` is SU-realizable — `δ(x,y)` equals the
> reciprocal canonical place value at the first difference, i.e. the `δ_ω` formula
> for the (unique, position-only) SU law `ω` with `radix = card ∘ length` — **iff**
> 1. **(C1) every open ball is a prefix cylinder** (`BallsAreCylinders`), and
> 2. **(C4) every depth-`n` cylinder has canonical diameter**
>    `(∏_{j<n} card Dⱼ)⁻¹` (`CanonicalDiameters`, stated as an `IsLUB`).

Both directions are proven (`theorem43`). The load-bearing discovery is **the
extraction** (`dist_eq_of_lcpLen_eq`, `dist_anti_of_lcpLen_lt`, `dist_local`):
condition (C1) *alone* forces `δ` to be a first-difference (gauge) ultrametric —
the ball-pivot argument: a ball of radius `δ(x,z)` is a cylinder, so it separates
partners by lcp depth, making the distance a function of the prefix at the first
difference. This is Theorem 43-general, the dendrogram/gauge step; (C4) then pins
the gauge to the canonical product schedule — Theorem 43-SU.

**Why the original statement needed correction** (machine-checked here):

* `conditions_insufficient` — the schedule `R n = 1/(2n+1)` on the binary product
  satisfies (C1) — hence also the original (1)–(3), which are weaker — but is not
  SU-realizable: the conditions pin the *tree*, not the *gauge* (the radius
  schedule need not be multiplicative).
* The original "finite **union** of cylinders" is too weak even for the extraction
  (three sibling subtrees at pairwise-unequal distances satisfy it while breaking
  the first-difference form); the corrected (C1) takes the single-cylinder form —
  exactly what the concrete side actually proves (`ball_is_cylinder`) and exactly
  SU0's `ball_eq_cylinder` shape (Phase 14, Theorem 83).

**Honest scope.** Realizability is defined *intrinsically* (the `δ_ω` defining
formula on `δ`'s own space, tied to the constructed law via
`prefixWeight_radixLawFromUltrametric`); the transport onto the
`InfiniteVariableSpace ω` model along per-level `Dᵢ ≃ Fin (card Dᵢ)` equivalences
is a mechanical relabeling (level-wise relabelings are `δ_ω`-isometries for
position-only laws) and is not re-proven here. The ultrametric ↔ dendrogram
correspondence is classical; the corpus contributions are the corrected statement,
the counterexample, and the verified artifact. No `sorry`; axiom-clean.
-/
import FdrsFormal.Modes.VariableRadix.Realizability.Sufficiency

namespace FdrsFormal.Modes.VariableRadix

open Classical Finset

/-! ## 1. First-difference machinery on dependent digit streams -/

section LcpMachinery

variable {D : ℕ → Type}

/-- The first position where two streams differ (`0` for equal streams). -/
noncomputable def lcpLenD (x y : ∀ i, D i) : ℕ :=
  if h : ∃ i, x i ≠ y i then Nat.find h else 0

theorem exists_ne_of_ne {x y : ∀ i, D i} (h : x ≠ y) : ∃ i, x i ≠ y i :=
  Function.ne_iff.mp h

theorem lcpLenD_eq_find {x y : ∀ i, D i} (h : ∃ i, x i ≠ y i) :
    lcpLenD x y = Nat.find h := by rw [lcpLenD, dif_pos h]

theorem lcpLenD_spec {x y : ∀ i, D i} (h : x ≠ y) :
    (∀ i, i < lcpLenD x y → x i = y i) ∧ x (lcpLenD x y) ≠ y (lcpLenD x y) := by
  have he := exists_ne_of_ne h
  rw [lcpLenD_eq_find he]
  exact ⟨fun i hi => not_not.mp (Nat.find_min he hi), Nat.find_spec he⟩

theorem lcpLenD_eq_iff {x y : ∀ i, D i} (h : x ≠ y) {n : ℕ} :
    lcpLenD x y = n ↔ (∀ i, i < n → x i = y i) ∧ x n ≠ y n := by
  have he := exists_ne_of_ne h
  rw [lcpLenD_eq_find he]
  rw [Nat.find_eq_iff]
  constructor
  · rintro ⟨hn, hmin⟩
    exact ⟨fun i hi => not_not.mp (hmin i hi), hn⟩
  · rintro ⟨hagree, hn⟩
    exact ⟨hn, fun i hi => not_not.mpr (hagree i hi)⟩

theorem lcpLenD_comm (x y : ∀ i, D i) : lcpLenD x y = lcpLenD y x := by
  by_cases h : ∃ i, x i ≠ y i
  · have h' : ∃ i, y i ≠ x i := by obtain ⟨i, hi⟩ := h; exact ⟨i, fun e => hi e.symm⟩
    rw [lcpLenD_eq_find h, lcpLenD_eq_find h']
    exact le_antisymm
      (Nat.find_min' _ (fun e => Nat.find_spec h' e.symm))
      (Nat.find_min' _ (fun e => Nat.find_spec h e.symm))
  · have h' : ¬ ∃ i, y i ≠ x i := fun ⟨i, hi⟩ => h ⟨i, fun e => hi e.symm⟩
    rw [lcpLenD, lcpLenD, dif_neg h, dif_neg h']

/-- Streams agreeing strictly below the lcps of both pairs share lcp lower bounds:
`lcp(x,z) ≥ min (lcp(x,y), lcp(y,z))`. -/
theorem min_lcpLenD_le {x y z : ∀ i, D i} (hxz : x ≠ z) :
    min (lcpLenD x y) (lcpLenD y z) ≤ lcpLenD x z := by
  by_cases hxy : x = y
  · subst hxy
    exact min_le_right _ _
  by_cases hyz : y = z
  · subst hyz
    exact min_le_left _ _
  have he := exists_ne_of_ne hxz
  rw [lcpLenD_eq_find he, Nat.le_find_iff]
  intro i hi
  rw [lt_min_iff] at hi
  have h1 := (lcpLenD_spec hxy).1 i hi.1
  have h2 := (lcpLenD_spec hyz).1 i hi.2
  exact fun hne => hne (h1.trans h2)

/-- The depth-`n` prefix cylinder of `x`. -/
def CylD (x : ∀ i, D i) (n : ℕ) : Set (∀ i, D i) := {y | ∀ i, i < n → y i = x i}

theorem self_mem_CylD (x : ∀ i, D i) (n : ℕ) : x ∈ CylD x n := fun _ _ => rfl

theorem mem_CylD_iff_le_lcpLenD {x y : ∀ i, D i} (h : x ≠ y) {n : ℕ} :
    y ∈ CylD x n ↔ n ≤ lcpLenD x y := by
  have he := exists_ne_of_ne h
  rw [lcpLenD_eq_find he, Nat.le_find_iff]
  constructor
  · intro hmem i hi
    exact not_not.mpr ((hmem i hi).symm)
  · intro hmin i hi
    exact (not_not.mp (hmin i hi)).symm

/-- Partner construction: a stream differing from `x` first at exactly `n`
(needs ≥ 2 digits at level `n`). -/
theorem exists_partner (x : ∀ i, D i) (n : ℕ) [Finite (D n)]
    (hcard : 2 ≤ Nat.card (D n)) :
    ∃ y : ∀ i, D i, x ≠ y ∧ lcpLenD x y = n ∧ y ∈ CylD x n := by
  haveI : Nontrivial (D n) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨d, hd⟩ := exists_ne (x n)
  refine ⟨Function.update x n d, ?_, ?_, ?_⟩
  · intro hxy
    have := congrFun hxy n
    rw [Function.update_self] at this
    exact hd this.symm
  · have hne : x ≠ Function.update x n d := by
      intro hxy
      have := congrFun hxy n
      rw [Function.update_self] at this
      exact hd this.symm
    rw [lcpLenD_eq_iff hne]
    constructor
    · intro i hi
      rw [Function.update_of_ne (Nat.ne_of_lt hi)]
    · rw [Function.update_self]
      exact fun e => hd e.symm
  · intro i hi
    rw [Function.update_of_ne (Nat.ne_of_lt hi)]

end LcpMachinery

/-! ## 2. The corrected conditions -/

/-- **(C1) Balls are cylinders** — the corrected cylinder-correspondence condition:
every open ball about every point is a single prefix cylinder of that point (the
single-cylinder form, matching the concrete `ball_is_cylinder` and SU0's
`ball_eq_cylinder`; the original "finite union" form is strictly weaker and
insufficient — see the module docstring). -/
def BallsAreCylinders (δ : AbstractUltrametric) : Prop :=
  ∀ (x : ∀ i, δ.digitSets i) (r : ℝ), 0 < r →
    ∃ n, {y | δ.dist x y < r} = CylD x n

/-- The canonical radius schedule: the reciprocal cumulative digit-set cardinality —
exactly `(β_ω)⁻¹` for the constructed position-only SU law (Definition 79's values). -/
noncomputable def canonicalRadius (δ : AbstractUltrametric) (n : ℕ) : ℝ :=
  (∏ j ∈ Finset.range n, (Nat.card (δ.digitSets j) : ℝ))⁻¹

/-- The set of pairwise distances within a depth-`n` cylinder. -/
def pairDists (δ : AbstractUltrametric) (x : ∀ i, δ.digitSets i) (n : ℕ) : Set ℝ :=
  {r | ∃ u ∈ CylD x n, ∃ v ∈ CylD x n, δ.dist u v = r}

/-- **(C4) Canonical diameters** — the condition the original statement was missing:
every depth-`n` cylinder has diameter exactly the canonical radius (as a least upper
bound). This is what pins the *gauge*, where (C1) pins only the *tree*. -/
def CanonicalDiameters (δ : AbstractUltrametric) : Prop :=
  ∀ (x : ∀ i, δ.digitSets i) (n : ℕ),
    IsLUB (pairDists δ x n) (canonicalRadius δ n)

/-- **SU-realizability, intrinsic form**: `δ` carries the `δ_ω` defining formula —
first-difference distance with the canonical (reciprocal place-value) schedule —
for the position-only SU law `radixLawFromUltrametric δ`
(`prefixWeight_radixLawFromUltrametric` ties the schedule to `β_ω`). -/
def SURealizable (δ : AbstractUltrametric) : Prop :=
  ∀ x y : ∀ i, δ.digitSets i, x ≠ y → δ.dist x y = canonicalRadius δ (lcpLenD x y)

/-! ## 3. Basic facts about the canonical schedule -/

section Canonical

variable (δ : AbstractUltrametric)

theorem canonicalProd_pos (h2 : AbstractRealizabilityConditions δ) (n : ℕ) :
    0 < ∏ j ∈ Finset.range n, (Nat.card (δ.digitSets j) : ℝ) := by
  apply Finset.prod_pos
  intro j _
  have := h2.digitSets_geTwo j
  positivity

theorem canonicalRadius_pos (h2 : AbstractRealizabilityConditions δ) (n : ℕ) :
    0 < canonicalRadius δ n := by
  rw [canonicalRadius]
  exact inv_pos.mpr (canonicalProd_pos δ h2 n)

theorem canonicalProd_mono (h2 : AbstractRealizabilityConditions δ) {m n : ℕ}
    (h : m ≤ n) :
    ∏ j ∈ Finset.range m, (Nat.card (δ.digitSets j) : ℝ)
      ≤ ∏ j ∈ Finset.range n, (Nat.card (δ.digitSets j) : ℝ) := by
  induction n, h using Nat.le_induction with
  | base => exact le_refl _
  | succ n hmn ih =>
    rw [Finset.prod_range_succ]
    have hone : (1 : ℝ) ≤ (Nat.card (δ.digitSets n) : ℝ) := by
      have := h2.digitSets_geTwo n
      exact_mod_cast by omega
    calc ∏ j ∈ Finset.range m, (Nat.card (δ.digitSets j) : ℝ)
        ≤ ∏ j ∈ Finset.range n, (Nat.card (δ.digitSets j) : ℝ) := ih
      _ ≤ _ := le_mul_of_one_le_right (canonicalProd_pos δ h2 n).le hone

theorem canonicalRadius_antitone (h2 : AbstractRealizabilityConditions δ)
    {m n : ℕ} (h : m ≤ n) :
    canonicalRadius δ n ≤ canonicalRadius δ m := by
  rw [canonicalRadius, canonicalRadius]
  exact (inv_le_inv₀ (canonicalProd_pos δ h2 n) (canonicalProd_pos δ h2 m)).mpr
    (canonicalProd_mono δ h2 h)

theorem two_pow_le_canonicalProd (h2 : AbstractRealizabilityConditions δ) (n : ℕ) :
    (2 : ℝ) ^ n ≤ ∏ j ∈ Finset.range n, (Nat.card (δ.digitSets j) : ℝ) := by
  rw [show (2 : ℝ) ^ n = ∏ _j ∈ Finset.range n, (2 : ℝ) by
    rw [Finset.prod_const, Finset.card_range]]
  apply Finset.prod_le_prod
  · intro j _; norm_num
  · intro j _
    exact_mod_cast h2.digitSets_geTwo j

/-- The canonical schedule vanishes: there is always a depth below any radius. -/
theorem canonicalRadius_lt (h2 : AbstractRealizabilityConditions δ) (r : ℝ)
    (hr : 0 < r) :
    ∃ n, canonicalRadius δ n < r := by
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / r)
  refine ⟨M, ?_⟩
  have h1 : (1 / r : ℝ) < (2 : ℝ) ^ M := by
    calc (1 / r : ℝ) < M := hM
      _ < (2 : ℝ) ^ M := by exact_mod_cast Nat.lt_two_pow_self
  have h2' : (2 : ℝ) ^ M ≤ ∏ j ∈ Finset.range M, (Nat.card (δ.digitSets j) : ℝ) :=
    two_pow_le_canonicalProd δ h2 M
  have hpos : (0 : ℝ) < ∏ j ∈ Finset.range M, (Nat.card (δ.digitSets j) : ℝ) :=
    canonicalProd_pos δ h2 M
  rw [canonicalRadius]
  have hgt : 1 / r < ∏ j ∈ Finset.range M, (Nat.card (δ.digitSets j) : ℝ) :=
    lt_of_lt_of_le h1 h2'
  have h1r : (0 : ℝ) < 1 / r := by positivity
  have := (inv_lt_inv₀ hpos h1r).mpr hgt
  rwa [one_div, inv_inv] at this

end Canonical

/-! ## 4. THE EXTRACTION — condition (C1) alone forces the first-difference form -/

section Extraction

variable {δ : AbstractUltrametric}

theorem dist_pos (δ : AbstractUltrametric) {x y : ∀ i, δ.digitSets i} (h : x ≠ y) :
    0 < δ.dist x y :=
  (δ.dist_nonneg x y).lt_of_ne
    (fun h0 => h ((δ.dist_eq_zero_iff x y).mp h0.symm))

/-- **L1 (rigidity at a point).** Under (C1), the distance from `x` depends only on
the lcp depth: partners differing from `x` first at the same position are
equidistant from it. *The ball-pivot argument*: the ball of the larger radius is a
cylinder, which separates the partners by depth — contradiction. -/
theorem dist_eq_of_lcpLenD_eq (hC1 : BallsAreCylinders δ)
    {x y z : ∀ i, δ.digitSets i} (hxy : x ≠ y) (hxz : x ≠ z)
    (h : lcpLenD x y = lcpLenD x z) : δ.dist x y = δ.dist x z := by
  have key : ∀ {u v : ∀ i, δ.digitSets i}, x ≠ u → x ≠ v →
      lcpLenD x u = lcpLenD x v → δ.dist x u < δ.dist x v → False := by
    intro u v hxu hxv hl hlt
    obtain ⟨n, hball⟩ := hC1 x (δ.dist x v) (dist_pos δ hxv)
    have hu : u ∈ CylD x n := by
      rw [← hball]; exact hlt
    have hv : v ∉ CylD x n := by
      rw [← hball]
      simp [Set.mem_setOf_eq]
    have h1 : n ≤ lcpLenD x u := (mem_CylD_iff_le_lcpLenD hxu).mp hu
    have h2 : ¬ n ≤ lcpLenD x v := fun hle =>
      hv ((mem_CylD_iff_le_lcpLenD hxv).mpr hle)
    rw [hl] at h1
    exact h2 h1
  rcases lt_trichotomy (δ.dist x y) (δ.dist x z) with hlt | heq | hgt
  · exact (key hxy hxz h hlt).elim
  · exact heq
  · exact (key hxz hxy h.symm hgt).elim

/-- **L2 (depth-antitonicity).** Under (C1), deeper first differences are not
farther: `lcp(x,y) < lcp(x,z) ⟹ δ(x,z) ≤ δ(x,y)`. -/
theorem dist_anti_of_lcpLenD_lt (hC1 : BallsAreCylinders δ)
    {x y z : ∀ i, δ.digitSets i} (hxy : x ≠ y) (hxz : x ≠ z)
    (h : lcpLenD x y < lcpLenD x z) : δ.dist x z ≤ δ.dist x y := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨n, hball⟩ := hC1 x (δ.dist x z) (dist_pos δ hxz)
  have hy : y ∈ CylD x n := by rw [← hball]; exact hlt
  have hz : z ∉ CylD x n := by
    rw [← hball]; simp [Set.mem_setOf_eq]
  have h1 : n ≤ lcpLenD x y := (mem_CylD_iff_le_lcpLenD hxy).mp hy
  have h2 : ¬ n ≤ lcpLenD x z := fun hle =>
    hz ((mem_CylD_iff_le_lcpLenD hxz).mpr hle)
  exact h2 (le_trans h1 (le_of_lt h))

/-- **L3 (prefix locality).** Under (C1), the first-difference distance depends only
on the shared prefix: if `x, x'` agree strictly below `n` and both pairs first
differ at `n`, the distances agree. Proof by the partner trick + the strong
triangle, splitting on whether `x` and `x'` agree at `n` itself. -/
theorem dist_local (hC1 : BallsAreCylinders δ)
    (h2 : AbstractRealizabilityConditions δ)
    {x y x' y' : ∀ i, δ.digitSets i} (hxy : x ≠ y) (hx'y' : x' ≠ y')
    (hlcp : lcpLenD x y = lcpLenD x' y')
    (hagree : ∀ i, i < lcpLenD x y → x i = x' i) :
    δ.dist x y = δ.dist x' y' := by
  set n := lcpLenD x y with hn
  by_cases hxx' : x = x'
  · subst hxx'
    exact dist_eq_of_lcpLenD_eq hC1 hxy hx'y' hlcp
  by_cases hat : x n = x' n
  · -- agree through n: pick a common partner w at depth n
    haveI := δ.digitSets_finite n
    obtain ⟨w, hxw, hlw, _⟩ := exists_partner x n (h2.digitSets_geTwo n)
    -- w also first-differs from x' at n
    have hx'w : x' ≠ w := by
      intro he
      have hspec := (lcpLenD_eq_iff hxw).mp hlw
      rw [he] at hat
      exact hspec.2 hat
    have hlw' : lcpLenD x' w = n := by
      rw [lcpLenD_eq_iff hx'w]
      have hspec := (lcpLenD_eq_iff hxw).mp hlw
      constructor
      · intro i hi
        rw [← hagree i hi]
        exact hspec.1 i hi
      · rw [← hat]
        exact hspec.2
    -- x and x' agree through n, so lcp(x,x') > n
    have hlxx' : n < lcpLenD x x' := by
      rcases Nat.lt_or_ge n (lcpLenD x x') with h | h
      · exact h
      · exfalso
        have hspec := (lcpLenD_spec hxx').1
        have heq : x (lcpLenD x x') = x' (lcpLenD x x') := by
          rcases Nat.lt_or_ge (lcpLenD x x') n with hlt | hge
          · exact hagree _ hlt
          · have : lcpLenD x x' = n := le_antisymm h hge
            rw [this]; exact hat
        exact (lcpLenD_spec hxx').2 heq
    -- triangle both ways through w
    have hred : δ.dist x y = δ.dist x w :=
      dist_eq_of_lcpLenD_eq hC1 hxy hxw (by rw [hlw])
    have hred' : δ.dist x' y' = δ.dist x' w :=
      dist_eq_of_lcpLenD_eq hC1 hx'y' hx'w (by rw [hlw', ← hlcp])
    have hxx'le : δ.dist x x' ≤ δ.dist x w :=
      dist_anti_of_lcpLenD_lt hC1 hxw hxx' (by rw [hlw]; exact hlxx')
    have h1 : δ.dist x' w ≤ δ.dist x w := by
      calc δ.dist x' w ≤ max (δ.dist x' x) (δ.dist x w) := δ.dist_ultrametric x' x w
        _ = max (δ.dist x x') (δ.dist x w) := by rw [δ.dist_symm x' x]
        _ = δ.dist x w := max_eq_right hxx'le
    have hx'x'le : δ.dist x' x ≤ δ.dist x' w := by
      have hlx'x : lcpLenD x' x = lcpLenD x x' := lcpLenD_comm x' x
      have hx'x : x' ≠ x := fun e => hxx' e.symm
      exact dist_anti_of_lcpLenD_lt hC1 hx'w hx'x (by rw [hlw', hlx'x]; exact hlxx')
    have h2' : δ.dist x w ≤ δ.dist x' w := by
      calc δ.dist x w ≤ max (δ.dist x x') (δ.dist x' w) := δ.dist_ultrametric x x' w
        _ = max (δ.dist x' x) (δ.dist x' w) := by rw [δ.dist_symm x x']
        _ = δ.dist x' w := max_eq_right hx'x'le
    rw [hred, hred', le_antisymm h1 h2']
  · -- x and x' first differ at exactly n: use each other as partners
    have hlxx' : lcpLenD x x' = n := by
      rw [lcpLenD_eq_iff hxx']
      exact ⟨fun i hi => hagree i hi, hat⟩
    have hx'x : x' ≠ x := fun e => hxx' e.symm
    have hlx'x : lcpLenD x' x = n := by rw [lcpLenD_comm]; exact hlxx'
    calc δ.dist x y = δ.dist x x' :=
          dist_eq_of_lcpLenD_eq hC1 hxy hxx' (by rw [hlxx'])
      _ = δ.dist x' x := δ.dist_symm x x'
      _ = δ.dist x' y' :=
          dist_eq_of_lcpLenD_eq hC1 hx'x hx'y' (by rw [hlx'x, ← hlcp])

end Extraction

/-! ## 5. Necessity: realizable ⟹ (C1) ∧ (C4) -/

section Necessity

variable {δ : AbstractUltrametric}

/-- First-difference metrics with antitone vanishing schedules have cylinder balls
(the SU0 `ball_eq_cylinder` argument, on the abstract space). -/
theorem ballsAreCylinders_of_schedule (R : ℕ → ℝ)
    (hanti : ∀ {m n : ℕ}, m ≤ n → R n ≤ R m)
    (hvan : ∀ r : ℝ, 0 < r → ∃ n, R n < r)
    (hδR : ∀ x y : ∀ i, δ.digitSets i, x ≠ y → δ.dist x y = R (lcpLenD x y)) :
    BallsAreCylinders δ := by
  intro x r hr
  have hex : ∃ n, R n < r := hvan r hr
  refine ⟨Nat.find hex, ?_⟩
  ext y
  simp only [Set.mem_setOf_eq]
  by_cases hxy : x = y
  · subst hxy
    constructor
    · intro _; exact self_mem_CylD x _
    · intro _
      rw [(δ.dist_eq_zero_iff x x).mpr rfl]
      exact hr
  · rw [hδR x y hxy]
    constructor
    · intro hlt
      apply (mem_CylD_iff_le_lcpLenD hxy).mpr
      by_contra hle
      push_neg at hle
      exact Nat.find_min hex hle hlt
    · intro hmem
      have hle : Nat.find hex ≤ lcpLenD x y := (mem_CylD_iff_le_lcpLenD hxy).mp hmem
      exact lt_of_le_of_lt (hanti hle) (Nat.find_spec hex)

/-- **Necessity.** A realizable `δ` satisfies both corrected conditions. -/
theorem necessity (h2 : AbstractRealizabilityConditions δ) (hreal : SURealizable δ) :
    BallsAreCylinders δ ∧ CanonicalDiameters δ := by
  constructor
  · exact ballsAreCylinders_of_schedule (canonicalRadius δ)
      (fun {m n} h => canonicalRadius_antitone δ h2 h)
      (fun r hr => canonicalRadius_lt δ h2 r hr)
      hreal
  · intro x n
    constructor
    · -- upper bound: distances within the cylinder are at most canonical n
      rintro r ⟨u, hu, v, hv, rfl⟩
      by_cases huv : u = v
      · subst huv
        rw [(δ.dist_eq_zero_iff u u).mpr rfl]
        exact (canonicalRadius_pos δ h2 n).le
      · rw [hreal u v huv]
        apply canonicalRadius_antitone δ h2
        -- u, v agree strictly below n (both agree with x there)
        by_contra hlt
        push_neg at hlt
        have hspec := (lcpLenD_spec huv).2
        have : u (lcpLenD u v) = v (lcpLenD u v) := by
          rw [hu _ hlt, hv _ hlt]
        exact hspec this
    · -- least: any upper bound dominates the witness pair's distance
      intro b hb
      haveI := δ.digitSets_finite n
      obtain ⟨w, hxw, hlw, hwc⟩ := exists_partner x n (h2.digitSets_geTwo n)
      have hwd : δ.dist x w = canonicalRadius δ n := by
        rw [hreal x w hxw, hlw]
      have hmem : δ.dist x w ∈ pairDists δ x n :=
        ⟨x, self_mem_CylD x n, w, hwc, rfl⟩
      rw [← hwd]
      exact hb hmem

end Necessity

/-! ## 6. Sufficiency: (C1) ∧ (C4) ⟹ realizable -/

section Sufficiency

variable {δ : AbstractUltrametric}

/-- **Sufficiency.** Under the corrected conditions, every distance is the canonical
first-difference value: the extraction (L1–L3) shows `δ.dist x y` is itself a least
upper bound of the cylinder's pairwise distances, and (C4) says the canonical radius
is too — LUBs are unique. -/
theorem sufficiency (h2 : AbstractRealizabilityConditions δ)
    (hC1 : BallsAreCylinders δ) (hdiam : CanonicalDiameters δ) :
    SURealizable δ := by
  intro x y hxy
  set n := lcpLenD x y with hn
  -- δ.dist x y is an LUB of pairDists δ x n
  have hlub : IsLUB (pairDists δ x n) (δ.dist x y) := by
    constructor
    · -- upper bound
      rintro r ⟨u, hu, v, hv, rfl⟩
      by_cases huv : u = v
      · subst huv
        rw [(δ.dist_eq_zero_iff u u).mpr rfl]
        exact δ.dist_nonneg x y
      · -- u, v agree with x below n, so lcp(u,v) ≥ n
        have hm : n ≤ lcpLenD u v := by
          by_contra hlt
          push_neg at hlt
          exact (lcpLenD_spec huv).2 (by rw [hu _ hlt, hv _ hlt])
        rcases eq_or_lt_of_le hm with heq | hlt
        · -- equal depth: prefix locality transfers the value
          exact le_of_eq (dist_local hC1 h2 huv hxy (by rw [← heq])
            (fun i hi => (hu i (by rw [← heq] at hi; exact hi))))
        · -- deeper: bound through a depth-n partner of u
          haveI := δ.digitSets_finite n
          obtain ⟨w, huw, hlw, _⟩ := exists_partner u n (h2.digitSets_geTwo n)
          have hstep : δ.dist u v ≤ δ.dist u w :=
            dist_anti_of_lcpLenD_lt hC1 huw huv (by rw [hlw]; exact hlt)
          have heqd : δ.dist u w = δ.dist x y :=
            dist_local hC1 h2 huw hxy (by rw [hlw])
              (fun i hi => hu i (by rw [hlw] at hi; exact hi))
          rw [← heqd]
          exact hstep
    · -- least upper bound: (x, y) itself is in the set
      intro b hb
      have hmem : δ.dist x y ∈ pairDists δ x n := by
        refine ⟨x, self_mem_CylD x n, y, ?_, rfl⟩
        intro i hi
        exact ((lcpLenD_spec hxy).1 i (by rw [hn] at hi; exact hi)).symm
      exact hb hmem
  exact hlub.unique (hdiam x n)

end Sufficiency

/-! ## 7. THEOREM 43 (corrected) — the full characterization -/

/-- **THEOREM 43 (corrected), solved.** An abstract ultrametric on `∏ᵢ Dᵢ` (digit
sets finite, ≥ 2 elements) is SU-realizable — carries the `δ_ω` defining formula of
the position-only SU law `radix = card ∘ length` — **iff** every open ball is a
prefix cylinder and every cylinder has canonical diameter. The conditions split
exactly as the Phase-14 erratum records: (C1) pins the tree (the extraction /
dendrogram step, Theorem 43-general); (C4) pins the gauge (Theorem 43-SU). -/
theorem theorem43 (δ : AbstractUltrametric) (h2 : AbstractRealizabilityConditions δ) :
    SURealizable δ ↔ BallsAreCylinders δ ∧ CanonicalDiameters δ :=
  ⟨necessity h2, fun ⟨hC1, hdiam⟩ => sufficiency h2 hC1 hdiam⟩

/-- The canonical schedule is the constructed SU law's reciprocal prefix weight:
`canonicalRadius δ n = (β_ω(s))⁻¹` for any prefix `s` of length `n` of the law
`radixLawFromUltrametric δ h2` — i.e. `SURealizable` is literally the `δ_ω`
defining formula (Definition 79) for the law the branching slice constructs. -/
theorem prefixWeight_radixLawFromUltrametric (δ : AbstractUltrametric)
    (h2 : AbstractRealizabilityConditions δ) (s : PrefixWord) :
    (prefixWeight (radixLawFromUltrametric δ h2) s : ℝ)
      = ∏ j ∈ Finset.range s.length, (Nat.card (δ.digitSets j) : ℝ) := by
  induction s using List.reverseRecOn with
  | nil => simp
  | append_singleton t d ih =>
    rw [prefixWeight_append, List.length_append]
    push_cast
    rw [ih]
    simp only [List.length_singleton, Finset.prod_range_succ]
    rfl

/-- Realizability, restated through the constructed law: the distance is the
reciprocal prefix weight at the first difference — `δ = δ_ω` in the intrinsic
sense, with `ω := radixLawFromUltrametric δ h2`. -/
theorem suRealizable_iff_prefixWeight (δ : AbstractUltrametric)
    (h2 : AbstractRealizabilityConditions δ) :
    SURealizable δ ↔ ∀ (x y : ∀ i, δ.digitSets i) (_ : x ≠ y) (s : PrefixWord),
      s.length = lcpLenD x y →
      δ.dist x y = ((prefixWeight (radixLawFromUltrametric δ h2) s : ℝ))⁻¹ := by
  constructor
  · intro hreal x y hxy s hs
    rw [hreal x y hxy, canonicalRadius, ← hs,
      prefixWeight_radixLawFromUltrametric δ h2]
  · intro h x y hxy
    have := h x y hxy (List.replicate (lcpLenD x y) 0) (List.length_replicate)
    rw [this, canonicalRadius, prefixWeight_radixLawFromUltrametric δ h2,
      List.length_replicate]

/-! ## 8. The insufficiency witness — why the correction was necessary -/

/-- A first-difference ultrametric from an arbitrary positive antitone schedule
(the schedule plays SU0's gauge role, position-only). -/
noncomputable def scheduleUltrametric (R : ℕ → ℝ) (hpos : ∀ n, 0 < R n)
    (hanti : ∀ {m n : ℕ}, m ≤ n → R n ≤ R m) : AbstractUltrametric where
  digitSets _ := Fin 2
  digitSets_finite _ := inferInstance
  dist x y := if x = y then 0 else R (lcpLenD x y)
  dist_nonneg x y := by
    by_cases h : x = y
    · rw [if_pos h]
    · rw [if_neg h]
      exact (hpos _).le
  dist_eq_zero_iff x y := by
    by_cases h : x = y
    · rw [if_pos h]
      simp [h]
    · rw [if_neg h]
      constructor
      · intro h0
        exact absurd h0 (ne_of_gt (hpos _))
      · intro he
        exact absurd he h
  dist_symm x y := by
    by_cases h : x = y
    · rw [if_pos h, if_pos h.symm]
    · have h' : y ≠ x := fun e => h e.symm
      rw [if_neg h, if_neg h', lcpLenD_comm]
  dist_ultrametric x y z := by
    by_cases hxz : x = z
    · subst hxz
      rw [if_pos rfl]
      apply le_max_of_le_left
      by_cases hxy : x = y
      · rw [if_pos hxy]
      · rw [if_neg hxy]
        exact (hpos _).le
    · rw [if_neg hxz]
      by_cases hxy : x = y
      · subst hxy
        rw [if_neg hxz]
        exact le_max_right _ _
      · by_cases hyz : y = z
        · subst hyz
          rw [if_neg hxy]
          exact le_max_left _ _
        · rw [if_neg hxy, if_neg hyz]
          have hmin := min_lcpLenD_le (x := x) (y := y) (z := z) hxz
          have hR : R (lcpLenD x z) ≤ R (min (lcpLenD x y) (lcpLenD y z)) :=
            hanti hmin
          rcases le_total (lcpLenD x y) (lcpLenD y z) with hab | hba
          · rw [min_eq_left hab] at hR
            exact le_max_of_le_left hR
          · rw [min_eq_right hba] at hR
            exact le_max_of_le_right hR

/-- The witness schedule: `R n = 1/(2n+1)` — positive, antitone, vanishing, and
NOT the canonical binary schedule. -/
noncomputable def witnessδ : AbstractUltrametric :=
  scheduleUltrametric (fun n => ((2 * n + 1 : ℕ) : ℝ)⁻¹)
    (fun n => by positivity)
    (fun {m n} h => by
      have h1 : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by positivity
      have h2 : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by positivity
      exact (inv_le_inv₀ h1 h2).mpr
        (by exact_mod_cast (by omega : (2 * m + 1 : ℕ) ≤ 2 * n + 1)))

theorem witnessδ_conditions : AbstractRealizabilityConditions witnessδ :=
  ⟨fun _ => by
    show 2 ≤ Nat.card (Fin 2)
    simp⟩

/-- The witness satisfies the corrected (C1) — hence also the original conditions
(1)–(3), which are weaker. -/
theorem witnessδ_ballsAreCylinders : BallsAreCylinders witnessδ := by
  apply ballsAreCylinders_of_schedule (fun n => ((2 * n + 1 : ℕ) : ℝ)⁻¹)
  · intro m n h
    have h1 : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by positivity
    have h2 : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by positivity
    exact (inv_le_inv₀ h1 h2).mpr
      (by exact_mod_cast (by omega : (2 * m + 1 : ℕ) ≤ 2 * n + 1))
  · intro r hr
    obtain ⟨M, hM⟩ := exists_nat_gt (1 / r)
    refine ⟨M, ?_⟩
    have h1 : (1 / r : ℝ) < ((2 * M + 1 : ℕ) : ℝ) := by
      calc (1 / r : ℝ) < M := hM
        _ ≤ ((2 * M + 1 : ℕ) : ℝ) := by exact_mod_cast by omega
    have hpos : (0 : ℝ) < ((2 * M + 1 : ℕ) : ℝ) := by positivity
    have h1r : (0 : ℝ) < 1 / r := by positivity
    have := (inv_lt_inv₀ hpos h1r).mpr h1
    rwa [one_div, inv_inv] at this
  · intro x y hxy
    show (if x = y then (0 : ℝ) else _) = _
    rw [if_neg hxy]

/-- **THE INSUFFICIENCY WITNESS (machine-checked).** `witnessδ` satisfies the
corrected (C1) — a fortiori the original conditions, which are weaker — but is NOT
SU-realizable: at first-difference depth 1 its distance is `1/3` while the canonical
binary value is `1/2`. The conditions pin the tree, not the gauge; condition (C4) is
genuinely necessary, and the original Theorem 43 statement required the erratum. -/
theorem conditions_insufficient :
    BallsAreCylinders witnessδ ∧ ¬ SURealizable witnessδ := by
  refine ⟨witnessδ_ballsAreCylinders, ?_⟩
  intro hreal
  -- the pair: the constant-0 stream and its update at position 1, typed at the
  -- witness's own digit sets (defeq `Fin 2`) so every lemma instantiates uniformly
  set x : ∀ i, witnessδ.digitSets i := fun _ => (0 : Fin 2) with hxdef
  set y : ∀ i, witnessδ.digitSets i := Function.update x 1 (1 : Fin 2) with hydef
  have hxy : x ≠ y := by
    intro he
    have h1 := congrFun he 1
    rw [hydef, Function.update_self] at h1
    have h2 : (0 : Fin 2) = 1 := h1
    exact absurd h2 (by decide)
  have hlcp : lcpLenD x y = 1 := by
    rw [lcpLenD_eq_iff hxy]
    constructor
    · intro i hi
      have hi0 : i = 0 := by omega
      subst hi0
      rw [hydef, Function.update_of_ne (by norm_num)]
    · rw [hydef, Function.update_self]
      intro he
      have h2 : (0 : Fin 2) = 1 := he
      exact absurd h2 (by decide)
  have hdist : witnessδ.dist x y = ((3 : ℕ) : ℝ)⁻¹ := by
    show (if x = y then (0 : ℝ) else ((2 * lcpLenD x y + 1 : ℕ) : ℝ)⁻¹) = _
    rw [if_neg hxy, hlcp]
  have hcanon : canonicalRadius witnessδ 1 = (2 : ℝ)⁻¹ := by
    rw [canonicalRadius, Finset.prod_range_one]
    norm_num [witnessδ, scheduleUltrametric, Nat.card_eq_fintype_card]
  have hkey := hreal x y hxy
  rw [hdist, hlcp, hcanon] at hkey
  norm_num at hkey

end FdrsFormal.Modes.VariableRadix
