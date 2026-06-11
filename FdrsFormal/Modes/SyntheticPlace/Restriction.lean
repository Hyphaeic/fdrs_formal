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

# Synthetic place complex SU3 — zoom-out restriction (the gauge prices observability)

The fourth stone of the Synthetic Place System (`docs/synthetic-place/00-thesis.md`;
roadmap `01-build-roadmap.md` §SU3). The thesis calls the ultrametric basis a
*representation-constraint generator*; this file proves the constraint in
gauge-general, **decode-free** form — no rank chart, no odometer, no `dec`/`enc`
anywhere (thesis §1 correction 2), so the results hold in the ragged regime of SU1
where the corpus's transport machinery is unavailable by design.

* **`decided_separation` / `separation_cost`** — *indistinguishability below the
  gauge*: an observable decided at depth `n` cannot separate points closer than
  `(gaugeAt G x n)⁻¹`; equivalently, separating two points by a depth-`n` observable
  costs at least the depth-`n` gauge reciprocal in distance. This is Theorem 44's
  Lipschitz bound (`Lip = max β_ω`) generalized from product gauges to every
  `PrefixGauge` — including the coupled gauges of SU1.
* **`decidedAt_mono` / `decidedAt_strict`** — the depth hierarchy of decidable
  observables is monotone and, at every genuine branch, **strict**: an explicit
  cylinder-indicator is decided at depth `n+1` but not at `n` (Prop 133's
  strict-hierarchy shape, gauge-general; `decidedAt_strict_base` instantiates the
  witness concretely).

**Honest scope.** The SU-regime modulus-by-depth — residue observables decided on
cylinders exactly when `q ∣ β_ω(s)` — **already exists** (Theorem 38 / Corollary 27,
`Integration/ThreeLineMediator/CoupledSystem.lean`) and is cited, not rebuilt: it
needs the decode that the ragged regime lacks. No measure-theoretic ceiling here
(Theorem 66's Fourier ceiling stays in `Analysis/DigitConditional/`); no claim that
`DecidedAt` exhausts "observables" — it is the cylinder-decided class, exactly what
the refinement geometry governs. Leaf module. No `sorry`; axiom-clean.
-/
import FdrsFormal.Modes.SyntheticPlace.GaugeUltrametric

namespace FdrsFormal.Modes.SyntheticPlace

variable {D : Type*} [DecidableEq D] {V : Type*}

/-! ## 1. Depth-decided observables -/

/-- An observable is **decided at depth `n`** when it is constant on every depth-`n`
cylinder: it factors through the first `n` emitted digits. This is the decode-free
notion of "computable from the zoom-out level `n`". -/
def DecidedAt (f : (ℕ → D) → V) (n : ℕ) : Prop :=
  ∀ x y : ℕ → D, pre x n = pre y n → f x = f y

/-- Deciding earlier is deciding later: the hierarchy is monotone in depth. -/
theorem decidedAt_mono {f : (ℕ → D) → V} {n : ℕ} (h : DecidedAt f n) :
    DecidedAt f (n + 1) := by
  intro x y hpre
  apply h
  simp only [pre]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  exact agree_of_pre_eq hpre (Nat.lt_succ_of_lt hi)

/-! ## 2. SU3 — indistinguishability below the gauge -/

/-- **SU3 — THE RESTRICTION THEOREM.** A depth-`n` observable cannot separate points
closer than the depth-`n` gauge reciprocal: below the gauge's resolution, all
depth-`n` views coincide. Decode-free, so it governs the ragged regime too — the
designed basis *restricts what any zoom-out level can represent* (thesis §1). -/
theorem decided_separation (G : PrefixGauge D) {x : ℕ → D}
    (hx : AdmissiblePoint G x) {f : (ℕ → D) → V} {n : ℕ} (hf : DecidedAt f n)
    {y : ℕ → D} (hclose : gaugeDist G x y < ((gaugeAt G x n : ℝ))⁻¹) : f x = f y := by
  by_cases h : ∃ i, x i ≠ y i
  · rw [gaugeDist_of_ne G h] at hclose
    have hlcp_pos : (0 : ℝ) < (G.gauge (pre x (lcpLen x y)) : ℝ) := by
      exact_mod_cast G.pos _ (hx _)
    have hn_pos : (0 : ℝ) < ((gaugeAt G x n : ℕ) : ℝ) := by
      exact_mod_cast gaugeAt_pos G hx n
    have hgauge : ((gaugeAt G x n : ℕ) : ℝ) < (G.gauge (pre x (lcpLen x y)) : ℝ) :=
      (inv_lt_inv₀ hlcp_pos hn_pos).mp hclose
    have hle : n ≤ lcpLen x y := by
      by_contra hlt
      push_neg at hlt
      have hmono : gaugeAt G x (lcpLen x y) ≤ gaugeAt G x n :=
        gaugeAt_monotone G hx (le_of_lt hlt)
      exact absurd hgauge (not_lt.mpr (by exact_mod_cast hmono))
    exact hf x y (pre_eq_of_le_lcp h hle)
  · rw [eq_of_not_exists_ne h]

/-- **The separation cost** (contrapositive form): distinguishing two points by a
depth-`n` observable costs at least `(gaugeAt G x n)⁻¹` in gauge distance — *the
gauge prices observability*. Theorem 44's bound, gauge-general and decode-free. -/
theorem separation_cost (G : PrefixGauge D) {x : ℕ → D}
    (hx : AdmissiblePoint G x) {f : (ℕ → D) → V} {n : ℕ} (hf : DecidedAt f n)
    {y : ℕ → D} (hsep : f x ≠ f y) :
    ((gaugeAt G x n : ℝ))⁻¹ ≤ gaugeDist G x y := by
  by_contra hlt
  push_neg at hlt
  exact hsep (decided_separation G hx hf hlt)

/-! ## 3. The hierarchy is strict at every branch -/

/-- **Strictness of the depth hierarchy.** Wherever the substrate genuinely branches
at depth `n` (two points agreeing to `n`, differing at `n`), the cylinder indicator of
the deeper prefix is decided at `n+1` but NOT at `n`: each zoom-in level can represent
strictly more (Prop 133's shape, gauge-general). The branch witnesses are instance
data — admissibility structures with a forced unique continuation everywhere have no
branch and no strictness, exactly as they should. -/
theorem decidedAt_strict {x y : ℕ → D} {n : ℕ}
    (hagree : pre x n = pre y n) (hdiff : x n ≠ y n) :
    ∃ f : (ℕ → D) → Bool, DecidedAt f (n + 1) ∧ ¬ DecidedAt f n := by
  classical
  refine ⟨fun z => decide (pre z (n + 1) = pre x (n + 1)), ?_, ?_⟩
  · intro a b hab
    simp only [hab]
  · intro hcon
    have hfx : decide (pre x (n + 1) = pre x (n + 1)) = true := by simp
    have hfy : decide (pre y (n + 1) = pre x (n + 1)) = false := by
      simp only [decide_eq_false_iff_not]
      intro heq
      exact hdiff ((agree_of_pre_eq heq (Nat.lt_succ_self n)).symm)
    have hcontra := hcon x y hagree
    simp only [hfx, hfy] at hcontra
    exact absurd hcontra (by simp)

/-- The strictness witness, concretely instantiated at the root (depth `0 → 1`,
digits `0` vs `1`): there is an observable decided after one emission that no
zero-emission observable matches. -/
theorem decidedAt_strict_base :
    ∃ f : (ℕ → ℕ) → Bool, DecidedAt f 1 ∧ ¬ DecidedAt f 0 :=
  decidedAt_strict (x := fun _ => 0) (y := fun i => if i = 0 then 1 else 0) (n := 0)
    (by simp) (by simp)

end FdrsFormal.Modes.SyntheticPlace
