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

# Subshift / transfer-matrix prefix weights (the constrained-alphabet gauge)

`subshiftWeight` generalizes `prefixWeight` (the free-product, per-path place
value `β_ω`) to a **per-path transfer-product** over a `d`-state alphabet
constraint — with no `Matrix` type-class, just a `Finset` contraction of a
carried state-vector.

The free product is the special case `d = 1`, where this recovers `prefixWeight`
**exactly** (`subshiftWeight_free_eq_prefixWeight`). This is the *defensive
perimeter*: every existing result that runs on `prefixWeight` — `InducedUltrametric`,
`ball_is_cylinder`, the Group-G `blockProjection` convergence — is the `d = 1`
instance and is therefore untouched by this generalization.

A constant `d ≥ 2` transition gives the continued-fraction / Ostrowski gauge:
the admissible-configuration count grows at the subshift's Perron eigenvalue
(e.g. `φ` for the golden-mean shift), even where the literal product of bases
would stagnate on base-1 "wires".

This file imports only `PrefixWeights.Definition`; it adds **no** dependency on
the topology layer and is not (yet) wired into any aggregator.
-/
import FdrsFormal.Modes.VariableRadix.PrefixWeights.Definition
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Basic

namespace FdrsFormal.Modes.VariableRadix

open Finset

variable {d : ℕ}

/-- One transfer step: contract the carried state-vector `v` with the local
transition weights `T`. Plain `Finset` sum — no `Matrix` type-class. -/
def stepVec (T : Fin d → Fin d → ℕ) (v : Fin d → ℕ) : Fin d → ℕ :=
  fun j => ∑ i, T j i * v i

/-- Accumulated state-vector after reading `s`. Mirrors `prefixWeight`'s
head-shift recursion: apply the root transition `M []`, then recurse on the
shifted transition `fun s => M (c :: s)`. -/
def weightVec (M : PrefixWord → Fin d → Fin d → ℕ) (start : Fin d → ℕ) :
    PrefixWord → (Fin d → ℕ)
  | [] => start
  | c :: ds => weightVec (fun s => M (c :: s)) (stepVec (M []) start) ds

/-- The scalar gauge: contract the accumulated state-vector with the boundary
vector `fin`. (`M` = prefix-indexed transition; `start`/`fin` = boundaries.) -/
def subshiftWeight (M : PrefixWord → Fin d → Fin d → ℕ) (start fin : Fin d → ℕ)
    (s : PrefixWord) : ℕ :=
  ∑ j, fin j * weightVec M start s j

/-- The free / complete transition (`d = 1`): the local weight is just the
radix at the current prefix. This is the unconstrained special case. -/
def freeTransition (ω : RadixLaw) : PrefixWord → Fin 1 → Fin 1 → ℕ :=
  fun s _ _ => ω.radix s

/-- **Key lemma (linearity of the free `d = 1` fold).**
Carrying a constant start `x` through the free transition yields `x · β_ω(s)`. -/
theorem weightVec_free_const (ω : RadixLaw) (x : ℕ) (s : PrefixWord) :
    weightVec (freeTransition ω) (fun _ => x) s = fun _ => x * prefixWeight ω s := by
  induction s generalizing ω x with
  | nil =>
    funext j
    simp [weightVec, prefixWeight_nil]
  | cons c ds ih =>
    have hstep : stepVec (freeTransition ω []) (fun _ : Fin 1 => x)
        = fun _ => ω.radix [] * x := by
      funext k; simp [stepVec, freeTransition, Fin.sum_univ_one]
    have hshift : (fun s => freeTransition ω (c :: s)) = freeTransition (ω.shift c) := by
      funext s a b; simp [freeTransition, RadixLaw.shift]
    have hpw : prefixWeight ω (c :: ds) = ω.radix [] * prefixWeight (ω.shift c) ds := rfl
    funext j
    show weightVec (fun s => freeTransition ω (c :: s))
          (stepVec (freeTransition ω []) (fun _ => x)) ds j
        = x * prefixWeight ω (c :: ds)
    rw [hstep, hshift, ih (ω.shift c) (ω.radix [] * x)]
    show (ω.radix [] * x) * prefixWeight (ω.shift c) ds = x * prefixWeight ω (c :: ds)
    rw [hpw]; ring

/-- **THEOREM (defensive perimeter).**
The subshift gauge over the free (complete, `d = 1`) transition recovers the
existing `prefixWeight` exactly. Consequently `InducedUltrametric`,
`ball_is_cylinder`, and the Group-G convergence — all defined over
`prefixWeight` — are precisely the `d = 1` instance of `subshiftWeight` and are
protected unchanged as the generalization is built out. -/
theorem subshiftWeight_free_eq_prefixWeight (ω : RadixLaw) (s : PrefixWord) :
    subshiftWeight (freeTransition ω) (fun _ => 1) (fun _ => 1) s = prefixWeight ω s := by
  unfold subshiftWeight
  rw [weightVec_free_const ω 1 s]
  simp [Fin.sum_univ_one]

/-! ## Step 1 — the convergent ledger (the integer transition matrix `[[a,1],[1,0]]`)

`RemainderState` carries the last two continued-fraction convergents
`(pₖ₋₁, pₖ ; qₖ₋₁, qₖ)` — the SL₂(ℤ) transition-matrix state, i.e. the "ledger of
debt". `step a` applies one *discovered* partial quotient via the convergent
recurrence `xₖ₊₁ = a·xₖ + xₖ₋₁`. The denominator `qCur = qₖ` is the gauge that
drives `subshiftWeight` (Fibonacci for `[0;1,1,…]`, Pell for `[0;2,2,…]`): this one
object is both the debt-ledger and the gauge generator.

The defining invariant is the consecutive-convergent cross-determinant
`pₖ·qₖ₋₁ − pₖ₋₁·qₖ = ±1` — each `step` multiplies by a determinant-`(-1)` matrix, so
it is `±1` along every run, making the bracket gap exactly `1/(qₖ₋₁ qₖ)`. This is the
exact, *general* (any quotient sequence) form of the periodic `|Q| = 1` check
verified numerically in `explorations/phi_vs_sqrt2.py`.
-/

/-- The convergent-pair ledger `(pₖ₋₁, pₖ ; qₖ₋₁, qₖ)` — the SL₂(ℤ) state.

**fdrs.md**: Definition 181 (The convergent-pair ledger) [§13.2.3 · Phase 13] -/
structure RemainderState where
  hPrev : ℤ
  hCur : ℤ
  qPrev : ℤ
  qCur : ℤ

namespace RemainderState

/-- The current convergent denominator `qₖ` — the gauge fed to `subshiftWeight`
(Fibonacci for `[0;1,1,…]`, Pell for `[0;2,2,…]`). -/
def gauge (r : RemainderState) : ℤ := r.qCur

/-- The consecutive-convergent cross-determinant `pₖ·qₖ₋₁ − pₖ₋₁·qₖ`. -/
def det (r : RemainderState) : ℤ := r.hCur * r.qPrev - r.hPrev * r.qCur

/-- One discovered partial quotient `a`: the convergent recurrence
`xₖ₊₁ = a·xₖ + xₖ₋₁` (multiply the SL₂ state by `[[a,1],[1,0]]`). -/
def step (r : RemainderState) (a : ℕ) : RemainderState where
  hPrev := r.hCur
  hCur := (a : ℤ) * r.hCur + r.hPrev
  qPrev := r.qCur
  qCur := (a : ℤ) * r.qCur + r.qPrev

/-- Initial ledger for a fractional CF `[0; a₁, a₂, …]`:
`(h₋₁, h₀, q₋₁, q₀) = (1, 0, 0, 1)`. -/
def init : RemainderState := ⟨1, 0, 0, 1⟩

/-- Replay a sequence of discovered quotients. -/
def steps (r : RemainderState) (as : List ℕ) : RemainderState :=
  as.foldl step r

/-- **Each step flips the determinant's sign** (the `[[a,1],[1,0]]` factor has
determinant `-1`). Pure integer algebra. -/
@[simp] theorem det_step (r : RemainderState) (a : ℕ) : (r.step a).det = - r.det := by
  simp only [det, step]; ring

@[simp] theorem init_det : init.det = -1 := by simp [det, init]

/-- Determinant after replaying `as` from `r`: `(-1)^|as| · det r`. -/
theorem det_steps (r : RemainderState) (as : List ℕ) :
    (r.steps as).det = (-1) ^ as.length * r.det := by
  induction as generalizing r with
  | nil => simp [steps]
  | cons a as ih =>
    have key : r.steps (a :: as) = (r.step a).steps as := rfl
    rw [key, ih (r.step a), det_step, List.length_cons, pow_succ]
    ring

/-- **THE BRACKET INVARIANT** (exact, any discovered quotient sequence):
the consecutive-convergent cross-determinant is `±1`, i.e.
`|pₖ·qₖ₋₁ − pₖ₋₁·qₖ| = 1` — so the bracket gap is exactly `1/(qₖ₋₁ qₖ)`. -/
theorem bracket_invariant (as : List ℕ) : (init.steps as).det.natAbs = 1 := by
  rw [det_steps, init_det]
  simp [Int.natAbs_mul, Int.natAbs_pow]

/-! ### Gauge growth — the justification of the "wire"

For a continued fraction every partial quotient is `≥ 1`. Under that hypothesis the
denominator `qCur = qₖ` is a **positive** integer (safe as a metric denominator) and
**grows without bound** (`|as| + 1 ≤ 2·qₖ`) — *even for the all-1 sequence* (φ), where
the literal base product `β = ∏ radix` stagnates. This is the formal content of the
Option-B "wire": base-1 wires don't deepen `β`, but `qₖ₊₁ = a·qₖ + qₖ₋₁` (the `+ qₖ₋₁`
Fibonacci term) keeps `qₖ` growing, so the cylinders `1/qₖ` still shrink to a point. -/

/-- Combined invariant (CF quotients `≥ 1`): the convergent pair is non-negative and
ordered, `qₖ ≥ 1`, and the pair-sum grows at least linearly in the step count. -/
theorem steps_invariant {as : List ℕ} (h : ∀ a ∈ as, 1 ≤ a) :
    0 ≤ (init.steps as).qPrev
      ∧ (init.steps as).qPrev ≤ (init.steps as).qCur
      ∧ 1 ≤ (init.steps as).qCur
      ∧ (as.length : ℤ) + 1 ≤ (init.steps as).qPrev + (init.steps as).qCur := by
  revert h
  induction as using List.reverseRecOn with
  | nil => intro _; refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [steps, init]
  | append_singleton bs a ih =>
    intro h
    have ha : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast h a (by simp)
    have hbs : ∀ x ∈ bs, 1 ≤ x := fun x hx => h x (by simp [hx])
    obtain ⟨hp, hpc, hq, hsum⟩ := ih hbs
    have hqp : (0 : ℤ) ≤ (init.steps bs).qCur := le_trans hp hpc
    have hmul : (init.steps bs).qCur ≤ (a : ℤ) * (init.steps bs).qCur := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ha) hqp]
    have hstep : init.steps (bs ++ [a]) = (init.steps bs).step a := by
      simp only [steps, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hstep]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [step]; linarith
    · simp only [step]; linarith
    · simp only [step]; linarith
    · simp only [step, List.length_append, List.length_singleton]; push_cast; linarith

/-- **Positivity.** `qₖ > 0`: the generated denominator is a positive integer, so the
eventual metric denominator `(qₖ : ℝ)⁻¹` is well-defined and positive — no
zero-division, no negative distance. -/
theorem steps_qCur_pos {as : List ℕ} (h : ∀ a ∈ as, 1 ≤ a) :
    0 < (init.steps as).qCur := by
  have hq := (steps_invariant h).2.2.1; linarith

/-- **Gauge growth (`qₖ → ∞`).** `|as| + 1 ≤ 2·qₖ`: the denominator is unbounded in the
number of discovered quotients — *even for all-1 quotients (φ)*, where the base product
`β` stagnates. This is the algebraic lemma the topological `ball_is_cylinder` / Group-G
shrink (`1/qₖ → 0`) will call. -/
theorem steps_qCur_unbounded {as : List ℕ} (h : ∀ a ∈ as, 1 ≤ a) :
    (as.length : ℤ) + 1 ≤ 2 * (init.steps as).qCur := by
  obtain ⟨_, hpc, _, hsum⟩ := steps_invariant h
  linarith

/-- Gauge growth in usable form: the denominator eventually exceeds any bound `M`
(take depth `≥ 2M`). -/
theorem steps_qCur_ge (M : ℕ) :
    ∃ N : ℕ, ∀ as : List ℕ, (∀ a ∈ as, 1 ≤ a) → N ≤ as.length →
      (M : ℤ) ≤ (init.steps as).qCur := by
  refine ⟨2 * M, fun as h hlen => ?_⟩
  have hub := steps_qCur_unbounded h
  have hlen' : (2 * M : ℤ) ≤ (as.length : ℤ) := by exact_mod_cast hlen
  omega

/-- **Cylinder diameter → 0.** For every `ε > 0` there is a depth `N` beyond which the
gauge reciprocal `1/qₖ` (the cylinder radius) is `< ε`. This is the topological shrink
that `ball_is_cylinder` and the Group-G martingale convergence consume — and it holds for
*any* CF (φ included), where the base product `β` would never shrink. -/
theorem gauge_inv_lt (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ as : List ℕ, (∀ a ∈ as, 1 ≤ a) → N ≤ as.length →
      ((init.steps as).qCur : ℝ)⁻¹ < ε := by
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / ε)
  obtain ⟨N, hN⟩ := steps_qCur_ge M
  refine ⟨N, fun as h hlen => ?_⟩
  have hposq : (0 : ℝ) < ((init.steps as).qCur : ℝ) := by exact_mod_cast steps_qCur_pos h
  have hMq : (M : ℝ) ≤ ((init.steps as).qCur : ℝ) := by exact_mod_cast hN as h hlen
  have hq : 1 / ε < ((init.steps as).qCur : ℝ) := lt_of_lt_of_le hM hMq
  have h1 : (0 : ℝ) < 1 / ε := one_div_pos.mpr hε
  have hlt : ((init.steps as).qCur : ℝ)⁻¹ < (1 / ε)⁻¹ := (inv_lt_inv₀ hposq h1).mpr hq
  rwa [one_div, inv_inv] at hlt

end RemainderState

end FdrsFormal.Modes.VariableRadix
