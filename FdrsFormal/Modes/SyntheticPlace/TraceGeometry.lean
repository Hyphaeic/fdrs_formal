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

# Synthetic place complex SU5.0/SU5.1 — trace geometry: projections and the scalar no-go

The network half of the SPS keystone (`docs/synthetic-place/02-phase14-design.md`
§4). A network history is not a word but a **Mazurkiewicz trace**: a schedule modulo
adjacent swaps of events at different places (`TraceEquiv` — the independence
relation here is the canonical place-disjointness one; general independence alphabets
are classical theory we cite, not rebuild).

* **SU5.1 — projections are schedule-invariant** (`proj_traceEquiv`,
  `proj_tuple_eq`): each place's linear history is blind to the interleaving of other
  places' events. This is the one real lemma of the network geometry: everything
  built on the projection tuple — metrics, observables, certificates — is
  automatically schedule-invariant.
* **SU5.0 — THE SCALAR NO-GO** (`scalar_trace_metric_no_go`, machine-checked): there
  is NO distance on schedules that simultaneously (i) satisfies the triangle
  inequality, (ii) calls two runs `(g u)⁻¹`-close whenever they share the common
  trace-prefix `u` — with a gauge unbounded along each of two places' own lines —
  and (iii) keeps root-divergent pure runs uniformly separated. Witness: `x = a^n`,
  `y = a^n ++ b^m`, `z = b^m`; the block-commute `b^m ++ a^n ~ a^n ++ b^m` makes
  both `a^n` and `b^m` trace-prefixes of `y`, so `δ(x,y), δ(y,z) → 0` while
  `δ(x,z) ≥ ε`. Depth earned at one place masks blindness at another; a single
  scalar cannot price both. **The formal statement is stronger than the design-note
  sketch**: no positivity or swap-invariance of the gauge is assumed — the gauge
  enters only as the closeness rate, and even the ordinary (not just strong)
  triangle inequality is refuted.

Consequence (built in `NetworkGauge.lean`): the network geometry must be
observer-indexed — per-place gauges glued by sup — not scalar. The §1 thesis's third
instance: geometry survives by becoming indexed and glued.

**Honest scope.** The no-go rules out the stated premise class (triangle +
trace-prefix closeness + uniform root separation), not every conceivable scalar
function; this is exactly the class containing all meet-reciprocal first-disagreement
metrics. Trace theory background (commutation, projections) is classical
(Mazurkiewicz); the corpus contributes the FDRS-shaped statements and the verified
artifact. Leaf module over SU0. No `sorry`; axiom-clean.
-/
import FdrsFormal.Modes.SyntheticPlace.GaugeUltrametric

namespace FdrsFormal.Modes.SyntheticPlace

variable {V : Type*} [DecidableEq V] {D : Type*}

/-! ## 1. Trace equivalence (schedules modulo independent swaps) -/

/-- **Mazurkiewicz trace equivalence** for the place-disjointness independence:
schedules are identified up to adjacent swaps of events at *different* places. -/
inductive TraceEquiv : List (V × D) → List (V × D) → Prop
  | refl (w : List (V × D)) : TraceEquiv w w
  | swap (s t : List (V × D)) (e₁ e₂ : V × D) (h : e₁.1 ≠ e₂.1) :
      TraceEquiv (s ++ e₁ :: e₂ :: t) (s ++ e₂ :: e₁ :: t)
  | trans {w₁ w₂ w₃ : List (V × D)} :
      TraceEquiv w₁ w₂ → TraceEquiv w₂ w₃ → TraceEquiv w₁ w₃

namespace TraceEquiv

theorem symm {w w' : List (V × D)} (h : TraceEquiv w w') : TraceEquiv w' w := by
  induction h with
  | refl w => exact .refl w
  | swap s t e₁ e₂ h => exact .swap s t e₂ e₁ (fun he => h he.symm)
  | trans _ _ ih₁ ih₂ => exact .trans ih₂ ih₁

theorem cons_congr (e : V × D) {w w' : List (V × D)} (h : TraceEquiv w w') :
    TraceEquiv (e :: w) (e :: w') := by
  induction h with
  | refl w => exact .refl _
  | swap s t e₁ e₂ hne =>
    have hs := TraceEquiv.swap (e :: s) t e₁ e₂ hne
    simpa using hs
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem append_left_congr (r : List (V × D)) {w w' : List (V × D)}
    (h : TraceEquiv w w') : TraceEquiv (r ++ w) (r ++ w') := by
  induction r with
  | nil => simpa using h
  | cons e r ih => exact cons_congr e ih

theorem append_right_congr (t : List (V × D)) {w w' : List (V × D)}
    (h : TraceEquiv w w') : TraceEquiv (w ++ t) (w' ++ t) := by
  induction h with
  | refl w => exact .refl _
  | swap s u e₁ e₂ hne =>
    have hs := TraceEquiv.swap s (u ++ t) e₁ e₂ hne
    simpa [List.append_assoc] using hs
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-- An event independent of every event of `w` commutes past all of it. -/
theorem cons_to_append (e : V × D) (w : List (V × D))
    (h : ∀ f ∈ w, e.1 ≠ f.1) : TraceEquiv (e :: w) (w ++ [e]) := by
  induction w with
  | nil => exact .refl _
  | cons f w ih =>
    have h1 : TraceEquiv (e :: f :: w) (f :: e :: w) := by
      have hs := TraceEquiv.swap [] w e f (h f (List.mem_cons_self ..))
      simpa using hs
    have h2 : TraceEquiv (f :: e :: w) (f :: (w ++ [e])) :=
      cons_congr f (ih (fun g hg => h g (List.mem_cons_of_mem f hg)))
    exact .trans h1 h2

/-- **The block commute**: two blocks of pairwise-independent events commute — the
trace-level fact behind "concurrent histories have no canonical interleaving". -/
theorem append_comm_of_indep (u w : List (V × D))
    (h : ∀ e ∈ u, ∀ f ∈ w, e.1 ≠ f.1) : TraceEquiv (u ++ w) (w ++ u) := by
  induction u with
  | nil => simpa using TraceEquiv.refl w
  | cons e u ih =>
    have h1 : TraceEquiv (e :: (u ++ w)) (e :: (w ++ u)) :=
      cons_congr e (ih (fun e' he' f hf => h e' (List.mem_cons_of_mem e he') f hf))
    have h2 : TraceEquiv (e :: w) (w ++ [e]) :=
      cons_to_append e w (fun f hf => h e (List.mem_cons_self ..) f hf)
    have h3 : TraceEquiv ((e :: w) ++ u) ((w ++ [e]) ++ u) :=
      append_right_congr u h2
    have h4 : TraceEquiv (e :: (w ++ u)) (w ++ e :: u) := by
      simpa [List.append_assoc] using h3
    exact .trans h1 h4

end TraceEquiv

/-! ## 2. Per-place projections, and their schedule-invariance (SU5.1) -/

/-- The projection of a schedule to one place: that place's digits, in order — the
observer's own linear history. -/
def proj (v : V) (w : List (V × D)) : List D :=
  (w.filter (fun e => e.1 = v)).map Prod.snd

@[simp] theorem proj_nil (v : V) : proj v ([] : List (V × D)) = [] := rfl

theorem proj_append (v : V) (w₁ w₂ : List (V × D)) :
    proj v (w₁ ++ w₂) = proj v w₁ ++ proj v w₂ := by
  simp [proj, List.filter_append]

theorem proj_cons (v : V) (e : V × D) (w : List (V × D)) :
    proj v (e :: w) = if e.1 = v then e.2 :: proj v w else proj v w := by
  simp only [proj, List.filter_cons]
  split <;> simp_all

/-- **SU5.1 — PROJECTIONS ARE SCHEDULE-INVARIANT.** Trace-equivalent schedules have
identical per-place projections: each observer is blind to the interleaving of the
other places' events. The lemma every network-level object rides on. -/
theorem proj_traceEquiv (v : V) {w w' : List (V × D)} (h : TraceEquiv w w') :
    proj v w = proj v w' := by
  induction h with
  | refl w => rfl
  | swap s t e₁ e₂ hne =>
    simp only [proj_append, proj_cons]
    by_cases h₁ : e₁.1 = v <;> by_cases h₂ : e₂.1 = v
    · exact absurd (h₁.trans h₂.symm) hne
    all_goals simp [h₁, h₂]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The full observation tuple is a trace invariant — hence so is anything built on
it (metrics, observables, certificates). -/
theorem proj_tuple_eq {w w' : List (V × D)} (h : TraceEquiv w w') :
    (fun v => proj v w) = (fun v => proj v w') :=
  funext fun v => proj_traceEquiv v h

/-! ## 3. Trace prefixes and pure words -/

/-- `u` is a trace-prefix of `w`: some completion of `u` is trace-equivalent to `w`. -/
def IsTracePrefix (u w : List (V × D)) : Prop := ∃ t, TraceEquiv (u ++ t) w

theorem isTracePrefix_self (w : List (V × D)) : IsTracePrefix w w :=
  ⟨[], by simpa using TraceEquiv.refl w⟩

theorem isTracePrefix_append (u t : List (V × D)) : IsTracePrefix u (u ++ t) :=
  ⟨t, TraceEquiv.refl _⟩

/-- `n` consecutive events of one place. -/
def pureWord (v : V) (d : D) (n : ℕ) : List (V × D) := List.replicate n (v, d)

/-- The right block of a two-place concatenation is a trace-prefix: pure blocks at
different places commute (`append_comm_of_indep`). This is precisely what a linear
prefix order cannot see. -/
theorem isTracePrefix_pure_right {v v' : V} (hvv : v' ≠ v) (d d' : D) (n m : ℕ) :
    IsTracePrefix (pureWord v' d' m) (pureWord v d n ++ pureWord v' d' m) := by
  refine ⟨pureWord v d n, ?_⟩
  apply TraceEquiv.append_comm_of_indep
  intro e he f hf
  simp only [pureWord] at he hf
  have he' := List.eq_of_mem_replicate he
  have hf' := List.eq_of_mem_replicate hf
  subst he'
  subst hf'
  exact hvv

/-! ## 4. SU5.0 — the scalar trace-gauge no-go -/

/-- **SU5.0 — THE SCALAR NO-GO (machine-checked).** No distance on schedules can
simultaneously:

* (`htri`) satisfy the triangle inequality (even the ordinary one);
* (`hclose`) call two schedules `(g u)⁻¹`-close whenever `u` is a common
  trace-prefix of both — for ANY gauge `g` unbounded along each of two places' own
  pure lines (`hg₁`, `hg₂`; no positivity, no swap-invariance assumed);
* (`hsep`) keep the root-divergent pure runs `a^n`, `b^m` uniformly separated.

Witness: `y = a^n ++ b^m` has BOTH `a^n` and `b^m` as trace-prefixes (the block
commute), so `δ(a^n, y) < ε/2` and `δ(y, b^m) < ε/2` for deep enough blocks, while
`δ(a^n, b^m) ≥ ε`. Depth earned at one place masks total blindness at another: **a
scalar refinement metric cannot price concurrency** — the network geometry must be
observer-indexed (`NetworkGauge.lean`). -/
theorem scalar_trace_metric_no_go
    {v₁ v₂ : V} (hv : v₁ ≠ v₂) (d : D)
    (g : List (V × D) → ℕ)
    (hg₁ : ∀ M : ℕ, ∃ n, M ≤ g (pureWord v₁ d n))
    (hg₂ : ∀ M : ℕ, ∃ m, M ≤ g (pureWord v₂ d m))
    (δ : List (V × D) → List (V × D) → ℝ)
    (htri : ∀ w₁ w₂ w₃, δ w₁ w₃ ≤ δ w₁ w₂ + δ w₂ w₃)
    (hclose : ∀ u w w', IsTracePrefix u w → IsTracePrefix u w' →
      δ w w' ≤ ((g u : ℝ))⁻¹)
    (hsep : ∃ ε : ℝ, 0 < ε ∧ ∀ n m, ε ≤ δ (pureWord v₁ d n) (pureWord v₂ d m)) :
    False := by
  obtain ⟨ε, hε, hsep⟩ := hsep
  obtain ⟨M, hM⟩ := exists_nat_gt (2 / ε)
  obtain ⟨n, hn⟩ := hg₁ M
  obtain ⟨m, hm⟩ := hg₂ M
  -- the bridge run: deep at place 1, then deep at place 2
  set y : List (V × D) := pureWord v₁ d n ++ pureWord v₂ d m with hy
  -- inverse-gauge bound: 2/ε < k ⟹ k⁻¹ < ε/2
  have key : ∀ k : ℕ, 2 / ε < (k : ℝ) → ((k : ℝ))⁻¹ < ε / 2 := by
    intro k hk
    have h2ε : (0 : ℝ) < 2 / ε := div_pos two_pos hε
    have hkpos : (0 : ℝ) < (k : ℝ) := lt_trans h2ε hk
    have hinv := (inv_lt_inv₀ hkpos h2ε).mpr hk
    rwa [inv_div] at hinv
  -- x = a^n and y share the trace-prefix a^n
  have h1 : δ (pureWord v₁ d n) y ≤ ((g (pureWord v₁ d n) : ℝ))⁻¹ :=
    hclose _ _ _ (isTracePrefix_self _) (isTracePrefix_append _ _)
  -- y and z = b^m share the trace-prefix b^m — by the BLOCK COMMUTE
  have h2 : δ y (pureWord v₂ d m) ≤ ((g (pureWord v₂ d m) : ℝ))⁻¹ :=
    hclose _ _ _ (isTracePrefix_pure_right (Ne.symm hv) d d n m)
      (isTracePrefix_self _)
  have hb₁ : ((g (pureWord v₁ d n) : ℝ))⁻¹ < ε / 2 :=
    key _ (lt_of_lt_of_le hM (by exact_mod_cast hn))
  have hb₂ : ((g (pureWord v₂ d m) : ℝ))⁻¹ < ε / 2 :=
    key _ (lt_of_lt_of_le hM (by exact_mod_cast hm))
  have hcontra : δ (pureWord v₁ d n) (pureWord v₂ d m) < ε := by
    calc δ (pureWord v₁ d n) (pureWord v₂ d m)
        ≤ δ (pureWord v₁ d n) y + δ y (pureWord v₂ d m) := htri _ _ _
      _ < ε / 2 + ε / 2 :=
          add_lt_add (lt_of_le_of_lt h1 hb₁) (lt_of_le_of_lt h2 hb₂)
      _ = ε := by ring
  exact absurd (hsep n m) (not_le.mpr hcontra)

-- sanity demo: the block commute makes the RIGHT block a trace-prefix —
-- exactly what a linear prefix order cannot see
example : IsTracePrefix (pureWord (1 : Fin 2) (0 : Fin 1) 2)
    (pureWord (0 : Fin 2) (0 : Fin 1) 3 ++ pureWord 1 0 2) :=
  isTracePrefix_pure_right (by decide) _ _ _ _

end FdrsFormal.Modes.SyntheticPlace
