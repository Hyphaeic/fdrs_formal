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

# Synthetic place complex SU5.2–SU5.4 — the observer-glued network ultrametric

The constructive half of the network keystone
(`docs/synthetic-place/02-phase14-design.md` §4). SU5.0 proved no scalar trace gauge
can support a refinement metric on networks; this file builds what the failure
forces: the gauge **indexed by observer** and glued by sup. A network point is its
tuple of per-place streams (the observed content of a configuration — by SU5.1 the
tuple is schedule-invariant, so this layer never sees the interleaving), each place
carries its own SU0 `PrefixGauge`, and

> `netDist x y = sup over places v of gaugeDist_v (x v) (y v)`

*— you are only as close as your most-disagreeing observer.*

* **SU5.2 — the gluing**: `netDist` is a genuine ultrametric (`netDist_triangle` —
  a finite sup of ultrametrics is an ultrametric), with identity of indiscernibles
  on admissible tuples, and `netBall_eq_cylinder`: every ball is a **cylinder
  profile** — a per-place depth vector, the network refinement domain.
* **SU0 reduction** (`netDist_unique`): one place ⇒ `netDist = gaugeDist` exactly.
* **SU5.3 — schedule-invariance** (`netObservable_traceEquiv`): anything built on the
  projection tuple — this metric included — is a trace invariant, by SU5.1.
* **SU5.4 — restriction transport** (`network_separation_cost`): a place-`v`
  observable decided at depth `n` cannot separate network points closer than
  `(gaugeAt_v n)⁻¹` — SU3's "the gauge prices observability", per observer: each
  place's information flows at its own gauge speed.

This is the third instance of the Phase 14 thesis: value, conservation, and now
geometry each survive the network regime by becoming **indexed and glued** (graded
observables / balance sheaf / gauge family).

**Honest scope.** Points here are per-place stream *tuples*; the bridge from infinite
network runs to total tuples needs a fairness hypothesis (every place steps
infinitely often) which is deliberately not formalized — finite schedules connect via
`proj` (SU5.1) and that is what schedule-invariance uses. "Gauge sheaf" remains
structural vocabulary (no sheaf axioms; design-note ledger item 1). No liveness, no
coupled confluence (open as documented). Metric values in `ℝ` (noncomputable; no
`#eval` demos, mirroring SU0/SU3). Leaf module over SU0/SU3/TraceGeometry. No
`sorry`; axiom-clean.
-/
import FdrsFormal.Modes.SyntheticPlace.TraceGeometry
import FdrsFormal.Modes.SyntheticPlace.Restriction

namespace FdrsFormal.Modes.SyntheticPlace

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
variable {D : Type*} [DecidableEq D]

/-! ## 1. The glued distance -/

/-- **The observer-glued network distance**: the sup over places of the per-place
gauge distances of the stream tuple. -/
noncomputable def netDist (G : V → PrefixGauge D) (x y : V → ℕ → D) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun v => gaugeDist (G v) (x v) (y v)

/-- Every observer's distance is dominated by the glued distance. -/
theorem gaugeDist_le_netDist (G : V → PrefixGauge D) (x y : V → ℕ → D) (v : V) :
    gaugeDist (G v) (x v) (y v) ≤ netDist G x y := by
  unfold netDist
  exact Finset.le_sup' (fun v => gaugeDist (G v) (x v) (y v)) (Finset.mem_univ v)

theorem netDist_le (G : V → PrefixGauge D) {x y : V → ℕ → D} {a : ℝ}
    (h : ∀ v, gaugeDist (G v) (x v) (y v) ≤ a) : netDist G x y ≤ a :=
  Finset.sup'_le _ _ (fun v _ => h v)

/-- A network point is admissible when every place's stream is. -/
def NetAdmissible (G : V → PrefixGauge D) (x : V → ℕ → D) : Prop :=
  ∀ v, AdmissiblePoint (G v) (x v)

/-! ## 2. SU5.2 — metric laws by gluing -/

theorem netDist_self (G : V → PrefixGauge D) (x : V → ℕ → D) : netDist G x x = 0 := by
  apply le_antisymm
  · exact netDist_le G (fun v => le_of_eq (gaugeDist_self _ _))
  · have h := gaugeDist_le_netDist G x x (Classical.arbitrary V)
    rwa [gaugeDist_self] at h

theorem netDist_comm (G : V → PrefixGauge D) (x y : V → ℕ → D) :
    netDist G x y = netDist G y x := by
  apply le_antisymm <;>
    exact netDist_le G (fun v =>
      le_of_le_of_eq (le_of_eq (gaugeDist_comm _ _ _)) (rfl) |>.trans
        (gaugeDist_le_netDist G _ _ v))

theorem netDist_nonneg (G : V → PrefixGauge D) {x : V → ℕ → D}
    (hx : NetAdmissible G x) (y : V → ℕ → D) : 0 ≤ netDist G x y := by
  have v := Classical.arbitrary V
  exact le_trans (gaugeDist_nonneg (G v) (hx v) (y v)) (gaugeDist_le_netDist G x y v)

/-- Identity of indiscernibles: zero glued distance forces agreement at EVERY
observer. -/
theorem netDist_eq_zero_iff (G : V → PrefixGauge D) {x : V → ℕ → D}
    (hx : NetAdmissible G x) (y : V → ℕ → D) : netDist G x y = 0 ↔ x = y := by
  constructor
  · intro h
    funext v
    have h1 : gaugeDist (G v) (x v) (y v) ≤ 0 := h ▸ gaugeDist_le_netDist G x y v
    have h2 := gaugeDist_nonneg (G v) (hx v) (y v)
    exact (gaugeDist_eq_zero_iff (G v) (hx v) (y v)).mp (le_antisymm h1 h2)
  · rintro rfl
    exact netDist_self G x

/-- **SU5.2 — THE GLUED ULTRAMETRIC (strong triangle).** A finite sup of ultrametrics
is an ultrametric: the network refinement geometry exists for ANY family of place
gauges — the geometry the scalar no-go (SU5.0) said must be indexed. *You are only
as close as your most-disagreeing observer.* -/
theorem netDist_triangle (G : V → PrefixGauge D) {x : V → ℕ → D}
    (hx : NetAdmissible G x) (y z : V → ℕ → D) :
    netDist G x z ≤ max (netDist G x y) (netDist G y z) := by
  apply netDist_le
  intro v
  calc gaugeDist (G v) (x v) (z v)
      ≤ max (gaugeDist (G v) (x v) (y v)) (gaugeDist (G v) (y v) (z v)) :=
        gaugeDist_triangle (G v) (hx v) (y v) (z v)
    _ ≤ max (netDist G x y) (netDist G y z) :=
        max_le_max (gaugeDist_le_netDist G x y v) (gaugeDist_le_netDist G y z v)

/-- **SU0 reduction**: with a single place, the network distance IS the SU0 distance —
the sequential theory is the one-observer case of the network theory. -/
theorem netDist_unique [Unique V] (G : V → PrefixGauge D) (x y : V → ℕ → D) :
    netDist G x y = gaugeDist (G default) (x default) (y default) := by
  apply le_antisymm
  · exact netDist_le G (fun v => by rw [Unique.eq_default v])
  · exact gaugeDist_le_netDist G x y default

/-- **Balls are cylinder profiles.** With per-place unbounded gauges, every glued
ball about an admissible point is exactly a conjunction of per-place cylinders — a
DEPTH VECTOR, the network's refinement domain (the metric face of the per-edge
indexing that conservation forced in SU4). -/
theorem netBall_eq_cylinder (G : V → PrefixGauge D) {x : V → ℕ → D}
    (hx : NetAdmissible G x) (hu : ∀ v, GaugeUnbounded (G v) (x v))
    (r : ℝ) (hr : 0 < r) :
    ∃ n : V → ℕ, {y : V → ℕ → D | netDist G x y < r}
      = {y | ∀ v, pre (y v) (n v) = pre (x v) (n v)} := by
  have h := fun v => ball_eq_cylinder (G v) (hx v) (hu v) r hr
  choose n hn using h
  refine ⟨n, ?_⟩
  ext y
  simp only [Set.mem_setOf_eq]
  rw [netDist, Finset.sup'_lt_iff]
  constructor
  · intro h v
    exact (Set.ext_iff.mp (hn v) (y v)).mp (h v (Finset.mem_univ v))
  · intro h v _
    exact (Set.ext_iff.mp (hn v) (y v)).mpr (h v)

/-! ## 3. SU5.3 — schedule invariance of everything built on observations -/

/-- **SU5.3 — schedule invariance.** Any network observable computed from the
projection tuple — the glued metric on finite observations included — takes equal
values on trace-equivalent schedules. Direct corollary of SU5.1. -/
theorem netObservable_traceEquiv {α : Type*} (F : (V → List D) → α)
    {w w' : List (V × D)} (h : TraceEquiv w w') :
    F (fun v => proj v w) = F (fun v => proj v w') := by
  rw [proj_tuple_eq h]

/-! ## 4. SU5.4 — restriction transported to the network -/

/-- An observable of the network decided by place `v`'s first `n` digits alone. -/
def DecidedAtPlace {α : Type*} (f : (V → ℕ → D) → α) (v : V) (n : ℕ) : Prop :=
  ∀ x y : V → ℕ → D, pre (x v) n = pre (y v) n → f x = f y

/-- **SU5.4 — NETWORK SEPARATION COST.** A place-`v` observable decided at depth `n`
cannot separate network points closer than `(gaugeAt_v n)⁻¹`: each observer's
information flows at its own gauge speed, and the glued distance dominates every
observer's. SU3's restriction theorem, transported through the gluing. -/
theorem network_separation_cost (G : V → PrefixGauge D) {x : V → ℕ → D} {v : V}
    (hx : AdmissiblePoint (G v) (x v)) {α : Type*} {f : (V → ℕ → D) → α} {n : ℕ}
    (hf : DecidedAtPlace f v n) {y : V → ℕ → D} (hsep : f x ≠ f y) :
    ((gaugeAt (G v) (x v) n : ℝ))⁻¹ ≤ netDist G x y := by
  -- factor f through place v by updating the v-coordinate of x
  set fv : (ℕ → D) → α := fun s => f (Function.update x v s) with hfv
  have hdec : DecidedAt fv n := by
    intro s s' hpre
    apply hf
    simpa [Function.update_self] using hpre
  have hxv : fv (x v) = f x := by
    simp [hfv, Function.update_eq_self]
  have hyv : fv (y v) = f y := by
    apply hf
    simp [Function.update_self]
  have hsep' : fv (x v) ≠ fv (y v) := by
    rw [hxv, hyv]; exact hsep
  exact le_trans (separation_cost (G v) hx hdec hsep')
    (gaugeDist_le_netDist G x y v)

end FdrsFormal.Modes.SyntheticPlace
