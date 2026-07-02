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

# Synthetic place complex SU7.5 — the conditional Kahn diamond (determinacy, local form)

`04-network-config.md` §4 row SU7.5: *stream determinacy under the latency
discipline — the conditional Kahn diamond; classical KPN, cited.* Per the ledger
(item 1): Kahn-network determinacy is classical (Kahn 1974 lineage) — this module
contributes the FDRS-shaped statement and the verified artifact, nothing more. The
disjoint-places precedent is the adelic scheduler confluence (`run_eq_of_counts`);
the coupled-places form was the open layer (b) of the thesis §3. It lands here, and
the latency discipline is what makes it land:

* **`no_edge_between`** — THE DISCIPLINE PAYS: under capacity-one, two distinct
  nodes that are *both enabled* can share **no** coupling edge in either direction —
  a connecting edge would have to be simultaneously pending (the receiver's in-guard)
  and empty (the sender's out-guard). The Kahn diamond's independence
  side-condition is not an assumption; it is **derived** from simultaneous
  enabledness. (This is "conditional" resolved: the condition is `v ≠ u` + both
  enabled, and the latency discipline supplies the rest.)
* **`fireC_comm`** — THE DIAMOND: two enabled firings at distinct nodes commute on
  the nose — `fireC (fireC cfg v d) u d' = fireC (fireC cfg u d') v d`. Grants are
  unaffected because non-adjacency (derived) keeps every read word and register
  out of the other firing's footprint.
* **`enabled_after_fire`** — each firing stays enabled after the other (all four
  guard conjuncts survive, including fan-out lawfulness — the sums are pointwise
  untouched).
* **`diamond`** — the packaged local confluence: from a reachable configuration
  with two distinct enabled firings, both interleavings are reachable and land on
  the same configuration.

**Honest scope.** This is the LOCAL diamond — the one-step confluence element.
Global stream determinacy (any two fair complete schedules produce the same
per-node streams) is the classical KPN theorem obtained by composing the diamond
with fairness/termination arguments; the fairness bridge is exactly the open
hypothesis of Phase 14 §14.7 and is cited, not formalized. Firings at the SAME
node with different digits do NOT commute and are not claimed to — determinism of
the choice is the scheduler's business, not the machine's. Leaf module over SU7.3.
No `sorry`; axiom-clean.
-/
import FdrsFormal.Modes.SyntheticPlace.NetworkCouplability

namespace FdrsFormal.Modes.SyntheticPlace

variable {N : NetworkShape} {M : Type*} [AddCommMonoid M] [DecidableEq N.V] [Fintype N.E]

/-! ## 1. The discipline pays: simultaneous enabledness forces non-adjacency -/

/-- Under capacity-one, two distinct simultaneously-enabled nodes share no coupling
edge in either direction: a connecting edge would need to be pending (receiver's
in-guard) and empty (sender's out-guard) at once. -/
theorem no_edge_between {R : ComplexRule N M} {cfg : CConfig N M} {v u : N.V}
    {d d' : ℕ} (hv : Enabled R cfg v d) (hu : Enabled R cfg u d') (e : N.E) :
    ¬ (N.src e = v ∧ N.tgt e = u) ∧ ¬ (N.src e = u ∧ N.tgt e = v) := by
  constructor
  · rintro ⟨hs, ht⟩
    obtain ⟨g, hpg, _⟩ := hu.2.1 e ht
    rw [hv.2.2.1 e hs] at hpg
    simp at hpg
  · rintro ⟨hs, ht⟩
    obtain ⟨g, hpg, _⟩ := hv.2.1 e ht
    rw [hu.2.2.1 e hs] at hpg
    simp at hpg

/-! ## 2. Footprint lemmas -/

omit [Fintype N.E] in
theorem fire_word_ne {R : ComplexRule N M} {cfg : CConfig N M} {v : N.V} {d : ℕ}
    {u : N.V} (h : u ≠ v) : (fireC R cfg v d).word u = cfg.word u := by
  simp [fireC, h]

omit [Fintype N.E] in
theorem fire_word_self {R : ComplexRule N M} {cfg : CConfig N M} {v : N.V} {d : ℕ} :
    (fireC R cfg v d).word v = cfg.word v ++ [d] := by
  simp [fireC]

omit [Fintype N.E] in
theorem fire_edge_untouched {R : ComplexRule N M} {cfg : CConfig N M} {v : N.V}
    {d : ℕ} {e : N.E} (ht : N.tgt e ≠ v) (hs : N.src e ≠ v) :
    (fireC R cfg v d).edge e = cfg.edge e := by
  simp [fireC, ht, hs]

/-! ## 3. Enabledness survives the other firing -/

/-- Each of two distinct enabled firings remains enabled after the other: every
guard conjunct reads only state the other firing (by derived non-adjacency) never
touches. -/
theorem enabled_after_fire {R : ComplexRule N M} {cfg : CConfig N M} {v u : N.V}
    {d d' : ℕ} (hvu : v ≠ u) (hv : Enabled R cfg v d) (hu : Enabled R cfg u d') :
    Enabled R (fireC R cfg v d) u d' := by
  have hword : (fireC R cfg v d).word u = cfg.word u := fire_word_ne (Ne.symm hvu)
  have hedgeU : ∀ e, N.src e = u → (fireC R cfg v d).edge e = cfg.edge e := by
    intro e hs
    refine fire_edge_untouched (fun ht => ?_) (fun hsv => hvu (hsv.symm.trans hs))
    exact (no_edge_between hv hu e).2 ⟨hs, ht⟩
  have hedgeIn : ∀ e, N.tgt e = u → (fireC R cfg v d).edge e = cfg.edge e := by
    intro e ht
    refine fire_edge_untouched (fun htv => hvu (htv.symm.trans ht)) (fun hsv => ?_)
    exact (no_edge_between hv hu e).1 ⟨hsv, ht⟩
  have hwordTgt : ∀ e, N.src e = u → (fireC R cfg v d).word (N.tgt e) = cfg.word (N.tgt e) := by
    intro e hs
    exact fire_word_ne (fun ht => (no_edge_between hv hu e).2 ⟨hs, ht⟩)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f hf
    rw [hword]
    exact hu.1 f hf
  · intro e ht
    rw [hedgeIn e ht]
    exact hu.2.1 e ht
  · intro e hs
    rw [hedgeU e hs]
    exact hu.2.2.1 e hs
  · intro c hc
    rw [hword]
    calc ∑ e ∈ transportOut R u,
          R.fanout e (cfg.word u ++ [d']) ((fireC R cfg v d).word (N.tgt e))
        = ∑ e ∈ transportOut R u,
            R.fanout e (cfg.word u ++ [d']) (cfg.word (N.tgt e)) := by
          refine Finset.sum_congr rfl fun e he => ?_
          have hs : N.src e = u := ((Finset.mem_filter.mp he).2).1
          rw [hwordTgt e hs]
      _ = c (cfg.word u ++ [d']) := hu.2.2.2.1 c hc
  · intro e hs hspec
    rw [hword, hwordTgt e hs]
    exact hu.2.2.2.2 e hs hspec

/-! ## 4. THE DIAMOND -/

/-- **SU7.5 — the conditional Kahn diamond, commutation half**: two enabled firings
at distinct nodes commute on the nose. Non-adjacency (derived from the latency
discipline) keeps every word and register each firing reads outside the other's
footprint. -/
theorem fireC_comm {R : ComplexRule N M} {cfg : CConfig N M} {v u : N.V}
    {d d' : ℕ} (hvu : v ≠ u) (hv : Enabled R cfg v d) (hu : Enabled R cfg u d') :
    fireC R (fireC R cfg v d) u d' = fireC R (fireC R cfg u d') v d := by
  have hno := no_edge_between hv hu
  ext1
  · funext x
    by_cases hxu : x = u <;> by_cases hxv : x = v <;>
      simp_all [fireC]
  · funext e
    by_cases htv : N.tgt e = v
    · have htu : N.tgt e ≠ u := fun h => hvu (htv.symm.trans h)
      have hsu : N.src e ≠ u := fun hs => (hno e).2 ⟨hs, htv⟩
      simp [fireC, htv, hsu, hvu, Ne.symm hvu]
    · by_cases htu : N.tgt e = u
      · have hsv : N.src e ≠ v := fun hs => (hno e).1 ⟨hs, htu⟩
        simp [fireC, htu, hsv, hvu, Ne.symm hvu]
      · by_cases hsv : N.src e = v
        · have hsu : N.src e ≠ u := fun h => hvu (hsv.symm.trans h)
          simp [fireC, htv, htu, hsv, Ne.symm hvu, hvu]
        · by_cases hsu : N.src e = u
          · simp [fireC, htv, htu, hsu, hvu, Ne.symm hvu]
          · simp [fireC, htv, htu, hsv, hsu]

/-- **SU7.5 — the diamond, packaged**: from a reachable configuration with two
distinct enabled firings, both interleavings are reachable and land on the same
configuration. Local confluence; the global KPN determinacy composes this with
fairness (classical, cited — Phase 14 §14.7's open bridge). -/
theorem diamond {R : ComplexRule N M} {cfg : CConfig N M} {v u : N.V} {d d' : ℕ}
    (hr : ComplexReachable R cfg) (hvu : v ≠ u)
    (hv : Enabled R cfg v d) (hu : Enabled R cfg u d') :
    ComplexReachable R (fireC R (fireC R cfg v d) u d') ∧
    ComplexReachable R (fireC R (fireC R cfg u d') v d) ∧
    fireC R (fireC R cfg v d) u d' = fireC R (fireC R cfg u d') v d :=
  ⟨(enabled_after_fire hvu hv hu).fire (hv.fire hr),
   (enabled_after_fire (Ne.symm hvu) hu hv).fire (hu.fire hr),
   fireC_comm hvu hv hu⟩

/-! ## Axiom audit -/

#print axioms no_edge_between
#print axioms enabled_after_fire
#print axioms fireC_comm
#print axioms diamond

end FdrsFormal.Modes.SyntheticPlace
