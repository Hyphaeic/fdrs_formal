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

# Synthetic place complex SU7.2 — network balance (SU6b's generic law, per edge)

The conservation layer of the three-clause machine (`04-network-config.md` §4, row
SU7.2): *per-edge, per-currency `issued = consumed + pending`, summed over edges;
fan-out exactness.* Everything here is transport of SU6b through the machine's
dynamics — no new conservation idea, which is the point:

* **`edge_currencyReachable`** — every edge's ledger of a reachable configuration is
  `CurrencyReachable`: the machine's firing discipline (consume only pending,
  issue only into empty — clause 2's guards) is exactly SU6b's reachability
  discipline, edge by edge. This is the literal "SU6b generic law per edge".
* **`network_balanced_per_edge`** — hence every edge is balanced
  (`issued = consumed + pending`), by `currencyReachable_balanced` applied verbatim.
* **`network_balanced_total`** — summed over edges (one ambient currency, D7 — the
  only regime where a cross-edge sum is meaningful; ledger item 3 of `04`):
  `Σ issued = Σ consumed + Σ pending`.
* **`fire_fanout_exact`** — fan-out exactness as a THEOREM: a firing at a node with
  a **declared** carry mass (D8) increases the total mass issued across its
  transport out-edges by exactly that carry — Theorem 88's partition law, now on
  the emission side of the machine. En route, **`fire_no_self_loop`**: a fireable
  node has no self-loop — clause 2's guards make a self-loop's register need to be
  simultaneously pending and empty, so such a node can never fire (a structural
  fact the design did not have to legislate).
* **The heterogeneous machine** (`HRule`/`HConfig`/`HReachable`) — per-edge
  currencies `Mfam e`, D7's deferred form: clause-2 guards and the trigger diagonal
  (each token in its own edge currency — meaningful heterogeneously), with
  **`hedge_currencyReachable`** and **`hnetwork_balanced_per_edge`**: the balance
  law holds per edge, each in its own declared currency.

**Recorded decision D9 (refining D7/D8).** In the heterogeneous machine there is no
carry-partition constraint: a cross-edge sum of shares in different currencies is
exactly the "total network charge" the anti-confabulation ledger forbids. The
partition law requires shares declared in the firing node's own currency and pushed
through **declared morphisms** `Mv →+ Mfam e` per edge; that plumbing (per-node
currencies + push morphisms) is recorded open here, not smuggled. Clause 3 (`deps` /
`WellFormed`) is currency-free and reusable as-is by any heterogeneous rule; it is
not duplicated.

**Honest scope.** The heterogeneous machine carries no lawfulness guard beyond the
trigger diagonal (see D9) and no kernel witness (the generic theorems are the
content; the ambient split witness lives in SU7.1). Couplability (SU7.3), per-node
traps (SU7.4), determinacy (SU7.5), liveness (SU7.6) remain ahead. Leaf module over
SU7.1 + SU6b. No `sorry`; axiom-clean.
-/
import FdrsFormal.Modes.SyntheticPlace.NetworkComplexStep

namespace FdrsFormal.Modes.SyntheticPlace

variable {N : NetworkShape} {M : Type*} [AddCommMonoid M] [DecidableEq N.V] [Fintype N.E]

/-! ## 1. Per-edge SU6b reachability: the machine respects the ledger discipline -/

/-- **The SU6b discipline, per edge**: through any reachable run of the three-clause
machine, each edge's ledger is `CurrencyReachable` — the firing guards are exactly
issue-into-empty / consume-pending. -/
theorem edge_currencyReachable {R : ComplexRule N M} {cfg : CConfig N M}
    (h : ComplexReachable R cfg) (e : N.E) :
    CurrencyReachable (Set.univ : Set M) (cfg.edge e) := by
  induction h with
  | init => exact CurrencyReachable.init
  | fire hr v d hown hin hout hlaw ih =>
    by_cases htgt : N.tgt e = v
    · obtain ⟨g, hpg, _⟩ := hin e htgt
      simp only [fireC, htgt, if_pos]
      exact CurrencyReachable.consume hpg ih
    · by_cases hsrc : N.src e = v
      · have hpn := hout e hsrc
        simp only [fireC, htgt, hsrc, if_pos]
        exact CurrencyReachable.issue _ (Set.mem_univ _) hpn ih
      · simp only [fireC, htgt, hsrc]
        exact ih

/-- **SU7.2, per edge**: every edge of a reachable configuration is balanced —
`currencyReachable_balanced`, applied verbatim. -/
theorem network_balanced_per_edge {R : ComplexRule N M} {cfg : CConfig N M}
    (h : ComplexReachable R cfg) (e : N.E) :
    CurrencyBalanced (cfg.edge e) :=
  currencyReachable_balanced (edge_currencyReachable h e)

/-- **SU7.2, summed over edges** (ambient currency — the only regime where the
cross-edge sum is meaningful, D7/D9): total issued = total consumed + total in
flight. -/
theorem network_balanced_total {R : ComplexRule N M} {cfg : CConfig N M}
    (h : ComplexReachable R cfg) :
    ∑ e, (cfg.edge e).issued
      = ∑ e, (cfg.edge e).consumed + ∑ e, (cfg.edge e).pending.getD 0 := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun e _ => network_balanced_per_edge h e

/-! ## 2. Fan-out exactness (the partition law on the emission side) -/

omit [DecidableEq N.V] [Fintype N.E] in
/-- **A fireable node has no self-loop**: clause 2's guards demand a self-loop's
register be simultaneously pending (in-edge) and empty (out-edge). Structural, not
legislated. -/
theorem fire_no_self_loop {R : ComplexRule N M} {cfg : CConfig N M} {v : N.V} {d : ℕ}
    (hin : ∀ e, N.tgt e = v → ∃ g, (cfg.edge e).pending = some g ∧ R.admit e g d)
    (hout : ∀ e, N.src e = v → (cfg.edge e).pending = none)
    {e : N.E} (hsrc : N.src e = v) : N.tgt e ≠ v := by
  intro htgt
  obtain ⟨g, hpg, _⟩ := hin e htgt
  rw [hout e hsrc] at hpg
  simp at hpg

/-- **SU7.2 — fan-out exactness**: a firing at a node with a declared carry mass
issues exactly that mass across its transport out-edges — the guard's partition
constraint, surfaced as the emission-side conservation theorem (Theorem 88's shape
on the machine). -/
theorem fire_fanout_exact {R : ComplexRule N M} {cfg : CConfig N M} {v : N.V} {d : ℕ}
    (hin : ∀ e, N.tgt e = v → ∃ g, (cfg.edge e).pending = some g ∧ R.admit e g d)
    (hout : ∀ e, N.src e = v → (cfg.edge e).pending = none)
    (hlaw : FanoutLawful R cfg v d)
    {c : List ℕ → M} (hc : R.carry v = some c) :
    ∑ e ∈ transportOut R v, ((fireC R cfg v d).edge e).issued
      = (∑ e ∈ transportOut R v, (cfg.edge e).issued) + c (cfg.word v ++ [d]) := by
  have hstep : ∀ e ∈ transportOut R v,
      ((fireC R cfg v d).edge e).issued
        = (cfg.edge e).issued + R.fanout e (cfg.word v ++ [d]) (cfg.word (N.tgt e)) := by
    intro e he
    have hsrc : N.src e = v := ((Finset.mem_filter.mp he).2).1
    have htgt : N.tgt e ≠ v := fire_no_self_loop hin hout hsrc
    simp [fireC, htgt, hsrc, CurrencyConfig.issue]
  calc ∑ e ∈ transportOut R v, ((fireC R cfg v d).edge e).issued
      = ∑ e ∈ transportOut R v,
          ((cfg.edge e).issued + R.fanout e (cfg.word v ++ [d]) (cfg.word (N.tgt e))) :=
        Finset.sum_congr rfl hstep
    _ = (∑ e ∈ transportOut R v, (cfg.edge e).issued)
          + ∑ e ∈ transportOut R v, R.fanout e (cfg.word v ++ [d]) (cfg.word (N.tgt e)) :=
        Finset.sum_add_distrib
    _ = (∑ e ∈ transportOut R v, (cfg.edge e).issued) + c (cfg.word v ++ [d]) := by
        rw [hlaw.1 c hc]

/-! ## 3. The heterogeneous machine: per-edge currencies (D7's deferred form) -/

/-- The heterogeneous coupling rule: each edge declares its own currency `Mfam e`;
tokens, shares, and windows live per edge in that currency. No carry partition (D9);
clause 3 is currency-free and reused from `ComplexRule` designs unchanged. -/
structure HRule (N : NetworkShape) (Mfam : N.E → Type*)
    [∀ e, AddCommMonoid (Mfam e)] where
  nodeFiber : N.V → Option (List ℕ → ℕ)
  species : N.E → Species
  token : (e : N.E) → Mfam e
  fanout : (e : N.E) → List ℕ → List ℕ → Mfam e
  admit : (e : N.E) → Mfam e → ℕ → Prop

/-- A heterogeneous configuration: each edge's ledger in its own currency. -/
structure HConfig (N : NetworkShape) (Mfam : N.E → Type*) where
  word : N.V → List ℕ
  edge : (e : N.E) → CurrencyConfig (Mfam e)

variable {Mfam : N.E → Type*} [∀ e, AddCommMonoid (Mfam e)]

/-- The initial heterogeneous configuration. -/
def initH (N : NetworkShape) (Mfam : N.E → Type*) [∀ e, AddCommMonoid (Mfam e)] :
    HConfig N Mfam :=
  { word := fun _ => [], edge := fun _ => CurrencyConfig.init }

/-- The heterogeneous firing update (the `fireC` shape, per-edge-typed). -/
def fireH (R : HRule N Mfam) (cfg : HConfig N Mfam) (v : N.V) (d : ℕ) :
    HConfig N Mfam where
  word := fun u => if u = v then cfg.word u ++ [d] else cfg.word u
  edge := fun e =>
    if N.tgt e = v then (cfg.edge e).consume
    else if N.src e = v then
      (cfg.edge e).issue (R.fanout e (cfg.word v ++ [d]) (cfg.word (N.tgt e)))
    else cfg.edge e

/-- Heterogeneous reachability: clause-2 guards plus the trigger diagonal (each
token in its own edge currency — the per-species law that IS meaningful
heterogeneously). -/
inductive HReachable (R : HRule N Mfam) : HConfig N Mfam → Prop
  | init : HReachable R (initH N Mfam)
  | fire {cfg : HConfig N Mfam} (hr : HReachable R cfg) (v : N.V) (d : ℕ)
      (hown : ∀ f, R.nodeFiber v = some f → d < f (cfg.word v))
      (hin : ∀ e, N.tgt e = v → ∃ g, (cfg.edge e).pending = some g ∧ R.admit e g d)
      (hout : ∀ e, N.src e = v → (cfg.edge e).pending = none)
      (htok : ∀ e, N.src e = v → R.species e = Species.trigger →
        R.fanout e (cfg.word v ++ [d]) (cfg.word (N.tgt e)) = R.token e) :
      HReachable R (fireH R cfg v d)

omit [Fintype N.E] in
/-- The SU6b discipline, per edge, per currency. -/
theorem hedge_currencyReachable {R : HRule N Mfam} {cfg : HConfig N Mfam}
    (h : HReachable R cfg) (e : N.E) :
    CurrencyReachable (Set.univ : Set (Mfam e)) (cfg.edge e) := by
  induction h with
  | init => exact CurrencyReachable.init
  | fire hr v d hown hin hout htok ih =>
    by_cases htgt : N.tgt e = v
    · obtain ⟨g, hpg, _⟩ := hin e htgt
      simp only [fireH, htgt, if_pos]
      exact CurrencyReachable.consume hpg ih
    · by_cases hsrc : N.src e = v
      · have hpn := hout e hsrc
        simp only [fireH, htgt, hsrc, if_pos]
        exact CurrencyReachable.issue _ (Set.mem_univ _) hpn ih
      · simp only [fireH, htgt, hsrc]
        exact ih

omit [Fintype N.E] in
/-- **SU7.2, heterogeneous**: every edge of a reachable heterogeneous configuration
is balanced — in its own declared currency. No cross-edge sum is stated (D9). -/
theorem hnetwork_balanced_per_edge {R : HRule N Mfam} {cfg : HConfig N Mfam}
    (h : HReachable R cfg) (e : N.E) :
    CurrencyBalanced (cfg.edge e) :=
  currencyReachable_balanced (hedge_currencyReachable h e)

/-! ## Axiom audit -/

#print axioms network_balanced_per_edge
#print axioms network_balanced_total
#print axioms fire_no_self_loop
#print axioms fire_fanout_exact
#print axioms hnetwork_balanced_per_edge

end FdrsFormal.Modes.SyntheticPlace
