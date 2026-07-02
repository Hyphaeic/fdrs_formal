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

# Synthetic place complex SU7.1 — `complexStep`: the three-clause network firing

The full network machine of `docs/synthetic-place/04-network-config.md` §2, on the
SU7.0 `Config` (probe gate PASSED, `NetworkConfig.lean`). One definition, three
clauses, all quantifying over the same in/out-edge sets of the firing node:

* **Clause 1 — fan-out (the comultiplication), lawful per species.** A firing node's
  overflow produces a family of grants across its out-edges (`fanout`, reading the
  fired source word and each target word — the issue-side window). Lawfulness
  (`FanoutLawful`, a GUARD of the step): where the node **declares** a carry mass
  (`carry v = some c`), the transport out-edges' grants **sum to it** — Theorem 88's
  partition shape as a *constraint* on the fan-out; every trigger out-edge receives
  exactly its declared unit `token` (the diagonal). Mixed fan-out is legal.
  Currencies never mix: one ambient monoid `M` in this module (D7 below).
* **Clause 2 — guards; couplability as liveness.** A node may fire `d` iff `d` is
  admitted by its own law (when autonomous), by **every** in-edge's pending grant
  through that edge's declared `admit` window (the joint fiber), and every out-edge
  has capacity (`pending = none` — the capacity-one latency discipline; an edge with
  an unconsumed grant blocks its source). Non-blocking as a decidable property is
  SU7.3.
* **Clause 3 — within-step dependency orientation: acyclicity as grading.** The rule
  declares its reads-before-writes order as a Phase 8 `DependencyGraph` per node;
  **well-formedness = a `timeOf` potential exists** (`WellFormed`), and the
  certificate is Phase 8's `time_ordered_deadlock_free`, **reused verbatim**
  (`wellFormed_deadlock_free`). The canonical single-firing discipline (all reads at
  time 0, all writes at time 1) is graded (`readsBeforeWrites_timeOrdered`). The
  design law: magnitude MAY be frustrated (SU6a's Penrose triangle is legal);
  causality MUST NOT be — a dependency cycle admits NO potential
  (`no_potential_of_cycle`), the *candidate* fourth obstruction to number-hood
  (candidate only; ledger item 2 of `04`).

**Conservative extension (the SU7.0 instance).** `ofRule` embeds every SU7.0
`NetworkRule` (all-transport, no declared carry, content windows `d < g`):
`ofRule_reachable_iff` — the three-clause machine's reachable set is exactly SU7.0's;
composed with the probe gate, the 2-node/1-edge instance is still the SU4b machine
(`pairComplex_reachable_iff`).

**Witnesses (clauses live, kernel-checked).** `splitShape`/`splitRule`: one source
with declared carry `4`, two transport out-edges (shares `1 + 3`) and one trigger
out-edge (token `1`) — the mixed fan-out fires (`split_step_lawful`) and lands the
partitioned ledgers (`split_fire_ledgers`); the unlawful variant (shares `1 + 2`) is
**blocked** (`badSplit_not_lawful`).

**Recorded design decisions (extending D1–D6 of `01-build-roadmap.md`):**
* **D7 — one ambient currency per module instance.** `ComplexRule N M` fixes one
  commutative monoid for all edges; SU6b proved balance monoid-generically, and the
  per-edge/per-currency machine (heterogeneous `M_e` + declared cross-currency
  morphisms) is SU7.2's arc, where the balance summation lives. No implicit
  exchange exists here because there is nothing to exchange between.
* **D8 — carry mass is a per-node declaration** (`carry : V → Option (List ℕ → M)`).
  `some c` = conserved-mass regime: the partition constraint binds (the split
  witness). `none` = capacity-grant regime: no node-mass discipline is claimed —
  exactly SU4b's bilateral capacity grant, whose conserved quantity lives on the
  interface (Theorem 90), not in a node charge. The constraint binds precisely
  where declared — never silently.

**Honest scope.** Trigger edges here still occupy a capacity-one register, so a
pending trigger blocks its source like transport does (`04` names only transport
blocking; non-blocking triggers need the queue-valued interfaces of the roadmap's
later arc — stated, not smuggled). Fan-out lawfulness is enforced per firing; the
network-wide balance sum and fan-out exactness theorem are SU7.2. Couplability
(SU7.3), per-node traps (SU7.4), determinacy (SU7.5), liveness (SU7.6) are not here.
Finite edge type (`Fintype N.E`) is assumed for the partition sum. Leaf module over
SU7.0 + SU6b + Phase 8. No `sorry`; axiom-clean; kernel-checked demos.
-/
import FdrsFormal.Modes.SyntheticPlace.NetworkConfig
import FdrsFormal.Composition.DeadlockAnalysis.Definition
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace FdrsFormal.Modes.SyntheticPlace

open FdrsFormal.Composition.DeadlockAnalysis in
/-- Re-export the Phase 8 dependency layer under short names for the clause-3 data. -/
abbrev DepGraph := DependencyGraph

/-! ## 1. The distribution species and the three-clause rule -/

/-- The two distribution species of `03-digit-coupling.md` §4: **transport** (the
carry is conserved mass — routed/split, shares sum) and **trigger** (a mirror — every
coupled digit gets its own event-token, copied like information). -/
inductive Species where
  | transport : Species
  | trigger : Species
  deriving DecidableEq, Repr

/-- The full coupling rule (`04` §2): per-node own law and declared carry mass,
per-edge species, trigger token, fan-out share, receiver window, and the declared
within-step dependency order (clause 3, a Phase 8 `DependencyGraph` per node). -/
structure ComplexRule (N : NetworkShape) (M : Type*) [AddCommMonoid M] where
  /-- clause 2: the node's own radix law (`some`), or edge-driven (`none`). -/
  nodeFiber : N.V → Option (List ℕ → ℕ)
  /-- D8: the node's declared conserved carry mass (reads the fired word), if any. -/
  carry : N.V → Option (List ℕ → M)
  /-- clause 1: distribution species per edge. -/
  species : N.E → Species
  /-- clause 1: the unit event-token a trigger edge receives (the diagonal). -/
  token : N.E → M
  /-- clause 1: the fan-out share of edge `e` — fired source word, target word. -/
  fanout : N.E → List ℕ → List ℕ → M
  /-- clause 2: the receiver-side window — is digit `d` admitted against grant `g`? -/
  admit : N.E → M → ℕ → Prop
  /-- clause 3: the declared reads-before-writes order of a firing at `v`. -/
  deps : N.V → DepGraph

variable {N : NetworkShape} {M : Type*} [AddCommMonoid M]

/-! ## 2. Configurations and the firing update -/

/-- A configuration of the three-clause machine: per-node words, per-edge ledgers in
the ambient currency (D7). -/
@[ext] structure CConfig (N : NetworkShape) (M : Type*) where
  word : N.V → List ℕ
  edge : N.E → CurrencyConfig M

/-- The initial configuration. -/
def initC (N : NetworkShape) (M : Type*) [AddCommMonoid M] : CConfig N M :=
  { word := fun _ => [], edge := fun _ => CurrencyConfig.init }

variable [DecidableEq N.V]

/-- The firing update (same shape as SU7.0's `fire`, with the fan-out share as the
issued grant): node `v` appends `d`; in-edges consume; out-edges are issued their
declared shares. -/
def fireC (R : ComplexRule N M) (cfg : CConfig N M) (v : N.V) (d : ℕ) : CConfig N M where
  word := fun u => if u = v then cfg.word u ++ [d] else cfg.word u
  edge := fun e =>
    if N.tgt e = v then (cfg.edge e).consume
    else if N.src e = v then
      (cfg.edge e).issue (R.fanout e (cfg.word v ++ [d]) (cfg.word (N.tgt e)))
    else cfg.edge e

/-! ## 3. Clause 1 — fan-out lawfulness (the partition constraint) -/

variable [Fintype N.E]

/-- The transport out-edges of `v` (the mass-splitting targets). -/
def transportOut (R : ComplexRule N M) (v : N.V) : Finset N.E :=
  Finset.univ.filter fun e => N.src e = v ∧ R.species e = Species.transport

/-- **Clause 1 — `FanoutLawful`**: where the node declares a carry mass, the
transport shares sum to it exactly (Theorem 88's partition law as a constraint on
the comultiplication); every trigger out-edge receives exactly its declared token. -/
def FanoutLawful (R : ComplexRule N M) (cfg : CConfig N M) (v : N.V) (d : ℕ) : Prop :=
  (∀ c, R.carry v = some c →
    ∑ e ∈ transportOut R v,
      R.fanout e (cfg.word v ++ [d]) (cfg.word (N.tgt e)) = c (cfg.word v ++ [d])) ∧
  (∀ e, N.src e = v → R.species e = Species.trigger →
    R.fanout e (cfg.word v ++ [d]) (cfg.word (N.tgt e)) = R.token e)

/-! ## 4. The three-clause step -/

/-- **`complexStep` — reachability under the three-clause firing** (`04` §2): clause 2
as the guards (own law · joint fiber over in-edge windows · out-edge capacity),
clause 1 as the lawfulness guard, clause 3 as machine well-formedness (below). -/
inductive ComplexReachable (R : ComplexRule N M) : CConfig N M → Prop
  | init : ComplexReachable R (initC N M)
  | fire {cfg : CConfig N M} (hr : ComplexReachable R cfg) (v : N.V) (d : ℕ)
      (hown : ∀ f, R.nodeFiber v = some f → d < f (cfg.word v))
      (hin : ∀ e, N.tgt e = v → ∃ g, (cfg.edge e).pending = some g ∧ R.admit e g d)
      (hout : ∀ e, N.src e = v → (cfg.edge e).pending = none)
      (hlaw : FanoutLawful R cfg v d) :
      ComplexReachable R (fireC R cfg v d)

/-! ## 5. Clause 3 — well-formedness is dependency grading (Phase 8, reused) -/

open FdrsFormal.Composition.DeadlockAnalysis

/-- **Clause 3 — well-formedness**: every firing node's declared dependency order is
graded — a `timeOf` potential exists. The order-cocycle sibling of SU6a's
`Gradable`: same potential-existence mathematics, different law (magnitude may be
frustrated; causality must not be). -/
def WellFormed (R : ComplexRule N M) : Prop :=
  ∀ v : N.V, Nonempty (TimeOrderedDependencies (R.deps v))

omit [DecidableEq N.V] [Fintype N.E] in
/-- **The clause-3 certificate — Phase 8 reused verbatim**: a well-formed rule's
per-node dependency graphs are deadlock-free (`time_ordered_deadlock_free`). -/
theorem wellFormed_deadlock_free {R : ComplexRule N M} (h : WellFormed R) (v : N.V) :
    isDeadlockFree (R.deps v) := by
  obtain ⟨ht⟩ := h v
  exact time_ordered_deadlock_free (R.deps v) ht

/-- The canonical single-firing discipline is graded: if a classifier `isWrite`
splits the operations with every dependency pointing from a read (time 0) to a write
(time 1), the potential exists. -/
def readsBeforeWrites_timeOrdered (dg : DepGraph) (isWrite : ℕ → Bool)
    (h : ∀ d ∈ dg.dependencies, isWrite d.waiting = true ∧ isWrite d.waitingFor = false) :
    TimeOrderedDependencies dg where
  timeOf := fun op => if isWrite op then 1 else 0
  forward := by
    intro d hd
    obtain ⟨hw, hr⟩ := h d hd
    simp [hw, hr]

/-- **The causal-frustration no-go** (candidate fourth obstruction, candidate only):
a dependency cycle admits NO `timeOf` potential — a causal loop within a step has no
execution order at all. Contrapositive of the Phase 8 certificate. -/
theorem no_potential_of_cycle {dg : DepGraph} (h : hasCycle dg) :
    ¬ Nonempty (TimeOrderedDependencies dg) := by
  rintro ⟨ht⟩
  exact time_ordered_deadlock_free dg ht h

/-! ## 6. Conservative extension: SU7.0 is the all-transport, no-declared-carry instance -/

/-- Embed an SU7.0 rule: all edges transport, no declared carry (D8's capacity-grant
regime — SU4b's bilateral grant), content windows `d < g`, empty dependency
declarations (trivially graded). -/
def ofRule (R₀ : NetworkRule N) : ComplexRule N ℕ where
  nodeFiber := R₀.nodeFiber
  carry := fun _ => none
  species := fun _ => Species.transport
  token := fun _ => 0
  fanout := R₀.grant
  admit := fun _ g d => d < g
  deps := fun _ => ⟨∅⟩

omit [DecidableEq N.V] [Fintype N.E] in
/-- The embedded rule is well-formed (empty dependency declarations are graded). -/
theorem ofRule_wellFormed (R₀ : NetworkRule N) : WellFormed (ofRule R₀) :=
  fun _ => ⟨readsBeforeWrites_timeOrdered _ (fun _ => true) (fun _ hd => hd.elim)⟩

/-- The embedded rule's fan-out is always lawful (no declared carry, no triggers). -/
theorem ofRule_fanoutLawful (R₀ : NetworkRule N)
    (cfg : CConfig N ℕ) (v : N.V) (d : ℕ) : FanoutLawful (ofRule R₀) cfg v d := by
  constructor
  · intro c hc
    exact absurd hc (by simp [ofRule])
  · intro e _ hs
    exact absurd hs (by simp [ofRule])

/-- Configurations transport across the (definitional) correspondence. -/
def toNet (cfg : CConfig N ℕ) : NetConfig N := { word := cfg.word, edge := cfg.edge }

def ofNet (cfg : NetConfig N) : CConfig N ℕ := { word := cfg.word, edge := cfg.edge }

omit [Fintype N.E] in
theorem toNet_fireC (R₀ : NetworkRule N) (cfg : CConfig N ℕ) (v : N.V) (d : ℕ) :
    toNet (fireC (ofRule R₀) cfg v d) = fire R₀ (toNet cfg) v d := rfl

omit [Fintype N.E] in
theorem ofNet_fire (R₀ : NetworkRule N) (cfg : NetConfig N) (v : N.V) (d : ℕ) :
    ofNet (fire R₀ cfg v d) = fireC (ofRule R₀) (ofNet cfg) v d := rfl

/-- **The conservative-extension theorem**: the three-clause machine at an embedded
SU7.0 rule reaches exactly SU7.0's configurations. New clauses, old machine — the
extension is conservative on the probe-validated fragment. -/
theorem ofRule_reachable_iff (R₀ : NetworkRule N) (cfg : CConfig N ℕ) :
    ComplexReachable (ofRule R₀) cfg ↔ NetReachable R₀ (toNet cfg) := by
  constructor
  · intro h
    induction h with
    | init => exact NetReachable.init
    | fire hr v d hown hin hout _ ih =>
      rw [toNet_fireC]
      exact NetReachable.fire ih v d hown hin hout
  · intro h
    have key : ∀ k : NetConfig N, NetReachable R₀ k →
        ComplexReachable (ofRule R₀) (ofNet k) := by
      intro k hk
      induction hk with
      | init => exact ComplexReachable.init
      | fire hr v d hown hin hout ih =>
        rw [ofNet_fire]
        exact ComplexReachable.fire ih v d hown hin hout
          (ofRule_fanoutLawful R₀ _ v d)
    exact key (toNet cfg) h

/-- **The probe, transported**: through the conservative extension and the SU7.0
gate, the 2-node/1-edge instance of the three-clause machine is still the SU4b
interface machine. -/
theorem pairComplex_reachable_iff (C : CoupledFiber) (cfg : CConfig pairShape ℕ) :
    ComplexReachable (ofRule (pairRule C)) cfg ↔ Reachable C (toCoupled (toNet cfg)) :=
  (ofRule_reachable_iff (pairRule C) cfg).trans (pairNet_reachable_iff C (toNet cfg))

/-! ## 7. The split witness — mixed lawful fan-out, live (clause 1 non-vacuous) -/

/-- Three places: a source (`0`) and two sinks (`1`, `2`). Three edges from the
source: two transport (`0 → 1`, `1 → 2`... edge `i` targets sink `i+1` for the
transports; edge `2` is the trigger into sink `2`). -/
@[reducible] def splitShape : NetworkShape :=
  { V := Fin 3, E := Fin 3
    src := fun _ => 0
    tgt := fun e => if e = 0 then 1 else 2 }

instance : DecidableEq splitShape.V := inferInstanceAs (DecidableEq (Fin 3))
instance : Fintype splitShape.E := inferInstanceAs (Fintype (Fin 3))

/-- The mixed rule: autonomous source (base 10), **declared carry mass 4**, transport
shares `1` and `3` (they sum), one trigger edge with token `1`. -/
def splitRule : ComplexRule splitShape ℕ where
  nodeFiber := fun v => if v = 0 then some (fun _ => 10) else none
  carry := fun v => if v = 0 then some (fun _ => 4) else none
  species := fun e => if e = 2 then Species.trigger else Species.transport
  token := fun _ => 1
  fanout := fun e _ _ => if e = 0 then 1 else if e = 1 then 3 else 1
  admit := fun _ g d => d < g
  deps := fun _ => ⟨∅⟩

/-- The unlawful variant: shares `1` and `2` against declared carry `4`. -/
def badSplitRule : ComplexRule splitShape ℕ :=
  { splitRule with fanout := fun e _ _ => if e = 0 then 1 else if e = 1 then 2 else 1 }

/-- The lawful mixed fan-out is enabled: shares partition the declared carry
(`1 + 3 = 4`) and the trigger receives its token. Kernel-checked. -/
theorem split_step_lawful : FanoutLawful splitRule (initC splitShape ℕ) (0 : Fin 3) 7 := by
  constructor
  · intro c hc
    have hc4 : c = fun _ => 4 := by simpa [splitRule] using hc.symm
    subst hc4
    decide
  · intro e hsrc hspec
    fin_cases e <;> simp_all [splitRule]

/-- The firing is reachable — one step from the initial configuration. -/
theorem split_fires :
    ComplexReachable (N := splitShape) (M := ℕ) splitRule
      (fireC (N := splitShape) (M := ℕ) splitRule (initC splitShape ℕ) (0 : Fin 3) 7) := by
  refine ComplexReachable.fire (R := splitRule) (ComplexReachable.init (R := splitRule))
    (0 : Fin 3) 7 ?_ ?_ ?_ split_step_lawful
  · intro f hf
    have : f = fun _ => 10 := by simpa [splitRule] using hf.symm
    subst this
    norm_num
  · intro e he
    exact absurd he (by fin_cases e <;> simp [splitShape])
  · intro e _
    rfl

/-- The partitioned ledgers, kernel-checked: transport edges hold `1` and `3`
in-flight, the trigger holds its token `1`. -/
theorem split_fire_ledgers :
    ((fireC splitRule (initC splitShape ℕ) (0 : Fin 3) 7).edge 0).pending = some 1 ∧
    ((fireC splitRule (initC splitShape ℕ) (0 : Fin 3) 7).edge 1).pending = some 3 ∧
    ((fireC splitRule (initC splitShape ℕ) (0 : Fin 3) 7).edge 2).pending = some 1 := by
  refine ⟨rfl, rfl, rfl⟩

/-- **The unlawful split is blocked**: shares `1 + 2` cannot partition the declared
carry `4` — the guard refuses the firing. Kernel-checked. -/
theorem badSplit_not_lawful : ¬ FanoutLawful badSplitRule (initC splitShape ℕ) (0 : Fin 3) 7 := by
  intro ⟨hmass, _⟩
  have h4 := hmass (fun _ => 4) (by simp [badSplitRule, splitRule])
  revert h4
  decide

/-! ## Axiom audit -/

#print axioms wellFormed_deadlock_free
#print axioms no_potential_of_cycle
#print axioms ofRule_reachable_iff
#print axioms pairComplex_reachable_iff
#print axioms split_fires
#print axioms badSplit_not_lawful

end FdrsFormal.Modes.SyntheticPlace
