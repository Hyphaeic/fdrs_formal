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

# Synthetic place complex SU7.0 — the network probe: `Config` + `complexStep` recover SU4b

First stone of the network arc (`docs/synthetic-place/04-network-config.md`): the
coupled radix network as an abstract machine. Per the build plan, SU7.0 is the
**mandatory probe gate**: the 2-node/1-edge instance of the network machine must be
(isomorphic to) the SU4b interface machine (`InterfaceBalance.lean`) — *"if SU7.0
fails to recover the SU4b machine, the `Config` design is wrong — fix the design,
not the probe."* This file passes the gate:

* **The machine.** `NetConfig` is exactly `04` §1's record: per-node digit words +
  per-edge interface registers (`CurrencyConfig ℕ` — SU6b's declared ledger, forced
  by Theorem 90: the conserved quantity lives ON the coupling; capacity-one = the D6
  latency discipline). One step (`NetReachable.fire`): a node fires a digit against
  its in-edge grants and its own radix law, consuming every in-edge and issuing into
  every out-edge (grant = the edge's declared window rule, reading the fired source
  word and the target word — the SU1 full-content shape).
* **The probe.** `pairShape` (nodes `A = false`, `B = true`, one edge `A → B`) with
  `pairRule C` instantiates the machine at a `CoupledFiber`; `toCoupled`/`ofCoupled`
  are mutually inverse (`toCoupled_ofCoupled`, `ofCoupled_toCoupled`), steps map to
  steps (`toCoupled_fire_A/B` — A-firing IS `applyA`, B-firing IS `applyB`), and
  **`pairNet_reachable_iff`**: the network's reachable set is exactly SU4b's. The
  network conservatively extends what is built.
* **The transported law.** `pairNet_balanced`: every reachable probe configuration
  carries a balanced edge ledger — SU4b's `issued = consumed + pending`, read
  through the correspondence. Kernel-checked demo run mirrors
  `InterfaceBalance.lean`'s (`ragged_net_run`, ledger `6 = 6 + 0`).

**Honest scope (the probe fragment, deliberately).** One firing clause over
arbitrary shapes, but: grants are full-content windows (SU1 shape — the window
lattice per edge is SU7.1's declaration table); multi-out-edge fan-out carries no
lawfulness constraint yet (transport splits summing to the carry — Theorem 88's
shape as a constraint — is SU7.2); currencies are fixed at `ℕ` transport (the
monoid-generic per-edge declaration is SU7.2); within-step dependency orientation
(clause 3, acyclicity-as-grading) does not arise — a probe step reads and writes
disjoint edge sets; self-loop edges take the consume branch by convention and are
out of scope; nodes are edge-driven (`nodeFiber = none`) or autonomous (`some f`),
the joint-fiber meet of both being SU7.1 territory. Liveness (`04` SU7.3/7.6) is
absent: `fire` is guarded, never guaranteed. Leaf module over SU4b + SU6b. No
`sorry`; axiom-clean; kernel-checked demos.
-/
import FdrsFormal.Modes.SyntheticPlace.InterfaceBalance
import FdrsFormal.Modes.SyntheticPlace.CurrencyBalance

namespace FdrsFormal.Modes.SyntheticPlace

/-! ## 1. The network shape, the coupling rule, and the configuration -/

/-- The static shape of a coupled radix network: places and directed coupling edges.
(Finiteness is not needed for the probe; the guards quantify over the shape.) -/
structure NetworkShape where
  V : Type*
  E : Type*
  src : E → V
  tgt : E → V

/-- The per-node and per-edge declarations of the coupling rule (`04` §1, probe
fragment): each node is a radix line — `some f` gives its own digit fiber at its
prefix, `none` marks an edge-driven line whose digit range comes entirely from its
in-edge grants (SU4b's B). Each edge declares its grant rule — what the carry opens
for the target — reading the fired source word (including the new digit, D6) and the
target word: the SU1 full-content window. -/
structure NetworkRule (N : NetworkShape) where
  nodeFiber : N.V → Option (List ℕ → ℕ)
  grant : N.E → List ℕ → List ℕ → ℕ

/-- A network configuration: one digit word per node, one declared interface ledger
per edge (`CurrencyConfig` — SU6b; the conserved quantity lives ON the coupling). -/
@[ext] structure NetConfig (N : NetworkShape) where
  word : N.V → List ℕ
  edge : N.E → CurrencyConfig ℕ

/-- The initial configuration: empty words, empty ledgers. -/
def initNet (N : NetworkShape) : NetConfig N :=
  { word := fun _ => [], edge := fun _ => CurrencyConfig.init }

/-! ## 2. `complexStep` — one node fires -/

variable {N : NetworkShape} [DecidableEq N.V]

/-- The firing update: node `v` appends digit `d`; every in-edge is consumed; every
out-edge is issued its declared grant (read off the fired word and the target word).
Self-loops take the consume branch by convention (out of probe scope). -/
def fire (R : NetworkRule N) (cfg : NetConfig N) (v : N.V) (d : ℕ) : NetConfig N where
  word := fun u => if u = v then cfg.word u ++ [d] else cfg.word u
  edge := fun e =>
    if N.tgt e = v then (cfg.edge e).consume
    else if N.src e = v then
      (cfg.edge e).issue (R.grant e (cfg.word v ++ [d]) (cfg.word (N.tgt e)))
    else cfg.edge e

/-- Reachability under the guarded dynamics — `04` §2's three clauses in probe form:
a node may fire a digit iff it is admitted by the node's own law (when it has one),
admitted by **every** in-edge's pending grant (the joint fiber), and every out-edge
has capacity (pending = none — the capacity-one latency discipline). -/
inductive NetReachable (R : NetworkRule N) : NetConfig N → Prop
  | init : NetReachable R (initNet N)
  | fire {cfg : NetConfig N} (hr : NetReachable R cfg) (v : N.V) (d : ℕ)
      (hown : ∀ f, R.nodeFiber v = some f → d < f (cfg.word v))
      (hin : ∀ e, N.tgt e = v → ∃ g, (cfg.edge e).pending = some g ∧ d < g)
      (hout : ∀ e, N.src e = v → (cfg.edge e).pending = none) :
      NetReachable R (fire R cfg v d)

/-! ## 3. The probe instance: two nodes, one edge -/

/-- The 2-node/1-edge shape: `A = false`, `B = true`, one coupling edge `A → B`. -/
@[reducible] def pairShape : NetworkShape :=
  { V := Bool, E := Unit, src := fun _ => false, tgt := fun _ => true }

instance : DecidableEq pairShape.V := inferInstanceAs (DecidableEq Bool)

/-- The SU4b coupling as a network rule: `A` is autonomous with fiber `fiberA`; `B`
is edge-driven; the edge's grant is `fiberB (target word) (fired source word)` —
exactly the grant `applyA` issues. -/
def pairRule (C : CoupledFiber) : NetworkRule pairShape where
  nodeFiber := fun v => if v then none else some C.fiberA
  grant := fun _ srcW tgtW => C.fiberB tgtW srcW

/-- Read a probe configuration as an SU4b configuration. -/
def toCoupled (cfg : NetConfig pairShape) : CoupledConfig :=
  { sA := cfg.word false
    sB := cfg.word true
    pending := (cfg.edge ()).pending
    issued := (cfg.edge ()).issued
    consumed := (cfg.edge ()).consumed }

/-- Read an SU4b configuration as a probe configuration. -/
def ofCoupled (k : CoupledConfig) : NetConfig pairShape :=
  { word := fun v => if v then k.sB else k.sA
    edge := fun _ => ⟨k.issued, k.consumed, k.pending⟩ }

theorem toCoupled_ofCoupled (k : CoupledConfig) : toCoupled (ofCoupled k) = k := rfl

theorem ofCoupled_toCoupled (cfg : NetConfig pairShape) : ofCoupled (toCoupled cfg) = cfg := by
  ext1
  · funext v
    cases v <;> rfl
  · funext e
    cases e
    rfl

/-! ## 4. Steps map to steps (both readings) -/

/-- The initial configurations correspond. -/
theorem ofCoupled_init : ofCoupled initConfig = initNet pairShape := by
  ext1
  · funext v
    cases v <;> rfl
  · funext e
    cases e
    rfl

/-- The SU4b A-half-step, lifted: `ofCoupled` intertwines `applyA` with firing `A`. -/
theorem ofCoupled_applyA (C : CoupledFiber) (k : CoupledConfig) (a : ℕ) :
    ofCoupled (applyA C k a) = fire (pairRule C) (ofCoupled k) false a := by
  ext1
  · funext v
    cases v <;> simp [ofCoupled, applyA, fire]
  · funext e
    cases e
    simp [ofCoupled, applyA, fire, pairRule, CurrencyConfig.issue]

/-- The SU4b B-half-step, lifted: `ofCoupled` intertwines `applyB` with firing `B`. -/
theorem ofCoupled_applyB (C : CoupledFiber) (k : CoupledConfig) (b : ℕ) :
    ofCoupled (applyB k b) = fire (pairRule C) (ofCoupled k) true b := by
  ext1
  · funext v
    cases v <;> simp [ofCoupled, applyB, fire]
  · funext e
    cases e
    simp [ofCoupled, applyB, fire, CurrencyConfig.consume]

/-- Firing `A` in the probe IS the SU4b A-half-step. -/
theorem toCoupled_fire_A (C : CoupledFiber) (cfg : NetConfig pairShape) (a : ℕ) :
    toCoupled (fire (pairRule C) cfg false a) = applyA C (toCoupled cfg) a := by
  unfold toCoupled fire applyA pairRule CurrencyConfig.issue
  simp

/-- Firing `B` in the probe IS the SU4b B-half-step. -/
theorem toCoupled_fire_B (C : CoupledFiber) (cfg : NetConfig pairShape) (b : ℕ) :
    toCoupled (fire (pairRule C) cfg true b) = applyB (toCoupled cfg) b := by
  unfold toCoupled fire applyB CurrencyConfig.consume
  simp

/-! ## 5. THE PROBE GATE — the network's reachable set is exactly SU4b's -/

/-- Forward: every reachable probe configuration reads as a reachable SU4b
configuration. -/
theorem netReachable_toCoupled {C : CoupledFiber} {cfg : NetConfig pairShape}
    (h : NetReachable (pairRule C) cfg) : Reachable C (toCoupled cfg) := by
  induction h with
  | init => exact Reachable.init
  | fire hr v d hown hin hout ih =>
    cases v with
    | false =>
      rw [toCoupled_fire_A]
      exact Reachable.stepA ih d (hown C.fiberA rfl) (hout () rfl)
    | true =>
      obtain ⟨g, hp, hb⟩ := hin () rfl
      rw [toCoupled_fire_B]
      exact Reachable.stepB ih d hp hb

/-- Backward: every reachable SU4b configuration lifts to a reachable probe
configuration. -/
theorem coupledReachable_ofCoupled {C : CoupledFiber} {k : CoupledConfig}
    (h : Reachable C k) : NetReachable (pairRule C) (ofCoupled k) := by
  induction h with
  | init =>
    rw [ofCoupled_init]
    exact NetReachable.init
  | @stepA cfg hr a ha hp ih =>
    rw [ofCoupled_applyA]
    refine NetReachable.fire ih false a ?_ ?_ ?_
    · intro f hf
      have : C.fiberA = f := by simpa [pairRule] using hf
      subst this
      simpa [ofCoupled, toCoupled] using ha
    · intro e he
      exact absurd he (by simp [pairShape])
    · intro e _
      simpa [ofCoupled] using hp
  | @stepB cfg hr g b hp hb ih =>
    rw [ofCoupled_applyB (C := C)]
    refine NetReachable.fire ih true b ?_ ?_ ?_
    · intro f hf
      exact absurd hf (by simp [pairRule])
    · intro e _
      exact ⟨g, by simpa [ofCoupled] using hp, hb⟩
    · intro e he
      exact absurd he (by simp [pairShape])

/-- **SU7.0 — THE PROBE GATE.** The 2-node/1-edge network machine is the SU4b
interface machine: reachability corresponds exactly under the (bijective)
configuration correspondence. The network `Config` conservatively extends what is
built — the design passes its own mandatory gate (`04-network-config.md` §4/§5.6). -/
theorem pairNet_reachable_iff (C : CoupledFiber) (cfg : NetConfig pairShape) :
    NetReachable (pairRule C) cfg ↔ Reachable C (toCoupled cfg) := by
  constructor
  · exact netReachable_toCoupled
  · intro h
    have := coupledReachable_ofCoupled h
    rwa [ofCoupled_toCoupled] at this

/-- **The transported law**: every reachable probe configuration carries a balanced
edge ledger — SU4b's `issued = consumed + pending`, per edge (SU6b's shape), read
through the probe correspondence. -/
theorem pairNet_balanced {C : CoupledFiber} {cfg : NetConfig pairShape}
    (h : NetReachable (pairRule C) cfg) :
    (cfg.edge ()).issued = (cfg.edge ()).consumed + (cfg.edge ()).pending.getD 0 :=
  reachable_balanced (netReachable_toCoupled h)

/-! ## 6. Demo — SU4b's ragged run, executed on the network machine -/

/-- The two-round run of `InterfaceBalance.lean`, as network firings: A fires 1
(grant 3 issued), B fires 2 (consumed), A fires 0, B fires 1 — same ledger. -/
def raggedNetRun : NetConfig pairShape :=
  fire (pairRule raggedFiber)
    (fire (pairRule raggedFiber)
      (fire (pairRule raggedFiber)
        (fire (pairRule raggedFiber) (initNet pairShape) false 1)
        true 2)
      false 0)
    true 1

#eval toCoupled raggedNetRun
  -- ⟨[1, 0], [2, 1], none, 6, 6⟩ — identical to InterfaceBalance's recursive run

/-- The network run lands on exactly the SU4b run's configuration (kernel-checked). -/
theorem ragged_net_run :
    toCoupled raggedNetRun
      = applyB (applyA raggedFiber (applyB (applyA raggedFiber initConfig 1) 2) 0) 1 := rfl

/-- ...and its ledger is balanced (`6 = 6 + 0`, kernel-checked). -/
theorem ragged_net_run_balanced : Balanced (toCoupled raggedNetRun) := rfl

/-! ## Axiom audit -/

#print axioms pairNet_reachable_iff
#print axioms pairNet_balanced
#print axioms ragged_net_run

end FdrsFormal.Modes.SyntheticPlace
