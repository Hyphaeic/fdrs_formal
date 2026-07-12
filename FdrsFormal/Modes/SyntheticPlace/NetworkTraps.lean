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

# Synthetic place complex SU7.4 — per-node traps on the network (SU2 transported)

`04-network-config.md` §4 row SU7.4: *per-node trap soundness on the network —
uncertainty sets per node, windows as the observation maps.* Each node runs an SU2
engine (`TransferStructure`) over its own substrate; its **uncertainty set** is the
ledger of substrate states consistent with what it has observed; and what it
observes of the network is read **through its window** — a declared map from the
in-flight grants (and the fired digit) to an observation. The module delivers:

* **The tracked machine** — `Tracked` pairs a network configuration with per-node
  uncertainty sets; `trackedFire` fires the SU7.1 machine and **refines** the firing
  node's ledger by its window observation (`refineSet`: the admissible one-step
  image filtered by the observation — SU2's driver step, per node);
  `TrackedReachable` runs it under the SU7.3 `Enabled` guards, and
  **`tracked_base`**: tracking is conservative — the base projection is exactly the
  SU7.1 machine.
* **Consistency** — `consistency_step`: refinement never loses the true substrate
  state when the window observation matches the true transition (node-local), and
  **`tracked_consistent_fire`**: the network form — a consistent truth assignment
  stays consistent through a tracked firing (only the firing node refines; the
  window-matching hypothesis is exactly "the window is a faithful observation map").
* **THE ROW THEOREM** — **`network_trap_sound`**: if a node's trap fires on its
  current uncertainty set (`emitNow = some o`), then **every** admissible tail from
  **every** state of that set observes `o` after one step — `trap_sound` and
  `emitNow_sound` **transported verbatim** (Theorem 86, per node, on the network).
  The transport being verbatim is the point: the network adds bookkeeping, never
  new trust.

**Honest scope.** The window (`window v pending d`) may read the whole pending map;
*which* grants a lawful window may read is the SU6c/SU6c′ accountability boundary —
declared per instance, not policed here. Consistency is delivered per step
(compositional); the trajectory-level bridge from infinite network runs to total
per-node substrate runs needs the fairness hypothesis Phase 14 §14.7 records as
open (SU7.5 territory). Nothing here makes certificates FIRE (liveness is SU7.6).
SU2's golden-mean demos instantiate per node unchanged and are not duplicated. The
experiments' Selection/graded-command artifacts (fdrs-sensor-fusion,
fdrs-theory-expansion) are the validated external mirrors of exactly this
composite. Leaf module over SU7.3 + SU2. No `sorry`; axiom-clean.
-/
import FdrsFormal.Modes.SyntheticPlace.NetworkCouplability
import FdrsFormal.Modes.SyntheticPlace.AdmissibilityTrap

namespace FdrsFormal.Modes.SyntheticPlace

open TransferStructure

variable {N : NetworkShape} {M : Type*} [AddCommMonoid M] [DecidableEq N.V] [Fintype N.E]
variable {Qf : N.V → Type*} {Df : N.V → Type*} {Of : N.V → Type*}
variable [∀ v, DecidableEq (Qf v)] [∀ v, Fintype (Df v)] [∀ v, DecidableEq (Of v)]
variable [∀ v, LinearOrder (Of v)]

/-! ## 1. Per-node engines: uncertainty sets and windows as observation maps -/

/-- The per-node engine assignment: each node's substrate (`T v`), its initial
uncertainty ledger (`S0 v`), and its **window** — the declared observation map from
the network's in-flight grants and the fired digit to the node's observation
alphabet. -/
structure NodeEngines (N : NetworkShape) (M : Type*) [AddCommMonoid M]
    (Qf : N.V → Type*) (Df : N.V → Type*) (Of : N.V → Type*) where
  T : (v : N.V) → TransferStructure (Qf v) (Df v) (Of v)
  S0 : (v : N.V) → Finset (Qf v)
  window : (v : N.V) → (N.E → Option M) → ℕ → Of v

/-- SU2's driver refinement, named: the admissible one-step image, filtered by the
observation. -/
def refineSet {Q D O : Type*} [DecidableEq Q] [Fintype D] [DecidableEq O]
    (T : TransferStructure Q D O) (S : Finset Q) (o : O) : Finset Q :=
  (T.stepSet S).filter fun q => T.obs q = o

/-- Refinement never loses the truth: if the true state is in the ledger and the
true transition's observation is `o`, the true next state is in the refined ledger. -/
theorem consistency_step {Q D O : Type*} [DecidableEq Q] [Fintype D] [DecidableEq O]
    {T : TransferStructure Q D O} {S : Finset Q} {q : Q} {d : D}
    (hq : q ∈ S) (hall : T.allowed q d = true) :
    T.step q d ∈ refineSet T S (T.obs (T.step q d)) :=
  Finset.mem_filter.mpr ⟨T.mem_stepSet.mpr ⟨q, hq, d, hall, rfl⟩, rfl⟩

/-! ## 2. The tracked machine -/

/-- A tracked configuration: the network state plus one uncertainty ledger per node. -/
structure Tracked (N : NetworkShape) (M : Type*) (Qf : N.V → Type*) where
  base : CConfig N M
  unc : (v : N.V) → Finset (Qf v)

/-- Fire the network at `v` and refine `v`'s ledger by its window observation of
the pending grants and the fired digit. Other nodes' ledgers are untouched. -/
def trackedFire (E : NodeEngines N M Qf Df Of) (R : ComplexRule N M)
    (tc : Tracked N M Qf) (v : N.V) (d : ℕ) : Tracked N M Qf where
  base := fireC R tc.base v d
  unc := Function.update tc.unc v
    (refineSet (E.T v) (tc.unc v) (E.window v (fun e => (tc.base.edge e).pending) d))

/-- Tracked reachability: the SU7.1 machine under the SU7.3 guards, with per-node
ledger refinement riding along. -/
inductive TrackedReachable (E : NodeEngines N M Qf Df Of) (R : ComplexRule N M) :
    Tracked N M Qf → Prop
  | init : TrackedReachable E R ⟨initC N M, E.S0⟩
  | fire {tc : Tracked N M Qf} (hr : TrackedReachable E R tc) (v : N.V) (d : ℕ)
      (henb : Enabled R tc.base v d) :
      TrackedReachable E R (trackedFire E R tc v d)

omit [∀ v, LinearOrder (Of v)] in
/-- **Tracking is conservative**: the base projection of the tracked machine is
exactly the SU7.1 machine. -/
theorem tracked_base {E : NodeEngines N M Qf Df Of} {R : ComplexRule N M}
    {tc : Tracked N M Qf} (h : TrackedReachable E R tc) :
    ComplexReachable R tc.base := by
  induction h with
  | init => exact ComplexReachable.init
  | fire hr v d henb ih => exact henb.fire ih

/-! ## 3. Consistency through a tracked firing -/

omit [Fintype N.E] [∀ v, LinearOrder (Of v)] in
/-- **Consistency is preserved by tracked firing**: if a truth assignment lies in
every ledger, and the firing node's true substrate transition is admissible with
its observation matching the window's reading (the window is a faithful observation
map), then the updated truth lies in every updated ledger. -/
theorem tracked_consistent_fire {E : NodeEngines N M Qf Df Of} {R : ComplexRule N M}
    (tc : Tracked N M Qf) (v : N.V) (d : ℕ)
    {truth : ∀ u, Qf u} (hcons : ∀ u, truth u ∈ tc.unc u)
    {x0 : Df v} (hall : (E.T v).allowed (truth v) x0 = true)
    (hobs : (E.T v).obs ((E.T v).step (truth v) x0)
      = E.window v (fun e => (tc.base.edge e).pending) d) :
    ∀ u, Function.update truth v ((E.T v).step (truth v) x0) u
      ∈ (trackedFire E R tc v d).unc u := by
  intro u
  by_cases hu : u = v
  · subst hu
    simp only [trackedFire, Function.update_self]
    exact hobs ▸ consistency_step (hcons u) hall
  · simp only [trackedFire, Function.update_of_ne hu]
    exact hcons u

/-! ## 4. THE ROW THEOREM — per-node trap soundness on the network -/

/-- **SU7.4 — per-node trap soundness on the network** (Theorem 86, transported
verbatim): if node `v`'s trap fires on its current uncertainty ledger, then every
admissible substrate tail from every state of that ledger observes the emitted
symbol after one step. The network adds bookkeeping (the tracked machine), never
new trust — the certificate is SU2's, unchanged.

**fdrs.md**: Theorem 108 (per-node traps on the network — Theorem 86 transported verbatim) [§14.12 · Phase 14] -/
theorem network_trap_sound {E : NodeEngines N M Qf Df Of} {R : ComplexRule N M}
    {tc : Tracked N M Qf} (_ : TrackedReachable E R tc) (v : N.V) {o : Of v}
    (hemit : (E.T v).emitNow (tc.unc v) = some o) :
    ∀ q ∈ tc.unc v, ∀ x : ℕ → Df v, (E.T v).AdmissibleRun q x 1 →
      (E.T v).obs ((E.T v).runState q x 1) = o :=
  fun _ hq _ hx => (E.T v).trap_sound ((E.T v).emitNow_sound hemit) hq hx

/-! ## Axiom audit -/

#print axioms consistency_step
#print axioms tracked_base
#print axioms tracked_consistent_fire
#print axioms network_trap_sound

end FdrsFormal.Modes.SyntheticPlace
