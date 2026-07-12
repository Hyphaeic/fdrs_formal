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

# Synthetic place complex SU7.6 — network liveness (the last row)

`04-network-config.md` §4 row SU7.6: *network liveness — certificates guaranteed to
fire under non-blocking + graded dependencies.* Phase 14 §14.7's standing honesty
was "every certificate is sound, none is yet guaranteed to fire." This module
completes the row in its honest shape — liveness at both scales of the machine,
with the certificate guarantee in exactly the conditional form the corpus's own
scope notes demand:

* **Progress (between steps)** — `Run`/`liveRun`/`nonBlocking_progress`: a
  non-blocking network extends to an **infinite run** from the initial
  configuration (each step fired at an enabled node), and `no_deadlock`: no
  reachable configuration is stuck. Couplability (SU7.3) is exactly the machine's
  between-step liveness.
* **No wedging (within steps)** — via SU7.1's `wellFormed_deadlock_free`: graded
  dependency declarations never wedge a firing internally. `network_live` packages
  both: a non-blocking, well-formed network lives at both scales.
* **Certificates fire when forced** — `emitNow_fires`: a singleton candidate set
  makes the trap ACTUALLY emit (the executable driver fires, not merely "would be
  sound"), and `network_trap_fires`: on the tracked machine, a forced node both
  fires and is sound (SU7.4's `network_trap_sound` composed). Firing is guaranteed
  exactly when the grammar forces.

**Honest scope — what "guaranteed to fire" can and cannot mean.** MAKING a node's
grammar force (driving its ledger to a singleton candidate set) is
instance-dependent by design — SU2's own scope note ("no claim of liveness; that is
instance-dependent, exactly as `pole_exists` gates the p-adic engine"). The general
guarantee therefore factors, and each factor has its owner: **progress** (proven
here, from SU7.3), **fairness** of the schedule (the §14.7 bridge, classical,
cited — open), and the **instance forcing bound** (a declared grammar property,
e.g. the golden-mean's forced zero after `1`). This module proves the machine-side
factors and names the instance-side hypothesis; it does not smuggle the
composition. `liveRun` uses choice (the run selects among enabled steps) — the
selection is the scheduler's freedom, and by SU7.5's diamond, independent
selections commute. Leaf module over SU7.3 + SU7.4. No `sorry`; axiom-clean.
-/
import FdrsFormal.Modes.SyntheticPlace.NetworkTraps
import FdrsFormal.Modes.SyntheticPlace.NetworkDeterminacy

namespace FdrsFormal.Modes.SyntheticPlace

open TransferStructure

variable {N : NetworkShape} {M : Type*} [AddCommMonoid M] [DecidableEq N.V] [Fintype N.E]

/-! ## 1. Progress: a non-blocking network runs forever -/

/-- An infinite run of the machine: starts at the initial configuration, every step
fires an enabled node. -/
def Run (R : ComplexRule N M) (f : ℕ → CConfig N M) : Prop :=
  f 0 = initC N M ∧
  ∀ n, ∃ v d, Enabled R (f n) v d ∧ f (n + 1) = fireC R (f n) v d

/-- Every stage of a run is reachable. -/
theorem Run.reachable {R : ComplexRule N M} {f : ℕ → CConfig N M} (h : Run R f) :
    ∀ n, ComplexReachable R (f n) := by
  intro n
  induction n with
  | zero => rw [h.1]; exact ComplexReachable.init
  | succ n ih =>
    obtain ⟨v, d, henb, hstep⟩ := h.2 n
    rw [hstep]
    exact henb.fire ih

/-- The canonical live run of a non-blocking network (choice selects among enabled
steps — the scheduler's freedom; by SU7.5, independent selections commute). -/
noncomputable def liveRun (R : ComplexRule N M) (h : NonBlocking R) :
    ℕ → {cfg : CConfig N M // ComplexReachable R cfg}
  | 0 => ⟨initC N M, ComplexReachable.init⟩
  | n + 1 =>
    let p := liveRun R h n
    let hvd := h p.1 p.2
    ⟨fireC R p.1 (Classical.choose hvd) (Classical.choose (Classical.choose_spec hvd)),
      (Classical.choose_spec (Classical.choose_spec hvd)).fire p.2⟩

/-- **SU7.6, progress**: a non-blocking network extends to an infinite run — the
machine never jams between steps. -/
theorem nonBlocking_progress {R : ComplexRule N M} (h : NonBlocking R) :
    ∃ f : ℕ → CConfig N M, Run R f := by
  refine ⟨fun n => (liveRun R h n).1, rfl, fun n => ?_⟩
  have hvd := h (liveRun R h n).1 (liveRun R h n).2
  exact ⟨Classical.choose hvd, Classical.choose (Classical.choose_spec hvd),
    (Classical.choose_spec (Classical.choose_spec hvd)), rfl⟩

/-- **No reachable deadlock**: non-blocking means exactly that no reachable
configuration is stuck. -/
theorem no_deadlock {R : ComplexRule N M} (h : NonBlocking R) :
    ¬ ∃ cfg, ComplexReachable R cfg ∧ ∀ v d, ¬ Enabled R cfg v d := by
  rintro ⟨cfg, hr, hstuck⟩
  obtain ⟨v, d, henb⟩ := h cfg hr
  exact hstuck v d henb

/-- **SU7.6 — the network lives at both scales**: between steps (an infinite run
exists — couplability) and within steps (every declared dependency order is
deadlock-free — graded dependencies, Phase 8's certificate via SU7.1).

**fdrs.md**: Theorem 110 (network liveness — the factored guarantee) [§14.12 · Phase 14] -/
theorem network_live {R : ComplexRule N M} (hnb : NonBlocking R) (hwf : WellFormed R) :
    (∃ f : ℕ → CConfig N M, Run R f) ∧
    ∀ v, FdrsFormal.Composition.DeadlockAnalysis.isDeadlockFree (R.deps v) :=
  ⟨nonBlocking_progress hnb, wellFormed_deadlock_free hwf⟩

/-! ## 2. Certificates fire when forced -/

variable {Qf : N.V → Type*} {Df : N.V → Type*} {Of : N.V → Type*}
variable [∀ v, DecidableEq (Qf v)] [∀ v, Fintype (Df v)] [∀ v, DecidableEq (Of v)]
variable [∀ v, LinearOrder (Of v)]

/-- A forced grammar ACTUALLY fires: a singleton candidate set makes the executable
driver emit — not merely "would be sound if it emitted". -/
theorem emitNow_fires {Q D O : Type*} [DecidableEq Q] [Fintype D] [DecidableEq O]
    [LinearOrder O] (T : TransferStructure Q D O) {S : Finset Q} {o : O}
    (h : T.candidates S = {o}) : T.emitNow S = some o := by
  unfold TransferStructure.emitNow
  rw [if_pos (T.ready_iff.mpr ⟨o, h⟩), h]
  simp

/-- **SU7.6 — certificates guaranteed to fire when forced, on the network**: at any
tracked configuration whose node-`v` ledger forces a unique observation, the trap
FIRES (`emitNow = some o`) and the emission is SOUND for every admissible tail from
every ledger state (SU7.4 composed). Driving the ledger to a forced state is the
progress + fairness + instance-forcing composition named in the banner. -/
theorem network_trap_fires {E : NodeEngines N M Qf Df Of} {R : ComplexRule N M}
    {tc : Tracked N M Qf} (hr : TrackedReachable E R tc) (v : N.V) {o : Of v}
    (hforced : (E.T v).candidates (tc.unc v) = {o}) :
    (E.T v).emitNow (tc.unc v) = some o ∧
    ∀ q ∈ tc.unc v, ∀ x : ℕ → Df v, (E.T v).AdmissibleRun q x 1 →
      (E.T v).obs ((E.T v).runState q x 1) = o :=
  have hfire := emitNow_fires (E.T v) hforced
  ⟨hfire, network_trap_sound hr v hfire⟩

/-! ## Axiom audit -/

#print axioms nonBlocking_progress
#print axioms no_deadlock
#print axioms network_live
#print axioms emitNow_fires
#print axioms network_trap_fires

end FdrsFormal.Modes.SyntheticPlace
