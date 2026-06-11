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

# Synthetic place complex SU2 — the admissibility trap (the third certificate)

The emission certificate for engines on designed gauges
(`docs/synthetic-place/00-thesis.md` §1 correction 1; roadmap `01-build-roadmap.md`
§SU2). The corpus has two emission certificates:

* the **order trap** — Archimedean: the candidate digit is verified by four corner
  inequalities, sound for every tail in `[1,∞)²` (`BihomographicSound.emit_traps`);
* the **congruence trap** — p-adic: the candidate residue is verified mod `p`, sound
  for every tail in `ℤ_p` (`PadicEmitTraps.padic_emit_traps`).

This file adds the third sibling, native to synthetic places where there is no order
and no ring — only an admissibility structure:

* the **admissibility trap**: the engine's ledger is an *uncertainty set* `S` of
  transfer states (the states consistent with what has been observed); the candidate
  symbol is **forced** when every admissible one-step continuation of every state in
  `S` produces the same observation. The check is a finite computation on the
  transfer-state set (`ready : Bool` — decidable by construction); the soundness
  theorem (`trap_sound`, `trap_sound_all_tails`) is quantified over **all admissible
  tails from all consistent states**. Emission = certified localization: a symbol is
  emitted only when the substrate's grammar forces it (thesis ledger item 4 —
  transductive, not generative).

**Demo.** The golden-mean (Zeckendorf) structure: after a `1` the next observation is
*forced* to `0` — `ready {1} = true`, candidate `0` — while from state `0` both
continuations are admissible and the engine must refine (`ready {0} = false`). The
forced transition is exactly `SubshiftParry`'s deterministic kernel row
(`goldenP 1 0 = 1`), now as a certified emission rather than a measure statement.

**Honest scope.** One-step forcing iterated by a fuel driver; no claim of liveness
(that `ready` ever fires — that is instance-dependent, exactly as `pole_exists` gates
the p-adic engine), no coupling (SU1×SU2 composite is post-SU3), no conserved
quantity (thesis §3 — open). Leaf module. No `sorry`; axiom-clean; `decide`-free
proofs, executable `Bool` gates.
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort

namespace FdrsFormal.Modes.SyntheticPlace

/-! ## 1. Transfer structures (the finite admissibility substrate) -/

/-- **A transfer structure**: finite-state admissibility grammar with observations.
`step` moves the substrate, `allowed` gates which digits are admissible from each
state, `obs` is what a place *sees* of a state (the projection — a "synthetic place"
observes the substrate through `obs`). -/
structure TransferStructure (Q D O : Type*) where
  /-- the substrate transition. -/
  step : Q → D → Q
  /-- the admissibility gate: which digits the grammar allows from each state. -/
  allowed : Q → D → Bool
  /-- the observation a place reads off a state. -/
  obs : Q → O

namespace TransferStructure

variable {Q D O : Type*} [DecidableEq Q] [Fintype D] [DecidableEq O]
variable (T : TransferStructure Q D O)

/-! ## 2. Runs and admissible tails -/

/-- The substrate state after `n` steps of the tail `x` from `q`. -/
def runState (q : Q) (x : ℕ → D) : ℕ → Q
  | 0 => q
  | n + 1 => T.step (runState q x n) (x n)

/-- The tail `x` is admissible from `q` for `n` steps: every step is allowed. -/
def AdmissibleRun (q : Q) (x : ℕ → D) : ℕ → Prop
  | 0 => True
  | n + 1 => AdmissibleRun q x n ∧ T.allowed (runState T q x n) (x n) = true

/-- Admissibility is downward-closed in the horizon. -/
theorem admissibleRun_mono {q : Q} {x : ℕ → D} {m n : ℕ} (hmn : m ≤ n)
    (h : T.AdmissibleRun q x n) : T.AdmissibleRun q x m := by
  induction n with
  | zero => have hm : m = 0 := Nat.le_zero.mp hmn; subst hm; exact h
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hmn with rfl | hlt
    · exact h
    · exact ih (Nat.lt_succ_iff.mp hlt) h.1

/-! ## 3. The uncertainty ledger and the trap -/

/-- The admissible one-step image of an uncertainty set: every state reachable from
some consistent state by some allowed digit. This is the ledger's *refinement* step —
emission descends one level of the synthetic basis. -/
def stepSet (S : Finset Q) : Finset Q :=
  S.biUnion fun q => (Finset.univ.filter fun d => T.allowed q d).image (T.step q)

theorem mem_stepSet {S : Finset Q} {q' : Q} :
    q' ∈ T.stepSet S ↔ ∃ q ∈ S, ∃ d, T.allowed q d = true ∧ T.step q d = q' := by
  simp [stepSet]

/-- The candidate observations: what the place could see after one admissible step. -/
def candidates (S : Finset Q) : Finset O := (T.stepSet S).image T.obs

/-- **The trap gate** (executable): the next observation is forced — exactly one
candidate survives. Decidable on the finite transfer-state set by construction. -/
def ready (S : Finset Q) : Bool := decide ((T.candidates S).card = 1)

theorem ready_iff {S : Finset Q} : T.ready S = true ↔ ∃ o, T.candidates S = {o} := by
  simp [ready, Finset.card_eq_one]

/-! ## 4. SU2 — soundness of the admissibility trap -/

/-- **SU2 — THE ADMISSIBILITY TRAP (one-step soundness).** If the candidate set is the
singleton `{o}`, then EVERY admissible tail from EVERY state of the uncertainty set
observes `o` after one step. The finite `Bool` check certifies a universally
quantified forcing — the third sibling of the order trap and the congruence trap,
with admissibility playing the role order played at `∞` and congruence played at `p`. -/
theorem trap_sound {S : Finset Q} {o : O} (h : T.candidates S = {o})
    {q : Q} (hq : q ∈ S) {x : ℕ → D} (hx : T.AdmissibleRun q x 1) :
    T.obs (T.runState q x 1) = o := by
  have hmem : T.obs (T.step q (x 0)) ∈ T.candidates S := by
    apply Finset.mem_image_of_mem
    rw [mem_stepSet]
    exact ⟨q, hq, x 0, hx.2, rfl⟩
  rw [h] at hmem
  exact Finset.mem_singleton.mp hmem

/-- The trap, quantified over all admissible tails of every horizon ≥ 1: the emitted
symbol never hallucinates, regardless of how the substrate continues. -/
theorem trap_sound_all_tails {S : Finset Q} {o : O} (h : T.candidates S = {o}) :
    ∀ q ∈ S, ∀ x : ℕ → D, ∀ n, 1 ≤ n → T.AdmissibleRun q x n →
      T.obs (T.runState q x 1) = o :=
  fun _ hq _ _ hn hx => T.trap_sound h hq (T.admissibleRun_mono hn hx)

/-! ## 5. The driver — emit only when forced -/

variable [LinearOrder O]

/-- The forced symbol, if any (`none` when the grammar does not force — the engine
must refine instead; thesis ledger item 4). The `LinearOrder` is only a computable
way to read the element out of the singleton candidate set. -/
def emitNow (S : Finset Q) : Option O :=
  if T.ready S then ((T.candidates S).sort (· ≤ ·)).head? else none

theorem emitNow_sound {S : Finset Q} {o : O} (h : T.emitNow S = some o) :
    T.candidates S = {o} := by
  unfold emitNow at h
  split at h
  · rename_i hready
    obtain ⟨o', ho'⟩ := T.ready_iff.mp hready
    rw [ho'] at h ⊢
    simpa [Finset.sort_singleton] using h
  · exact absurd h (by simp)

/-- The fuel driver: emit while forced, refining the uncertainty set each step. -/
def emitDriver (S : Finset Q) : ℕ → List O
  | 0 => []
  | fuel + 1 =>
    match T.emitNow S with
    | some o => o :: emitDriver (T.stepSet S) fuel
    | none => []

/-- **Driver soundness (first emission).** Whatever the driver emits first is correct
for every admissible tail from every consistent state. -/
theorem emitDriver_head_sound {S : Finset Q} {fuel : ℕ} {o : O} {rest : List O}
    (h : T.emitDriver S (fuel + 1) = o :: rest)
    {q : Q} (hq : q ∈ S) {x : ℕ → D} (hx : T.AdmissibleRun q x 1) :
    T.obs (T.runState q x 1) = o := by
  unfold emitDriver at h
  cases hemit : T.emitNow S with
  | none => rw [hemit] at h; simp at h
  | some o' =>
    rw [hemit] at h
    have ho : o' = o := by
      have h' := congrArg List.head? h
      simpa using h'
    subst ho
    exact T.trap_sound (T.emitNow_sound hemit) hq hx

end TransferStructure

/-! ## 6. Demo — the golden-mean grammar: Zeckendorf's forced zero, certified -/

/-- The golden-mean (no `11`) transfer structure: state = last digit, observation =
state. `SubshiftParry`'s subshift, as an admissibility substrate. -/
def goldenTransfer : TransferStructure (Fin 2) (Fin 2) (Fin 2) where
  step _ d := d
  allowed q d := !(q == 1 && d == 1)
  obs q := q

-- After a `1`, the next observation is FORCED to `0` (Zeckendorf), certified:
#eval goldenTransfer.ready {1}                       -- true
#eval (goldenTransfer.candidates {1}).sort (· ≤ ·)   -- [0]
-- From `0`, the grammar forces nothing — the engine must refine, not emit:
#eval goldenTransfer.ready {0}                       -- false
#eval (goldenTransfer.candidates {0}).sort (· ≤ ·)   -- [0, 1]
-- The driver emits exactly the one forced symbol, then stops:
#eval goldenTransfer.emitDriver {1} 5                -- [0]
-- Total uncertainty (both states possible): nothing is forced:
#eval goldenTransfer.ready ({0, 1} : Finset (Fin 2)) -- false

end FdrsFormal.Modes.SyntheticPlace
