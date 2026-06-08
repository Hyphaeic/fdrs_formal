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

# Adelic complex M1 — the two-place complex `S = {∞, p}` (L1)

The first honest "adelic" artifact: one quantity tracked at two places at once — its
continued fraction at `∞` and its Hensel digits at `p` — each an exact `ℤ` transducer
(M0/M0.5), advancing **independently** with **no shared clock**. The places are coupled
only by being two views of one quantity; they are *incommensurable timelines*
(the `ThreeLineMediator` philosophy), and the central theorem here makes that precise.

**Honest banner.** This is the two-place toy `S = {∞, p}`, **NOT** the adele ring
(handoff anti-confabulation). It establishes the coupling *mechanics* — heterogeneous
place-engines under one scheduler, advancing asynchronously and confluently. The
restricted product over all primes is M3; the conserved cross-place law (product formula)
is M4. Here there is no cross-place invariant yet — only the scheduling fabric.

**The one real theorem (scheduler-independence, as confluence).** The two place-steps
`stepArch`/`stepPadic` touch *disjoint* state, so they commute (`stepArch_stepPadic_comm`,
the local diamond). Lifting the diamond through iteration gives the confluence
(`run_counts`): **the resulting configuration depends only on how many steps each place
took, not on the interleaving.** Hence any two schedules with the same per-place step
counts yield identical configurations and identical emitted streams
(`run_eq_of_counts`). This — not a vague "order doesn't matter" — is the formal content
of *no coerced common clock*: places are independent timelines, and the result is
determinate regardless of scheduling.

**No floats (NF1–NF3, by construction).** Every `PlaceState` holds an exact `ℤ` ledger,
an emitted stream of `ℤ` digits, and a buffered `ℤ` input stream; no `ℝ`/`ℚ_p` value is
ever materialized (NF1/NF2), and `step` is always taken at an *explicit* place — there is
no shared global counter (NF3). The emitted streams only ever grow (`step_emitted_prefix`).

Leaf module (imports M0.5). No `sorry`; axiom-clean.
-/
import FdrsFormal.Modes.Adelic.PlaceEngine

namespace FdrsFormal.Modes.Adelic

open FdrsFormal.Modes.VariableRadix

/-! ## 1. Per-place state and its step -/

/-- Per-place transducer state: the exact `ℤ` ledger `L`, the emitted output-digit stream
(the quantity's expansion at this place so far), and the buffered input digits. No `ℝ` or
`ℚ_p` value is ever stored — only `ℤ` ledgers and `ℤ` digit streams (NF1/NF2). -/
structure PlaceState (L : Type) where
  ledger : L
  emitted : List ℤ
  pending : List ℤ

/-- One step of a single place: emit the forced digit when `ready` (append it, advance the
ledger), else absorb the next pending input digit, else idle. The per-place driver of
M0.5, carrying the emitted/pending streams. -/
def PlaceState.step {L : Type} (E : PlaceEngine L) (s : PlaceState L) : PlaceState L :=
  if E.ready s.ledger then
    { s with emitted := s.emitted ++ [E.candidate s.ledger],
             ledger := E.emit (E.candidate s.ledger) s.ledger }
  else
    match s.pending with
    | d :: ds => { s with ledger := E.absorb d s.ledger, pending := ds }
    | [] => s

/-- **NF2 / monotone streams.** A place step only ever *extends* the emitted stream — the
old output is a prefix of the new. (Used for the "prefix-equal streams" reading of
confluence.) -/
theorem PlaceState.step_emitted_prefix {L : Type} (E : PlaceEngine L) (s : PlaceState L) :
    s.emitted <+: (s.step E).emitted := by
  unfold PlaceState.step
  split
  · exact List.prefix_append _ _
  · split
    · exact List.prefix_rfl
    · exact List.prefix_rfl

/-! ## 2. The two-place configuration and its place-steps -/

/-- The two-place adelic configuration `S = {∞, p}`: one transducer per place. The places
advance independently — there is no shared clock field (NF3). A genuine *toy*: two places,
not the adele ring. -/
structure AdelicConfig where
  arch : PlaceState RemainderState
  padic : PlaceState PadicLedger

/-- Advance the Archimedean place (`∞`) one step; the p-adic place is untouched. -/
def AdelicConfig.stepArch (cfg : AdelicConfig) : AdelicConfig :=
  { cfg with arch := cfg.arch.step archEngine }

/-- Advance the p-adic place (`p`) one step; the Archimedean place is untouched. -/
def AdelicConfig.stepPadic (p : ℕ) [Fact p.Prime] (cfg : AdelicConfig) : AdelicConfig :=
  { cfg with padic := cfg.padic.step (padicEngine p) }

/-! ## 3. Scheduler-independence: the local diamond and confluence -/

/-- **The local diamond.** Stepping the two places commutes — they touch disjoint state
(`arch` vs. `padic`), so the order is irrelevant. This is the formal seed of "places are
independent timelines / no global clock." -/
theorem AdelicConfig.stepArch_stepPadic_comm (p : ℕ) [Fact p.Prime] (cfg : AdelicConfig) :
    (cfg.stepPadic p).stepArch = cfg.stepArch.stepPadic p := rfl

/-- The Archimedean step commutes with *any number* of p-adic steps (the diamond lifted
through iteration). -/
theorem AdelicConfig.stepArch_iterate_padic (p : ℕ) [Fact p.Prime] (m : ℕ)
    (cfg : AdelicConfig) :
    ((AdelicConfig.stepPadic p)^[m] cfg).stepArch
      = (AdelicConfig.stepPadic p)^[m] cfg.stepArch := by
  induction m generalizing cfg with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        ← AdelicConfig.stepArch_stepPadic_comm, ih]

/-- Run a schedule: `true` advances `∞`, `false` advances `p`. The asynchronous,
non-blocking scheduler over the two places. -/
def AdelicConfig.run (p : ℕ) [Fact p.Prime] (cfg : AdelicConfig) (sched : List Bool) :
    AdelicConfig :=
  sched.foldl (fun c b => if b then c.stepArch else c.stepPadic p) cfg

/-- **Confluence (the canonical form).** Running *any* schedule equals doing all the p-adic
steps first and all the Archimedean steps after — the configuration depends only on the
per-place step *counts*, not the interleaving. -/
theorem AdelicConfig.run_counts (p : ℕ) [Fact p.Prime] (cfg : AdelicConfig)
    (sched : List Bool) :
    cfg.run p sched
      = (AdelicConfig.stepArch)^[sched.count true]
          ((AdelicConfig.stepPadic p)^[sched.count false] cfg) := by
  induction sched generalizing cfg with
  | nil => rfl
  | cons b sched ih =>
    cases b with
    | true =>
      have hstep : cfg.run p (true :: sched) = cfg.stepArch.run p sched := rfl
      have ht : (true :: sched).count true = sched.count true + 1 := by simp
      have hf : (true :: sched).count false = sched.count false := by simp
      rw [hstep, ih, ht, hf, Function.iterate_succ_apply,
          AdelicConfig.stepArch_iterate_padic]
    | false =>
      have hstep : cfg.run p (false :: sched) = (cfg.stepPadic p).run p sched := rfl
      have ht : (false :: sched).count true = sched.count true := by simp
      have hf : (false :: sched).count false = sched.count false + 1 := by simp
      rw [hstep, ih, ht, hf, ← Function.iterate_succ_apply]

/-- **Scheduler-independence.** Any two schedules with the same number of steps at each
place produce *identical* configurations — hence identical emitted streams at every place.
The exact "no coerced common clock": the result is determinate, independent of the
interleaving. -/
theorem AdelicConfig.run_eq_of_counts (p : ℕ) [Fact p.Prime] (cfg : AdelicConfig)
    (s₁ s₂ : List Bool)
    (ht : s₁.count true = s₂.count true) (hf : s₁.count false = s₂.count false) :
    cfg.run p s₁ = cfg.run p s₂ := by
  rw [AdelicConfig.run_counts, AdelicConfig.run_counts, ht, hf]

/-! ## 4. Demo — one quantity, two coupled exact streams, scheduler-independent -/

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- A two-place configuration: the p-adic place runs the Demo B map `(3x+2)/(5x+1)` over
`ℤ₅` on the Hensel digits of `2/3`; the Archimedean place runs the single-stream `∞`
ledger on a CF input. Two exact `ℤ` transducers, one configuration. -/
def demoConfig : AdelicConfig where
  arch := { ledger := RemainderState.init, emitted := [], pending := [3, 1, 4, 1, 5, 9] }
  padic := { ledger := ⟨3, 2, 5, 1⟩, emitted := [], pending := [4, 1, 3, 1, 3, 1, 3, 1] }

-- The p-adic stream emitted by the complex (= Hensel digits of M(2/3) = 12/13):
#eval (demoConfig.run 5 (List.replicate 30 true ++ List.replicate 30 false)).padic.emitted
-- The Archimedean stream emitted by the complex:
#eval (demoConfig.run 5 (List.replicate 30 true ++ List.replicate 30 false)).arch.emitted

-- Scheduler-independence, concretely: a different interleaving with the same per-place
-- counts yields the SAME emitted streams (both booleans print `true`) — `run_eq_of_counts`.
#eval (demoConfig.run 5 (List.replicate 30 true ++ List.replicate 30 false)).padic.emitted
        == (demoConfig.run 5 (List.replicate 30 false ++ List.replicate 30 true)).padic.emitted
#eval (demoConfig.run 5 (List.replicate 30 true ++ List.replicate 30 false)).arch.emitted
        == (demoConfig.run 5 (List.replicate 30 false ++ List.replicate 30 true)).arch.emitted

end FdrsFormal.Modes.Adelic
