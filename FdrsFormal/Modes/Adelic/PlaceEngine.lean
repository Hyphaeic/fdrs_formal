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

# Adelic complex M0.5 — the place-generic engine interface & scheduler

One quantity is tracked at many *places*, each running its native numeration with its own
ledger algebra: continued fractions at `∞` (`RemainderState`, `HomographicCarry.lean`),
Hensel digits at each prime `p` (`PadicLedger`, M0). They differ in their recurrence and
their emission certificate (order trap vs. congruence), but they share one **scheduling
shape**: *emit the forced digit when ready, else absorb the next input digit.* This file
factors that shape into a place-generic interface so the scheduler is written once and run
at any place.

`PlaceEngine L` is a record of the four scheduling operations on a ledger type `L`
(`absorb`, `emit`, `candidate`, `ready`); `PlaceEngine.run` is the engine-generic
single-stream driver. Two instances are supplied:

* `archEngine` — the Archimedean place (`∞`): the single-stream Gosper ledger
  `RemainderState` (`step`/`emit`/`emitDigit`/`emitReady`).
* `padicEngine p` — the p-adic place: the M0 Hensel ledger `PadicLedger`
  (`absorb`/`emit`/`candidate`/`ready`).

**Soundness is deliberately *separated from* scheduling** — exactly the corpus's own design
(`BihomographicDriver`: *"the emission correctness is the proven `emit_traps`; the
scheduling is engineering; the two are cleanly separable"*). So `PlaceEngine` carries only
the executable operations; the *certificates* live beside it as the proven per-place
theorems: `padic_emit_traps` (✅, M0d) at `p`, and `emitReady_traps` (✅, the two-stream
four-corner trap) at `∞` — with a single-stream `∞` floor-trap a noted follow-up (the
corpus proves the bihomographic trap; `RemainderState.emitDigit` uses truncating `/`, so a
clean single-stream statement carries the `fdiv`-vs-`/` caveat the handoff flags).

This is M0.5 of the adelic roadmap (`docs/adelic-machine/05`): the refactor that lets the
M1 two-place complex drive heterogeneous place-engines through one scheduler. Leaf module
(imports the `∞` ledger + the M0 `p` ledger). No `sorry`; axiom-clean.
-/
import FdrsFormal.Modes.VariableRadix.HomographicCarry
import FdrsFormal.Modes.Adelic.PadicEmitTraps

namespace FdrsFormal.Modes.Adelic

open FdrsFormal.Modes.VariableRadix

/-- The place-generic **scheduling interface**: the four executable operations a place
engine exposes, on its ledger type `L`. Pure data — no order, no place-specific detail;
soundness lives outside as the per-place certificate theorems (this is the corpus's
scheduler/soundness separation, made into an interface). -/
structure PlaceEngine (L : Type) where
  /-- Read one input digit into the ledger. -/
  absorb : ℤ → L → L
  /-- Write one output digit, advancing the ledger. -/
  emit : ℤ → L → L
  /-- The proposed next output digit. -/
  candidate : L → ℤ
  /-- Decidable: is the next output digit forced? -/
  ready : L → Bool

namespace PlaceEngine

/-- The engine-generic **single-stream driver**: emit the forced digit when `ready`, else
absorb the next input digit, else halt (input exhausted). The non-blocking transducer
loop, abstracted over the place engine — it never mentions order, the floor, or a
congruence; each is hidden inside the engine's `ready`/`candidate`. This is the
single-stream sibling of the corpus `BihomographicDriver.run`, reusable at every place. -/
def run {L : Type} (E : PlaceEngine L) (s : L) (input : List ℤ) : ℕ → List ℤ
  | 0 => []
  | fuel + 1 =>
    if E.ready s then
      E.candidate s :: run E (E.emit (E.candidate s) s) input fuel
    else
      match input with
      | d :: ds => run E (E.absorb d s) ds fuel
      | [] => []

end PlaceEngine

/-- **The Archimedean place engine** (`∞`): the existing single-stream Gosper ledger
`RemainderState`. `absorb` is the CF read `step` (a partial quotient `≥ 1`); `emit`,
`candidate = emitDigit`, `ready = emitReady` are its homographic-carry duals. The proven
`∞` certificate is the four-corner `emitReady_traps` (✅). -/
def archEngine : PlaceEngine RemainderState where
  absorb := fun a r => r.step a.toNat
  emit := RemainderState.emit
  candidate := RemainderState.emitDigit
  ready := RemainderState.emitReady

/-- **The p-adic place engine** (`p`): the M0 single-stream Hensel ledger `PadicLedger`.
`absorb`/`emit` are the shift recurrence; `candidate` is the forced Hensel digit as its
integer residue in `{0,…,p−1}`; `ready` is the congruence gate. The proven `p` certificate
is `padic_emit_traps` (✅, M0d) — congruence, not order. -/
def padicEngine (p : ℕ) [Fact p.Prime] : PlaceEngine PadicLedger where
  absorb := PadicLedger.absorb (p : ℤ)
  emit := PadicLedger.emitStep (p : ℤ)   -- emit + reduceOnce: stay primitive so iteration works
  candidate := fun M => ((PadicLedger.candidate p M).val : ℤ)
  ready := PadicLedger.ready p

/-! ## Demos — the SAME generic runner drives both places (exact, no float) -/

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

-- p-adic place: the Demo B map `(3x+2)/(5x+1)` over `ℤ₅`, fed the Hensel digits of
-- `x = 2/3` (= `[4,1,3,1,3,…]`), emits the Hensel digits of `M(2/3) = 12/13` — which are
-- `[4,4,1,0,3,…]` (verified exactly by the scratch validator). All congruence, no float.
#eval PlaceEngine.run (padicEngine 5) ⟨3, 2, 5, 1⟩ [4, 1, 3, 1, 3, 1, 3, 1] 40

-- Archimedean place: the same generic runner drives the single-stream `∞` ledger
-- (`RemainderState`) — proving the scheduler is genuinely place-generic (a different
-- ledger type, a different emission rule, one driver). Output is exact `ℤ` CF data.
#eval PlaceEngine.run archEngine RemainderState.init [3, 1, 4, 1, 5, 9, 2] 40

end FdrsFormal.Modes.Adelic
