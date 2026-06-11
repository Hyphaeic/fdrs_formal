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

# Synthetic place complex SU4b — the interface balance law (carry accounting)

Second piece of the conservation arc (`docs/synthetic-place/00-thesis.md` §3): the
carry-accounting candidate, made a theorem. The coupled step of SU1 is run as a
two-place **stepped machine** with an explicit interface:

* an A-half-step appends an A-digit and **issues a grant** into the interface — the
  fiber capacity `fiberB sB (sA ++ [a])` that A's move opens for B (the "carry
  crossing the coupling", D6 convention);
* a B-half-step **consumes** the pending grant by choosing a digit below it.

The configuration carries the declared ledger (`issued`, `consumed`, `pending` — the
extended state of the thesis's conservation definition: no hidden memory). The law:

* **`reachable_balanced`** — PROP-128-SHAPE EXACTNESS: on every reachable
  configuration, `issued = consumed + pending` — Theorem 57's shape verbatim: *the
  residual is exactly the undelivered in-flight payload*. Every grant is accounted:
  consumed or still on the interface; nothing anonymous. The transfer rule τ of each
  half-step is the grant itself, read off the step's own data.
* **`reachable_consumed_le_issued`** — the obstruction reading: configurations with
  `consumed > issued` are unreachable. The charge separates.

**Honest scope.** The interface register has capacity one (an A-step requires the
interface empty) — the latency/Kahn discipline of `CoupledSystem.lean`'s `Coupling`,
inherited deliberately; richer interfaces (queues) are a later generalization. The
grant τ is *local to the step* but reads BOTH prefixes — whether it can be accounted
from one place alone is exactly the SU4c rigidity question (`ConservationRigidity.lean`).
This is a species-(iii) accounting law; it is NOT a product formula and is not
presented as one (thesis §3, ledger item 1). Leaf module over SU1. No `sorry`;
axiom-clean; fully executable.
-/
import FdrsFormal.Modes.SyntheticPlace.Composition

namespace FdrsFormal.Modes.SyntheticPlace

/-! ## 1. The two-place machine with a declared ledger -/

/-- A configuration of the coupled machine: the two prefixes, the in-flight grant on
the interface (`pending`), and the cumulative ledger (`issued`, `consumed`). The
ledger is part of the state by design — conservation laws may not use hidden memory. -/
structure CoupledConfig where
  sA : List ℕ
  sB : List ℕ
  /-- the grant currently on the interface: issued by A, not yet consumed by B. -/
  pending : Option ℕ
  /-- cumulative capacity issued across the interface. -/
  issued : ℕ
  /-- cumulative capacity consumed by B. -/
  consumed : ℕ
  deriving Repr, DecidableEq

/-- The initial configuration: empty prefixes, empty interface, zero ledger. -/
def initConfig : CoupledConfig := ⟨[], [], none, 0, 0⟩

/-- The A-half-step: append an A-digit and issue the grant it opens for B
(the carry crossing the coupling — note it reads BOTH prefixes). -/
def applyA (C : CoupledFiber) (cfg : CoupledConfig) (a : ℕ) : CoupledConfig :=
  { sA := cfg.sA ++ [a]
    sB := cfg.sB
    pending := some (C.fiberB cfg.sB (cfg.sA ++ [a]))
    issued := cfg.issued + C.fiberB cfg.sB (cfg.sA ++ [a])
    consumed := cfg.consumed }

/-- The B-half-step: consume the pending grant by choosing a digit below it. -/
def applyB (cfg : CoupledConfig) (b : ℕ) : CoupledConfig :=
  { sA := cfg.sA
    sB := cfg.sB ++ [b]
    pending := none
    issued := cfg.issued
    consumed := cfg.consumed + cfg.pending.getD 0 }

/-- Reachability under the guarded dynamics: A may step only into an empty interface
(capacity-one latency discipline); B may step only against a pending grant, with a
digit below it. -/
inductive Reachable (C : CoupledFiber) : CoupledConfig → Prop
  | init : Reachable C initConfig
  | stepA {cfg : CoupledConfig} (hr : Reachable C cfg) (a : ℕ)
      (ha : a < C.fiberA cfg.sA) (hp : cfg.pending = none) :
      Reachable C (applyA C cfg a)
  | stepB {cfg : CoupledConfig} (hr : Reachable C cfg) {g : ℕ} (b : ℕ)
      (hp : cfg.pending = some g) (hb : b < g) :
      Reachable C (applyB cfg b)

/-! ## 2. SU4b — the balance law -/

/-- **The balance invariant** (Theorem 57's shape): everything issued is either
consumed or still in flight. -/
def Balanced (cfg : CoupledConfig) : Prop :=
  cfg.issued = cfg.consumed + cfg.pending.getD 0

/-- **SU4b — THE INTERFACE BALANCE LAW (Prop-128-shape exactness).** Every reachable
configuration of the coupled machine is balanced: `issued = consumed + pending`. Per
step the change is exactly the step's own grant (τ local to the step label); summed,
nothing is created or destroyed anonymously — the carry-accounting charge of the
thesis §3, proven for arbitrary `CoupledFiber` coupling. -/
theorem reachable_balanced {C : CoupledFiber} {cfg : CoupledConfig}
    (h : Reachable C cfg) : Balanced cfg := by
  induction h with
  | init => rfl
  | stepA hr a ha hp ih =>
    unfold Balanced applyA
    unfold Balanced at ih
    rw [hp] at ih
    simp only [Option.getD_some, Option.getD_none] at *
    omega
  | stepB hr b hp hb ih =>
    unfold Balanced applyB
    unfold Balanced at ih
    rw [hp] at ih ⊢
    simp only [Option.getD_some, Option.getD_none] at *
    omega

/-- **The obstruction reading**: no reachable configuration has consumed more than was
issued — the charge genuinely separates configurations from unreachable ones. -/
theorem reachable_consumed_le_issued {C : CoupledFiber} {cfg : CoupledConfig}
    (h : Reachable C cfg) : cfg.consumed ≤ cfg.issued := by
  have hb := reachable_balanced h
  unfold Balanced at hb
  omega

/-! ## 3. Demos — the ledger, live (raggedFiber from SU1) -/

-- A issues 3 into the interface (A-digit 1 ⇒ fiberB grant 3); B consumes it:
#eval applyA raggedFiber initConfig 1
  -- ⟨[1], [], some 3, 3, 0⟩ : balanced (3 = 0 + 3)
#eval applyB (applyA raggedFiber initConfig 1) 2
  -- ⟨[1], [2], none, 3, 3⟩ : balanced (3 = 3 + 0)
-- Two full steps: every grant accounted, interface empty at the end:
#eval applyB (applyA raggedFiber (applyB (applyA raggedFiber initConfig 1) 2) 0) 1
  -- ⟨[1, 0], [2, 1], none, 6, 6⟩

/-- The balance, kernel-checked on a concrete two-step run (`6 = 6 + 0`). -/
theorem ragged_run_balanced :
    Balanced (applyB (applyA raggedFiber (applyB (applyA raggedFiber initConfig 1) 2) 0) 1) :=
  rfl

end FdrsFormal.Modes.SyntheticPlace
