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

# Adelic complex — driver correctness (sound representation → provably correct implementation)

The `ValuationStream` demos *observe* that the p-adic node, on the constant ledger
`⟨0, n, 0, 1⟩` (the homographic encoding "value = `n`"), emits the base-`p` Hensel digits
of `n`. This file *proves* it — promoting "demo that matches `Nat.digits`" into a
**certified transcoder**.

The proof is an **inductive invariant over the ledger state**, not a fuel-bounded
simulation. The invariant is that the ledger stays in the canonical constant form
`⟨0, m, 0, 1⟩`, and a single ready→emit→`reduceOnce` step is *exactly*

> `run ⟨0, m, 0, 1⟩ … (k+1) = (m % p) :: run ⟨0, m / p, 0, 1⟩ … k`     (`run_step`)

— the ledger transition step **is** the `Nat.digits` recursion `digits p m =
(m % p) :: digits p (m / p)`. Pinning the fuel to `(Nat.digits p m).length` makes the
correspondence exact (no trailing-zero slack):

> **`run_padic_constant_eq_digits`** : `run (padicEngine p) ⟨0, m, 0, 1⟩ [] (digits p m).length
>   = (Nat.digits p m).map (↑·)`.

Scope (honest): this certifies the *constant-ledger* transcoder (computing a single
rational's own digits) — the case the `ValuationStream` bridge uses. The general
homographic transducer (`run` on `M(x)` for a live input stream) and `bihRun` (two-stream
combination) need the stronger invariant "the ledger tracks `M` applied to the absorbed
prefix"; those are deferred. Leaf module. No `sorry`; axiom-clean.
-/
import FdrsFormal.Modes.Adelic.PlaceEngine
import Mathlib.Data.Nat.Digits.Defs

namespace FdrsFormal.Modes.Adelic

/-- **The ledger-invariant step lemma (the heart).** On the canonical constant ledger
`⟨0, m, 0, 1⟩`, one driver step emits `m % p` and advances the ledger to `⟨0, m / p, 0, 1⟩`
— the `Nat.digits` recursion, realized by the engine. Proved by computing `ready`,
`candidate`, and `emitStep` on the canonical ledger (the invariant: the ledger stays
`⟨0, ·, 0, 1⟩`). -/
theorem run_step (p : ℕ) [Fact p.Prime] (j fuel : ℕ) :
    PlaceEngine.run (padicEngine p) ⟨0, (j : ℤ), 0, 1⟩ [] (fuel + 1)
      = ((j % p : ℕ) : ℤ) ::
          PlaceEngine.run (padicEngine p) ⟨0, ((j / p : ℕ) : ℤ), 0, 1⟩ [] fuel := by
  have hpp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hpp.ne_zero⟩
  have hpz : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hpp.pos
  -- the three engine computations on the canonical ledger:
  have hready : (padicEngine p).ready ⟨0, (j : ℤ), 0, 1⟩ = true := by
    simp [padicEngine, PadicLedger.ready, PadicLedger.denomUnitOnDisk]
  have hcand : (padicEngine p).candidate ⟨0, (j : ℤ), 0, 1⟩ = ((j % p : ℕ) : ℤ) := by
    simp only [padicEngine, PadicLedger.candidate, Int.cast_zero, Int.cast_one, inv_one, mul_one]
    rw [Int.cast_natCast, ZMod.val_natCast]
  have hpne : (p : ℤ) ≠ 0 := ne_of_gt hpz
  have key : (j : ℤ) - ((j % p : ℕ) : ℤ) = (p : ℤ) * ((j / p : ℕ) : ℤ) := by
    have h : (j : ℤ) = (p : ℤ) * ((j / p : ℕ) : ℤ) + ((j % p : ℕ) : ℤ) := by
      exact_mod_cast (Nat.div_add_mod j p).symm
    linarith
  have hemit : (padicEngine p).emit ((j % p : ℕ) : ℤ) ⟨0, (j : ℤ), 0, 1⟩
      = ⟨0, ((j / p : ℕ) : ℤ), 0, 1⟩ := by
    show PadicLedger.emitStep (p : ℤ) ((j % p : ℕ) : ℤ) ⟨0, (j : ℤ), 0, 1⟩ = _
    simp only [PadicLedger.emitStep, PadicLedger.emit, mul_zero, sub_zero, mul_one, zero_mul,
      one_mul, key]
    unfold PadicLedger.reduceOnce
    split_ifs with hcond
    · simp [Int.mul_ediv_cancel_left _ hpne, Int.ediv_self hpne]
    · exact absurd (by simp [Int.mul_emod_right, Int.emod_self]) hcond
  -- unfold one driver step and substitute
  simp only [PlaceEngine.run, hready, hcand, hemit, if_true]

/-- **Driver correctness (constant ledger).** Running the p-adic engine on the canonical
constant ledger `⟨0, m, 0, 1⟩` for exactly `(Nat.digits p m).length` steps emits *exactly*
the base-`p` Hensel digits of `m` — `Nat.digits p m`. The engine `run` is a **certified
transcoder**, not merely a demo that matches. -/
theorem run_padic_constant_eq_digits (p : ℕ) [Fact p.Prime] (m : ℕ) :
    PlaceEngine.run (padicEngine p) ⟨0, (m : ℤ), 0, 1⟩ [] (Nat.digits p m).length
      = (Nat.digits p m).map (fun d => (d : ℤ)) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases eq_or_ne m 0 with rfl | hm
    · simp [PlaceEngine.run]
    · have hp1 : 1 < p := (Fact.out (p := p.Prime)).one_lt
      have hdig : Nat.digits p m = (m % p) :: Nat.digits p (m / p) :=
        Nat.digits_def' hp1 (Nat.pos_of_ne_zero hm)
      have hlt : m / p < m := Nat.div_lt_self (Nat.pos_of_ne_zero hm) hp1
      rw [hdig, List.length_cons, run_step, ih (m / p) hlt]; rfl

/-! ## Demo — the certified transcoder reproduces the `ValuationStream` numbers -/

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

-- `run ⟨0,12,0,1⟩ … (digits 5 12).length = [2,2]` — now a *theorem*, not just an #eval.
#eval PlaceEngine.run (padicEngine 5) ⟨0, 12, 0, 1⟩ [] (Nat.digits 5 12).length   -- [2, 2]
#eval (Nat.digits 5 12).map (fun d => (d : ℤ))                                     -- [2, 2]

end FdrsFormal.Modes.Adelic
