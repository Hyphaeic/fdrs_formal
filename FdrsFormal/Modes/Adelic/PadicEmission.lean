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

# Adelic complex M0b/M0c — the p-adic emission certificate (congruence, not order)

The non-Archimedean dual of `emitDigit`/`emitReady` (`Bihomographic.lean`) and the
soundness `emit_traps`/`emitReady_traps` (`BihomographicSound.lean`). At `∞` a digit is
forced by an **order trap** — the floor `⌊a/e⌋` pinned between four corner inequalities.
At `p` a digit is forced by a **congruence** — the residue `mod p` pinned across the
residue-disks of the unread tail. This file builds that certificate for the single-stream
`PadicLedger` of M0a.

The mechanism (archived design `03` §3c and scratch `NOTES.md` §2,
`docs/archive/adelic-machine/`):

* **`candidate`** — the forced output digit is `b · d⁻¹ (mod p)`, the value at the
  `x ≡ 0` corner.
* **`denomUnitOnDisk`** — the gate: the denominator `c·x + d` is a unit for *every* tail
  `x ∈ ℤ_p`, i.e. `c ≡ 0 ∧ d ≢ 0 (mod p)`. When it fails there is a tail where the
  denominator hits the maximal ideal — a **pole on the disk** (`pole_exists_of_not_unit`,
  the sharp converse / "do not emit early"), and the engine must refine rather than emit.
* **`ready`** — `denomUnitOnDisk` *and* the numerator is constant mod `p` (`a ≡ 0`, so
  `a·x + b ≡ b` for every tail). These are the `p`-corner congruences: pure congruence,
  decidable, **no `<`, no floor**.
* **`ready_sound_mod_p` (M0c)** — the load-bearing soundness: `ready ⟹` the value mod `p`
  equals `candidate` for *every* tail `x : ZMod p`. Proved with only `ZMod`/divisibility
  (no `Valued`, no order) — the concrete combinatorial core that M0d will restate over a
  general valued field.

Everything is exact, integer/`ZMod`-driven: no order, no floor, no float — the
no-floats / congruence-not-order discipline (archived design `00` §4). Leaf module (imports only M0a). No
`sorry`; axiom-clean.
-/
import FdrsFormal.Modes.Adelic.PadicHomographic
import Mathlib.Data.ZMod.Basic

namespace FdrsFormal.Modes.Adelic

namespace PadicLedger

/-! ## 1. The value, the candidate digit, and the readiness gate -/

/-- The homographic value `y = (a·x + b)/(c·x + d)` reduced `mod p`, for a residue tail
`x : ZMod p`. This is the non-Archimedean *value* against which emission is certified —
the congruence analogue of the real value the Archimedean `emit_traps` traps with a floor.
Pure `ZMod p`: no order, no float. -/
def valueMod (p : ℕ) (M : PadicLedger) (x : ZMod p) : ZMod p :=
  ((M.a : ZMod p) * x + (M.b : ZMod p)) * ((M.c : ZMod p) * x + (M.d : ZMod p))⁻¹

/-- The candidate output Hensel digit: the residue `b · d⁻¹ (mod p)` — the value at the
`x ≡ 0` corner. When `ready`, this is the value at *every* corner (`ready_sound_mod_p`),
so it is the forced digit. -/
def candidate (p : ℕ) (M : PadicLedger) : ZMod p :=
  (M.b : ZMod p) * (M.d : ZMod p)⁻¹

/-- **`denom_unit_on_disk`** (the named gate, archived design `03` §3c): the denominator `c·x + d`
is a p-adic unit for *every* tail `x ∈ ℤ_p`, i.e. `c ≡ 0 ∧ d ≢ 0 (mod p)` (then
`c·x + d ≡ d`, a unit, for all `x`). A decidable congruence condition — no order. -/
def denomUnitOnDisk (p : ℕ) (M : PadicLedger) : Bool :=
  decide ((M.c : ZMod p) = 0) && decide ((M.d : ZMod p) ≠ 0)

/-- **Emission is ready** when the digit is *forced for every tail*: the denominator is a
unit on the whole disk (`denomUnitOnDisk`) *and* the numerator is constant `mod p`
(`a ≡ 0`, so `a·x + b ≡ b` for all `x`). These are the non-Archimedean **`p`-corner
congruences** — the congruence dual of the four order-corner inequalities in `emitReady`.
Decidable, pure congruence: no `<`, no floor. -/
def ready (p : ℕ) (M : PadicLedger) : Bool :=
  denomUnitOnDisk p M && decide ((M.a : ZMod p) = 0)

/-! ## 2. The disk has no pole when the gate holds (and a pole when it fails) -/

/-- **No pole on the disk.** When `denomUnitOnDisk` holds, the denominator `c·x + d` is
nonzero `mod p` for *every* tail `x` — so the value `valueMod` is well-defined on the
whole disk. -/
theorem denom_ne_zero_on_disk (p : ℕ) (M : PadicLedger)
    (h : denomUnitOnDisk p M = true) (x : ZMod p) :
    (M.c : ZMod p) * x + (M.d : ZMod p) ≠ 0 := by
  simp only [denomUnitOnDisk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hc, hd⟩ := h
  rw [hc, zero_mul, zero_add]; exact hd

/-- **The sharp converse (do not emit early).** When the gate *fails* on the unit side
(`c ≢ 0 mod p`), there is a tail residue `x ≡ −d/c` at which the denominator vanishes — a
**pole on the disk**. So the engine cannot emit; it must refine (absorb another input
digit). This is the non-Archimedean analogue of the Archimedean engine *withholding* a
digit at a boundary (`√2·√2 = 2 → []`), and the dual of the sharp necessity theorem
`congruenceSet_not_cylinder_union_of_not_dvd`. -/
theorem pole_exists_of_not_unit (p : ℕ) [Fact p.Prime] (M : PadicLedger)
    (hc : (M.c : ZMod p) ≠ 0) :
    ∃ x : ZMod p, (M.c : ZMod p) * x + (M.d : ZMod p) = 0 := by
  refine ⟨(M.c : ZMod p)⁻¹ * -(M.d : ZMod p), ?_⟩
  rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul, neg_add_cancel]

/-! ## 3. M0c — concrete soundness over `ZMod p` -/

/-- **M0c — the p-adic emission soundness (concrete, over `ZMod p`).** When `ready` holds,
the value `mod p` equals the candidate digit for *every* tail `x : ZMod p` — the next
Hensel digit is forced regardless of the unread input. This is the congruence dual of
`emitReady_traps` (the floor is trapped between the four order-corners), proved with only
`ZMod` arithmetic: no `Valued`, no order, no floor. The combinatorial core that M0d
restates over a general valued field. -/
theorem ready_sound_mod_p (p : ℕ) (M : PadicLedger)
    (h : ready p M = true) (x : ZMod p) :
    valueMod p M x = candidate p M := by
  simp only [ready, denomUnitOnDisk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hc, _hd⟩, ha⟩ := h
  simp only [valueMod, candidate, hc, ha, zero_mul, zero_add]

/-! ## 4. Reduction — keeping the iterated transducer ledger primitive

**A correction to the archived design's emit recurrence** (scratch `NOTES.md` §1,
`docs/archive/adelic-machine/`). The raw emit
`M ↦ [[a−βc, b−βd],[p·c, p·d]]` (det ↦ p·det) is a correct *value* transform, but it
leaves the denominator `p·c·x + p·d ≡ 0 (mod p)`, so `denomUnitOnDisk` (which needs
`d ≢ 0`) can **never** fire again — the engine emits one digit and stalls. (The design's
numerical validator does not exercise this path: its Demo B reads Hensel digits directly,
never iterating the ledger emit.)

The fix: at a *valid* (ready) emit the four new entries are all `≡ 0 (mod p)` — because
`a ≡ c ≡ 0` and `β ≡ b·d⁻¹` give `a−βc ≡ 0` and `b−βd ≡ 0`, and `p·c, p·d` are visibly
divisible — so the ledger carries a spurious common factor of `p` that must be divided
out to return to the primitive representative `⟨(a−βc)/p, (b−βd)/p, c, d⟩` (denominator
`c·x + d` restored, so `ready` can fire again). `reduceOnce` performs exactly that single
cancellation (one suffices: `d ≢ 0 (mod p)` blocks any further division). Dividing all
four entries by `p` does not change the value `(a·x+b)/(c·x+d)`, so the soundness M0c/M0d
— stated on the primitive ledger — is unaffected; only the *driver* uses `reduceOnce`. -/

/-- Divide all four ledger entries by `p` **iff** all are divisible by `p` (else leave the
ledger unchanged). After a valid emit this cancels the single spurious factor of `p` that
`emit` introduces, restoring the primitive ledger on which `ready`/`candidate` are
meaningful. Pure `ℤ`: exact division, no float. -/
def reduceOnce (p : ℤ) (M : PadicLedger) : PadicLedger :=
  if M.a % p == 0 && M.b % p == 0 && M.c % p == 0 && M.d % p == 0 then
    ⟨M.a / p, M.b / p, M.c / p, M.d / p⟩
  else M

/-- One full output step of the iterated transducer: emit the digit `β`, then renormalize
(`reduceOnce`) so the ledger stays primitive and the next digit can be forced. -/
def emitStep (p : ℤ) (β : ℤ) (M : PadicLedger) : PadicLedger :=
  reduceOnce p (M.emit p β)

/-! ## 5. Demos (the archived design's Demo B numbers, exact `ZMod` arithmetic) -/

-- Demo B map `y = (3x+2)/(5x+1)` over `ℤ₅` is **not** ready initially (`a = 3 ≢ 0 mod 5`):
#eval ready 5 ⟨3, 2, 5, 1⟩        -- false — must absorb an input digit first
-- After absorbing one input digit `α = 4` (= `x mod 5` for the reference value `x = 2/3`) it IS
-- ready, and the forced output digit is `4` — matching the reference `a₀(y₀) = 4`.
#eval ready 5 (absorb 5 4 ⟨3, 2, 5, 1⟩)        -- true
#eval candidate 5 (absorb 5 4 ⟨3, 2, 5, 1⟩)    -- 4

end PadicLedger

end FdrsFormal.Modes.Adelic
