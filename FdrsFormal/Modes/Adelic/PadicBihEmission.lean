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

# Adelic complex — the p²-corner bihomographic emission (Axis I at `p`)

Upgrades the p-adic leg from a *passive transducer* (one input stream, `PadicLedger`,
M0) to an *active computational node* (two input streams combined, `PadicBihTensor`,
M0a) — native, exact, asynchronous arithmetic **inside** the non-Archimedean field.
The 8-field `ℤ` algebra and the three channel commutations already exist (M0a,
`PadicHomographic.lean`); this file supplies the missing **emission certificate**.

**The congruence-trap is the algebraic shortcut, not a `p²`-grid.** The Archimedean
`emit_traps` checks the four order-corners `{1,∞}²` and *interpolates* (`bilinear_ge_const`,
`nlinarith`) because a floor is an ORDER decision: the value varies over the quadrant but
must stay in `[k,k+1)`. A congruence demands more, and cleaner — the digit `z mod p` must
be **exactly one residue**, i.e. the value must be *literally constant* in the tails. So we
do **not** enumerate the `p²` residue-corners; we kill the tail-dependence identically:

> `z = (a·xy+b·x+c·y+d)/(e·xy+f·x+g·y+h)` is constant `≡ d·h⁻¹` for **all** `(x,y) ∈ ℤ_p²`
> exactly when the non-constant monomial coefficients vanish mod `p`:
> `ready ⟺ p∣a ∧ p∣b ∧ p∣c  (numerator ≡ d)  ∧  p∣e ∧ p∣f ∧ p∣g ∧ ¬p∣h  (denom ≡ h, a unit)`.

Seven divisibility conditions on the 8 integer coefficients, decidable by `decide`; the
soundness collapses by `simp [zero_mul, zero_add]` (the `xy, x, y` terms annihilate) — the
direct generalization of M0c's single-stream `a≡c≡0, d≢0`, with **no** `nlinarith`, no
convexity, no corner enumeration. The non-Archimedean trap is *simpler* than the order one.

Contents: `valueMod`/`candidate`/`ready` (the gate), `ready_sound_mod_p` (the soundness
over `ZMod p`, the bilinear M0c), `padic_emit_traps` (over genuine `ℤ_[p]`, the bilinear
M0d), `reduceOnce`/`emitStep` (the primitive-ledger renormalization), a two-stream driver
`bihRun`, and `addTensor`/`mulTensor` demos combining two `ℤ_5` integers exactly. Leaf
module. No `sorry`; axiom-clean.
-/
import FdrsFormal.Modes.Adelic.PadicEmitTraps
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.RingHoms

namespace FdrsFormal.Modes.Adelic

namespace PadicBihTensor

/-! ## 1. The value, the candidate digit, and the readiness gate -/

/-- The bihomographic value `z = (a·xy+b·x+c·y+d)/(e·xy+f·x+g·y+h)` reduced `mod p`, for
residue tails `x, y : ZMod p`. Pure `ZMod p`: no order, no float. -/
def valueMod (p : ℕ) (T : PadicBihTensor) (x y : ZMod p) : ZMod p :=
  ((T.a : ZMod p) * x * y + (T.b : ZMod p) * x + (T.c : ZMod p) * y + (T.d : ZMod p)) *
    ((T.e : ZMod p) * x * y + (T.f : ZMod p) * x + (T.g : ZMod p) * y + (T.h : ZMod p))⁻¹

/-- The candidate output Hensel digit: `d · h⁻¹ (mod p)` — the value at the `(0,0)` corner.
When `ready`, this is the value at *every* corner (`ready_sound_mod_p`). -/
def candidate (p : ℕ) (T : PadicBihTensor) : ZMod p := (T.d : ZMod p) * (T.h : ZMod p)⁻¹

/-- **The denominator is a unit on the whole bidisk**: `e ≡ f ≡ g ≡ 0 ∧ h ≢ 0 (mod p)`
(then `D ≡ h`, a unit, for every `(x,y)`). The two-input analogue of `denomUnitOnDisk`. -/
def denomUnitOnBidisk (p : ℕ) (T : PadicBihTensor) : Bool :=
  decide ((T.e : ZMod p) = 0) && decide ((T.f : ZMod p) = 0) &&
    decide ((T.g : ZMod p) = 0) && decide ((T.h : ZMod p) ≠ 0)

/-- **Emission is ready** when the digit is forced for *every* tail pair: the denominator
is a unit on the bidisk *and* the numerator is constant mod `p` (`a ≡ b ≡ c ≡ 0`). These
are the non-Archimedean **`p²`-corner congruences** — collapsed, by the algebraic shortcut,
to coefficient conditions: decidable, pure congruence, **no `<`, no floor**. -/
def ready (p : ℕ) (T : PadicBihTensor) : Bool :=
  denomUnitOnBidisk p T && decide ((T.a : ZMod p) = 0) &&
    decide ((T.b : ZMod p) = 0) && decide ((T.c : ZMod p) = 0)

/-! ## 2. No pole on the bidisk when the gate holds -/

/-- **No pole on the bidisk.** When `denomUnitOnBidisk` holds, the denominator is nonzero
`mod p` for *every* tail pair — so `valueMod` is well-defined on all of `ℤ_p²`. -/
theorem denom_ne_zero_on_bidisk (p : ℕ) (T : PadicBihTensor)
    (h : denomUnitOnBidisk p T = true) (x y : ZMod p) :
    (T.e : ZMod p) * x * y + (T.f : ZMod p) * x + (T.g : ZMod p) * y + (T.h : ZMod p) ≠ 0 := by
  simp only [denomUnitOnBidisk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨he, hf⟩, hg⟩, hh⟩ := h
  rw [he, hf, hg]; simpa using hh

/-! ## 3. The soundness over `ZMod p` (the bilinear M0c) -/

/-- **The p²-corner emission soundness (concrete, over `ZMod p`).** When `ready` holds, the
value `mod p` equals the candidate digit for *every* tail pair `(x,y)` — the next Hensel
digit of the combined stream is forced regardless of the unread inputs. The bilinear
congruence analogue of `bilinear_ge_const`/`emit_traps`, proved by the algebraic shortcut:
the tail-dependent monomials vanish (`simp [zero_mul]`), no corner enumeration, no order. -/
theorem ready_sound_mod_p (p : ℕ) (T : PadicBihTensor) (h : ready p T = true) (x y : ZMod p) :
    valueMod p T x y = candidate p T := by
  simp only [ready, denomUnitOnBidisk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨he, hf⟩, hg⟩, hh⟩, ha⟩, hb⟩, hc⟩ := h
  simp only [valueMod, candidate, ha, hb, hc, he, hf, hg, zero_mul, zero_add]

/-! ## 4. The soundness over genuine `ℤ_[p]` (the bilinear M0d) -/

/-- **`padic_emit_traps` for the two-stream tensor, over `ℤ_[p]`.** When `ready` holds, for
*every* pair of p-adic-integer tails the combined value's leading residue is forced:
numerator `≡ candidate · denominator (mod p)`, denominator a unit. The genuine-p-adic
restatement of `ready_sound_mod_p`, lifted through `PadicInt.toZMod`. -/
theorem padic_emit_traps (p : ℕ) [Fact p.Prime] (T : PadicBihTensor) (h : ready p T = true)
    (x y : ℤ_[p]) :
    PadicInt.toZMod ((T.a : ℤ_[p]) * x * y + (T.b : ℤ_[p]) * x + (T.c : ℤ_[p]) * y + (T.d : ℤ_[p]))
        = candidate p T * PadicInt.toZMod
            ((T.e : ℤ_[p]) * x * y + (T.f : ℤ_[p]) * x + (T.g : ℤ_[p]) * y + (T.h : ℤ_[p]))
      ∧ PadicInt.toZMod
          ((T.e : ℤ_[p]) * x * y + (T.f : ℤ_[p]) * x + (T.g : ℤ_[p]) * y + (T.h : ℤ_[p])) ≠ 0 := by
  simp only [ready, denomUnitOnBidisk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨he, hf⟩, hg⟩, hh⟩, ha⟩, hb⟩, hc⟩ := h
  simp only [map_add, map_mul, map_intCast]
  rw [ha, hb, hc, he, hf, hg]
  refine ⟨?_, ?_⟩
  · simp only [zero_mul, zero_add, candidate]
    rw [mul_assoc, inv_mul_cancel₀ hh, mul_one]
  · simpa using hh

/-! ## 5. Reduction and the two-stream driver -/

/-- Divide all eight tensor entries by `p` iff all are divisible (else unchanged): cancels
the spurious factor of `p` a valid emit introduces (the bilinear analogue of `reduceOnce`,
one suffices: `h ≢ 0` blocks more). Pure `ℤ`. -/
def reduceOnce (p : ℤ) (T : PadicBihTensor) : PadicBihTensor :=
  if T.a % p == 0 && T.b % p == 0 && T.c % p == 0 && T.d % p == 0 &&
      T.e % p == 0 && T.f % p == 0 && T.g % p == 0 && T.h % p == 0 then
    ⟨T.a / p, T.b / p, T.c / p, T.d / p, T.e / p, T.f / p, T.g / p, T.h / p⟩
  else T

/-- One output step: emit the digit `β`, then renormalize so the tensor stays primitive. -/
def emitStep (p : ℤ) (β : ℤ) (T : PadicBihTensor) : PadicBihTensor :=
  reduceOnce p (emit p β T)

/-- The two-stream p-adic driver: combine input Hensel streams `xs` (A) and `ys` (B) into
the output stream, emitting the forced digit when `ready`, else absorbing the next input
(alternating A/B). The non-Archimedean sibling of `BihomographicDriver.run`. -/
def bihRun (p : ℕ) (T : PadicBihTensor) (xs ys : List ℤ) (turn : Bool) : ℕ → List ℤ
  | 0 => []
  | fuel + 1 =>
    if ready p T then
      let β : ℤ := (candidate p T).val
      β :: bihRun p (emitStep (p : ℤ) β T) xs ys turn fuel
    else if turn then
      match xs with
      | x :: xs' => bihRun p (absorbX (p : ℤ) x T) xs' ys false fuel
      | [] => match ys with
              | y :: ys' => bihRun p (absorbY (p : ℤ) y T) [] ys' true fuel
              | [] => []
    else
      match ys with
      | y :: ys' => bihRun p (absorbY (p : ℤ) y T) xs ys' true fuel
      | [] => match xs with
              | x :: xs' => bihRun p (absorbX (p : ℤ) x T) xs' [] false fuel
              | [] => []

/-- `z = x + y` tensor: numerator `x + y`, denominator `1`. -/
def addTensor : PadicBihTensor := ⟨0, 1, 1, 0, 0, 0, 0, 1⟩

/-- `z = x · y` tensor: numerator `xy`, denominator `1`. -/
def mulTensor : PadicBihTensor := ⟨1, 0, 0, 0, 0, 0, 0, 1⟩

/-! ## 6. Demos — native p-adic multi-stream arithmetic over `ℤ₅` (exact, no float) -/

-- `12 = [2,2]` and `8 = [3,1]` in base 5.  Their SUM `20 = [0,4]` and PRODUCT `96 = [1,4,3]`,
-- computed by combining the two Hensel streams natively at the place `p = 5`:
#eval bihRun 5 addTensor [2, 2, 0, 0, 0] [3, 1, 0, 0, 0] true 30     -- [0, 4, 0, …]  = digits of 20
#eval Nat.digits 5 20                                                -- [0, 4]
#eval bihRun 5 mulTensor [2, 2, 0, 0, 0] [3, 1, 0, 0, 0] true 30     -- [1, 4, 3, …] = digits of 96
#eval Nat.digits 5 96                                                -- [1, 4, 3]

end PadicBihTensor

end FdrsFormal.Modes.Adelic
