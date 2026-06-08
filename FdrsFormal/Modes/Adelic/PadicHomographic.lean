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

# Adelic complex M0a — the p-adic homographic ledger (within-place exactness at `p`)

The non-Archimedean dual of the continued-fraction ledger `RemainderState`
(`Modes/VariableRadix/SubshiftWeight.lean`) and its emission `emit`
(`HomographicCarry.lean`). Where the Archimedean engine reads a CF quotient by
*inversion* `x ↦ a + 1/x` (right-multiply by `[[a,1],[1,0]]`, determinant `−1`, so
`|det| = 1` stays unimodular forever), the p-adic engine reads a **Hensel digit by a
shift** `x = α + p·x'` (right-multiply by `[[p,α],[0,1]]`, determinant `p`). Dually it
**emits** a Hensel digit `β` by `y' = (y − β)/p` (left-multiply by `[[1,−β],[0,p]]`,
determinant `p`).

So every absorb/emit multiplies the determinant by `p`, and the within-place exactness
invariant is **not** `|det| = 1` but `det = p^{#steps}` (`v_p(det) = #steps`): the ledger
is exact, but its determinant is a pure power of `p` rather than a unit (design
`docs/adelic-machine/04` §2, `03` §3b; scratch `NOTES.md` §1). Everything here is pure
`ℤ` arithmetic — no order, no floor, no float (the p-adic emission *certificate* of
M0b–M0d is a congruence, not an order trap).

This file is **M0a** of the adelic build roadmap (`docs/adelic-machine/05`): the ledger,
the absorb/emit recurrence, the determinant law, and the `det = p^{#steps}` exactness
invariant — plus the two-stream `PadicBihTensor` (Axis I at `p`) and its channel
commutations, the pure-`ℤ` algebra that transfers verbatim from `BihTensor`. Candidate /
readiness (M0b) and soundness (M0c/M0d) live in sibling modules.

Provenance: the *algebra* mirrors the verified corpus structures `RemainderState` /
`BihTensor` (✅); the *p-adic shift recurrence and the `det ↦ p·det` law* are new (this
file), proved by the same `det_step` / `congr 1 <;> ring` idioms. Leaf module: nothing
imports it. No `sorry`; axiom-clean.
-/
import Mathlib.Tactic

namespace FdrsFormal.Modes.Adelic

/-! ## 1. The single-stream p-adic ledger -/

/-- The p-adic homographic ledger `M = [[a,b],[c,d]]`, representing the value
`y = (a·x + b)/(c·x + d)` of a tail `x ∈ ℤ_p`. A flat 4-field `ℤ` structure (NOT a
`Matrix`), so every law closes by `ring`. The non-Archimedean dual of `RemainderState`,
but with a *shift* recurrence (Hensel) in place of the CF *inversion*. -/
structure PadicLedger where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  deriving Repr, DecidableEq, Inhabited

namespace PadicLedger

/-- The determinant `a·d − b·c`. Unlike the CF ledger (where `|det| = 1` forever), here
every absorb/emit multiplies this by `p` (`det_absorb`, `det_emit`). -/
def det (r : PadicLedger) : ℤ := r.a * r.d - r.b * r.c

/-- **Absorb** a Hensel digit `α` of the input `x = α + p·x'`: right-multiply `M` by the
shift `[[p,α],[0,1]]`, giving `M ↦ [[a·p, a·α+b],[c·p, c·α+d]]`. The non-Archimedean dual
of `RemainderState.step` (which right-multiplies by the CF inversion `[[a,1],[1,0]]`). -/
def absorb (p α : ℤ) (r : PadicLedger) : PadicLedger where
  a := r.a * p
  b := r.a * α + r.b
  c := r.c * p
  d := r.c * α + r.d

/-- **Emit** a Hensel digit `β` of the output `y = β + p·y'`: left-multiply `M` by
`[[1,−β],[0,p]]` (`y' = (y − β)/p`), giving `M ↦ [[a−β·c, b−β·d],[p·c, p·d]]`. The
non-Archimedean dual of `RemainderState.emit`. -/
def emit (p β : ℤ) (r : PadicLedger) : PadicLedger where
  a := r.a - β * r.c
  b := r.b - β * r.d
  c := r.c * p
  d := r.d * p

/-- The identity ledger `[[1,0],[0,1]]` (the value `y = x`), with `det = 1`. -/
def init : PadicLedger := ⟨1, 0, 0, 1⟩

/-- **Absorb multiplies the determinant by `p`** (the shift factor `[[p,α],[0,1]]` has
determinant `p`). Pure integer algebra — the p-adic dual of `det_step`. -/
@[simp] theorem det_absorb (p α : ℤ) (r : PadicLedger) :
    (absorb p α r).det = p * r.det := by
  simp only [det, absorb]; ring

/-- **Emit multiplies the determinant by `p`** (the factor `[[1,−β],[0,p]]` has
determinant `p`). -/
@[simp] theorem det_emit (p β : ℤ) (r : PadicLedger) :
    (emit p β r).det = p * r.det := by
  simp only [det, emit]; ring

@[simp] theorem init_det : init.det = 1 := by simp [det, init]

/-- **Channel independence** (the p-adic dual of `emit_step_comm`): absorbing an input
Hensel digit and emitting an output Hensel digit commute. `absorb` is a right-multiply,
`emit` a left-multiply, so they commute structurally — the engine interleaves reads and
writes freely. This is the seed of the M1 scheduler-confluence lemma. -/
theorem emit_absorb_comm (p α β : ℤ) (r : PadicLedger) :
    emit p β (absorb p α r) = absorb p α (emit p β r) := by
  cases r; simp only [emit, absorb]; congr 1 <;> ring

/-! ### The exactness invariant: `det = p^{#steps}` -/

/-- A single engine operation: read a Hensel digit (`absorb`) or write one (`emit`). -/
inductive Op where
  | absorb (α : ℤ)
  | emit (β : ℤ)
  deriving Repr, DecidableEq

/-- Apply one operation at base `p`. -/
def applyOp (p : ℤ) (r : PadicLedger) : Op → PadicLedger
  | .absorb α => absorb p α r
  | .emit β => emit p β r

/-- Replay a sequence of operations (the p-adic dual of `RemainderState.steps`). -/
def applyOps (p : ℤ) (r : PadicLedger) (ops : List Op) : PadicLedger :=
  ops.foldl (applyOp p) r

@[simp] theorem det_applyOp (p : ℤ) (r : PadicLedger) (op : Op) :
    (applyOp p r op).det = p * r.det := by
  cases op <;> simp [applyOp]

/-- **The determinant after `k` operations is `p^k · det`** (the p-adic dual of
`det_steps`'s `(−1)^|as| · det`). Each step contributes a factor of `p`. -/
theorem det_applyOps (p : ℤ) (r : PadicLedger) (ops : List Op) :
    (applyOps p r ops).det = p ^ ops.length * r.det := by
  induction ops generalizing r with
  | nil => simp [applyOps]
  | cons op ops ih =>
    have hstep : applyOps p r (op :: ops) = applyOps p (applyOp p r op) ops := rfl
    rw [hstep, ih (applyOp p r op), det_applyOp, List.length_cons, pow_succ]; ring

/-- **THE p-adic EXACTNESS INVARIANT (raw operations).** From the identity ledger, after
any sequence of `k` *raw* absorb/emit operations the determinant is *exactly* `p^k`. This
is the within-place analogue of the CF `bracket_invariant` (`|det| = 1`): the p-adic
ledger never rounds, but its determinant is a pure power of `p` (so `v_p(det) = #steps`)
rather than a unit (design `04` §2).

NB: the *operative* transducer renormalizes after each emit (`reduceOnce`, M0b) — a valid
emit leaves a spurious common factor of `p`, divided out to keep the ledger primitive — so
along a real driver run the determinant's `p`-valuation tracks the absorb−emit *lookahead*,
not the raw step count. This raw law is the exactness of the underlying operations; the
renormalized run is `PadicLedger.emitStep`. -/
theorem det_applyOps_init (p : ℤ) (ops : List Op) :
    (applyOps p init ops).det = p ^ ops.length := by
  rw [det_applyOps, init_det, mul_one]

/-- The exactness invariant in `natAbs` form for a natural base `p`: the determinant's
absolute value is `p^{#steps}` — its only prime factor is `p`, the non-Archimedean
replacement for "`|det| = 1`". (`v_p(det) = #steps` when `p` is prime.) -/
theorem det_applyOps_init_natAbs (p : ℕ) (ops : List Op) :
    ((applyOps (p : ℤ) init ops).det).natAbs = p ^ ops.length := by
  rw [det_applyOps_init]; simp [Int.natAbs_pow]

end PadicLedger

/-! ## 2. The two-stream p-adic tensor (Axis I at `p`)

The two-input combinator at a non-Archimedean place. Same 8-field `ℤ` shape as the
Archimedean `BihTensor` — the tensor *algebra* is place-agnostic (design `02` §1/§3) —
but with Hensel *shift* reads in place of CF inversion. The three channel commutations
(both inputs and the output pairwise commute) transfer verbatim: each operation acts on
an independent leg, so they commute by `ring`, exactly as for `BihTensor`.

NB (honesty): unlike the single-stream ledger, the *tensor* carries **no** clean scalar
determinant invariant. Whether a `|det|=1`-style quantity is conserved across a node's
two inputs and its output is the handoff's **open** frontier #1 — not claimed here. -/

/-- The p-adic bihomographic tensor
`z = (a·xy + b·x + c·y + d)/(e·xy + f·x + g·y + h)`, two inputs `x, y ∈ ℤ_p`. Flat 8-field
`ℤ` structure (NOT a `Matrix`), so every channel law closes by `ring`. -/
structure PadicBihTensor where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  e : ℤ
  f : ℤ
  g : ℤ
  h : ℤ
  deriving Repr, DecidableEq, Inhabited

namespace PadicBihTensor

/-- **Absorb A**: read a Hensel digit `α` from input `x = α + p·x'` (substitute into the
`x`-leg; pure `ℤ`). -/
def absorbX (p α : ℤ) (T : PadicBihTensor) : PadicBihTensor where
  a := T.a * p
  b := T.b * p
  c := T.a * α + T.c
  d := T.b * α + T.d
  e := T.e * p
  f := T.f * p
  g := T.e * α + T.g
  h := T.f * α + T.h

/-- **Absorb B**: read a Hensel digit `α` from input `y = α + p·y'`. -/
def absorbY (p α : ℤ) (T : PadicBihTensor) : PadicBihTensor where
  a := T.a * p
  b := T.a * α + T.b
  c := T.c * p
  d := T.c * α + T.d
  e := T.e * p
  f := T.e * α + T.f
  g := T.g * p
  h := T.g * α + T.h

/-- **Emit C**: write a Hensel digit `β` of the output `z = β + p·z'` (`z' = (z − β)/p`). -/
def emit (p β : ℤ) (T : PadicBihTensor) : PadicBihTensor where
  a := T.a - β * T.e
  b := T.b - β * T.f
  c := T.c - β * T.g
  d := T.d - β * T.h
  e := T.e * p
  f := T.f * p
  g := T.g * p
  h := T.h * p

/-- **Inputs commute.** Reading from `x` and from `y` commute — the two input channels are
independent (the p-adic dual of `BihTensor.absorbX_absorbY_comm`). -/
theorem absorbX_absorbY_comm (p α α' : ℤ) (T : PadicBihTensor) :
    absorbX p α (absorbY p α' T) = absorbY p α' (absorbX p α T) := by
  cases T; simp only [absorbX, absorbY]; congr 1 <;> ring

/-- **Output is independent of input A.** Emitting to `z` and reading from `x` commute. -/
theorem emit_absorbX_comm (p β α : ℤ) (T : PadicBihTensor) :
    emit p β (absorbX p α T) = absorbX p α (emit p β T) := by
  cases T; simp only [emit, absorbX]; congr 1 <;> ring

/-- **Output is independent of input B.** Emitting to `z` and reading from `y` commute. -/
theorem emit_absorbY_comm (p β α : ℤ) (T : PadicBihTensor) :
    emit p β (absorbY p α T) = absorbY p α (emit p β T) := by
  cases T; simp only [emit, absorbY]; congr 1 <;> ring

end PadicBihTensor

/-! ## 3. Demos (exact integer arithmetic, no floats) -/

/-- The scratch Demo B map `y = (3x+2)/(5x+1)` over `ℤ₅`, as a ledger. -/
def demoMap : PadicLedger := ⟨3, 2, 5, 1⟩

-- `det = 3·1 − 2·5 = −7` (a 5-adic unit: `v₅(−7) = 0`, as the demo map should be).
#eval demoMap.det
-- From the identity, three operations at `p = 5` give `det = 5³ = 125` (the invariant).
#eval (PadicLedger.applyOps 5 PadicLedger.init
        [.absorb 2, .absorb 1, .emit 0]).det
#eval ((5 : ℤ) ^ 3 : ℤ)

end FdrsFormal.Modes.Adelic
