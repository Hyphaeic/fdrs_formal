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

# Homographic carry — the density-free emission engine (single stream)

The exact-real-arithmetic *dual* of `RemainderState.step`. Where `step a` **absorbs**
an input partial quotient (right-multiply the `SL₂(ℤ)` state by `[[a,1],[1,0]]`),
`emit q` **emits** an output partial quotient — the homographic map `v ↦ 1/(v − q)`,
i.e. left-multiply by `[[0,1],[1,-q]]`.

Everything here is exact integer arithmetic — no real density, no rounding. The
engine's correctness is carried by the `|det| = ±1` invariant (`bracket_invariant`),
preserved by *both* channels: `step` flips the determinant, and so does `emit`
(`emit_det`), so the ledger stays unimodular forever. And the two channels **commute**
(`emit_step_comm`): input absorption and output emission are independent — exactly the
streaming-transducer property the irrational-timeline engine is built on.

This is the foundational single-stream brick. The two-stream (bihomographic) coupling
for the A/B mediator `C`, and the carry-frequency accounting that plays the role of
"measure", build on top of it.
-/
import FdrsFormal.Modes.VariableRadix.SubshiftWeight

namespace FdrsFormal.Modes.VariableRadix.RemainderState

/-- **Emit** one output partial quotient `q`: the homographic map `v ↦ 1/(v − q)`,
i.e. left-multiply the `SL₂(ℤ)` state by `[[0,1],[1,-q]]`. The dual of `step`.

**fdrs.md**: Definition 188 (Homographic emission — single stream) [§13.6.1 · Phase 13] -/
def emit (q : ℤ) (r : RemainderState) : RemainderState where
  hPrev := r.qPrev
  hCur  := r.qCur
  qPrev := r.hPrev - q * r.qPrev
  qCur  := r.hCur  - q * r.qCur

/-- Emission flips the determinant (the `[[0,1],[1,-q]]` factor has determinant `-1`). -/
@[simp] theorem emit_det (q : ℤ) (r : RemainderState) : (emit q r).det = - r.det := by
  simp only [det, emit]; ring

/-- **Exactness.** Emission preserves `|det|`, so combined with `init` (`init_det = -1`)
every emit/absorb keeps `|det| = 1`: the engine is exact integer arithmetic, no rounding.

**fdrs.md**: Theorem 80 (Exactness and channel independence) [§13.6.2 · Phase 13] -/
theorem emit_det_natAbs (q : ℤ) (r : RemainderState) :
    (emit q r).det.natAbs = r.det.natAbs := by
  rw [emit_det, Int.natAbs_neg]

/-- **Channel independence.** Absorbing an input quotient and emitting an output quotient
commute — the input and output streams are decoupled. This is the defining property of an
exact-real streaming transducer: the engine can interleave reads and writes freely. -/
theorem emit_step_comm (q : ℤ) (a : ℕ) (r : RemainderState) :
    emit q (step r a) = step (emit q r) a := by
  cases r
  rw [emit, step, step, emit, RemainderState.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- The candidate output quotient: the output floor `⌊M(∞)⌋ = ⌊hCur / qCur⌋`. -/
def emitDigit (r : RemainderState) : ℤ := r.hCur / r.qCur

/-- **Emission is ready** when the output floor agrees at both ends of the input range
`[1, ∞)` — `⌊(hCur+hPrev)/(qCur+qPrev)⌋ = ⌊hCur/qCur⌋` — so the next output quotient is
forced no matter the unread input tail. Guarded by positive denominators. -/
def emitReady (r : RemainderState) : Bool :=
  0 < r.qCur && 0 < r.qCur + r.qPrev &&
    r.hCur / r.qCur == (r.hCur + r.hPrev) / (r.qCur + r.qPrev)

end FdrsFormal.Modes.VariableRadix.RemainderState
