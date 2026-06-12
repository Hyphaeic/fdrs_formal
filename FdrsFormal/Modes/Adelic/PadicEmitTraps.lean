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

# Adelic complex M0d — `padic_emit_traps` over the genuine p-adic integers `ℤ_[p]`

The p-adic emission certificate, lifted from the concrete `ZMod p` soundness M0c
(`ready_sound_mod_p`) to Mathlib's actual ring of p-adic integers `ℤ_[p]` — the
non-Archimedean counterpart of how the Archimedean `emit_traps` is stated over `ℝ` (the
real value is only a *semantic target*; the engine itself stays in `ℤ`). Here `ℚ_p`/`ℤ_p`
is the semantic target, reached through the residue ring homomorphism
`PadicInt.toZMod : ℤ_[p] →+* ZMod p`.

**Statement (M0d).** When `ready` holds, then for *every* p-adic-integer tail `x ∈ ℤ_[p]`
the homographic numerator/denominator reduce mod `p` to

    toZMod(a·x + b)  =  candidate · toZMod(c·x + d),     toZMod(c·x + d) ≠ 0,

i.e. the leading Hensel digit of the value `(a·x+b)/(c·x+d)` is forced to `candidate`,
*regardless of the unread tail* `x`. This is the residue-field "trap" form — the
congruence analogue of the four-corner floor trap `emitReady_traps` — stated without any
p-adic division (the unit-denominator condition makes the digit well-defined; we certify
it multiplicatively).

**How it reduces.** `toZMod` is a ring hom, so it pushes through `+`, `·`, and integer
casts; the value's residue is therefore `valueMod`'s numerator/denominator at the residue
`toZMod x : ZMod p`, and M0c (`ready_sound_mod_p`) pins it. So M0d is a *restatement* of
the concrete M0c over the genuine object, **not** a new hard proof (roadmap `05` M0d).

**Honest scope note.** M0c/M0d certify the digit at an *already-pinned* ledger (`ready`):
"given the trap, the emission is sound." The complementary *liveness* fact — that the
ledger *reaches* the pinned state after finitely many `absorb`s (the digit stabilizes once
a finite input prefix is known) — is the corpus keystone `residue_depends_on_prefix`
(`NumberTheory/CylinderMeasurability.lean`) specialized to constant base `p`; it
belongs to the driver milestone, not to this local-soundness theorem. Conflating the two
is the error the archived design `04` §4 warns against; they are kept separate here.

Leaf module (imports M0b/M0c + Mathlib `PadicInt`). No `sorry`; axiom-clean.
-/
import FdrsFormal.Modes.Adelic.PadicEmission
import Mathlib.NumberTheory.Padics.RingHoms

namespace FdrsFormal.Modes.Adelic

namespace PadicLedger

variable {p : ℕ} [Fact p.Prime]

/-- **M0d — `padic_emit_traps` over `ℤ_[p]`.** When `ready` holds, for every p-adic
integer tail `x ∈ ℤ_[p]` the homographic value's leading residue is forced: the numerator
reduces (mod `p`, via `PadicInt.toZMod`) to `candidate · denom`, with the denominator a
nonzero residue (a unit). So the next Hensel digit of `(a·x+b)/(c·x+d)` is `candidate`,
independent of the unread tail `x`. The genuine-p-adic restatement of `ready_sound_mod_p`
(M0c): the non-Archimedean `emit_traps`, certified by a congruence rather than an order
trap. -/
theorem padic_emit_traps (M : PadicLedger) (h : ready p M = true) (x : ℤ_[p]) :
    PadicInt.toZMod ((M.a : ℤ_[p]) * x + (M.b : ℤ_[p]))
        = candidate p M * PadicInt.toZMod ((M.c : ℤ_[p]) * x + (M.d : ℤ_[p]))
      ∧ PadicInt.toZMod ((M.c : ℤ_[p]) * x + (M.d : ℤ_[p])) ≠ 0 := by
  -- Extract the readiness congruences over `ZMod p`.
  simp only [ready, denomUnitOnDisk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hc, hd⟩, ha⟩ := h
  -- Push the residue hom through the ring operations and the integer casts.
  simp only [map_add, map_mul, map_intCast]
  -- Now everything is over `ZMod p`; the readiness congruences collapse the `x`-terms.
  rw [hc, ha]
  refine ⟨?_, ?_⟩
  · -- numerator residue = candidate · denominator residue
    simp only [zero_mul, zero_add, candidate]
    rw [mul_assoc, inv_mul_cancel₀ hd, mul_one]
  · -- denominator residue is the unit `d ≠ 0`
    simpa using hd

end PadicLedger

end FdrsFormal.Modes.Adelic
