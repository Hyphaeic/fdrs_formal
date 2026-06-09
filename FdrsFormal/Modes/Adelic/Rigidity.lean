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

# Adelic complex — gauge rigidity (the machine's boundary, machine-checked)

The boundary of the whole adelic project, proven. We asked: can an FDRS section with a
*variable* base sequence `b = (b₀, b₁, …)` be glued to a `p`-adic place — a "synthetic
prime" — preserving the place value? The honest answer is **no, except trivially**, and
this file proves it.

The cumulative place value (the Baire-cylinder capacity / FDRS gauge) is
`B_L = placeValue b L = ∏_{i<L} bᵢ`. The `p`-adic place value at depth `L` is `p^L`. The
isometry/alignment condition — "the FDRS gauge matches `|·|_p`" — is `∀ L, B_L = p^L`.

> **`isometric_iff` (gauge rigidity).** `Isometric b p ↔ (∀ i, bᵢ = p)`.

So the gluing constraint **forces the constant base**: the only FDRS section aligned to a
`p`-adic place *is* the constant-`p` one, which is the `p`-adic place itself. There is no
genuine synthetic prime on `ℚ`. Any non-constant base is a **topological drain**
(`not_isometric_of_ne`), and the drain opens at the *first* deviation
(`gauge_deviates`) — a ledger-level safety interlock.

**Honest naming.** This is FDRS-*gauge* rigidity — the necessary condition for a base
sequence to reproduce the `p`-adic place value. It is **not** Ostrowski's theorem (which
classifies *all* absolute values of `ℚ`, and is the *background* fact guaranteeing the
classical places are then the only ones). What is proven here is that the FDRS machine
*respects* that boundary, constructively and import-free.

**Self-containment** (`placeValue_constRadix`): the constant-`p` FDRS gauge *is* `p^L`, so
the machine measures `p`-adic precision with the FDRS-native `placeValue` — no `PadicInt`
import for the metric (the only `ℚ_p` reference in the corpus is M0d's *soundness target*,
as `ℝ` is for `emit_traps`). The constant-`p` section is the isometry-preserving drop-in
for the `p`-adic place. Leaf module. No `sorry`; axiom-clean.
-/
import FdrsFormal.Core.Primitives.PlaceValue
import Mathlib.Tactic

namespace FdrsFormal.Modes.Adelic

open FdrsFormal.Core.Primitives

/-- The constant radix sequence `bᵢ ≡ p` (a `RadixSeq` needs `p ≥ 2`). -/
def constRadix (p : ℕ) (hp : 2 ≤ p) : RadixSeq := ⟨fun _ => p, fun _ => hp⟩

@[simp] theorem constRadix_apply (p : ℕ) (hp : 2 ≤ p) (i : ℕ) :
    (constRadix p hp) i = p := rfl

/-- **Gauge-alignment predicate.** An FDRS section with base `b` is aligned to the p-adic
place `p` when its cumulative place value `B_L = ∏ bᵢ` equals the p-adic place value `p^L`
at every depth — the precise sense of "the FDRS gauge matches `|·|_p`". -/
def Isometric (b : RadixSeq) (p : ℕ) : Prop := ∀ L, placeValue b L = p ^ L

/-- **THE GAUGE RIGIDITY THEOREM.** An FDRS section is gauge-aligned to the p-adic place
`p` **iff** its base sequence is the *constant* sequence `p`. The gluing constraint forces
the classical place — there is no genuine "synthetic prime" on `ℚ`: any non-constant base
breaks the alignment. (FDRS-gauge rigidity — the necessary condition to reproduce the
p-adic place value; Ostrowski is the background fact that the classical places are then the
only places of `ℚ`.) -/
theorem isometric_iff (b : RadixSeq) (p : ℕ) : Isometric b p ↔ ∀ i, b i = p := by
  constructor
  · -- alignment ⟹ constant base: cancel `p^i` from `p^i · bᵢ = p^{i+1} = p^i · p`
    intro hiso i
    have hp0 : 0 < p := by
      have h := hiso 1; rw [pow_one] at h; rw [← h]; exact placeValue.pos 1
    have h1 := hiso (i + 1)
    rw [placeValue.succ, hiso i, pow_succ] at h1
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp0 i) h1
  · -- constant base ⟹ alignment: induction, `B_{L+1} = B_L · p = p^L · p = p^{L+1}`
    intro hb L
    induction L with
    | zero => simp
    | succ L ih => rw [placeValue.succ, ih, hb L, pow_succ]

/-- **Self-containment / the isometry-preserving drop-in.** The constant-`p` FDRS gauge IS
the p-adic place value: `placeValue (constRadix p) L = p^L`. So the adelic machine measures
p-adic precision with the FDRS-native `placeValue` gauge — no `PadicInt` import needed for
the metric. The constant-`p` FDRS section is an exact, alignment-preserving replacement for
the p-adic place value. -/
theorem placeValue_constRadix (p : ℕ) (hp : 2 ≤ p) (L : ℕ) :
    placeValue (constRadix p hp) L = p ^ L :=
  (isometric_iff (constRadix p hp) p).mpr (fun _ => rfl) L

/-- **The drain theorem (failure mode).** Any base that deviates from the constant `p`
(`∃ i, bᵢ ≠ p`) is **not** gauge-aligned — a "topological drain" that would break the
product-formula conservation. The aligned sections are the single point `b ≡ p`. -/
theorem not_isometric_of_ne (b : RadixSeq) (p : ℕ) (h : ∃ i, b i ≠ p) :
    ¬ Isometric b p := fun hiso => by
  obtain ⟨i, hi⟩ := h; exact hi ((isometric_iff b p).mp hiso i)

/-- **The drain opens at the first deviation (the ledger-level interlock).** If the gauge
is still aligned up to depth `i` (`B_i = p^i`) but `bᵢ ≠ p`, then the gauge *fails* at
depth `i+1` (`B_{i+1} ≠ p^{i+1}`). A non-constant base is detectable — and rejectable — at
exactly the depth it deviates, before any product-formula violation can propagate. -/
theorem gauge_deviates (b : RadixSeq) (p : ℕ) (hp : 0 < p) (i : ℕ) (hi : b i ≠ p)
    (h : placeValue b i = p ^ i) : placeValue b (i + 1) ≠ p ^ (i + 1) := by
  rw [placeValue.succ, h, pow_succ]
  exact fun heq => hi (Nat.eq_of_mul_eq_mul_left (pow_pos hp i) heq)

/-! ## Demo — the only aligned base for `p = 5` is the constant `5` (exact ℕ) -/

-- The constant-5 FDRS gauge is exactly the 5-adic place values `5^L`:
#eval (List.range 6).map (placeValue (constRadix 5 (by norm_num)))   -- [1, 5, 25, 125, 625, 3125]
#eval (List.range 6).map (fun L => 5 ^ L)                            -- [1, 5, 25, 125, 625, 3125]
-- a drain: the non-constant base `bᵢ = i+2` deviates from `5` immediately, so its gauge
-- `B₁ = b₀ = 2 ≠ 5 = 5¹` — `not_isometric_of_ne`/`gauge_deviates` reject it.
#eval placeValue ⟨fun i => i + 2, fun i => Nat.le_add_left 2 i⟩ 1   -- 2  (≠ 5¹ = 5: a drain)

end FdrsFormal.Modes.Adelic
