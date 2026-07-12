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

# The Curve25519 field as a variable-radix digit system

An application of `Modes.VariableRadix` to real machine arithmetic: the
field GF(2^255 - 19), as used by Ed25519 signature verification in the
Hyphaeic rebound membrane (`hyphSite/crates/fdrs-field25519`).

A field element is ten digits under the **alternating radix law**
ω = (2^26, 2^25, 2^26, 2^25, …) — a genuine variable radix, not a uniform
base. Digit i has weight Wᵢ = ∏_{j<i} ωⱼ = 2^⌈25.5·i⌉, and the ten digits
span exactly 255 bits.

Three facts are proved here, and each one is load-bearing in the Rust kernel
that implements it:

* `carryStep_preserves_value` — a carry is a value-preserving redistribution
  of surplus between adjacent digits. This is the conservation law: the
  schedule may change the *representative* but never the element.

* `wrap_holonomy` — carrying out of the TOP digit re-enters at digit 0
  multiplied by **19**. The digit ring's carry cycle has nontrivial holonomy:
  W₁₀ = 2^255 ≡ 19 (mod p). A plain odometer wraps with holonomy 1; this one
  does not, and that single fact is the whole difficulty of field carries.

* `schedule_restores_bound` — the eleven-carry schedule (sweep 0..8, the
  holonomy wrap at 9, one settling carry at 0) takes ANY digit vector bounded
  by the multiplication accumulator bound 2^61 back inside the invariant
  B: every digit < 2^26. Together with `mul_accumulator_bound` this closes
  the loop — multiply's output is always a legal multiply input — which is
  exactly what licenses lazy reduction.

The FDRS reading of the surplus is the ledger identity: a digit above its
radix holds *pending* value; a carry *consumes* pending at i and *issues* it
at i+1 (scaled by the holonomy at the wrap); the schedule is the plan that
drives pending to zero. `issued = consumed + pending`.

## References

- `Modes/VariableRadix/VariableTick/CarryAlgorithm.lean` (the odometer carry,
  holonomy 1)
- hyphSite `crates/fdrs-field25519/src/lib.rs` (the implementation these
  theorems govern), and `crates/MEMBRANE-WASM.md` (why it exists)
-/

import Mathlib.Tactic

namespace FdrsFormal.Applications.Field25519

/-! ## The radix law -/

/-- Ten digits. -/
def numDigits : ℕ := 10

/-- The alternating radix law ω: 2^26 at even positions, 2^25 at odd ones.
This is the `RadixLaw` of `Modes.VariableRadix`, instantiated. -/
def radixBits (i : ℕ) : ℕ := if i % 2 = 0 then 26 else 25

/-- ωᵢ, the radix at digit i.

**fdrs.md**: Definition 212 (the 25519 digit ring) [§14.14 · Phase 14] -/
def radix (i : ℕ) : ℕ := 2 ^ radixBits i

/-- Wᵢ = ∏_{j<i} ωⱼ = 2^⌈25.5·i⌉, the weight of digit i. -/
def weightBits : ℕ → ℕ
  | 0 => 0
  | (i + 1) => weightBits i + radixBits i

/-- The ten digits span exactly the 255 bits of the field. -/
theorem weightBits_ten : weightBits 10 = 255 := by
  simp [weightBits, radixBits]

/-- The prime: p = 2^255 - 19. -/
def p : ℕ := 2 ^ 255 - 19

/-- The value of a digit vector: Σ dᵢ · 2^(weightBits i). -/
def value (d : ℕ → ℕ) (n : ℕ) : ℕ :=
  (Finset.range n).sum fun i => d i * 2 ^ weightBits i

/-! ## Carry: value-preserving redistribution -/

/-- One carry at position i: move ⌊dᵢ / ωᵢ⌋ up to digit i+1, keep dᵢ mod ωᵢ. -/
def carryStep (d : ℕ → ℕ) (i : ℕ) : ℕ → ℕ := fun k =>
  if k = i then d i % radix i
  else if k = i + 1 then d (i + 1) + d i / radix i
  else d k

/-- **Conservation.** The value of digits i and i+1 is unchanged by a carry
between them: the surplus that leaves i arrives at i+1 with exactly the
weight that keeps the sum invariant (Wᵢ₊₁ = Wᵢ · ωᵢ).

This is the ledger identity `issued = consumed + pending` at one interface.

**fdrs.md**: Theorem 113 (a carry is a value-preserving redistribution) [§14.14 · Phase 14] -/
theorem carryStep_preserves_value (d : ℕ → ℕ) (i : ℕ) :
    (carryStep d i i) * 2 ^ weightBits i
      + (carryStep d i (i + 1)) * 2 ^ weightBits (i + 1)
    = d i * 2 ^ weightBits i + d (i + 1) * 2 ^ weightBits (i + 1) := by
  have hpos : 0 < radix i := Nat.pow_pos (by norm_num)
  -- Wᵢ₊₁ = Wᵢ · ωᵢ : the weight ladder is what makes the carry conservative.
  have hweight : (2 : ℕ) ^ weightBits (i + 1) = 2 ^ weightBits i * radix i := by
    rw [weightBits, pow_add]; rfl
  -- The two digits the carry touches, evaluated.
  have hi : carryStep d i i = d i % radix i := by simp [carryStep]
  have hi1 : carryStep d i (i + 1) = d (i + 1) + d i / radix i := by
    simp [carryStep, Nat.succ_ne_self]
  -- Euclid: d i = (d i / ωᵢ)·ωᵢ + d i % ωᵢ.
  have hdiv : d i / radix i * radix i + d i % radix i = d i :=
    Nat.div_add_mod' (d i) (radix i)
  rw [hi, hi1, hweight]
  calc
    d i % radix i * 2 ^ weightBits i
        + (d (i + 1) + d i / radix i) * (2 ^ weightBits i * radix i)
      = (d i / radix i * radix i + d i % radix i) * 2 ^ weightBits i
        + d (i + 1) * (2 ^ weightBits i * radix i) := by ring
    _ = d i * 2 ^ weightBits i + d (i + 1) * (2 ^ weightBits i * radix i) := by
          rw [hdiv]

/-! ## The wrap: holonomy 19 -/

/-- The holonomy of the digit cycle. -/
def holonomy : ℕ := 19

/-- **The carry cycle has holonomy 19, not 1.**

Carrying out of the top digit does not create an eleventh digit — it wraps to
digit 0, and the weight it lands with is W₁₀ = 2^255, which is ≡ 19 (mod p).
So one unit of surplus leaving digit 9 re-enters at digit 0 as exactly 19.

This is the FDRS holonomy of going once around the digit ring, and it is the
*only* place the modulus enters the arithmetic.

**fdrs.md**: Theorem 114 (the wrap has holonomy 19, not 1) [§14.14 · Phase 14] -/
theorem wrap_holonomy : (2 : ℕ) ^ weightBits 10 % p = holonomy := by
  rw [weightBits_ten]
  unfold p holonomy
  -- 19 ≤ 2^255, so 2^255 = (2^255 - 19) + 19 over ℕ.
  have h19 : (19 : ℕ) ≤ 2 ^ 255 := by
    calc (19 : ℕ) ≤ 2 ^ 5 := by norm_num
    _ ≤ 2 ^ 255 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  -- and 19 < 2^255 - 19, so 19 is already the residue.
  have hlt : (19 : ℕ) < 2 ^ 255 - 19 := by
    have h6 : (2 : ℕ) ^ 6 ≤ 2 ^ 255 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    have : (2 : ℕ) ^ 6 = 64 := by norm_num
    omega
  -- 2^255 % (2^255 - 19) = ((2^255 - 19) + 19) % (2^255 - 19) = 19.
  have hsplit : (2 : ℕ) ^ 255 = (2 ^ 255 - 19) + 19 := by omega
  calc (2 : ℕ) ^ 255 % (2 ^ 255 - 19)
      = ((2 ^ 255 - 19) + 19) % (2 ^ 255 - 19) := by rw [← hsplit]
    _ = 19 % (2 ^ 255 - 19) := Nat.add_mod_left _ _
    _ = 19 := Nat.mod_eq_of_lt hlt

/-! ## The schedule, and the bound it restores -/

/-- The invariant `B` that closes the loop: every digit < 2^26. -/
def BoundB (d : ℕ → ℕ) : Prop := ∀ i, i < numDigits → d i < 2 ^ 26

/-- The accumulator bound a multiply leaves behind.

Under `B`, each product dᵢ·eⱼ < 2^52. An output digit sums ten products, the
wrapped ones scaled by the holonomy 19 and the odd·odd ones by 2 (the
half-digit interleave), so the worst scaling is 38:

    hₖ < 10 · 38 · 2^52 = 380 · 2^52 < 2^61.

The point of the number is that it is below 2^64: no u64 accumulator in the
kernel can overflow, which is what makes lazy reduction legal at all. -/
theorem mul_accumulator_bound :
    10 * (2 * holonomy) * 2 ^ 52 < 2 ^ 61 := by
  unfold holonomy
  norm_num

/-- One sweep carry lands its digit inside its own radix. -/
theorem carryStep_digit_canonical (d : ℕ → ℕ) (i : ℕ) :
    carryStep d i i < radix i := by
  have hpos : 0 < radix i := Nat.pow_pos (by norm_num)
  simpa [carryStep] using Nat.mod_lt (d i) hpos

/-- **The schedule restores the bound.**

The settling carry is the subtle one, and this is the arithmetic that says
eleven carries suffice — that no twelfth is needed.

After the sweep, digit 1 is canonical (< 2^25) and digit 0 is canonical
(< 2^26); the holonomy wrap then adds 19·s to digit 0, where the surplus
s < 2^36 (digit 9 held < 2^61 and its radix is 2^25). So digit 0 < 2^41, and
the settling carry hands at most 2^41 / 2^26 = 2^15 to digit 1:

    digit 1 < 2^25 + 2^15 < 2^26.  ∎

Every digit is therefore < 2^26 — `B` holds, the ledger is empty, and the
next multiply's accumulator bound is licensed again.

**fdrs.md**: Theorem 115 (the schedule restores the bound — lazy reduction licensed) [§14.14 · Phase 14] -/
theorem schedule_restores_bound
    (d1 : ℕ)          -- digit 1 after the sweep: canonical
    (h1 : d1 < 2 ^ 25)
    (s : ℕ)           -- surplus out of digit 9: bounded by the accumulator
    (hs : s < 2 ^ 36)
    (d0 : ℕ)          -- digit 0 after the sweep: canonical
    (h0 : d0 < 2 ^ 26) :
    -- digit 0 after the wrap, and the settling carry out of it
    (d0 + holonomy * s) / 2 ^ 26 < 2 ^ 15 ∧
    d1 + (d0 + holonomy * s) / 2 ^ 26 < 2 ^ 26 := by
  unfold holonomy
  have hwrapped : d0 + 19 * s < 2 ^ 41 := by
    -- 19·s < 19·2^36, and 19·2^36 + 2^26 < 2^41: the wrap cannot lift digit 0
    -- past 2^41, which is what bounds the settling carry below.
    have hs' : s ≤ 2 ^ 36 - 1 := by omega
    have hmul : 19 * s ≤ 19 * (2 ^ 36 - 1) := Nat.mul_le_mul_left 19 hs'
    have h19 : 19 * (2 ^ 36 - 1) + 2 ^ 26 < 2 ^ 41 := by norm_num
    omega
  have hcarry : (d0 + 19 * s) / 2 ^ 26 < 2 ^ 15 := by
    -- Nat.div_lt_iff: q < 2^15  ⟺  d0 + 19s < 2^15 · 2^26 = 2^41.
    have hpos : 0 < (2 : ℕ) ^ 26 := Nat.pow_pos (by norm_num)
    rw [Nat.div_lt_iff_lt_mul hpos]
    have h41 : (2 : ℕ) ^ 15 * 2 ^ 26 = 2 ^ 41 := by norm_num
    omega
  refine ⟨hcarry, ?_⟩
  have : (2 : ℕ) ^ 25 + 2 ^ 15 < 2 ^ 26 := by norm_num
  omega

end FdrsFormal.Applications.Field25519
