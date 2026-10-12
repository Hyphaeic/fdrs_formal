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

# The radix complex of a wrapped ring: a ring, a line, and the hop between them
(Phase 1 addendum, §3.16)

§3.15 split the carry quotient `ℤ/M` (`M = |B − c|`) into a free part `M₁`, where the
helix closes, and a tied part `M₂`, where weights die. This file treats the two parts as
**branches of one radix complex** and asks how they meet.

- **The helix is a rho.** Read in `ℤ/M`, the weights `B_k` run down a tail and into a
  cycle: past depth `r N` (the tied line's depth) they are periodic with period `L N`
  (`L` the order of the wrap on the free branch). Weights still carrying tied residue
  never come back: the start of the helix is not revisited.
- **The tied branch is a radix line.** `M₂ ∣ B_{rN}`, so every tied residue is the value of
  a digit string on the open (unwrapped) line of the periodic schedule, truncated at depth
  `r N` — an ordinary finite mixed-radix space (Proposition 1).
- **Branches are orthogonal.** The CRT idempotents `ε_free + ε_tied = 1`,
  `ε_free ε_tied = 0` split every product: `x y = (ε_free x)(ε_free y) + (ε_tied x)(ε_tied y)`.
  A free residue times a tied residue is zero: different residue types do not couple
  through products; each type multiplies on its own branch.
- **The path back is a hop.** For every place `k`,
  `B_k ≡ ε_free · B_{k + L N} + ε_tied · B_k (mod M)`: the free share returns around the
  ring, the tied share is held on the line. A path back to any sheet exists — through
  both branches of the complex, not along the helix alone.

Witnesses on `(2, 3, 2)` with `c = −3` (`15 = 5 · 3`): the idempotents are `6` and `10`;
past depth `3` the weights repeat with period `12`; the start `B_0 = 1` is never revisited.

Reuses `RingLineSplit.lean` (the split, the closing ring, the dying line),
`CarryQuotient.lean` (weights, modulus), `Core/Finite/Bijection.lean` (finite radix
spaces, `decodeFinite_surjective`) and `ProductSpread.lean` (the `(2, 3, 2)` ring).

- **Definition 235** (`freeIdem`, `tiedIdem`): the branch idempotents of a split.
- **Theorem 155** (`helix_rho`, `no_return`): the helix in the quotient is a rho; tied
  sheets are never revisited.
- **Theorem 156** (`tied_dvd_line`, `tied_line_digits`): the tied branch is a finite
  radix line.
- **Theorem 157** (`idem_sum`, `idem_orth`, `freeIdem_sq`, `tiedIdem_sq`, `mixed_vanish`,
  `mul_split`, `idem_unique`): the branches are orthogonal.
- **Corollary 54** (`path_back_hop`): the path back is a hop through both branches.
- **Proposition 182** (`ring232_freeIdem`, `ring232_tiedIdem`, `ring232_rho`,
  `ring232_no_return`, `ring232_line`): the `(2, 3, 2)`, `c = −3` witnesses.

**Honest scope.** Elementary (CRT idempotents, eventually periodic sequences). The corpus
contributes the reading of the carry quotient as a two-branch radix complex — a closing
ring and an open line — the tied branch as a finite radix space, and the path back as a
hop between branches. Several tied primes (several lines), coupling of branches through
carries (rather than products), and context-chosen radices for new branches are not
covered.
-/

import FdrsFormal.Modes.SyntheticPlace.RingLineSplit

namespace FdrsFormal.Modes.SyntheticPlace.BranchComplex

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite
open FdrsFormal.Modes.SyntheticPlace.RingUnrolling FdrsFormal.Modes.SyntheticPlace.CarryQuotient
open FdrsFormal.Modes.SyntheticPlace.ProductSpread FdrsFormal.Modes.SyntheticPlace.RingLineSplit

section Ring

variable {n : ℕ} (ρ : Fin (n + 1) → ℕ) (hρ : ∀ i, 2 ≤ ρ i) (c : ℤ) (S : FreeTiedSplit ρ hρ c)

theorem free_dvd_mod : S.free ∣ modulus ρ hρ c := ⟨S.tied, S.mul_eq.symm⟩

theorem tied_dvd_mod : S.tied ∣ modulus ρ hρ c := ⟨S.free, by rw [← S.mul_eq, mul_comm]⟩

theorem dvd_of_zmod {D : ℕ} {x y : ℤ} (h : (x : ZMod D) = (y : ZMod D)) : (D : ℤ) ∣ x - y := by
  rwa [← sub_eq_zero, ← Int.cast_sub, CharP.intCast_eq_zero_iff (ZMod D) D] at h

/-- Congruent modulo both branches, congruent modulo `M`. -/
theorem eq_of_dvd {x y : ℤ} (h1 : (S.free : ℤ) ∣ x - y) (h2 : (S.tied : ℤ) ∣ x - y) :
    (x : ZMod (modulus ρ hρ c)) = (y : ZMod (modulus ρ hρ c)) := by
  rw [← sub_eq_zero, ← Int.cast_sub, CharP.intCast_eq_zero_iff (ZMod _) (modulus ρ hρ c),
    ← S.mul_eq, Nat.cast_mul]
  exact (Nat.isCoprime_iff_coprime.mpr S.coprime).mul_dvd h1 h2

/-! ## Definition 235: the branch idempotents -/

theorem split_coprime : IsCoprime (S.free : ℤ) (S.tied : ℤ) :=
  Nat.isCoprime_iff_coprime.mpr S.coprime

/-- The free idempotent: `≡ 1` on the free branch, `≡ 0` on the tied branch.

**fdrs.md**: Definition 235 (the branch idempotents). -/
noncomputable def freeIdem : ℤ :=
  Classical.choose (Classical.choose_spec (split_coprime ρ hρ c S)) * S.tied

/-- The tied idempotent: `≡ 0` on the free branch, `≡ 1` on the tied branch.

**fdrs.md**: Definition 235 (the branch idempotents). -/
noncomputable def tiedIdem : ℤ := Classical.choose (split_coprime ρ hρ c S) * S.free

theorem idem_sum_int : freeIdem ρ hρ c S + tiedIdem ρ hρ c S = 1 := by
  have h := Classical.choose_spec (Classical.choose_spec (split_coprime ρ hρ c S))
  rw [freeIdem, tiedIdem]; linarith

theorem tied_dvd_freeIdem : (S.tied : ℤ) ∣ freeIdem ρ hρ c S := dvd_mul_left _ _

theorem free_dvd_tiedIdem : (S.free : ℤ) ∣ tiedIdem ρ hρ c S := dvd_mul_left _ _

theorem free_dvd_freeIdem_sub : (S.free : ℤ) ∣ freeIdem ρ hρ c S - 1 := by
  have h := idem_sum_int ρ hρ c S
  rw [show freeIdem ρ hρ c S - 1 = -tiedIdem ρ hρ c S by linarith]
  exact (free_dvd_tiedIdem ρ hρ c S).neg_right

theorem tied_dvd_tiedIdem_sub : (S.tied : ℤ) ∣ tiedIdem ρ hρ c S - 1 := by
  have h := idem_sum_int ρ hρ c S
  rw [show tiedIdem ρ hρ c S - 1 = -freeIdem ρ hρ c S by linarith]
  exact (tied_dvd_freeIdem ρ hρ c S).neg_right

/-! ## Theorem 157: the branches are orthogonal -/

local notation "Q" => ZMod (modulus ρ hρ c)

/-- **Theorem 157 (the idempotents sum to one).**

**fdrs.md**: Theorem 157 (the branches are orthogonal). -/
theorem idem_sum : ((freeIdem ρ hρ c S : ℤ) : Q) + (tiedIdem ρ hρ c S : ℤ) = 1 := by
  rw [← Int.cast_add, idem_sum_int, Int.cast_one]

/-- **Theorem 157 (the idempotents are orthogonal).**

**fdrs.md**: Theorem 157 (the branches are orthogonal). -/
theorem idem_orth : ((freeIdem ρ hρ c S : ℤ) : Q) * (tiedIdem ρ hρ c S : ℤ) = 0 := by
  rw [← Int.cast_mul, ← Int.cast_zero]
  refine eq_of_dvd ρ hρ c S ?_ ?_
  · rw [sub_zero]; exact (free_dvd_tiedIdem ρ hρ c S).mul_left _
  · rw [sub_zero]; exact (tied_dvd_freeIdem ρ hρ c S).mul_right _

theorem freeIdem_sq : ((freeIdem ρ hρ c S : ℤ) : Q) ^ 2 = (freeIdem ρ hρ c S : ℤ) := by
  rw [← Int.cast_pow]
  refine eq_of_dvd ρ hρ c S ?_ ?_
  · rw [show freeIdem ρ hρ c S ^ 2 - freeIdem ρ hρ c S =
      freeIdem ρ hρ c S * (freeIdem ρ hρ c S - 1) by ring]
    exact (free_dvd_freeIdem_sub ρ hρ c S).mul_left _
  · rw [show freeIdem ρ hρ c S ^ 2 - freeIdem ρ hρ c S =
      freeIdem ρ hρ c S * (freeIdem ρ hρ c S - 1) by ring]
    exact (tied_dvd_freeIdem ρ hρ c S).mul_right _

theorem tiedIdem_sq : ((tiedIdem ρ hρ c S : ℤ) : Q) ^ 2 = (tiedIdem ρ hρ c S : ℤ) := by
  rw [← Int.cast_pow]
  refine eq_of_dvd ρ hρ c S ?_ ?_
  · rw [show tiedIdem ρ hρ c S ^ 2 - tiedIdem ρ hρ c S =
      tiedIdem ρ hρ c S * (tiedIdem ρ hρ c S - 1) by ring]
    exact (free_dvd_tiedIdem ρ hρ c S).mul_right _
  · rw [show tiedIdem ρ hρ c S ^ 2 - tiedIdem ρ hρ c S =
      tiedIdem ρ hρ c S * (tiedIdem ρ hρ c S - 1) by ring]
    exact (tied_dvd_tiedIdem_sub ρ hρ c S).mul_left _

/-- **Theorem 157 (mixed products vanish).** A free residue times a tied residue is zero.

**fdrs.md**: Theorem 157 (the branches are orthogonal). -/
theorem mixed_vanish (x y : Q) :
    (((freeIdem ρ hρ c S : ℤ) : Q) * x) * (((tiedIdem ρ hρ c S : ℤ) : Q) * y) = 0 := by
  rw [show (((freeIdem ρ hρ c S : ℤ) : Q) * x) * (((tiedIdem ρ hρ c S : ℤ) : Q) * y) =
    (((freeIdem ρ hρ c S : ℤ) : Q) * (tiedIdem ρ hρ c S : ℤ)) * (x * y) by ring,
    idem_orth, zero_mul]

/-- **Theorem 157 (every product splits by branch).**
`x y = (ε_free x)(ε_free y) + (ε_tied x)(ε_tied y)`.

**fdrs.md**: Theorem 157 (the branches are orthogonal). -/
theorem mul_split (x y : Q) :
    x * y = (((freeIdem ρ hρ c S : ℤ) : Q) * x) * (((freeIdem ρ hρ c S : ℤ) : Q) * y) +
      (((tiedIdem ρ hρ c S : ℤ) : Q) * x) * (((tiedIdem ρ hρ c S : ℤ) : Q) * y) := by
  have h1 := freeIdem_sq ρ hρ c S
  have h2 := tiedIdem_sq ρ hρ c S
  have hs := idem_sum ρ hρ c S
  calc x * y = (((freeIdem ρ hρ c S : ℤ) : Q) + (tiedIdem ρ hρ c S : ℤ)) * (x * y) := by
        rw [hs, one_mul]
    _ = ((freeIdem ρ hρ c S : ℤ) : Q) ^ 2 * (x * y) +
          ((tiedIdem ρ hρ c S : ℤ) : Q) ^ 2 * (x * y) := by rw [h1, h2]; ring
    _ = _ := by ring

/-- **Theorem 157 (the idempotents are canonical).** Any `e ≡ 1` on the free branch and
`≡ 0` on the tied branch is the free idempotent.

**fdrs.md**: Theorem 157 (the branches are orthogonal). -/
theorem idem_unique {e : ℤ} (h1 : (S.free : ℤ) ∣ e - 1) (h2 : (S.tied : ℤ) ∣ e) :
    (e : Q) = (freeIdem ρ hρ c S : ℤ) := by
  refine eq_of_dvd ρ hρ c S ?_ ?_
  · rw [show e - freeIdem ρ hρ c S = (e - 1) - (freeIdem ρ hρ c S - 1) by ring]
    exact dvd_sub h1 (free_dvd_freeIdem_sub ρ hρ c S)
  · exact dvd_sub h2 (tied_dvd_freeIdem ρ hρ c S)

/-! ## Theorem 155: the helix is a rho -/

theorem tied_dies_dvd (j : ℕ) : (S.tied : ℤ) ∣ weight ρ hρ (j + S.laps * (n + 1)) :=
  (CharP.intCast_eq_zero_iff (ZMod S.tied) S.tied _).mp
    (tied_line_dies ρ hρ c (tied_dvd_mod ρ hρ c S) S.tied_dvd j)

/-- **Theorem 155 (the helix is a rho).** Past the depth `r N` of the tied line, the
weights are periodic modulo `M` with period `L N`, `L ≥ 1` the closing time of the free
ring: a tail (the line) running into a cycle (the ring).

**fdrs.md**: Theorem 155 (the helix in the quotient is a rho). -/
theorem helix_rho [NeZero S.free] : ∃ L, 0 < L ∧ ∀ j,
    ((weight ρ hρ (j + S.laps * (n + 1) + L * (n + 1)) : ℤ) : Q) =
      (weight ρ hρ (j + S.laps * (n + 1)) : ℤ) := by
  obtain ⟨L, hL, hcl⟩ := free_helix_closes ρ hρ c (free_dvd_mod ρ hρ c S) S.free_coprime
  refine ⟨L, hL, fun j => eq_of_dvd ρ hρ c S (dvd_of_zmod (hcl _)) ?_⟩
  have h2 := tied_dies_dvd ρ hρ c S (j + L * (n + 1))
  rw [show j + L * (n + 1) + S.laps * (n + 1) = j + S.laps * (n + 1) + L * (n + 1) by ring] at h2
  exact dvd_sub h2 (tied_dies_dvd ρ hρ c S j)

/-- **Theorem 155 (tied sheets are never revisited).** If the weight `B_k` still carries
tied residue (`M₂ ∤ B_k`), no weight past the depth of the tied line is congruent to it
modulo `M`.

**fdrs.md**: Theorem 155 (the helix in the quotient is a rho). -/
theorem no_return (k : ℕ) (hk : ¬ (S.tied : ℤ) ∣ weight ρ hρ k) (j : ℕ) :
    ((weight ρ hρ (j + S.laps * (n + 1)) : ℤ) : Q) ≠ (weight ρ hρ k : ℤ) := by
  intro h
  have hd := (Int.natCast_dvd_natCast.mpr (tied_dvd_mod ρ hρ c S)).trans (dvd_of_zmod h)
  apply hk
  have := dvd_sub (tied_dies_dvd ρ hρ c S j) hd
  rwa [sub_sub_cancel] at this

/-! ## Theorem 156: the tied branch is a radix line -/

/-- **Theorem 156 (the tied modulus divides the line's place value).**
`M₂ ∣ B_{rN}`.

**fdrs.md**: Theorem 156 (the tied branch is a radix line). -/
theorem tied_dvd_line : S.tied ∣ placeValue (ringSchedule ρ hρ) (S.laps * (n + 1)) := by
  have h := tied_dies_dvd ρ hρ c S 0
  rw [zero_add, weight] at h
  exact Int.natCast_dvd_natCast.mp h

theorem tied_ne_zero : S.tied ≠ 0 := by
  intro h
  have := tied_dvd_line ρ hρ c S
  rw [h, zero_dvd_iff] at this
  exact placeValue.ne_zero _ this

/-- **Theorem 156 (every tied residue has digits on the line).** Every residue modulo
`M₂` is the value of a digit string on the open line of the periodic schedule of depth
`r N`.

**fdrs.md**: Theorem 156 (the tied branch is a radix line). -/
theorem tied_line_digits (x : ZMod S.tied) :
    ∃ σ : FiniteRadixSpace (ringSchedule ρ hρ) (S.laps * (n + 1)),
      ((decodeFinite (ringSchedule ρ hρ) _ σ : ℕ) : ZMod S.tied) = x := by
  haveI : NeZero S.tied := ⟨tied_ne_zero ρ hρ c S⟩
  have hlt : x.val < placeValue (ringSchedule ρ hρ) (S.laps * (n + 1) + 1) :=
    calc x.val < S.tied := ZMod.val_lt x
      _ ≤ placeValue (ringSchedule ρ hρ) (S.laps * (n + 1)) :=
          Nat.le_of_dvd (placeValue.pos _) (tied_dvd_line ρ hρ c S)
      _ < _ := placeValue.strictMono (Nat.lt_succ_self _)
  obtain ⟨σ, hσ⟩ := decodeFinite_surjective (b := ringSchedule ρ hρ) _ ⟨x.val, hlt⟩
  exact ⟨σ, by rw [hσ]; exact ZMod.natCast_zmod_val x⟩

/-! ## Corollary 54: the path back is a hop -/

/-- **Corollary 54 (the path back is a hop).** For some `L ≥ 1` and every place `k`,
`B_k ≡ ε_free · B_{k + L N} + ε_tied · B_k (mod M)`: the free share of the sheet returns
around the ring after `L` laps, the tied share is held on the line.

**fdrs.md**: Corollary 54 (the path back is a hop). -/
theorem path_back_hop [NeZero S.free] : ∃ L, 0 < L ∧ ∀ k,
    ((weight ρ hρ k : ℤ) : Q) =
      ((freeIdem ρ hρ c S * weight ρ hρ (k + L * (n + 1)) +
        tiedIdem ρ hρ c S * weight ρ hρ k : ℤ) : Q) := by
  obtain ⟨L, hL, hcl⟩ := free_helix_closes ρ hρ c (free_dvd_mod ρ hρ c S) S.free_coprime
  refine ⟨L, hL, fun k => eq_of_dvd ρ hρ c S ?_ ?_⟩
  all_goals
    have ht : tiedIdem ρ hρ c S = 1 - freeIdem ρ hρ c S := by
      have := idem_sum_int ρ hρ c S; linarith
    rw [ht, show weight ρ hρ k - (freeIdem ρ hρ c S * weight ρ hρ (k + L * (n + 1)) +
        (1 - freeIdem ρ hρ c S) * weight ρ hρ k) =
        -(freeIdem ρ hρ c S * (weight ρ hρ (k + L * (n + 1)) - weight ρ hρ k)) by ring]
  · exact ((dvd_of_zmod (hcl k)).mul_left _).neg_right
  · exact ((tied_dvd_freeIdem ρ hρ c S).mul_right _).neg_right

end Ring

/-! ## Proposition 182: the (2, 3, 2), c = −3 witnesses -/

section Witness

local notation "Q15" => ZMod (modulus ring232 ring232_ge_two (-3))

/-- **Proposition 182 (the idempotents are 6 and 10).**

**fdrs.md**: Proposition 182 (the (2,3,2), c = −3 complex). -/
theorem ring232_freeIdem :
    ((6 : ℤ) : Q15) = (freeIdem ring232 ring232_ge_two (-3) ring232_split : ℤ) :=
  idem_unique _ _ _ _ (by decide) (by decide)

theorem ring232_tiedIdem :
    ((10 : ℤ) : Q15) = (tiedIdem ring232 ring232_ge_two (-3) ring232_split : ℤ) := by
  have hs := idem_sum ring232 ring232_ge_two (-3) ring232_split
  rw [← ring232_freeIdem] at hs
  rw [eq_sub_of_add_eq' hs, ring232_modulus_15]
  decide

/-- **Proposition 182 (the rho).** Past depth `3` the weights repeat with period `12`
modulo `15` (`12^5 ≡ 12`).

**fdrs.md**: Proposition 182 (the (2,3,2), c = −3 complex). -/
theorem ring232_rho (j : ℕ) :
    ((weight ring232 ring232_ge_two (j + 1 * 3 + 4 * 3) : ℤ) : Q15) =
      (weight ring232 ring232_ge_two (j + 1 * 3) : ℤ) := by
  rw [show j + 1 * 3 + 4 * 3 = j + 5 * 3 by ring, weight_laps ring232 ring232_ge_two j 5,
    weight_laps ring232 ring232_ge_two j 1, show lapValue ring232 ring232_ge_two = 12 from rfl,
    ring232_modulus_15]
  push_cast
  have : (248832 : ZMod 15) = 12 := by decide
  rw [this]

/-- **Proposition 182 (the start is never revisited).** No weight past depth `3` is
`≡ 1 (mod 15)`: sheet `1` carries tied residue (`3 ∤ 1`).

**fdrs.md**: Proposition 182 (the (2,3,2), c = −3 complex). -/
theorem ring232_no_return (j : ℕ) :
    ((weight ring232 ring232_ge_two (j + 1 * 3) : ℤ) : Q15) ≠ (weight ring232 ring232_ge_two 0 : ℤ) :=
  no_return ring232 ring232_ge_two (-3) ring232_split 0 (by decide) j

/-- **Proposition 182 (the tied line has depth 3).** `3 ∣ B_3 = 12`: tied residues live on
the line `1, 2, 6` (radices `2, 3, 2`).

**fdrs.md**: Proposition 182 (the (2,3,2), c = −3 complex). -/
theorem ring232_line : 3 ∣ placeValue (ringSchedule ring232 ring232_ge_two) 3 :=
  tied_dvd_line ring232 ring232_ge_two (-3) ring232_split

end Witness

end FdrsFormal.Modes.SyntheticPlace.BranchComplex
