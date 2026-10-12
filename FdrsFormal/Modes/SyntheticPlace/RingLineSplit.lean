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

# Rings and lines: the free/tied split of a carry quotient (Phase 1 addendum, §3.15)

§3.14 found that a product can fail to land only at primes shared by the modulus
`M = |B − c|` and the wrap gain `c`. Split `M = M₁ · M₂` (coprime) into a **free** part
coprime to `c` and a **tied** part dividing a power of `c`. The two parts behave
oppositely:

- **The free part is a ring.** `c` is a unit modulo `M₁`, so the lap value `B ≡ c` has
  finite order `L`, and `B_{k + L N} ≡ B_k (mod M₁)`: after `L` laps the helix of §3.11
  returns to its starting sheet. A path back exists — in the quotient, after `L` laps.
- **The tied part is a line.** `M₂ ∣ c^r` gives `B_{k + r N} ≡ 0 (mod M₂)`: after `r`
  laps every weight vanishes. Residues there cannot circulate; they live on a finite line
  of depth `r` laps.

Products follow the split. Modulo `M₁` every product lands on its target place (every
weight is a unit). Modulo `M₂` it lands exactly on the place of one of its factors
(`B_m B_j = B_j · B_m`). Gluing by CRT, **every product spreads over at most two places**:
its target, carrying the free residue, and its own place `m`, carrying the tied residue.

On `(2, 3, 2)` with `c = −3` (`M = 15 = 5 · 3`) the product of two units at place `1` is
blocked at place `2` (`gcd(6, 15) = 3 ∤ 4`) and spreads to `9` units at place `2` plus
`5` units at place `1`; the free helix closes after `4` laps, the tied line dies after `1`.

Reuses `CarryQuotient.lean` (weights, lap, modulus), `RingUnrolling.lean`
(`placeValue_period`) and `ProductSpread.lean` (landing, the criterion, `weight_dvd_lap`,
the `(2, 3, 2)` ring).

- **Definition 234** (`FreeTiedSplit`): a coprime split of the modulus into a free part
  (coprime to `c`) and a tied part (dividing a power of `c`).
- **Theorem 153** (`weight_laps`, `free_helix_closes`, `tied_line_dies`): the free part is a
  ring whose helix closes; the tied part is a line on which weights die.
- **Theorem 154** (`two_line_spread`): residues landing on two places modulo coprime moduli
  glue to a two-place spread modulo the product.
- **Corollary 53** (`product_spreads`): on a split ring every product spreads over its
  target and its own place.
- **Proposition 181** (`ring232_split`, `ring232_blocked_15`, `ring232_spread_15`,
  `ring232_free_closes`, `ring232_tied_dies`): the `(2, 3, 2)`, `c = −3` witnesses.

**Honest scope.** Elementary (CRT, finite order of a unit). The corpus contributes the
reading of the carry quotient as a ring (free) glued to a line (tied), the path back as
the order of the wrap gain, and the two-place spread. Existence of the canonical split for
every modulus (the `c`-primary part) is not proved here; it is supplied as data.
-/

import FdrsFormal.Modes.SyntheticPlace.ProductSpread

namespace FdrsFormal.Modes.SyntheticPlace.RingLineSplit

open FdrsFormal.Core.Primitives FdrsFormal.Modes.SyntheticPlace.RingUnrolling
open FdrsFormal.Modes.SyntheticPlace.CarryQuotient FdrsFormal.Modes.SyntheticPlace.ProductSpread

/-! ## Theorem 154: gluing two landings -/

/-- **Theorem 154 (two-line spread).** If `t₁ w ≡ v (mod M₁)` and `s₂ w' ≡ v (mod M₂)` with
`M₁, M₂` coprime, then some `t, s` give `t w + s w' ≡ v (mod M₁ M₂)`: a residue that lands
on one place modulo `M₁` and on another modulo `M₂` spreads over the two modulo `M₁ M₂`.

**fdrs.md**: Theorem 154 (two-line spread). -/
theorem two_line_spread {M₁ M₂ : ℕ} (hcop : Nat.Coprime M₁ M₂) {w w' v t₁ s₂ : ℤ}
    (h₁ : (M₁ : ℤ) ∣ t₁ * w - v) (h₂ : (M₂ : ℤ) ∣ s₂ * w' - v) :
    ∃ t s : ℤ, ((M₁ * M₂ : ℕ) : ℤ) ∣ t * w + s * w' - v := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  refine ⟨b * M₂ * t₁, a * M₁ * s₂, ?_⟩
  have e : b * M₂ * t₁ * w + a * M₁ * s₂ * w' - v =
      b * M₂ * (t₁ * w - v) + a * M₁ * (s₂ * w' - v) + (a * M₁ + b * M₂ - 1) * v := by ring
  rw [e, hab, sub_self, zero_mul, add_zero, Nat.cast_mul]
  obtain ⟨x, hx⟩ := h₁
  obtain ⟨y, hy⟩ := h₂
  exact ⟨b * x + a * y, by rw [hx, hy]; ring⟩

/-! ## Definition 234 and Theorem 153: the free ring and the tied line -/

section Ring

variable {n : ℕ} (ρ : Fin (n + 1) → ℕ) (hρ : ∀ i, 2 ≤ ρ i) (c : ℤ)

/-- A **free/tied split** of the modulus `|B − c|`: coprime factors, the free one coprime
to the wrap gain, the tied one dividing a power of it.

**fdrs.md**: Definition 234 (the free/tied split). -/
structure FreeTiedSplit where
  free : ℕ
  tied : ℕ
  laps : ℕ
  mul_eq : free * tied = modulus ρ hρ c
  coprime : Nat.Coprime free tied
  free_coprime : IsCoprime c (free : ℤ)
  tied_dvd : (tied : ℤ) ∣ c ^ laps

theorem modulus_dvd : (modulus ρ hρ c : ℤ) ∣ lapValue ρ hρ - c :=
  Int.natAbs_dvd.mpr dvd_rfl

theorem lap_cast {D : ℕ} (hD : D ∣ modulus ρ hρ c) :
    ((lapValue ρ hρ : ℤ) : ZMod D) = (c : ZMod D) := by
  rw [← sub_eq_zero, ← Int.cast_sub, CharP.intCast_eq_zero_iff (ZMod D) D]
  exact (Int.natCast_dvd_natCast.mpr hD).trans (modulus_dvd ρ hρ c)

/-- Each lap multiplies a weight by the lap value: `B_{k + L N} = B^L B_k`. -/
theorem weight_laps (k : ℕ) : ∀ L, weight ρ hρ (k + L * (n + 1)) = lapValue ρ hρ ^ L * weight ρ hρ k
  | 0 => by simp
  | L + 1 => by
    rw [show k + (L + 1) * (n + 1) = (k + L * (n + 1)) + (n + 1) by ring]
    have h := placeValue_period ρ hρ (k + L * (n + 1))
    have h' : weight ρ hρ (k + L * (n + 1) + (n + 1)) =
        lapValue ρ hρ * weight ρ hρ (k + L * (n + 1)) := by
      simp only [weight, lapValue]; rw [h]; push_cast; ring
    rw [h', weight_laps k L, pow_succ]
    ring

/-- **Theorem 153 (the free part is a ring: its helix closes).** If `c` is coprime to `M₁`
(`M₁ ∣ |B − c|`, `M₁ ≠ 0`), there is `L ≥ 1` with `B_{k + L N} ≡ B_k (mod M₁)` for all `k`:
after `L` laps the helix returns to its starting sheet.

**fdrs.md**: Theorem 153 (the free part is a ring, the tied part a line). -/
theorem free_helix_closes {M₁ : ℕ} [NeZero M₁] (hD : M₁ ∣ modulus ρ hρ c)
    (hfree : IsCoprime c (M₁ : ℤ)) :
    ∃ L, 0 < L ∧ ∀ k, ((weight ρ hρ (k + L * (n + 1)) : ℤ) : ZMod M₁) = (weight ρ hρ k : ℤ) := by
  obtain ⟨a, b, hab⟩ := hfree
  have hu : IsUnit (c : ZMod M₁) := by
    refine IsUnit.of_mul_eq_one (a : ZMod M₁) ?_
    have := congrArg (fun z : ℤ => (z : ZMod M₁)) hab
    push_cast [ZMod.natCast_self] at this
    rw [mul_comm]; simpa using this
  refine ⟨orderOf hu.unit, (isOfFinOrder_of_finite hu.unit).orderOf_pos, fun k => ?_⟩
  rw [weight_laps, Int.cast_mul, Int.cast_pow, lap_cast ρ hρ c hD]
  have h1 : (c : ZMod M₁) ^ orderOf hu.unit = 1 := by
    calc (c : ZMod M₁) ^ orderOf hu.unit = (hu.unit : ZMod M₁) ^ orderOf hu.unit := by
          rw [hu.unit_spec]
      _ = ((hu.unit ^ orderOf hu.unit : (ZMod M₁)ˣ) : ZMod M₁) := (Units.val_pow_eq_pow_val _ _).symm
      _ = 1 := by rw [pow_orderOf_eq_one, Units.val_one]
  rw [h1, one_mul]

/-- **Theorem 153 (the tied part is a line: its weights die).** If `M₂ ∣ c^r`
(`M₂ ∣ |B − c|`), then `B_{k + r N} ≡ 0 (mod M₂)` for all `k`: after `r` laps nothing
survives.

**fdrs.md**: Theorem 153 (the free part is a ring, the tied part a line). -/
theorem tied_line_dies {M₂ r : ℕ} (hD : M₂ ∣ modulus ρ hρ c) (htied : (M₂ : ℤ) ∣ c ^ r)
    (k : ℕ) : ((weight ρ hρ (k + r * (n + 1)) : ℤ) : ZMod M₂) = 0 := by
  rw [weight_laps, Int.cast_mul, Int.cast_pow, lap_cast ρ hρ c hD, ← Int.cast_pow,
    (CharP.intCast_eq_zero_iff (ZMod M₂) M₂ _).mpr htied, zero_mul]

/-! ## Corollary 53: every product spreads over two places -/

theorem free_lands {M₁ : ℕ} (hD : M₁ ∣ modulus ρ hρ c) (hfree : IsCoprime c (M₁ : ℤ))
    (m j : Fin (n + 1)) :
    ∃ t : ℤ, (M₁ : ℤ) ∣ t * (landingGain c m j * weight ρ hρ (m + j : Fin (n + 1))) -
      weight ρ hρ m * weight ρ hρ j := by
  have hB : IsCoprime (lapValue ρ hρ) (M₁ : ℤ) := by
    obtain ⟨x, hx⟩ := (Int.natCast_dvd_natCast.mpr hD).trans (modulus_dvd ρ hρ c)
    have := hfree.add_mul_left_left x
    rwa [← hx, add_sub_cancel] at this
  have hW : IsCoprime (weight ρ hρ (m + j : Fin (n + 1))) (M₁ : ℤ) :=
    hB.of_isCoprime_of_dvd_left (weight_dvd_lap ρ hρ _)
  have hE : IsCoprime (landingGain c m j) (M₁ : ℤ) := by
    unfold landingGain; split_ifs
    · exact isCoprime_one_left
    · exact hfree
  obtain ⟨t, ht⟩ := (lands_iff_gcd M₁ (landingGain c m j * weight ρ hρ (m + j : Fin (n + 1)))
    (weight ρ hρ m * weight ρ hρ j)).mpr (by
      rw [Int.isCoprime_iff_gcd_eq_one.mp (hE.mul_left hW), Nat.cast_one]; exact one_dvd _)
  refine ⟨t, ?_⟩
  rw [← sub_eq_zero, ← Int.cast_sub, CharP.intCast_eq_zero_iff (ZMod M₁) M₁] at ht
  exact ht

/-- **Corollary 53 (every product spreads over two places).** On a ring with a free/tied
split, the product of places `m` and `j` is carried by its target place `m + j (mod N)`
(the free residue) together with place `m` (the tied residue).

**fdrs.md**: Corollary 53 (every product spreads over two places). -/
theorem product_spreads (S : FreeTiedSplit ρ hρ c) (m j : Fin (n + 1)) :
    ∃ t s : ℤ, ((t * (landingGain c m j * weight ρ hρ (m + j : Fin (n + 1))) +
        s * weight ρ hρ m : ℤ) : ZMod (modulus ρ hρ c)) =
      ((weight ρ hρ m * weight ρ hρ j : ℤ) : ZMod (modulus ρ hρ c)) := by
  have hD : S.free ∣ modulus ρ hρ c := ⟨S.tied, S.mul_eq.symm⟩
  obtain ⟨t₁, h₁⟩ := free_lands ρ hρ c hD S.free_coprime m j
  have h₂ : (S.tied : ℤ) ∣ weight ρ hρ j * weight ρ hρ m - weight ρ hρ m * weight ρ hρ j := by
    rw [mul_comm, sub_self]; exact dvd_zero _
  obtain ⟨t, s, h⟩ := two_line_spread S.coprime h₁ h₂
  refine ⟨t, s, ?_⟩
  rw [← sub_eq_zero, ← Int.cast_sub, CharP.intCast_eq_zero_iff (ZMod (modulus ρ hρ c)),
    ← S.mul_eq]
  exact h

end Ring

/-! ## Proposition 181: the (2, 3, 2) ring with wrap gain −3 -/

section Witness

theorem ring232_modulus_15 : modulus ring232 ring232_ge_two (-3) = 15 := rfl

/-- **Proposition 181 (the split `15 = 5 · 3`).** Free part `5` (coprime to `−3`), tied part
`3` (dividing `(−3)^1`).

**fdrs.md**: Proposition 181 (the (2,3,2), c = −3 witnesses). -/
def ring232_split : FreeTiedSplit ring232 ring232_ge_two (-3) where
  free := 5
  tied := 3
  laps := 1
  mul_eq := ring232_modulus_15.symm
  coprime := by decide
  free_coprime := Int.isCoprime_iff_gcd_eq_one.mpr (by decide)
  tied_dvd := ⟨-1, by norm_num⟩

/-- **Proposition 181 (blocked modulo 15).** `gcd(6, 15) = 3 ∤ 4`.

**fdrs.md**: Proposition 181 (the (2,3,2), c = −3 witnesses). -/
theorem ring232_blocked_15 : ¬ Lands ring232 ring232_ge_two (-3) 1 1 := by
  rw [lands_iff, ring232_modulus_15]
  decide

/-- **Proposition 181 (the two-place spread).** `9` units at place `2` plus `5` units at
place `1` carry the product of two units at place `1`: `9 · 6 + 5 · 2 ≡ 4 (mod 15)`.

**fdrs.md**: Proposition 181 (the (2,3,2), c = −3 witnesses). -/
theorem ring232_spread_15 :
    ((9 * (landingGain (-3) (1 : Fin 3) 1 * weight ring232 ring232_ge_two ((1 : Fin 3) + 1)) +
        5 * weight ring232 ring232_ge_two (1 : Fin 3) : ℤ) :
      ZMod (modulus ring232 ring232_ge_two (-3))) =
      ((weight ring232 ring232_ge_two (1 : Fin 3) * weight ring232 ring232_ge_two (1 : Fin 3) : ℤ) :
        ZMod (modulus ring232 ring232_ge_two (-3))) := by
  rw [ring232_modulus_15]
  decide

/-- **Proposition 181 (the free helix closes after 4 laps).** Modulo `5`, `B = 12 ≡ 2` and
`2^4 ≡ 1`, so `B_{k+12} ≡ B_k`.

**fdrs.md**: Proposition 181 (the (2,3,2), c = −3 witnesses). -/
theorem ring232_free_closes (k : ℕ) :
    ((weight ring232 ring232_ge_two (k + 4 * 3) : ℤ) : ZMod 5) = (weight ring232 ring232_ge_two k : ℤ) := by
  rw [weight_laps ring232 ring232_ge_two k 4, Int.cast_mul, Int.cast_pow,
    show lapValue ring232 ring232_ge_two = 12 from rfl]
  have : ((12 : ℤ) : ZMod 5) ^ 4 = 1 := by decide
  rw [this, one_mul]

/-- **Proposition 181 (the tied line dies after one lap).** Modulo `3`, every weight past
the first lap vanishes.

**fdrs.md**: Proposition 181 (the (2,3,2), c = −3 witnesses). -/
theorem ring232_tied_dies (k : ℕ) :
    ((weight ring232 ring232_ge_two (k + 1 * 3) : ℤ) : ZMod 3) = 0 :=
  tied_line_dies ring232 ring232_ge_two (-3) (by rw [ring232_modulus_15]; decide) ⟨-1, by norm_num⟩ k

end Witness

end FdrsFormal.Modes.SyntheticPlace.RingLineSplit
