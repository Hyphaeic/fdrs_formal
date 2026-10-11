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

# Products that do not close (Phase 1 addendum, §3.14)

§3.13 multiplied on product-closed rings, where `κ(m, j) = B_m B_j / B_{m+j}` is an integer.
On a ring such as `(2, 3, 2)` it is not (`κ(1, 1) = 4/6`): over the integers the product of
two units at place `1` cannot land on place `2`. This file asks where products can land
once the ring is closed by its wrap, i.e. in the carry quotient `ℤ/(B − c)` (§3.12).

- Any **product table** — any choice of states `T(m, j)` carrying the class of `B_m B_j` —
  gives a multiplication law; products may be spread over several places.
- A product **lands** on its target place `m + j (mod N)` with an integer coefficient
  exactly when `gcd(ε B_{m+j}, B − c) ∣ B_m B_j` (`ε = c` on a wrap): the residue that
  fails to merge over `ℚ` merges in the quotient precisely when this gcd allows it.
- If the wrap gain is coprime to the lap value, every product lands: every ring is
  **residue-closed**, and multiplication is a mixed wrapped convolution (§3.13) with
  *residue* coefficients. On `(2, 3, 2)` with `c = 1`, `κ(1, 1) = 4/6` is `8` in `ℤ/11`.
- If not, landing can fail: on `(2, 3, 2)` with `c = 3` the product of two units at place
  `1` cannot land on place `2` even modulo `9` (`gcd(6, 9) = 3 ∤ 4`); it must spread — here
  to `2` units at place `1`.

Reuses `CarryQuotient.lean` (the value map and its quotient) and `MixedRingProduct.lean`
(mixed wrapped convolution, Theorem 149, product-closed rings).

- **Definition 233** (`ProductTable`, `spreadMul`, `landingGain`, `Lands`, `ResidueClosed`).
- **Theorem 151** (`ev_spreadMul`, `collapse_table`): every product table multiplies;
  every ring has one.
- **Theorem 152** (`lands_iff_gcd`, `lands_iff`): the landing criterion.
- **Corollary 52** (`ev_residueConv`, `residueClosed_of_coprime`): residue-closed rings
  multiply by mixed wrapped convolution; a wrap gain coprime to the lap closes every ring.
- **Proposition 180** (`ring232_not_productClosed`, `ring232_residue_one`,
  `ring232_kappa_eight`, `ring232_blocked`, `ring232_spread`): the `(2, 3, 2)` witnesses.

**Honest scope.** Elementary (linear congruences, Bézout). The corpus contributes the
landing criterion for its carry rings, the separation of integer closure (§3.13) from
residue closure, and the witnesses. The canonical spread of a blocked product (which
places, which residue lines) is not determined here.
-/

import FdrsFormal.Modes.SyntheticPlace.MixedRingProduct

namespace FdrsFormal.Modes.SyntheticPlace.ProductSpread

open FdrsFormal.Core.Primitives FdrsFormal.Modes.SyntheticPlace.RingUnrolling
open FdrsFormal.Modes.SyntheticPlace.CarryQuotient FdrsFormal.Modes.SyntheticPlace.MixedRingProduct

/-! ## Theorem 152 (abstract form): when does `t · w ≡ v (mod M)` have a solution? -/

/-- **Theorem 152 (the landing criterion, abstract).** `t · w ≡ v (mod M)` is solvable in
integers iff `gcd(w, M) ∣ v`.

**fdrs.md**: Theorem 152 (the landing criterion). -/
theorem lands_iff_gcd (M : ℕ) (w v : ℤ) :
    (∃ t : ℤ, ((t * w : ℤ) : ZMod M) = (v : ZMod M)) ↔ (Int.gcd w M : ℤ) ∣ v := by
  constructor
  · rintro ⟨t, ht⟩
    rw [← sub_eq_zero, ← Int.cast_sub, CharP.intCast_eq_zero_iff (ZMod M) M] at ht
    have h1 : (Int.gcd w M : ℤ) ∣ t * w := (Int.gcd_dvd_left _ _).mul_left t
    have h2 : (Int.gcd w M : ℤ) ∣ t * w - v := (Int.gcd_dvd_right _ _).trans ht
    have := dvd_sub h1 h2
    rwa [sub_sub_cancel] at this
  · rintro ⟨d, hd⟩
    refine ⟨w.gcdA M * d, ?_⟩
    have hv : v = w.gcdA M * d * w + (M : ℤ) * (w.gcdB M * d) := by
      rw [hd, Int.gcd_eq_gcd_ab]; ring
    rw [hv]
    push_cast
    rw [ZMod.natCast_self]
    ring

/-! ## Definition 233 and Theorem 151: product tables -/

section Ring

variable {n : ℕ} (ρ : Fin (n + 1) → ℕ) (hρ : ∀ i, 2 ≤ ρ i) (c : ℤ)

/-- A **product table**: for each pair of places a state carrying the class of
`B_m B_j`.

**fdrs.md**: Definition 233 (product tables and landing). -/
def ProductTable (T : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → ℤ) : Prop :=
  ∀ m j, ev ρ hρ c (T m j) = ev ρ hρ c (cell m) * ev ρ hρ c (cell j)

/-- The product of two states through a table: `Σ_{m,j} a_m b_j T(m, j)`. -/
def spreadMul (T : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → ℤ) (a b : Fin (n + 1) → ℤ) :
    Fin (n + 1) → ℤ :=
  ∑ m, ∑ j, (a m * b j) • T m j

theorem ev_eq_sum (x : Fin (n + 1) → ℤ) :
    ev ρ hρ c x = ∑ i, (x i : ZMod (modulus ρ hρ c)) * ev ρ hρ c (cell i) := by
  simp only [ev_apply, value_cell]
  rw [value_apply]
  push_cast
  rfl

/-- **Theorem 151 (every product table multiplies).** The class of `spreadMul T a b` is
the product of the classes of `a` and `b`.

**fdrs.md**: Theorem 151 (product tables multiply). -/
theorem ev_spreadMul {T : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → ℤ}
    (hT : ProductTable ρ hρ c T) (a b : Fin (n + 1) → ℤ) :
    ev ρ hρ c (spreadMul T a b) = ev ρ hρ c a * ev ρ hρ c b := by
  rw [ev_eq_sum ρ hρ c a, ev_eq_sum ρ hρ c b, Finset.sum_mul, spreadMul, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, hT, zsmul_eq_mul]
  push_cast
  ring

/-- **Theorem 151 (every ring has a product table).** Collapsing every product onto place
`0` (`T(m, j) = B_m B_j` units at place `0`) is a product table.

**fdrs.md**: Theorem 151 (product tables multiply). -/
theorem collapse_table :
    ProductTable ρ hρ c (fun m j => (weight ρ hρ m * weight ρ hρ j) • cell 0) := by
  intro m j
  simp only [ev_apply, map_zsmul, value_cell, Fin.val_zero, weight_zero]
  push_cast
  ring

/-- The gain on the way from `(m, j)` to the target place `m + j (mod N)`: `c` if the
target passes the top, `1` otherwise. -/
def landingGain (m j : Fin (n + 1)) : ℤ := if m ≤ m + j then 1 else c

/-- The product of the units at places `m` and `j` **lands** on its target place
`m + j (mod N)`: some integer coefficient `t` gives `t · ε · B_{m+j} ≡ B_m B_j`.

**fdrs.md**: Definition 233 (product tables and landing). -/
def Lands (m j : Fin (n + 1)) : Prop :=
  ∃ t : ℤ, ((t * (landingGain c m j * weight ρ hρ (m + j : Fin (n + 1))) : ℤ) :
    ZMod (modulus ρ hρ c)) = ((weight ρ hρ m * weight ρ hρ j : ℤ) : ZMod (modulus ρ hρ c))

/-- A ring is **residue-closed** if every product lands on its target place.

**fdrs.md**: Definition 233 (product tables and landing). -/
def ResidueClosed : Prop := ∀ m j : Fin (n + 1), Lands ρ hρ c m j

/-- **Theorem 152 (the landing criterion).** The product of places `m` and `j` lands on
its target iff `gcd(ε B_{m+j}, |B − c|) ∣ B_m B_j`.

**fdrs.md**: Theorem 152 (the landing criterion). -/
theorem lands_iff (m j : Fin (n + 1)) :
    Lands ρ hρ c m j ↔
      (Int.gcd (landingGain c m j * weight ρ hρ (m + j : Fin (n + 1))) (modulus ρ hρ c) : ℤ) ∣
        weight ρ hρ m * weight ρ hρ j :=
  lands_iff_gcd _ _ _

/-- The residue coefficients of a residue-closed ring. -/
noncomputable def kappaRes (h : ResidueClosed ρ hρ c) (m j : Fin (n + 1)) : ℤ :=
  Classical.choose (h m j)

theorem weights_mul_res (h : ResidueClosed ρ hρ c) (m k : Fin (n + 1)) :
    ((weight ρ hρ m : ℤ) : ZMod (modulus ρ hρ c)) * (weight ρ hρ (k - m : Fin (n + 1)) : ℤ) =
      (if m ≤ k then 1 else (c : ZMod (modulus ρ hρ c))) *
        (kappaRes ρ hρ c h m (k - m) : ℤ) * (weight ρ hρ k : ℤ) := by
  have hk : m + (k - m) = k := add_sub_cancel m k
  rw [kappaRes]
  have hs := Classical.choose_spec (h m (k - m))
  generalize Classical.choose (h m (k - m)) = t at hs ⊢
  rw [hk] at hs
  rw [← Int.cast_mul, ← hs, landingGain, hk]
  split_ifs <;> push_cast <;> ring

/-- **Corollary 52 (residue-closed rings multiply).** On a residue-closed ring, the carry
class of the mixed wrapped convolution with residue coefficients is the product of the
classes.

**fdrs.md**: Corollary 52 (residue closure). -/
theorem ev_residueConv (h : ResidueClosed ρ hρ c) (a b : Fin (n + 1) → ℤ) :
    ev ρ hρ c (mixedConv c (kappaRes ρ hρ c h) a b) = ev ρ hρ c a * ev ρ hρ c b := by
  have key := evalW_mixedConv (W := fun i => ((weight ρ hρ i : ℤ) : ZMod (modulus ρ hρ c)))
    (c := (c : ZMod (modulus ρ hρ c))) (κ := fun m j => ((kappaRes ρ hρ c h m j : ℤ) : ZMod _))
    (weights_mul_res ρ hρ c h) (fun i => (a i : ZMod _)) (fun i => (b i : ZMod _))
  simp only [ev_apply, value_apply, evalW] at key ⊢
  push_cast
  rw [← key]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [mixedConv, apply_ite]

theorem placeValue_dvd_add (b : RadixSeq) (k : ℕ) : ∀ d, placeValue b k ∣ placeValue b (k + d)
  | 0 => dvd_rfl
  | d + 1 => by
    rw [← add_assoc, placeValue.succ]
    exact (placeValue_dvd_add b k d).mul_right _

theorem weight_dvd_lap (k : Fin (n + 1)) : weight ρ hρ k ∣ lapValue ρ hρ := by
  have h := placeValue_dvd_add (ringSchedule ρ hρ) k (n + 1 - k)
  rw [Nat.add_sub_cancel' (by omega)] at h
  exact Int.natCast_dvd_natCast.mpr h

/-- **Corollary 52 (a coprime wrap closes every ring).** If the wrap gain is coprime to the
lap value, every product lands on its target place: the ring is residue-closed.

**fdrs.md**: Corollary 52 (residue closure). -/
theorem residueClosed_of_coprime (hc : IsCoprime (lapValue ρ hρ) c) : ResidueClosed ρ hρ c := by
  intro m j
  rw [lands_iff]
  have hB : IsCoprime (lapValue ρ hρ) (lapValue ρ hρ - c) := by
    have := hc.neg_right.add_mul_left_right 1
    rwa [show -c + lapValue ρ hρ * 1 = lapValue ρ hρ - c by ring] at this
  have hC : IsCoprime c (lapValue ρ hρ - c) := by
    have := hc.symm.add_mul_left_right (-1)
    rwa [show lapValue ρ hρ + c * -1 = lapValue ρ hρ - c by ring] at this
  have hW : IsCoprime (weight ρ hρ (m + j : Fin (n + 1))) (lapValue ρ hρ - c) :=
    hB.of_isCoprime_of_dvd_left (weight_dvd_lap ρ hρ _)
  have hE : IsCoprime (landingGain c m j) (lapValue ρ hρ - c) := by
    unfold landingGain; split_ifs
    · exact isCoprime_one_left
    · exact hC
  have hM : IsCoprime (landingGain c m j * weight ρ hρ (m + j : Fin (n + 1)))
      (modulus ρ hρ c : ℤ) := by
    rw [modulus]
    rcases Int.natAbs_eq (lapValue ρ hρ - c) with h | h
    · rw [← h]; exact hE.mul_left hW
    · rw [show ((lapValue ρ hρ - c).natAbs : ℤ) = -(lapValue ρ hρ - c) by omega]
      exact (hE.mul_left hW).neg_right
  rw [Int.isCoprime_iff_gcd_eq_one.mp hM, Nat.cast_one]
  exact one_dvd _

end Ring

/-! ## Proposition 180: the (2, 3, 2) witnesses -/

section Witnesses

/-- The ring with radices `(2, 3, 2)`: place values `1, 2, 6`, lap value `12`. -/
def ring232 : Fin 3 → ℕ := ![2, 3, 2]

theorem ring232_ge_two (i : Fin 3) : 2 ≤ ring232 i := by
  fin_cases i <;> decide

theorem ring232_weight (k : Fin 3) :
    weight ring232 ring232_ge_two k = ![1, 2, 6] k := by
  fin_cases k <;> rfl

theorem ring232_lap : lapValue ring232 ring232_ge_two = 12 := rfl

/-- **Proposition 180 (not product-closed).** `B_1 B_1 = 4` is not a multiple of
`B_2 = 6`: over the integers the product of two units at place `1` cannot land on place
`2`.

**fdrs.md**: Proposition 180 (the (2,3,2) witnesses). -/
theorem ring232_not_productClosed : ¬ ProductClosed ring232 ring232_ge_two := by
  intro h
  have h1 := h 1 1
  revert h1
  decide

/-- **Proposition 180 (closed by a coprime wrap).** With wrap gain `1` (arithmetic modulo
`11`) the `(2, 3, 2)` ring is residue-closed.

**fdrs.md**: Proposition 180 (the (2,3,2) witnesses). -/
theorem ring232_residue_one : ResidueClosed ring232 ring232_ge_two 1 :=
  residueClosed_of_coprime _ _ _ isCoprime_one_right

theorem ring232_modulus_one : modulus ring232 ring232_ge_two 1 = 11 := rfl

/-- **Proposition 180 (`4/6` is `8` modulo `11`).** With wrap gain `1`, the product of two
units at place `1` lands on place `2` with coefficient `8`: `8 · 6 ≡ 4 (mod 11)`.

**fdrs.md**: Proposition 180 (the (2,3,2) witnesses). -/
theorem ring232_kappa_eight :
    ((8 * (landingGain 1 (1 : Fin 3) 1 * weight ring232 ring232_ge_two ((1 : Fin 3) + 1)) : ℤ) :
      ZMod (modulus ring232 ring232_ge_two 1)) =
      ((weight ring232 ring232_ge_two (1 : Fin 3) * weight ring232 ring232_ge_two (1 : Fin 3) : ℤ) :
        ZMod (modulus ring232 ring232_ge_two 1)) := by
  rw [ring232_modulus_one]
  decide

theorem ring232_modulus_three : modulus ring232 ring232_ge_two 3 = 9 := rfl

/-- **Proposition 180 (blocked by a non-coprime wrap).** With wrap gain `3` (arithmetic
modulo `9`) the product of two units at place `1` does not land on place `2`:
`gcd(6, 9) = 3 ∤ 4`.

**fdrs.md**: Proposition 180 (the (2,3,2) witnesses). -/
theorem ring232_blocked : ¬ Lands ring232 ring232_ge_two 3 1 1 := by
  rw [lands_iff, ring232_modulus_three]
  decide

/-- **Proposition 180 (the blocked product spreads).** Instead it lands one place lower,
exactly: `B_1 B_1 = 2 · B_1`.

**fdrs.md**: Proposition 180 (the (2,3,2) witnesses). -/
theorem ring232_spread :
    weight ring232 ring232_ge_two (1 : Fin 3) * weight ring232 ring232_ge_two (1 : Fin 3) =
      2 * weight ring232 ring232_ge_two (1 : Fin 3) := by
  decide

end Witnesses

end FdrsFormal.Modes.SyntheticPlace.ProductSpread
