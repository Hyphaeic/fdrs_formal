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

# Multiplication on a mixed ring (Phase 1 addendum, §3.13)

§3.12 multiplied on constant rings only. On a mixed ring the product of the unit at place
`m` and the unit at place `j` has weight `B_m B_j`, which is not `B_{m+j}`: it lands at
place `m + j` (unrolled on the periodic schedule) with a **product coefficient**
`κ(m, j) = B_m B_j / B_{m+j}`, and if it passes the top it wraps with the gain `c`
(because `B_{k+N} = B_N B_k ≡ c B_k`, Proposition 174). When every `κ(m, j)` is an integer
the ring is **product-closed** and limb multiplication is a *mixed wrapped convolution*
followed by carries.

The 25519 ring is product-closed with `κ(m, j) = 2` when `m` and `j` are both odd and `1`
otherwise, so its product is the schoolbook formula with gains `19` (wrap), `2` (odd×odd)
and `38` (both). The ring with radices `(2, 3)` is not product-closed: a product of two
cells cannot land on one cell and must be spread across places.

Reuses `CarryQuotient.lean` (the value map, its quotient, the 25519 modulus),
`RingUnrolling.lean` (the periodic schedule, `placeValue_period`, the 25519 unrolling) and
`Field25519Carry.lean` (the weight ladder `W_i`).

- **Definition 232** (`mixedConv`, `evalW`, `ProductClosed`, `kappa`): mixed wrapped
  convolution, weighted evaluation, product-closed rings and their product coefficients.
- **Theorem 149** (`evalW_mixedConv`): if `W_m W_{k−m} = ε κ(m, k−m) W_k` (`ε = c` on a
  wrap), weighted evaluation turns mixed wrapped convolution into the product.
- **Theorem 150** (`ev_mixedConv`): on a product-closed ring, the carry class of the mixed
  wrapped convolution of two states is the product of their classes.
- **Proposition 178** (`const_productClosed`, `const_kappa`, `ring23_not_productClosed`):
  constant rings are product-closed with `κ = 1` (Corollary 51); the `(2, 3)` ring is not.
- **Proposition 179** (`field25519_productClosed`, `field25519_kappa`,
  `field25519_mul`): the 25519 ring is product-closed with `κ = 2` on odd×odd, and the
  schoolbook product with gains `19`, `2`, `38` computes multiplication modulo `p`.

**Honest scope.** Classical as arithmetic (the 25519 formula is the standard
radix-`2^25.5` schoolbook multiplication). The corpus contributes the derivation of the
gains from the ring's unrolled weights (`κ` from the schedule, `c` from the lap), the
product-closed criterion, and the obstruction on rings like `(2, 3)`. Rings that are not
product-closed (products spread over several places) are not covered.
-/

import FdrsFormal.Modes.SyntheticPlace.CarryQuotient

namespace FdrsFormal.Modes.SyntheticPlace.MixedRingProduct

open FdrsFormal.Core.Primitives FdrsFormal.Modes.SyntheticPlace.RingUnrolling
open FdrsFormal.Modes.SyntheticPlace.CarryQuotient

/-! ## Definition 232 and Theorem 149: mixed wrapped convolution -/

section Abstract

variable {R : Type*} [CommRing R] {N : ℕ} [NeZero N]

/-- **Mixed wrapped convolution** with gain `c` and product coefficients `κ`: the product
of places `m` and `k − m` lands at `k` with coefficient `κ(m, k−m)`, times `c` if it wraps.

**fdrs.md**: Definition 232 (mixed wrapped convolution and product-closed rings). -/
def mixedConv (c : R) (κ : Fin N → Fin N → R) (f g : Fin N → R) (k : Fin N) : R :=
  ∑ m, (if m ≤ k then 1 else c) * κ m (k - m) * (f m * g (k - m))

/-- Weighted evaluation: `Σ_k f_k W_k`. -/
def evalW (W : Fin N → R) (f : Fin N → R) : R := ∑ k, f k * W k

/-- **Theorem 149 (mixed wrapped convolution is multiplication).** If the weights satisfy
`W_m W_{k−m} = ε κ(m, k−m) W_k` with `ε = 1` for `m ≤ k` and `ε = c` otherwise, weighted
evaluation turns mixed wrapped convolution into the product.

**fdrs.md**: Theorem 149 (mixed wrapped convolution is multiplication). -/
theorem evalW_mixedConv {W : Fin N → R} {c : R} {κ : Fin N → Fin N → R}
    (hW : ∀ m k : Fin N, W m * W (k - m) = (if m ≤ k then 1 else c) * κ m (k - m) * W k)
    (f g : Fin N → R) :
    evalW W (mixedConv c κ f g) = evalW W f * evalW W g := by
  simp only [evalW, mixedConv, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  calc ∑ k, (if m ≤ k then 1 else c) * κ m (k - m) * (f m * g (k - m)) * W k
      = ∑ k, f m * W m * (g (k - m) * W (k - m)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        calc (if m ≤ k then 1 else c) * κ m (k - m) * (f m * g (k - m)) * W k
            = f m * g (k - m) * ((if m ≤ k then 1 else c) * κ m (k - m) * W k) := by ring
          _ = _ := by rw [← hW]; ring
    _ = ∑ j, f m * W m * (g j * W j) :=
        Equiv.sum_comp (Equiv.subRight m) (fun j => f m * W m * (g j * W j))

end Abstract

/-! ## Theorem 150: multiplication on a product-closed ring -/

section Ring

variable {n : ℕ} (ρ : Fin (n + 1) → ℕ) (hρ : ∀ i, 2 ≤ ρ i) (c : ℤ)

/-- A ring is **product-closed** if `B_{m+j} ∣ B_m B_j` for all places `m, j` (place values
of the periodic schedule, so `m + j` may pass the top).

**fdrs.md**: Definition 232 (mixed wrapped convolution and product-closed rings). -/
def ProductClosed : Prop :=
  ∀ m j : Fin (n + 1), placeValue (ringSchedule ρ hρ) ((m : ℕ) + j) ∣
    placeValue (ringSchedule ρ hρ) m * placeValue (ringSchedule ρ hρ) j

/-- The product coefficient `κ(m, j) = B_m B_j / B_{m+j}`.

**fdrs.md**: Definition 232 (mixed wrapped convolution and product-closed rings). -/
def kappa (m j : Fin (n + 1)) : ℤ :=
  (placeValue (ringSchedule ρ hρ) m * placeValue (ringSchedule ρ hρ) j /
    placeValue (ringSchedule ρ hρ) ((m : ℕ) + j) : ℕ)

theorem lap_eq_wrap :
    ((lapValue ρ hρ : ℤ) : ZMod (modulus ρ hρ c)) = (c : ZMod (modulus ρ hρ c)) := by
  rw [← sub_eq_zero, ← Int.cast_sub,
    CharP.intCast_eq_zero_iff (ZMod (modulus ρ hρ c)) (modulus ρ hρ c), modulus,
    Int.natAbs_dvd]

theorem weights_mul (hP : ProductClosed ρ hρ) (m k : Fin (n + 1)) :
    ((weight ρ hρ m : ℤ) : ZMod (modulus ρ hρ c)) * (weight ρ hρ (k - m : Fin (n + 1)) : ℤ) =
      (if m ≤ k then 1 else (c : ZMod (modulus ρ hρ c))) * (kappa ρ hρ m (k - m) : ℤ) *
        (weight ρ hρ k : ℤ) := by
  set P := placeValue (ringSchedule ρ hρ) with hPdef
  have hd := Nat.div_mul_cancel (hP m (k - m))
  have hcast : ((P m * P (k - m : Fin (n + 1)) : ℕ) : ZMod (modulus ρ hρ c)) =
      ((P m * P (k - m : Fin (n + 1)) / P ((m : ℕ) + (k - m : Fin (n + 1))) : ℕ) :
        ZMod (modulus ρ hρ c)) * (P ((m : ℕ) + (k - m : Fin (n + 1))) : ℕ) := by
    rw [← Nat.cast_mul, hd]
  simp only [weight, kappa, Int.cast_natCast, ← hPdef]
  rw [← Nat.cast_mul, hcast]
  generalize P m * P (k - m : Fin (n + 1)) / P ((m : ℕ) + (k - m : Fin (n + 1))) = κ0
  split_ifs with h
  · rw [one_mul, Fin.sub_val_of_le h, Nat.add_sub_cancel' (Fin.le_iff_val_le_val.mp h)]
  · have hm := m.isLt
    have hk : (k : ℕ) < m := Fin.lt_def.mp (not_le.mp h)
    have he : (m : ℕ) + (k - m : Fin (n + 1)) = k + (n + 1) := by
      rw [Fin.val_sub, Nat.mod_eq_of_lt (by omega)]; omega
    rw [he, hPdef, placeValue_period ρ hρ k, Nat.cast_mul, ← lap_eq_wrap ρ hρ c]
    simp only [lapValue, weight, Int.cast_natCast]
    ring

/-- **Theorem 150 (multiplication on a product-closed ring).** On a product-closed ring with
wrap gain `c`, the carry class of the mixed wrapped convolution (coefficients `κ`) of two
states is the product of their classes: limb multiplication is mixed wrapped convolution
followed by carries.

**fdrs.md**: Theorem 150 (multiplication on a product-closed ring). -/
theorem ev_mixedConv (hP : ProductClosed ρ hρ) (a b : Fin (n + 1) → ℤ) :
    ev ρ hρ c (mixedConv c (kappa ρ hρ) a b) = ev ρ hρ c a * ev ρ hρ c b := by
  have key := evalW_mixedConv (W := fun i => ((weight ρ hρ i : ℤ) : ZMod (modulus ρ hρ c)))
    (c := (c : ZMod (modulus ρ hρ c))) (κ := fun m j => ((kappa ρ hρ m j : ℤ) : ZMod _))
    (weights_mul ρ hρ c hP) (fun i => (a i : ZMod _)) (fun i => (b i : ZMod _))
  simp only [ev_apply, value_apply, evalW] at key ⊢
  push_cast
  rw [← key]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [mixedConv, apply_ite]

end Ring

/-! ## Proposition 178: constant rings, and an obstruction -/

section Witnesses

/-- **Proposition 178 (constant rings are product-closed).** With all radices `r`,
`B_m B_j = B_{m+j}`.

**fdrs.md**: Proposition 178 (constant rings close; the (2,3) ring does not). -/
theorem const_productClosed {n r : ℕ} (hr : 2 ≤ r) :
    ProductClosed (fun _ : Fin (n + 1) => r) (fun _ => hr) := by
  intro m j
  have h := weight_const (n := n) hr
  simp only [weight] at h
  have e : ∀ k, placeValue (ringSchedule (fun _ : Fin (n + 1) => r) (fun _ => hr)) k = r ^ k :=
    fun k => by exact_mod_cast h k
  rw [e, e, e, pow_add]

/-- **Proposition 178 (constant rings have `κ = 1`).** Theorem 150 reduces to Corollary 51.

**fdrs.md**: Proposition 178 (constant rings close; the (2,3) ring does not). -/
theorem const_kappa {n r : ℕ} (hr : 2 ≤ r) (m j : Fin (n + 1)) :
    kappa (fun _ : Fin (n + 1) => r) (fun _ => hr) m j = 1 := by
  have h := weight_const (n := n) hr
  simp only [weight] at h
  have e : ∀ k, placeValue (ringSchedule (fun _ : Fin (n + 1) => r) (fun _ => hr)) k = r ^ k :=
    fun k => by exact_mod_cast h k
  have hr0 : 0 < r ^ ((m : ℕ) + j) := pow_pos (by omega) _
  simp only [kappa, e, ← pow_add, Nat.div_self hr0, Nat.cast_one]

/-- The ring with radices `(2, 3)`. -/
def ring23 : Fin 2 → ℕ := ![2, 3]

theorem ring23_ge_two (i : Fin 2) : 2 ≤ ring23 i := by
  fin_cases i <;> decide

/-- **Proposition 178 (an obstruction).** The `(2, 3)` ring is not product-closed:
`B_1 B_1 = 4` is not a multiple of `B_2 = 6`, so the product of two units at place `1`
cannot land on a single place.

**fdrs.md**: Proposition 178 (constant rings close; the (2,3) ring does not). -/
theorem ring23_not_productClosed : ¬ ProductClosed ring23 ring23_ge_two := by
  intro h
  have h1 := h 1 1
  revert h1
  decide

end Witnesses

/-! ## Proposition 179: the 25519 product -/

section Field25519

open FdrsFormal.Applications.Field25519

/-- The weight ladder's defect: `W_m + W_j = W_{m+j} + [m, j odd]` for `m, j < 10`. -/
theorem weightBits_add : ∀ m < 10, ∀ j < 10,
    weightBits m + weightBits j = weightBits (m + j) + (if m % 2 = 1 ∧ j % 2 = 1 then 1 else 0) := by
  decide

theorem field25519_pv (i : ℕ) :
    placeValue (ringSchedule ring25519 ring25519_ge_two) i = 2 ^ weightBits i :=
  field25519_unrolls i

theorem field25519_pv_mul (m j : Fin 10) :
    placeValue (ringSchedule ring25519 ring25519_ge_two) m *
        placeValue (ringSchedule ring25519 ring25519_ge_two) j =
      2 ^ (if (m : ℕ) % 2 = 1 ∧ (j : ℕ) % 2 = 1 then 1 else 0) *
        placeValue (ringSchedule ring25519 ring25519_ge_two) ((m : ℕ) + j) := by
  rw [field25519_pv, field25519_pv, field25519_pv, ← pow_add, ← pow_add,
    weightBits_add m m.isLt j j.isLt, add_comm]

/-- **Proposition 179 (the 25519 ring is product-closed).**

**fdrs.md**: Proposition 179 (the 25519 product). -/
theorem field25519_productClosed : ProductClosed ring25519 ring25519_ge_two := by
  intro m j
  rw [field25519_pv_mul]
  exact Dvd.intro_left _ rfl

/-- **Proposition 179 (the 25519 product coefficients).** `κ(m, j) = 2` if `m` and `j` are
both odd, `1` otherwise.

**fdrs.md**: Proposition 179 (the 25519 product). -/
theorem field25519_kappa (m j : Fin 10) :
    kappa ring25519 ring25519_ge_two m j = if (m : ℕ) % 2 = 1 ∧ (j : ℕ) % 2 = 1 then 2 else 1 := by
  have hpos := placeValue.pos (b := ringSchedule ring25519 ring25519_ge_two) ((m : ℕ) + j)
  rw [kappa, field25519_pv_mul, Nat.mul_div_cancel _ hpos]
  split_ifs <;> rfl

/-- The 25519 schoolbook product: the term `a_m b_{k−m}` enters limb `k` with gain `19` if
it wraps, `2` if `m` and `k − m` are both odd (`38` if both). -/
def mul25519 (a b : Fin 10 → ℤ) (k : Fin 10) : ℤ :=
  ∑ m, (if m ≤ k then 1 else 19) *
    (if (m : ℕ) % 2 = 1 ∧ ((k - m : Fin 10) : ℕ) % 2 = 1 then 2 else 1) * (a m * b (k - m))

/-- **Proposition 179 (the 25519 product).** The schoolbook product with gains `19`, `2`,
`38` computes multiplication modulo `p = 2^255 − 19`:
`Σ_k (a ⊛ b)_k 2^{W_k} ≡ (Σ_i a_i 2^{W_i}) (Σ_i b_i 2^{W_i}) (mod p)`.

**fdrs.md**: Proposition 179 (the 25519 product). -/
theorem field25519_mul (a b : Fin 10 → ℤ) :
    (p : ℤ) ∣ (∑ k, mul25519 a b k * 2 ^ weightBits k) -
      (∑ i, a i * 2 ^ weightBits i) * (∑ i, b i * 2 ^ weightBits i) := by
  have h := ev_mixedConv ring25519 ring25519_ge_two 19 field25519_productClosed a b
  have hm : mixedConv 19 (kappa ring25519 ring25519_ge_two) a b = mul25519 a b := by
    funext k
    simp only [mixedConv, mul25519, field25519_kappa]
  rw [hm, ev_apply, ev_apply, ev_apply, ← Int.cast_mul, ← sub_eq_zero, ← Int.cast_sub,
    CharP.intCast_eq_zero_iff (ZMod _) _, field25519_modulus] at h
  simpa [value_apply, weight, field25519_pv] using h

end Field25519

end FdrsFormal.Modes.SyntheticPlace.MixedRingProduct
