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

# The cost law of the ceiling schedule (Phase 1 addendum, §3.24)

§3.23 showed that the ceiling schedule `W_k = ⌈q k / N⌉` is the unique power-of-two
schedule whose product coefficients are all `1` or `2`. Here we count the `2`s: among the
`N²` partial products of a schoolbook multiplication on the ceiling schedule, exactly

  `N (N − gcd(q, N)) / 2`

are doubled (defect `1`). For Curve25519 (`q = 255`, `N = 10`) that is `25`; for P-521
(`q = 521`, `N = 9`) it is `36`.

The proof runs through the **lag** `u(k) = (−q k) mod N`:

- `N ⌈q k / N⌉ = q k + u(k)` (Lemma `ceil_lag`);
- the defect of the product of limbs `a, b` is `1` iff `u(a) + u(b) ≥ N`, else `0`
  (Theorem 176);
- the involution `(a, b) ↦ (−a, −b)` exchanges `u(a) + u(b) ≥ N` with `u(a) + u(b) ≤ N` on
  pairs of nonzero lags, so the doubled pairs are half of those pairs plus half the ties;
- every lag value occurs equally often — as often as `0`, i.e. `gcd(q, N)` times (fibres of
  `x ↦ −q x` on `ℤ/N`).

Reuses `ChristoffelSchedule.lean` (`ceilSched`, `defect`).

- **Definition 246** (`lag`): the lag of an index.
- **Theorem 176** (`ceil_lag`, `ceil_defect`): the defect law of the ceiling schedule.
- **Theorem 177** (`lag_fiber`, `card_zeros`, `cost_law`): the cost law.

**Honest scope.** Elementary counting in `ℤ/N`. The closed form was first observed with
`tools/limb-schedule` (it matches every brute-force case); this file proves it.
-/

import FdrsFormal.Modes.SyntheticPlace.ChristoffelSchedule

namespace FdrsFormal.Modes.SyntheticPlace.CostLaw

open FdrsFormal.Modes.SyntheticPlace.ChristoffelSchedule

variable {N : ℕ} [NeZero N] (q : ℕ)

/-! ## Definition 246: the lag -/

/-- The lag of an index: `u(x) = (−q x) mod N`, so that `N ⌈q k / N⌉ = q k + u(k)`.

**fdrs.md**: Definition 246 (the lag). -/
def lag (x : ZMod N) : ℕ := (-((q : ZMod N) * x)).val

theorem lag_lt (x : ZMod N) : lag q x < N := ZMod.val_lt _

theorem lag_dvd (k : ℕ) : N ∣ q * k + lag q (k : ZMod N) := by
  rw [← CharP.cast_eq_zero_iff (ZMod N) N]
  push_cast
  rw [lag, ZMod.natCast_zmod_val]
  ring

theorem lag_add (a b : ℕ) :
    lag q ((a + b : ℕ) : ZMod N) = (lag q (a : ZMod N) + lag q (b : ZMod N)) % N := by
  rw [lag, lag, lag, ← ZMod.val_add]
  congr 1
  push_cast
  ring

/-! ## Theorem 176: the defect law -/

/-- **Theorem 176 (the ceiling in terms of the lag).** `N ⌈q k / N⌉ = q k + u(k)`.

**fdrs.md**: Theorem 176 (the defect law of the ceiling schedule). -/
theorem ceil_lag (k : ℕ) : (N : ℤ) * ceilSched N q k = q * k + lag q (k : ZMod N) := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨z, hz⟩ := lag_dvd (N := N) q k
  have hl := lag_lt q (k : ZMod N)
  have hzi : ((q * k + lag q (k : ZMod N) : ℕ) : ℤ) = N * z := by exact_mod_cast hz
  push_cast at hzi
  have hc : ceilSched N q k = z := by
    have hNq : (0 : ℚ) < N := by exact_mod_cast hN
    rw [ceilSched, Int.ceil_eq_iff]
    constructor
    · rw [lt_div_iff₀ hNq]
      have : ((z : ℤ) - 1) * N < ((q * k : ℕ) : ℤ) := by push_cast; nlinarith
      exact_mod_cast this
    · rw [div_le_iff₀ hNq]
      have : ((q * k : ℕ) : ℤ) ≤ (z : ℤ) * N := by push_cast; nlinarith
      exact_mod_cast this
  rw [hc]
  linarith

/-- **Theorem 176 (the defect law).** On the ceiling schedule, the product of limbs `a, b`
has defect `1` iff `u(a) + u(b) ≥ N`, and `0` otherwise.

**fdrs.md**: Theorem 176 (the defect law of the ceiling schedule). -/
theorem ceil_defect (a b : ℕ) :
    defect (ceilSched N q) a b =
      if N ≤ lag q (a : ZMod N) + lag q (b : ZMod N) then 1 else 0 := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have ha := ceil_lag (N := N) q a
  have hb := ceil_lag (N := N) q b
  have hab := ceil_lag (N := N) q (a + b)
  rw [lag_add] at hab
  have hla := lag_lt q (a : ZMod N)
  have hlb := lag_lt q (b : ZMod N)
  set la := lag q (a : ZMod N)
  set lb := lag q (b : ZMod N)
  have key : (N : ℤ) * defect (ceilSched N q) a b = la + lb - ((la + lb) % N : ℕ) := by
    simp only [defect]
    have : (N : ℤ) * (ceilSched N q a + ceilSched N q b - ceilSched N q (a + b)) =
        N * ceilSched N q a + N * ceilSched N q b - N * ceilSched N q (a + b) := by ring
    rw [this, ha, hb, hab]
    push_cast
    ring
  have hNz : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  split_ifs with h
  · have hm : (la + lb) % N = la + lb - N := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    rw [hm] at key
    have : (N : ℤ) * defect (ceilSched N q) a b = N * 1 := by
      rw [key]; push_cast [Nat.cast_sub h]; ring
    exact mul_left_cancel₀ hNz this
  · have hm : (la + lb) % N = la + lb := Nat.mod_eq_of_lt (by omega)
    rw [hm] at key
    have : (N : ℤ) * defect (ceilSched N q) a b = N * 0 := by rw [key]; push_cast; ring
    exact mul_left_cancel₀ hNz this

/-! ## Theorem 177: the cost law -/

omit [NeZero N] in
theorem lag_eq_zero_iff (x : ZMod N) : lag q x = 0 ↔ (q : ZMod N) * x = 0 := by
  rw [lag, ZMod.val_eq_zero, neg_eq_zero]

theorem lag_neg {x : ZMod N} (h : lag q x ≠ 0) : lag q (-x) = N - lag q x := by
  have hx : (q : ZMod N) * x ≠ 0 := fun h' => h ((lag_eq_zero_iff q x).mpr h')
  have h1 : lag q x = N - ((q : ZMod N) * x).val := by
    rw [lag, ZMod.neg_val, if_neg hx]
  have h2 : lag q (-x) = ((q : ZMod N) * x).val := by
    rw [lag, mul_neg, neg_neg]
  have h3 := ZMod.val_lt ((q : ZMod N) * x)
  omega

/-- The zeros of the lag. -/
noncomputable def zeros : Finset (ZMod N) := Finset.univ.filter (fun x => lag q x = 0)

/-- **Theorem 177 (every lag value occurs as often as 0).**

**fdrs.md**: Theorem 177 (the cost law). -/
theorem lag_fiber (y : ZMod N) :
    (Finset.univ.filter (fun x : ZMod N => lag q x = lag q y)).card = (zeros (N := N) q).card := by
  have hfib : ∀ x : ZMod N, lag q x = lag q y ↔ (q : ZMod N) * x = q * y := by
    intro x
    rw [lag, lag]
    constructor
    · intro h; exact neg_inj.mp (ZMod.val_injective N h)
    · intro h; rw [h]
  symm
  refine Finset.card_nbij' (fun x => x + y) (fun x => x - y) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [zeros, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
      lag_eq_zero_iff] at hx ⊢
    rw [hfib, mul_add, hx, zero_add]
  · intro x hx
    simp only [zeros, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
      lag_eq_zero_iff, hfib] at hx ⊢
    rw [mul_sub, hx, sub_self]
  · intro x _; simp
  · intro x _; simp

theorem lag_fiber_of_ne {a : ZMod N} (ha : lag q a ≠ 0) :
    (Finset.univ.filter (fun b : ZMod N => lag q a + lag q b = N)).card = (zeros (N := N) q).card := by
  rw [← lag_fiber q (-a)]
  congr 1
  ext b
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, lag_neg q ha]
  have := lag_lt q a
  omega

/-- The number of nonzero-lag indices is `N − #zeros`. -/
theorem card_nonzero :
    (Finset.univ.filter (fun x : ZMod N => lag q x ≠ 0)).card = N - (zeros (N := N) q).card := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (ZMod N)))
    (fun x => lag q x = 0)
  rw [Finset.card_univ, ZMod.card] at h
  have e : Finset.univ.filter (fun x : ZMod N => lag q x ≠ 0) =
      Finset.univ.filter (fun x : ZMod N => ¬ lag q x = 0) := rfl
  rw [e, zeros]
  omega

/-- The doubled pairs, counted through the lag. -/
theorem card_doubled :
    2 * (Finset.univ.filter
        (fun p : ZMod N × ZMod N => N ≤ lag q p.1 + lag q p.2)).card =
      N * (N - (zeros (N := N) q).card) := by
  classical
  set A := Finset.univ.filter (fun x : ZMod N => lag q x ≠ 0) with hA
  set S := Finset.univ.filter (fun p : ZMod N × ZMod N => N ≤ lag q p.1 + lag q p.2) with hS
  set S' := (A ×ˢ A).filter (fun p : ZMod N × ZMod N => lag q p.1 + lag q p.2 ≤ N) with hS'
  set T := (A ×ˢ A).filter (fun p : ZMod N × ZMod N => lag q p.1 + lag q p.2 = N) with hT
  have hlt : ∀ x : ZMod N, lag q x < N := lag_lt q
  -- S lies in A × A
  have hSA : ∀ p ∈ S, p ∈ A ×ˢ A := by
    intro p hp
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have h1 := hlt p.1; have h2 := hlt p.2
    simp only [hA, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  -- the involution
  have hcard : S'.card = S.card := by
    refine Finset.card_nbij' (fun p => (-p.1, -p.2)) (fun p => (-p.1, -p.2)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [hS', Finset.coe_filter, Finset.mem_product, hA, Finset.mem_filter,
        Finset.mem_univ, true_and, Set.mem_setOf_eq] at hp
      simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      rw [lag_neg q hp.1.1, lag_neg q hp.1.2]
      have h1 := hlt p.1; have h2 := hlt p.2
      omega
    · intro p hp
      have hpA := hSA p hp
      simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hp
      simp only [hA, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hpA
      simp only [hS', Finset.coe_filter, Finset.mem_product, hA, Finset.mem_filter,
        Finset.mem_univ, true_and, Set.mem_setOf_eq]
      rw [lag_neg q hpA.1, lag_neg q hpA.2]
      have h1 := hlt p.1; have h2 := hlt p.2
      refine ⟨⟨by omega, by omega⟩, by omega⟩
    · intro p _; simp
    · intro p _; simp
  -- union and intersection
  have hunion : S ∪ S' = A ×ˢ A := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_union.mp hp with h | h
      · exact hSA p h
      · exact (Finset.mem_filter.mp h).1
    · intro hp
      rcases le_total N (lag q p.1 + lag q p.2) with h | h
      · exact Finset.mem_union_left _ (by simp [hS, h])
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, h⟩)
  have hinter : S ∩ S' = T := by
    ext p
    simp only [hS, hS', hT, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2, by omega⟩
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h1, by omega⟩
  have hU := Finset.card_union_add_card_inter S S'
  rw [hunion, hinter, hcard, Finset.card_product] at hU
  -- the ties
  have hTcard : T.card = A.card * (zeros (N := N) q).card := by
    rw [hT, Finset.card_filter, Finset.sum_product]
    rw [Finset.sum_congr rfl (g := fun _ => (zeros (N := N) q).card)]
    · rw [Finset.sum_const, smul_eq_mul]
    · intro a ha
      have ha' : lag q a ≠ 0 := (Finset.mem_filter.mp ha).2
      rw [← lag_fiber_of_ne q ha', ← Finset.card_filter]
      congr 1
      ext b
      simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, h⟩; exact h
      · intro h; exact ⟨by have := hlt a; omega, h⟩
  rw [hTcard] at hU
  have hAc := card_nonzero (N := N) q
  rw [← hA] at hAc
  have hZ : (zeros (N := N) q).card ≤ N := by
    have := Finset.card_le_univ (zeros (N := N) q); rwa [ZMod.card] at this
  rw [hAc] at hU
  have : (N - (zeros (N := N) q).card) * (N - (zeros (N := N) q).card) + (N - (zeros (N := N) q).card) * (zeros (N := N) q).card =
      N * (N - (zeros (N := N) q).card) := by
    rw [← mul_add, Nat.sub_add_cancel hZ, mul_comm]
  omega

/-- **Theorem 177 (the zeros of the lag).** `#{x ∈ ℤ/N : q x = 0} = gcd(q, N)`.

**fdrs.md**: Theorem 177 (the cost law). -/
theorem card_zeros : (zeros (N := N) q).card = Nat.gcd q N := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  set d := Nat.gcd q N with hd
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_right _ hN
  set N' := N / d with hN'
  have hNeq : N = d * N' := (Nat.mul_div_cancel' (Nat.gcd_dvd_right q N)).symm
  have hqeq : q = d * (q / d) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left q N)).symm
  have hN'pos : 0 < N' := Nat.div_pos (Nat.gcd_le_right _ hN) hdpos
  have hcop : Nat.Coprime N' (q / d) := (Nat.coprime_div_gcd_div_gcd hdpos).symm
  -- zeros are the multiples of N'
  have hiff : ∀ k : ℕ, N ∣ q * k ↔ N' ∣ k := by
    intro k
    rw [hNeq, hqeq, mul_assoc, Nat.mul_dvd_mul_iff_left hdpos]
    constructor
    · intro h; exact hcop.dvd_of_dvd_mul_left h
    · intro h; exact Dvd.dvd.mul_left h _
  have hcast : (zeros (N := N) q).card = ((Finset.range N).filter (fun k => N ∣ q * k)).card := by
    refine Finset.card_nbij' (fun x => x.val) (fun k => (k : ZMod N)) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [zeros, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
        lag_eq_zero_iff] at hx
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
      refine ⟨ZMod.val_lt x, ?_⟩
      rw [← CharP.cast_eq_zero_iff (ZMod N) N]
      push_cast
      rw [ZMod.natCast_zmod_val]; exact hx
    · intro k hk
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hk
      simp only [zeros, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
        lag_eq_zero_iff]
      have := (CharP.cast_eq_zero_iff (ZMod N) N (q * k)).mpr hk.2
      push_cast at this; exact this
    · intro x _; simp
    · intro k hk
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hk
      simp [ZMod.val_natCast, Nat.mod_eq_of_lt hk.1]
  rw [hcast]
  have himg : (Finset.range N).filter (fun k => N ∣ q * k) =
      (Finset.range d).image (fun t => t * N') := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, hiff]
    constructor
    · rintro ⟨hk, t, rfl⟩
      refine ⟨t, ?_, by ring⟩
      rw [hNeq] at hk
      exact (Nat.mul_lt_mul_left hN'pos).mp (by linarith)
    · rintro ⟨t, ht, rfl⟩
      refine ⟨?_, ⟨t, by ring⟩⟩
      rw [hNeq]; nlinarith
  rw [himg, Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_right hN'pos h),
    Finset.card_range]

/-- **Theorem 177 (the cost law).** On the ceiling schedule, exactly `N (N − gcd(q, N)) / 2` of
the `N²` partial products are doubled.

**fdrs.md**: Theorem 177 (the cost law). -/
theorem cost_law :
    2 * (Finset.univ.filter (fun p : ZMod N × ZMod N =>
        defect (ceilSched N q) p.1.val p.2.val = 1)).card = N * (N - Nat.gcd q N) := by
  rw [← card_zeros (N := N) q, ← card_doubled (N := N) q]
  congr 2
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ceil_defect, ZMod.natCast_zmod_val]
  split_ifs with h <;> simp [h]

end FdrsFormal.Modes.SyntheticPlace.CostLaw
