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

# The Christoffel ring of a holonomy (Phase 1 addendum, §3.26)

§3.25 showed that a ring whose product coefficients are all squarefree is determined by its
number of places `N` and its holonomy `h = ∏ ρ_i`: every valuation schedule must be the
ceiling schedule `v_p(B_k) = ⌈k e_p / N⌉`, `e_p = v_p(h)`. Here: when does it exist?

- **The ceiling ring** (Definition 248): `C_k = ∏_{p ∣ h} p^{⌈k e_p / N⌉}` and
  `ρ_k = C_{k+1} / C_k`. These are the only candidate radices.
- **Steps** (Theorem 180): the ceiling schedule of lap `e` rises at every step when `e ≥ N`,
  and at the last step `k = N − 1` only when `e ≥ N`.
- **The existence criterion** (Theorem 181): an `N`-place ring of holonomy `h` that is
  product-closed with squarefree product coefficients exists **iff some prime power `p^N`
  divides `h`**. With uniqueness (Theorem 179) it is the ceiling ring.
- **First and last radix** (Corollary 62): on such a ring the first radix is the least `r`
  (for divisibility) with `h ∣ r^N`, and the last radix the greatest `r` with `r^N ∣ h` —
  the ceiling and floor `N`-th roots of the holonomy.
- **Witnesses** (Proposition 192): no three-place ring of holonomy `36` has squarefree
  product coefficients; for `(12, 6, 2)`, `144 ∣ r³ ↔ 12 ∣ r` and `r³ ∣ 144 ↔ r ∣ 2`.

The criterion was first checked with `tools/limb-schedule rings --verify` (every ordered
factorization of every `h ≤ 3000` into `N ≤ 7` radices: no exceptions), then proved here.

Reuses `ValuationClosure.lean` (valuation schedules, Theorem 179, `sched_eq_of_agree`),
`ChristoffelSchedule.lean` (ceiling schedules), `CostLaw.lean` (`ceil_lag`, `lag_lt`) and
`RingUnrolling.lean`.

- **Definition 248** (`expo`, `C`, `rad`): the ceiling ring.
- **Theorem 180** (`ceil_bounds`, `jump_of_le`, `le_of_last_jump`): steps of a ceiling
  schedule.
- **Theorem 181** (`rad_ge_two`, `pv_rad`, `rad_holonomy`, `rad_christoffel`,
  `exists_iff`): the existence criterion.
- **Corollary 62** (`radix_val`, `first_radix_root`, `last_radix_root`): first and last
  radix.
- **Proposition 192** (`no_ring_36`, `ring1262_first`, `ring1262_last`): witnesses.

**Honest scope.** Elementary. The last step of the ceiling schedule forces a prime of
multiplicity at least `N` in the holonomy; that prime alone makes every radix at least `2`.
-/

import FdrsFormal.Modes.SyntheticPlace.ValuationClosure

namespace FdrsFormal.Modes.SyntheticPlace.ChristoffelRing

open FdrsFormal.Core.Primitives FdrsFormal.Modes.SyntheticPlace.RingUnrolling
open FdrsFormal.Modes.SyntheticPlace.CarryQuotient FdrsFormal.Modes.SyntheticPlace.MixedRingProduct
open FdrsFormal.Modes.SyntheticPlace.ChristoffelSchedule FdrsFormal.Modes.SyntheticPlace.CostLaw
open FdrsFormal.Modes.SyntheticPlace.ValuationClosure

/-! ## Theorem 180: steps of a ceiling schedule -/

section Steps

variable (n : ℕ)

theorem ceil_nonneg (q k : ℕ) : 0 ≤ ceilSched (n + 1) q k :=
  Int.ceil_nonneg (by positivity)

theorem ceil_bounds (q k : ℕ) :
    (q : ℤ) * k ≤ (n + 1 : ℕ) * ceilSched (n + 1) q k ∧
      ((n + 1 : ℕ) : ℤ) * ceilSched (n + 1) q k < q * k + (n + 1 : ℕ) := by
  have e := ceil_lag (N := n + 1) q k
  have hl := lag_lt (N := n + 1) q (k : ZMod (n + 1))
  constructor
  · rw [e]; omega
  · rw [e]; omega

theorem ceil_lap (q : ℕ) : ceilSched (n + 1) q (n + 1) = q := by
  have := (ceilSched_isSchedule (N := n + 1) (q := q) (by omega)).2 0
  simpa [(ceilSched_isSchedule (N := n + 1) (q := q) (by omega)).1] using this

theorem ceil_mono (q k : ℕ) : ceilSched (n + 1) q k ≤ ceilSched (n + 1) q (k + 1) := by
  obtain ⟨a1, a2⟩ := ceil_bounds n q k
  obtain ⟨b1, b2⟩ := ceil_bounds n q (k + 1)
  by_contra hc
  push_neg at hc
  have : ((n + 1 : ℕ) : ℤ) * ceilSched (n + 1) q (k + 1) + (n + 1 : ℕ) ≤
      (n + 1 : ℕ) * ceilSched (n + 1) q k := by nlinarith
  push_cast at *
  nlinarith

/-- **Theorem 180 (every step rises when `e ≥ N`).**

**fdrs.md**: Theorem 180 (steps of a ceiling schedule). -/
theorem jump_of_le {q : ℕ} (hq : n + 1 ≤ q) (k : ℕ) :
    ceilSched (n + 1) q k < ceilSched (n + 1) q (k + 1) := by
  obtain ⟨a1, a2⟩ := ceil_bounds n q k
  obtain ⟨b1, b2⟩ := ceil_bounds n q (k + 1)
  have h : ((n + 1 : ℕ) : ℤ) * ceilSched (n + 1) q k < (n + 1 : ℕ) * ceilSched (n + 1) q (k + 1) := by
    have : ((n + 1 : ℕ) : ℤ) ≤ q := by exact_mod_cast hq
    push_cast at *
    nlinarith
  exact lt_of_mul_lt_mul_left h (by positivity)

/-- **Theorem 180 (the last step rises only when `e ≥ N`).**

**fdrs.md**: Theorem 180 (steps of a ceiling schedule). -/
theorem le_of_last_jump {q : ℕ} (h : ceilSched (n + 1) q n < ceilSched (n + 1) q (n + 1)) :
    n + 1 ≤ q := by
  rw [ceil_lap] at h
  obtain ⟨a1, -⟩ := ceil_bounds n q n
  have h' : ceilSched (n + 1) q n ≤ (q : ℤ) - 1 := by omega
  have : ((n + 1 : ℕ) : ℤ) * ceilSched (n + 1) q n ≤ (n + 1 : ℕ) * ((q : ℤ) - 1) :=
    mul_le_mul_of_nonneg_left h' (by positivity)
  push_cast at *
  have : ((n : ℤ) + 1) ≤ q := by nlinarith
  exact_mod_cast this

end Steps

/-! ## Definition 248 and Theorem 181: the ceiling ring and the existence criterion -/

section Construction

variable (n h : ℕ)

/-- The exponent `⌈k e_p / N⌉` as a natural number.

**fdrs.md**: Definition 248 (the ceiling ring). -/
noncomputable def expo (p k : ℕ) : ℕ := (ceilSched (n + 1) (h.factorization p) k).toNat

/-- The ceiling place values `C_k = ∏_{p ∣ h} p^{⌈k e_p / N⌉}`.

**fdrs.md**: Definition 248 (the ceiling ring). -/
noncomputable def C (k : ℕ) : ℕ := ∏ p ∈ h.primeFactors, p ^ expo n h p k

/-- The ceiling radices `ρ_k = C_{k+1} / C_k`.

**fdrs.md**: Definition 248 (the ceiling ring). -/
noncomputable def rad (i : Fin (n + 1)) : ℕ := C n h ((i : ℕ) + 1) / C n h i

theorem expo_cast (p k : ℕ) : (expo n h p k : ℤ) = ceilSched (n + 1) (h.factorization p) k :=
  Int.toNat_of_nonneg (ceil_nonneg n _ _)

theorem C_ne_zero (k : ℕ) : C n h k ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ hp => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero

theorem C_factorization (k q : ℕ) : (C n h k).factorization q = expo n h q k := by
  rw [C, Nat.factorization_prod
    (fun p hp => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero),
    Finsupp.finset_sum_apply]
  rw [Finset.sum_congr rfl (fun p hp => by
    rw [(Nat.prime_of_mem_primeFactors hp).factorization_pow, Finsupp.single_apply]),
    Finset.sum_ite_eq']
  split_ifs with hq
  · rfl
  · have : h.factorization q = 0 := by
      rw [← Finsupp.notMem_support_iff, Nat.support_factorization]; exact hq
    simp [expo, this, ceilSched]

theorem C_zero : C n h 0 = 1 :=
  Nat.eq_of_factorization_eq (C_ne_zero n h 0) one_ne_zero fun q => by
    rw [C_factorization]; simp [expo, ceilSched]

theorem C_dvd_succ (k : ℕ) : C n h k ∣ C n h (k + 1) := by
  rw [← Nat.factorization_le_iff_dvd (C_ne_zero n h _) (C_ne_zero n h _), Finsupp.le_def]
  intro q
  rw [C_factorization, C_factorization, expo, expo]
  exact Int.toNat_le_toNat (ceil_mono n _ k)

theorem C_lap (hh : h ≠ 0) : C n h (n + 1) = h :=
  Nat.eq_of_factorization_eq (C_ne_zero n h _) hh fun q => by
    rw [C_factorization, expo, ceil_lap, Int.toNat_natCast]

variable {n h}

theorem ne_zero_of_le {p : ℕ} (hp : n + 1 ≤ h.factorization p) : h ≠ 0 := by
  rintro rfl; simp at hp

/-- **Theorem 181 (the ceiling radices are at least 2).** If `p^N ∣ h` for some prime `p`,
`p` rises at every step.

**fdrs.md**: Theorem 181 (the existence criterion). -/
theorem rad_ge_two {p : ℕ} (hp : n + 1 ≤ h.factorization p) (i : Fin (n + 1)) : 2 ≤ rad n h i := by
  have hr : C n h i * rad n h i = C n h ((i : ℕ) + 1) := Nat.mul_div_cancel' (C_dvd_succ n h i)
  have hj := jump_of_le n hp i
  rcases (by omega : rad n h i = 0 ∨ rad n h i = 1 ∨ 2 ≤ rad n h i) with h0 | h1 | h2
  · rw [h0, mul_zero] at hr; exact absurd hr.symm (C_ne_zero n h _)
  · rw [h1, mul_one] at hr
    have := congrArg (fun x => ((x.factorization p : ℕ) : ℤ)) hr
    simp only [C_factorization, expo_cast] at this
    omega
  · exact h2

/-- The place values of the ceiling ring are the ceiling place values. -/
theorem pv_rad {p : ℕ} (hp : n + 1 ≤ h.factorization p) :
    ∀ k ≤ n + 1, placeValue (ringSchedule (rad n h) (rad_ge_two hp)) k = C n h k
  | 0, _ => by simp [C_zero]
  | k + 1, hk => by
    rw [placeValue.succ, pv_rad hp k (by omega), ringSchedule_lt _ _ (by omega : k < n + 1)]
    exact Nat.mul_div_cancel' (C_dvd_succ n h k)

theorem rad_holonomy {p : ℕ} (hp : n + 1 ≤ h.factorization p) :
    holonomy (rad n h) (rad_ge_two hp) = h := by
  rw [holonomy, B, pv_rad hp _ le_rfl, C_lap n h (ne_zero_of_le hp)]

/-- **Theorem 181 (the ceiling ring is product-closed with squarefree coefficients).**

**fdrs.md**: Theorem 181 (the existence criterion). -/
theorem rad_christoffel {p : ℕ} (hp : n + 1 ≤ h.factorization p) :
    ProductClosed (rad n h) (rad_ge_two hp) ∧
      ∀ m j : Fin (n + 1), Squarefree (kappaN (rad n h) (rad_ge_two hp) m j) := by
  refine (squarefree_iff_ceil _ _).2 fun q => ?_
  refine sched_eq_of_agree (by omega) (val_isSchedule _ _ q) (ceilSched_isSchedule (by omega))
    fun r hr => ?_
  rw [rad_holonomy hp, val, B, pv_rad hp r hr.le, C_factorization, expo_cast]

/-- **Theorem 181 (the existence criterion).** An `N`-place ring of holonomy `h` that is
product-closed with squarefree product coefficients exists iff `v_p(h) ≥ N` for some `p`
(i.e. `p^N ∣ h`, `h ≠ 0`).

**fdrs.md**: Theorem 181 (the existence criterion). -/
theorem exists_iff :
    (∃ (ρ : Fin (n + 1) → ℕ) (hρ : ∀ i, 2 ≤ ρ i), holonomy ρ hρ = h ∧ ProductClosed ρ hρ ∧
        ∀ m j : Fin (n + 1), Squarefree (kappaN ρ hρ m j)) ↔
      ∃ p, n + 1 ≤ h.factorization p := by
  constructor
  · rintro ⟨ρ, hρ, hh, hP, hS⟩
    have hv := (squarefree_iff_ceil ρ hρ).1 ⟨hP, hS⟩
    have hlt : B ρ hρ n < B ρ hρ (n + 1) := placeValue.strictMono (Nat.lt_succ_self n)
    have hnd : ¬ B ρ hρ (n + 1) ∣ B ρ hρ n := fun hd =>
      absurd (Nat.le_of_dvd (placeValue.pos _) hd) (not_le.2 hlt)
    rw [← Nat.factorization_le_iff_dvd (placeValue.ne_zero _) (placeValue.ne_zero _),
      Finsupp.le_def] at hnd
    push_neg at hnd
    obtain ⟨p, hp⟩ := hnd
    refine ⟨p, ?_⟩
    have e1 := congrFun (hv p) n
    have e2 := congrFun (hv p) (n + 1)
    simp only [val] at e1 e2
    rw [hh] at e1 e2
    exact le_of_last_jump n (by rw [← e1, ← e2]; exact_mod_cast hp)
  · rintro ⟨p, hp⟩
    exact ⟨rad n h, rad_ge_two hp, rad_holonomy hp, rad_christoffel hp⟩

end Construction

/-! ## Corollary 62: first and last radix -/

section Roots

variable {n : ℕ} (ρ : Fin (n + 1) → ℕ) (hρ : ∀ i, 2 ≤ ρ i)

theorem radix_val (k : ℕ) (hk : k < n + 1) (p : ℕ) :
    (((ρ ⟨k, hk⟩).factorization p : ℕ) : ℤ) = val ρ hρ p (k + 1) - val ρ hρ p k := by
  have hne : ρ ⟨k, hk⟩ ≠ 0 := by have := hρ ⟨k, hk⟩; omega
  simp only [val, B, placeValue.succ, ringSchedule_lt ρ hρ hk,
    Nat.factorization_mul (placeValue.ne_zero _) hne, Finsupp.add_apply]
  push_cast; ring

theorem dvd_pow_iff {a r : ℕ} (ha : a ≠ 0) (hr : r ≠ 0) :
    a ∣ r ^ (n + 1) ↔ ∀ p, a.factorization p ≤ (n + 1) * r.factorization p := by
  rw [← Nat.factorization_le_iff_dvd ha (pow_ne_zero _ hr), Finsupp.le_def,
    Nat.factorization_pow]
  simp

theorem pow_dvd_iff {a r : ℕ} (ha : a ≠ 0) (hr : r ≠ 0) :
    r ^ (n + 1) ∣ a ↔ ∀ p, (n + 1) * r.factorization p ≤ a.factorization p := by
  rw [← Nat.factorization_le_iff_dvd (pow_ne_zero _ hr) ha, Finsupp.le_def,
    Nat.factorization_pow]
  simp

variable (hv : ∀ p, val ρ hρ p = ceilSched (n + 1) ((holonomy ρ hρ).factorization p))
include hv

/-- **Corollary 62 (the first radix is the ceiling `N`-th root).** `h ∣ r^N ↔ ρ_0 ∣ r`.

**fdrs.md**: Corollary 62 (first and last radix). -/
theorem first_radix_root {r : ℕ} (hr : r ≠ 0) :
    holonomy ρ hρ ∣ r ^ (n + 1) ↔ ρ 0 ∣ r := by
  have h0 : ρ 0 ≠ 0 := by have := hρ 0; omega
  have hH : holonomy ρ hρ ≠ 0 := placeValue.ne_zero _
  rw [dvd_pow_iff hH hr,
    ← Nat.factorization_le_iff_dvd h0 hr, Finsupp.le_def]
  refine forall_congr' fun p => ?_
  have e := radix_val ρ hρ 0 (by omega) p
  rw [hv p] at e
  simp only [Fin.zero_eta, zero_add] at e
  have c0 : ceilSched (n + 1) ((holonomy ρ hρ).factorization p) 0 = 0 := by simp [ceilSched]
  rw [c0, sub_zero] at e
  obtain ⟨a1, a2⟩ := ceil_bounds n ((holonomy ρ hρ).factorization p) 1
  rw [← e] at a1 a2
  push_cast at a1 a2
  constructor
  · intro h
    have : (((holonomy ρ hρ).factorization p : ℕ) : ℤ) ≤ ((n : ℤ) + 1) * (r.factorization p : ℕ) := by
      exact_mod_cast h
    have : ((n : ℤ) + 1) * ((ρ 0).factorization p : ℕ) < ((n : ℤ) + 1) * ((r.factorization p : ℕ) + 1) := by
      linarith
    have := lt_of_mul_lt_mul_left this (by positivity)
    omega
  · intro h
    have h' : (((ρ 0).factorization p : ℕ) : ℤ) ≤ (r.factorization p : ℕ) := by exact_mod_cast h
    have : ((n : ℤ) + 1) * ((ρ 0).factorization p : ℕ) ≤ ((n : ℤ) + 1) * (r.factorization p : ℕ) :=
      mul_le_mul_of_nonneg_left h' (by positivity)
    have : (((holonomy ρ hρ).factorization p : ℕ) : ℤ) ≤ ((n : ℤ) + 1) * (r.factorization p : ℕ) := by
      linarith
    exact_mod_cast this

/-- **Corollary 62 (the last radix is the floor `N`-th root).** `r^N ∣ h ↔ r ∣ ρ_{N−1}`.

**fdrs.md**: Corollary 62 (first and last radix). -/
theorem last_radix_root {r : ℕ} (hr : r ≠ 0) :
    r ^ (n + 1) ∣ holonomy ρ hρ ↔ r ∣ ρ (Fin.last n) := by
  have hl : ρ (Fin.last n) ≠ 0 := by have := hρ (Fin.last n); omega
  have hH : holonomy ρ hρ ≠ 0 := placeValue.ne_zero _
  rw [pow_dvd_iff hH hr,
    ← Nat.factorization_le_iff_dvd hr hl, Finsupp.le_def]
  refine forall_congr' fun p => ?_
  have e := radix_val ρ hρ n (by omega) p
  rw [hv p, ceil_lap] at e
  obtain ⟨a1, a2⟩ := ceil_bounds n ((holonomy ρ hρ).factorization p) n
  have hc : ceilSched (n + 1) ((holonomy ρ hρ).factorization p) n =
      ((holonomy ρ hρ).factorization p : ℕ) - (((ρ (Fin.last n)).factorization p : ℕ) : ℤ) := by
    rw [show (Fin.last n) = ⟨n, by omega⟩ from rfl, e]; ring
  rw [hc] at a1 a2
  push_cast at a1 a2
  constructor
  · intro h
    have h' : ((n : ℤ) + 1) * (r.factorization p : ℕ) ≤ ((holonomy ρ hρ).factorization p : ℕ) := by
      exact_mod_cast h
    have : ((n : ℤ) + 1) * (r.factorization p : ℕ) <
        ((n : ℤ) + 1) * (((ρ (Fin.last n)).factorization p : ℕ) + 1) := by nlinarith
    have := lt_of_mul_lt_mul_left this (by positivity)
    omega
  · intro h
    have h' : ((r.factorization p : ℕ) : ℤ) ≤ ((ρ (Fin.last n)).factorization p : ℕ) := by
      exact_mod_cast h
    have : ((n : ℤ) + 1) * (r.factorization p : ℕ) ≤
        ((n : ℤ) + 1) * ((ρ (Fin.last n)).factorization p : ℕ) :=
      mul_le_mul_of_nonneg_left h' (by positivity)
    have : ((n : ℤ) + 1) * (r.factorization p : ℕ) ≤ ((holonomy ρ hρ).factorization p : ℕ) := by
      nlinarith
    exact_mod_cast this

end Roots

/-! ## Proposition 192: witnesses -/

section Witnesses

theorem fact36 : (36 : ℕ).factorization = Finsupp.single 2 2 + Finsupp.single 3 2 := by
  rw [show (36 : ℕ) = 2 ^ 2 * 3 ^ 2 from rfl, Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.prime_two.factorization_pow, Nat.prime_three.factorization_pow]

/-- **Proposition 192 (no three-place ring of holonomy 36).** `36 = 2²3²` has no cube factor,
so no three-place ring of holonomy `36` is product-closed with squarefree coefficients.

**fdrs.md**: Proposition 192 (the existence criterion: witnesses). -/
theorem no_ring_36 :
    ¬ ∃ (ρ : Fin 3 → ℕ) (hρ : ∀ i, 2 ≤ ρ i), holonomy ρ hρ = 36 ∧ ProductClosed ρ hρ ∧
        ∀ m j : Fin 3, Squarefree (kappaN ρ hρ m j) := by
  rw [exists_iff]
  rintro ⟨p, hp⟩
  rw [fact36, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply] at hp
  split_ifs at hp <;> omega

theorem ring1262_vals_all :
    ∀ p, val ring1262 ring1262_ge_two p =
      ceilSched 3 ((holonomy ring1262 ring1262_ge_two).factorization p) :=
  (squarefree_iff_ceil ring1262 ring1262_ge_two).1 ring1262_squarefree

/-- **Proposition 192 (the first radix of `(12, 6, 2)`).** `144 ∣ r³ ↔ 12 ∣ r`.

**fdrs.md**: Proposition 192 (the existence criterion: witnesses). -/
theorem ring1262_first {r : ℕ} (hr : r ≠ 0) : 144 ∣ r ^ 3 ↔ 12 ∣ r :=
  first_radix_root ring1262 ring1262_ge_two ring1262_vals_all hr

/-- **Proposition 192 (the last radix of `(12, 6, 2)`).** `r³ ∣ 144 ↔ r ∣ 2`.

**fdrs.md**: Proposition 192 (the existence criterion: witnesses). -/
theorem ring1262_last {r : ℕ} (hr : r ≠ 0) : r ^ 3 ∣ 144 ↔ r ∣ 2 :=
  last_radix_root ring1262 ring1262_ge_two ring1262_vals_all hr

end Witnesses

end FdrsFormal.Modes.SyntheticPlace.ChristoffelRing
