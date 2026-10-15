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

# Product closure prime by prime (Phase 1 addendum, §3.25)

§3.13 called a ring product-closed when `B_{m+j} ∣ B_m B_j`; §3.23 studied power-of-two
schedules, where the product coefficient is `κ = 2^{defect}`. On an arbitrary ring the place
values `B_k` mix primes, and divisibility splits prime by prime. For each prime `p` the
**valuation schedule** `V_p(k) = v_p(B_k)` is a limb schedule (Definition 245) with lap
`e_p = v_p(h)`, `h = B_N` the holonomy — its increments may be `0`, which §3.23 allows.

- **The valuation criterion** (Theorem 178): a ring is product-closed iff every valuation
  schedule has non-negative defects, and then `v_p(κ(a, b)) = d_p(a, b)` — the product
  coefficient is `κ = ∏_p p^{d_p}`. A ring fails to close one prime at a time.
- **Christoffel prime by prime** (Theorem 179): on a product-closed ring
  `v_p(B_k) ≥ ⌈k e_p / N⌉` for every `p`; and the ring is product-closed with every `κ`
  squarefree iff **every** valuation schedule is the ceiling schedule of its lap. Hence the
  holonomy alone determines such a ring: two rings with the same `N` and holonomy, both with
  squarefree product coefficients, are equal.
- **The cost law per prime** (Corollary 61): on such a ring, exactly
  `N (N − gcd(e_p, N)) / 2` of the `N²` products carry the factor `p` in their coefficient.
- **Witnesses** (Proposition 191): the `(2, 3)` ring is 2-adically the ceiling schedule and
  fails only 3-adically (`d_3(1, 1) = −1`); the ring `(12, 6, 2)` (holonomy `144 = 2⁴3²`) has
  product coefficients `1, 2, 3, 6`, so it is the unique three-limb ring of holonomy `144`
  with squarefree coefficients; its valuation schedules are `⌈4k/3⌉` and `⌈2k/3⌉`.

Corollary 60 (radix `2^25.5`) is the case of a single prime.

Reuses `MixedRingProduct.lean` (`ProductClosed`, the `(2, 3)` ring), `RingUnrolling.lean`
(`placeValue_period`), `ChristoffelSchedule.lean` (schedules, defects, the defect bounds,
Christoffel optimality), `CostLaw.lean` (the cost law) and Mathlib's factorizations.

- **Definition 247** (`B`, `holonomy`, `val`, `kappaN`): valuation schedules.
- **Theorem 178** (`val_isSchedule`, `dvd_iff_defect`, `productClosed_iff`,
  `dvd_of_closed`, `kappa_factorization`): the valuation criterion.
- **Theorem 179** (`val_above_ceiling`, `squarefree_iff_ceil`, `christoffel_ring_unique`):
  Christoffel optimality prime by prime.
- **Corollary 61** (`prime_cost_law`): the cost law per prime.
- **Proposition 191** (`ring23_two_adic`, `ring23_three_adic`, `ring1262_*`): witnesses.

**Honest scope.** Elementary (unique factorization applied to §3.23–3.24). The corpus
contributes the reduction of product closure on arbitrary rings to power-of-prime schedules,
and the resulting uniqueness of the ring with squarefree product coefficients for a given
holonomy. Existence of that ring (every step must be a jump of the ceiling schedule of some
prime) is not formalized here.
-/

import FdrsFormal.Modes.SyntheticPlace.CostLaw

namespace FdrsFormal.Modes.SyntheticPlace.ValuationClosure

open FdrsFormal.Core.Primitives FdrsFormal.Modes.SyntheticPlace.RingUnrolling
open FdrsFormal.Modes.SyntheticPlace.CarryQuotient FdrsFormal.Modes.SyntheticPlace.MixedRingProduct
open FdrsFormal.Modes.SyntheticPlace.ChristoffelSchedule FdrsFormal.Modes.SyntheticPlace.CostLaw

section Ring

variable {n : ℕ} (ρ : Fin (n + 1) → ℕ) (hρ : ∀ i, 2 ≤ ρ i)

/-! ## Definition 247: valuation schedules -/

/-- The place values of the periodic schedule. -/
abbrev B (k : ℕ) : ℕ := placeValue (ringSchedule ρ hρ) k

/-- The holonomy `h = B_N`. -/
def holonomy : ℕ := B ρ hρ (n + 1)

/-- The `p`-**valuation schedule** `V_p(k) = v_p(B_k)`.

**fdrs.md**: Definition 247 (valuation schedules). -/
def val (p k : ℕ) : ℤ := ((B ρ hρ k).factorization p : ℤ)

/-- The product coefficient `κ(a, b) = B_a B_b / B_{a+b}` at all indices.

**fdrs.md**: Definition 247 (valuation schedules). -/
def kappaN (a b : ℕ) : ℕ := B ρ hρ a * B ρ hρ b / B ρ hρ (a + b)

/-! ## Theorem 178: the valuation criterion -/

/-- Each valuation schedule is a limb schedule with lap `v_p(h)`. -/
theorem val_isSchedule (p : ℕ) :
    IsSchedule (n + 1) ((holonomy ρ hρ).factorization p) (val ρ hρ p) := by
  refine ⟨by simp [val, B], fun k => ?_⟩
  simp only [val, B, holonomy]
  rw [placeValue_period, Nat.factorization_mul (placeValue.ne_zero _) (placeValue.ne_zero _),
    Finsupp.add_apply]
  push_cast; ring

theorem defect_val (p a b : ℕ) : defect (val ρ hρ p) a b =
    ((B ρ hρ a * B ρ hρ b).factorization p : ℤ) - (B ρ hρ (a + b)).factorization p := by
  simp only [defect, val, Nat.factorization_mul (placeValue.ne_zero _) (placeValue.ne_zero _),
    Finsupp.add_apply]
  push_cast; ring

/-- `B_{a+b} ∣ B_a B_b` iff every `p`-defect at `(a, b)` is non-negative. -/
theorem dvd_iff_defect (a b : ℕ) :
    B ρ hρ (a + b) ∣ B ρ hρ a * B ρ hρ b ↔ ∀ p, 0 ≤ defect (val ρ hρ p) a b := by
  rw [← Nat.factorization_le_iff_dvd (placeValue.ne_zero _)
    (mul_ne_zero (placeValue.ne_zero _) (placeValue.ne_zero _)), Finsupp.le_def]
  simp only [defect_val, sub_nonneg, Nat.cast_le]

/-- **Theorem 178 (the valuation criterion).** A ring is product-closed iff every valuation
schedule has non-negative defects.

**fdrs.md**: Theorem 178 (the valuation criterion). -/
theorem productClosed_iff : ProductClosed ρ hρ ↔ ∀ p a b, 0 ≤ defect (val ρ hρ p) a b := by
  constructor
  · intro hP p a b
    rw [defect_mod (val_isSchedule ρ hρ p)]
    exact (dvd_iff_defect ρ hρ _ _).1
      (hP ⟨a % (n + 1), Nat.mod_lt _ (by omega)⟩ ⟨b % (n + 1), Nat.mod_lt _ (by omega)⟩) p
  · intro h m j
    exact (dvd_iff_defect ρ hρ _ _).2 (fun p => h p m j)

/-- On a product-closed ring, products land at every pair of indices, not only within a lap. -/
theorem dvd_of_closed (hP : ProductClosed ρ hρ) (a b : ℕ) :
    B ρ hρ (a + b) ∣ B ρ hρ a * B ρ hρ b :=
  (dvd_iff_defect ρ hρ a b).2 (fun p => (productClosed_iff ρ hρ).1 hP p a b)

theorem kappaN_ne_zero (hP : ProductClosed ρ hρ) (a b : ℕ) : kappaN ρ hρ a b ≠ 0 :=
  (Nat.div_pos (Nat.le_of_dvd (Nat.mul_pos (placeValue.pos _) (placeValue.pos _))
    (dvd_of_closed ρ hρ hP a b)) (placeValue.pos _)).ne'

/-- **Theorem 178 (the product coefficient factors by defects).** `v_p(κ(a, b)) = d_p(a, b)`.

**fdrs.md**: Theorem 178 (the valuation criterion). -/
theorem kappa_factorization (hP : ProductClosed ρ hρ) (a b p : ℕ) :
    ((kappaN ρ hρ a b).factorization p : ℤ) = defect (val ρ hρ p) a b := by
  have hd := dvd_of_closed ρ hρ hP a b
  have hle := (Nat.factorization_le_iff_dvd (placeValue.ne_zero _)
    (mul_ne_zero (placeValue.ne_zero _) (placeValue.ne_zero _))).2 hd p
  rw [kappaN, Nat.factorization_div hd, Finsupp.tsub_apply, Nat.cast_sub hle, defect_val]

/-! ## Theorem 179: Christoffel optimality prime by prime -/

/-- **Theorem 179 (every closed ring lies above the ceiling, prime by prime).**
`v_p(B_k) ≥ ⌈k v_p(h) / N⌉`.

**fdrs.md**: Theorem 179 (Christoffel optimality prime by prime). -/
theorem val_above_ceiling (hP : ProductClosed ρ hρ) (p k : ℕ) :
    ceilSched (n + 1) ((holonomy ρ hρ).factorization p) k ≤ val ρ hρ p k :=
  above_ceiling (by omega) (val_isSchedule ρ hρ p) ((productClosed_iff ρ hρ).1 hP p) k

/-- **Theorem 179 (Christoffel optimality prime by prime).** A ring is product-closed with
squarefree product coefficients iff every valuation schedule is the ceiling schedule of its
lap.

**fdrs.md**: Theorem 179 (Christoffel optimality prime by prime). -/
theorem squarefree_iff_ceil :
    (ProductClosed ρ hρ ∧ ∀ m j : Fin (n + 1), Squarefree (kappaN ρ hρ m j)) ↔
      ∀ p, val ρ hρ p = ceilSched (n + 1) ((holonomy ρ hρ).factorization p) := by
  constructor
  · rintro ⟨hP, hS⟩ p
    refine christoffel_unique (by omega) (val_isSchedule ρ hρ p)
      ((productClosed_iff ρ hρ).1 hP p) (fun a b => ?_)
    rw [defect_mod (val_isSchedule ρ hρ p), ← kappa_factorization ρ hρ hP]
    have := (Nat.squarefree_iff_factorization_le_one (kappaN_ne_zero ρ hρ hP _ _)).1
      (hS ⟨a % (n + 1), Nat.mod_lt _ (by omega)⟩ ⟨b % (n + 1), Nat.mod_lt _ (by omega)⟩) p
    exact_mod_cast this
  · intro h
    have hb : ∀ p a b, 0 ≤ defect (val ρ hρ p) a b ∧ defect (val ρ hρ p) a b ≤ 1 :=
      fun p a b => by rw [h p]; exact ceilSched_defect a b
    have hP : ProductClosed ρ hρ := (productClosed_iff ρ hρ).2 fun p a b => (hb p a b).1
    refine ⟨hP, fun m j => ?_⟩
    rw [Nat.squarefree_iff_factorization_le_one (kappaN_ne_zero ρ hρ hP _ _)]
    intro p
    have h1 := kappa_factorization ρ hρ hP m j p
    have h2 := (hb p m j).2
    omega

/-- **Theorem 179 (the holonomy determines the ring).** Two rings with the same number of
places and the same holonomy, both product-closed with squarefree product coefficients, are
equal.

**fdrs.md**: Theorem 179 (Christoffel optimality prime by prime). -/
theorem christoffel_ring_unique (ρ' : Fin (n + 1) → ℕ) (hρ' : ∀ i, 2 ≤ ρ' i)
    (hh : holonomy ρ hρ = holonomy ρ' hρ')
    (h : ProductClosed ρ hρ ∧ ∀ m j : Fin (n + 1), Squarefree (kappaN ρ hρ m j))
    (h' : ProductClosed ρ' hρ' ∧ ∀ m j : Fin (n + 1), Squarefree (kappaN ρ' hρ' m j)) :
    ρ = ρ' := by
  have hB : ∀ k, B ρ hρ k = B ρ' hρ' k := fun k => by
    refine Nat.eq_of_factorization_eq (placeValue.ne_zero _) (placeValue.ne_zero _) fun p => ?_
    have e := congrFun ((squarefree_iff_ceil ρ hρ).1 h p) k
    have e' := congrFun ((squarefree_iff_ceil ρ' hρ').1 h' p) k
    rw [hh] at e
    have := e.trans e'.symm
    simp only [val, Nat.cast_inj] at this
    exact this
  funext i
  have h1 := hB (i + 1)
  simp only [B, placeValue.succ] at h1
  have hi : placeValue (ringSchedule ρ hρ) i = placeValue (ringSchedule ρ' hρ') i := hB i
  rw [hi] at h1
  have h2 := Nat.eq_of_mul_eq_mul_left (placeValue.pos _) h1
  have e1 := ringSchedule_lt ρ hρ i.isLt
  have e2 := ringSchedule_lt ρ' hρ' i.isLt
  simp only [Fin.eta] at e1 e2
  exact e1.symm.trans (h2.trans e2)

/-! ## Corollary 61: the cost law per prime -/

/-- **Corollary 61 (the cost law per prime).** On a ring whose valuation schedules are all
ceiling schedules, exactly `N (N − gcd(v_p(h), N)) / 2` of the `N²` products have a product
coefficient divisible by the prime `p`.

**fdrs.md**: Corollary 61 (the cost law per prime). -/
theorem prime_cost_law
    (h : ∀ p, val ρ hρ p = ceilSched (n + 1) ((holonomy ρ hρ).factorization p))
    {p : ℕ} (hp : p.Prime) :
    2 * (Finset.univ.filter (fun x : ZMod (n + 1) × ZMod (n + 1) =>
        p ∣ kappaN ρ hρ x.1.val x.2.val)).card =
      (n + 1) * ((n + 1) - Nat.gcd ((holonomy ρ hρ).factorization p) (n + 1)) := by
  have hP := ((squarefree_iff_ceil ρ hρ).2 h).1
  rw [← cost_law (N := n + 1)]
  congr 2
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have h1 := kappa_factorization ρ hρ hP x.1.val x.2.val p
  have h2 := ceilSched_defect (N := n + 1) (q := (holonomy ρ hρ).factorization p) x.1.val x.2.val
  rw [← h p] at h2 ⊢
  rw [hp.dvd_iff_one_le_factorization (kappaN_ne_zero ρ hρ hP _ _)]
  omega

end Ring

/-! ## Proposition 191: witnesses -/

section Witnesses

/-- Two schedules with the same limb count and lap agree everywhere once they agree on a lap. -/
theorem sched_eq_of_agree {N q : ℕ} (hN : 0 < N) {W W' : ℕ → ℤ} (hW : IsSchedule N q W)
    (hW' : IsSchedule N q W') (h : ∀ r < N, W r = W' r) : W = W' := by
  funext a
  rw [← Nat.mod_add_div a N, period_decomp hW, period_decomp hW', h _ (Nat.mod_lt _ hN)]

theorem fact6 : (6 : ℕ).factorization = Finsupp.single 2 1 + Finsupp.single 3 1 := by
  rw [show (6 : ℕ) = 2 * 3 from rfl, Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.prime_two.factorization, Nat.prime_three.factorization]

theorem fact144 : (144 : ℕ).factorization = Finsupp.single 2 4 + Finsupp.single 3 2 := by
  rw [show (144 : ℕ) = 2 ^ 4 * 3 ^ 2 from rfl, Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.prime_two.factorization_pow, Nat.prime_three.factorization_pow]

theorem ring23_holonomy : holonomy ring23 ring23_ge_two = 6 := rfl

/-- **Proposition 191 (the `(2, 3)` ring, 2-adically).** `v_2(B_k) = ⌈k/2⌉`: the 2-adic
schedule is the ceiling schedule, so its defects lie in `{0, 1}`.

**fdrs.md**: Proposition 191 (product closure prime by prime: witnesses). -/
theorem ring23_two_adic : val ring23 ring23_ge_two 2 = ceilSched 2 1 := by
  have hs := val_isSchedule ring23 ring23_ge_two 2
  rw [ring23_holonomy, fact6] at hs
  simp only [Finsupp.add_apply, Finsupp.single_apply] at hs
  norm_num at hs
  refine sched_eq_of_agree (by norm_num) hs (ceilSched_isSchedule (by norm_num)) fun r hr => ?_
  interval_cases r
  · simp [val, ceilSched]
  · have h2 : placeValue (ringSchedule ring23 ring23_ge_two) 1 = 2 := rfl
    simp only [val, B, h2, Nat.prime_two.factorization_self, ceilSched]
    norm_num [Int.ceil_eq_iff]

/-- **Proposition 191 (the `(2, 3)` ring fails 3-adically).** `d_3(1, 1) = −1`: the failure
of product closure (Proposition 178) is entirely at the prime `3`.

**fdrs.md**: Proposition 191 (product closure prime by prime: witnesses). -/
theorem ring23_three_adic : defect (val ring23 ring23_ge_two 3) 1 1 = -1 := by
  have h1 : placeValue (ringSchedule ring23 ring23_ge_two) 1 = 2 := rfl
  have h2 : placeValue (ringSchedule ring23 ring23_ge_two) 2 = 6 := rfl
  simp only [defect, val, B, h1, h2, fact6, Nat.prime_two.factorization, Finsupp.add_apply,
    Finsupp.single_apply]
  norm_num

/-- The ring with radices `(12, 6, 2)`. -/
def ring1262 : Fin 3 → ℕ := ![12, 6, 2]

theorem ring1262_ge_two (i : Fin 3) : 2 ≤ ring1262 i := by
  fin_cases i <;> decide

theorem ring1262_holonomy : holonomy ring1262 ring1262_ge_two = 144 := rfl

theorem ring1262_productClosed : ProductClosed ring1262 ring1262_ge_two := by
  intro m j
  fin_cases m <;> fin_cases j <;> decide

/-- The product coefficients of `(12, 6, 2)` are `1, 2, 3, 6`. -/
theorem ring1262_kappa (m j : Fin 3) :
    kappaN ring1262 ring1262_ge_two m j ∈ ({1, 2, 3, 6} : Finset ℕ) := by
  fin_cases m <;> fin_cases j <;> decide

/-- **Proposition 191 (the `(12, 6, 2)` ring).** It is product-closed with squarefree product
coefficients.

**fdrs.md**: Proposition 191 (product closure prime by prime: witnesses). -/
theorem ring1262_squarefree :
    ProductClosed ring1262 ring1262_ge_two ∧
      ∀ m j : Fin 3, Squarefree (kappaN ring1262 ring1262_ge_two m j) := by
  refine ⟨ring1262_productClosed, fun m j => ?_⟩
  have h := ring1262_kappa m j
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h | h <;> rw [h]
  · exact squarefree_one
  · exact Nat.prime_two.prime.squarefree
  · exact Nat.prime_three.prime.squarefree
  · rw [show (6 : ℕ) = 2 * 3 from rfl, Nat.squarefree_mul_iff]
    exact ⟨by norm_num, Nat.prime_two.prime.squarefree, Nat.prime_three.prime.squarefree⟩

/-- **Proposition 191 (its valuation schedules are ceilings).** `v_2(B_k) = ⌈4k/3⌉` and
`v_3(B_k) = ⌈2k/3⌉`.

**fdrs.md**: Proposition 191 (product closure prime by prime: witnesses). -/
theorem ring1262_vals :
    val ring1262 ring1262_ge_two 2 = ceilSched 3 4 ∧ val ring1262 ring1262_ge_two 3 = ceilSched 3 2 := by
  have h := (squarefree_iff_ceil ring1262 ring1262_ge_two).1 ring1262_squarefree
  rw [ring1262_holonomy, fact144] at h
  have h2 := h 2
  have h3 := h 3
  simp only [Finsupp.add_apply, Finsupp.single_apply] at h2 h3
  norm_num at h2 h3
  exact ⟨h2, h3⟩

/-- **Proposition 191 (the unique ring of holonomy 144).** Every three-place ring of holonomy
`144` that is product-closed with squarefree product coefficients is `(12, 6, 2)`.

**fdrs.md**: Proposition 191 (product closure prime by prime: witnesses). -/
theorem ring1262_unique (ρ : Fin 3 → ℕ) (hρ : ∀ i, 2 ≤ ρ i) (hh : holonomy ρ hρ = 144)
    (h : ProductClosed ρ hρ ∧ ∀ m j : Fin 3, Squarefree (kappaN ρ hρ m j)) : ρ = ring1262 :=
  christoffel_ring_unique ρ hρ ring1262 ring1262_ge_two (hh.trans ring1262_holonomy.symm) h
    ring1262_squarefree

/-- **Proposition 191 (its cost per prime).** Of the nine products, three carry a factor `2`
and three a factor `3` (Corollary 61 with `gcd(4, 3) = gcd(2, 3) = 1`).

**fdrs.md**: Proposition 191 (product closure prime by prime: witnesses). -/
theorem ring1262_cost :
    (Finset.univ.filter (fun x : ZMod 3 × ZMod 3 =>
        2 ∣ kappaN ring1262 ring1262_ge_two x.1.val x.2.val)).card = 3 ∧
    (Finset.univ.filter (fun x : ZMod 3 × ZMod 3 =>
        3 ∣ kappaN ring1262 ring1262_ge_two x.1.val x.2.val)).card = 3 := by
  have h := (squarefree_iff_ceil ring1262 ring1262_ge_two).1 ring1262_squarefree
  have c2 := prime_cost_law ring1262 ring1262_ge_two h Nat.prime_two
  have c3 := prime_cost_law ring1262 ring1262_ge_two h Nat.prime_three
  rw [ring1262_holonomy, fact144] at c2 c3
  simp only [Finsupp.add_apply, Finsupp.single_apply] at c2 c3
  norm_num at c2 c3
  exact ⟨Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) c2,
    Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) c3⟩

end Witnesses

end FdrsFormal.Modes.SyntheticPlace.ValuationClosure
