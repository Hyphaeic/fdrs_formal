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

# Tick Pullback Dynamics

Tick as an operator on tensors (pullback dynamics on finite spaces).

## Mathematical Content (fdrs.md lines 1219-1268)

**Definition 33 (cyclic Tick on R^(k))**:
T̃_k(τ) := enc_k((dec_k(τ) + 1) mod B_{k+1})

**Definition 34 (pullback on functions)**:
(T̃_k^* f)(τ) := f(T̃_k(τ))

**Proposition 31**: T̃_k preserves μ_k (measure-preserving bijection)
**Proposition 32**: Cylinders are permuted by T̃_k
**Theorem 10**: T̃_k^* P_L = P_L T̃_k^* (commutes with all projections)
**Corollary 7**: T̃_k^* preserves each detail scale D_L

## References

- fdrs.md, Phase 2 Fragment 3 (lines 1219-1268)
- THEOREM_MAPPING.md
-/

import FdrsFormal.FunctionSpaces.Commutant.MultiLevelCommutant

namespace FdrsFormal.FunctionSpaces.Commutant

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite
open FdrsFormal.FunctionSpaces.Basic
open scoped Classical

/-!
## Cyclic Tick on Finite Spaces
-/

variable (b : RadixSeq) (k : ℕ)

/--
**Definition 33**: Cyclic Tick on R^(k).

T̃_k(τ) := enc_k((dec_k(τ) + 1) mod B_{k+1})
-/
def cyclicTick : FiniteRadixSpace b k → FiniteRadixSpace b k :=
  fun τ =>
    let n := decodeFinite b k τ
    let N := placeValue b (k + 1)
    encodeFinite b k ⟨(n + 1) % N, Nat.mod_lt _ (placeValue.pos _)⟩

/--
**Definition 34**: Pullback on functions.

(T̃_k^* f)(τ) := f(T̃_k(τ))
-/
def tickPullback {V : Type*} (f : FiniteRadixSpace b k → V) : FiniteRadixSpace b k → V :=
  fun τ => f (cyclicTick b k τ)

/-!
## Proposition 31: Measure Preservation
-/

/--
Cyclic Tick is a bijection (permutation of finite set).

**Proof**: On a finite type, injective implies bijective. We show cyclicTick is injective
by showing its composition with decodeFinite is injective.
-/
theorem cyclicTick_bijective (b : RadixSeq) (k : ℕ) : Function.Bijective (cyclicTick b k) := by
  -- For finite types, injective implies bijective
  have h_inj : Function.Injective (cyclicTick b k) := by
    intro τ σ h
    simp only [cyclicTick] at h
    -- encodeFinite b k ⟨(dec τ + 1) % N, _⟩ = encodeFinite b k ⟨(dec σ + 1) % N, _⟩
    -- Since encodeFinite is injective, (dec τ + 1) % N = (dec σ + 1) % N
    let N := placeValue b (k + 1)
    have hN : 0 < N := placeValue.pos _
    have h_enc_inj := (finiteRadixEquiv b k).symm.injective
    simp only [finiteRadixEquiv, Equiv.symm] at h_enc_inj
    have h1 : (⟨(decodeFinite b k τ + 1) % N, Nat.mod_lt _ hN⟩ : Fin N) =
              ⟨(decodeFinite b k σ + 1) % N, Nat.mod_lt _ hN⟩ := h_enc_inj h
    simp only [Fin.mk.injEq] at h1
    -- (dec τ + 1) % N = (dec σ + 1) % N and both are < N
    -- This implies dec τ = dec σ
    have h_τ_lt : decodeFinite b k τ < N := decodeFinite_lt k τ
    have h_σ_lt : decodeFinite b k σ < N := decodeFinite_lt k σ
    have h2 : decodeFinite b k τ = decodeFinite b k σ := by
      -- (a + 1) % N = (b + 1) % N with a, b < N implies a = b
      have ha1 : decodeFinite b k τ + 1 ≤ N := Nat.succ_le_of_lt h_τ_lt
      have hb1 : decodeFinite b k σ + 1 ≤ N := Nat.succ_le_of_lt h_σ_lt
      by_cases ha : decodeFinite b k τ + 1 = N
      · -- τ + 1 = N, so (τ + 1) % N = 0
        have hτ_mod : (decodeFinite b k τ + 1) % N = 0 := by simp [ha]
        rw [hτ_mod] at h1
        -- (σ + 1) % N = 0 means σ + 1 ≡ 0 mod N, with σ < N, so σ + 1 = N
        have h_σ1 : (decodeFinite b k σ + 1) % N = 0 := h1.symm
        have h_σ_pos : 0 < decodeFinite b k σ + 1 := Nat.zero_lt_succ _
        have h_σ_eq_N : decodeFinite b k σ + 1 = N := by
          have h_dvd : N ∣ decodeFinite b k σ + 1 := Nat.dvd_of_mod_eq_zero h_σ1
          -- N | (σ + 1) and 0 < σ + 1 ≤ N implies σ + 1 = N
          rcases h_dvd with ⟨c, hc⟩
          cases c with
          | zero => simp only [Nat.mul_zero] at hc; omega
          | succ c' =>
            -- σ + 1 = N * (c' + 1), and σ + 1 ≤ N means c' + 1 ≤ 1, so c' = 0
            have hc_bound : N * (c' + 1) ≤ N := by rw [← hc]; exact hb1
            have hc_bound' : N * (c' + 1) ≤ N * 1 := by simp only [Nat.mul_one]; exact hc_bound
            have : c' + 1 ≤ 1 := Nat.le_of_mul_le_mul_left hc_bound' hN
            have : c' = 0 := by omega
            simp only [this, Nat.zero_add, Nat.mul_one] at hc
            exact hc
        -- Now ha : τ + 1 = N and h_σ_eq_N : σ + 1 = N
        -- So τ = σ
        omega
      · -- τ + 1 < N
        have ha' : decodeFinite b k τ + 1 < N := Nat.lt_of_le_of_ne ha1 ha
        have h_τ_mod : (decodeFinite b k τ + 1) % N = decodeFinite b k τ + 1 :=
          Nat.mod_eq_of_lt ha'
        rw [h_τ_mod] at h1
        by_cases hb : decodeFinite b k σ + 1 = N
        · -- σ + 1 = N, contradiction with (σ + 1) % N = τ + 1 > 0
          have h_σ_mod : (decodeFinite b k σ + 1) % N = 0 := by simp [hb]
          rw [h_σ_mod] at h1
          omega
        · -- σ + 1 < N
          have hb' : decodeFinite b k σ + 1 < N := Nat.lt_of_le_of_ne hb1 hb
          have h_σ_mod : (decodeFinite b k σ + 1) % N = decodeFinite b k σ + 1 :=
            Nat.mod_eq_of_lt hb'
          rw [h_σ_mod] at h1
          omega
    exact decodeFinite_injective k h2
  exact Finite.injective_iff_bijective.mp h_inj

/-!
## Prefix Preservation

CyclicTick preserves the L-prefix of elements in the same cylinder.
The key digit-locality lemma: if n ≡ m (mod B_L), then their i-th digits agree for i < L.
-/

/-- Digit extraction locality: (n / B_i) % b_i depends only on n % B_L for i < L. -/
private lemma digit_mod_of_mod_eq (b : RadixSeq) (i L : ℕ) (hiL : i < L)
    (n m : ℕ) (h : n % placeValue b L = m % placeValue b L) :
    (n / placeValue b i) % b i = (m / placeValue b i) % b i := by
  have h_mod_succ : n % placeValue b (i + 1) = m % placeValue b (i + 1) := by
    have hdvd : placeValue b (i + 1) ∣ placeValue b L :=
      placeValue.dvd_of_le (Nat.succ_le_of_lt hiL)
    calc n % placeValue b (i + 1)
        = n % placeValue b L % placeValue b (i + 1) := (Nat.mod_mod_of_dvd n hdvd).symm
      _ = m % placeValue b L % placeValue b (i + 1) := by rw [h]
      _ = m % placeValue b (i + 1) := Nat.mod_mod_of_dvd m hdvd
  suffices key : ∀ x, (x / placeValue b i) % b i =
      (x % placeValue b (i + 1)) / placeValue b i by
    rw [key n, key m, h_mod_succ]
  intro x
  have hBi_pos : 0 < placeValue b i := placeValue.pos i
  have hBi1 : placeValue b (i + 1) = placeValue b i * b i := placeValue.succ i
  set r := x % placeValue b (i + 1)
  set q := x / placeValue b (i + 1)
  have hr_lt : r < placeValue b i * b i := hBi1 ▸ Nat.mod_lt _ (placeValue.pos (i + 1))
  have hx_eq : x = r + placeValue b i * (q * b i) := by
    have h1 : placeValue b (i + 1) * q + r = x := Nat.div_add_mod x (placeValue b (i + 1))
    rw [hBi1] at h1
    linarith [show placeValue b i * b i * q = placeValue b i * (q * b i) from by ring]
  have hdiv : x / placeValue b i = r / placeValue b i + q * b i := by
    rw [hx_eq, Nat.add_mul_div_left r _ hBi_pos]
  have hr_div_lt : r / placeValue b i < b i := by
    rw [Nat.div_lt_iff_lt_mul hBi_pos, mul_comm]; exact hr_lt
  rw [hdiv, show r / placeValue b i + q * b i =
    r / placeValue b i + b i * q from by ring,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr_div_lt]

/--
**Proposition 32**: CyclicTick preserves L-prefixes within cylinders.

If τ and σ have the same L-prefix, then T̃(τ) and T̃(σ) also have the same L-prefix.

**Proof**: Same L-prefix means dec(τ) ≡ dec(σ) (mod B_L), so
(dec(τ)+1) ≡ (dec(σ)+1) (mod B_L), which gives enc(dec(τ)+1) and enc(dec(σ)+1)
have the same L-prefix by digit locality.
-/
theorem cyclicTick_preserves_prefix (b : RadixSeq) (k L : ℕ) (hLk : L ≤ k + 1)
    (τ σ : FiniteRadixSpace b k)
    (h : finitePrefix b L τ hLk = finitePrefix b L σ hLk) :
    finitePrefix b L (cyclicTick b k τ) hLk = finitePrefix b L (cyclicTick b k σ) hLk := by
  funext ⟨i, hi⟩; simp only [cyclicTick, finitePrefix]; ext
  apply digit_mod_of_mod_eq b i L hi
  have hBL_dvd_N : placeValue b L ∣ placeValue b (k + 1) := placeValue.dvd_of_le hLk
  rw [Nat.mod_mod_of_dvd _ hBL_dvd_N, Nat.mod_mod_of_dvd _ hBL_dvd_N]
  have h_prefix_eq : ∀ j : Fin L, τ ⟨j.val, by omega⟩ = σ ⟨j.val, by omega⟩ :=
    fun j => congr_fun h j
  have h_dec_mod : decodeFinite b k τ % placeValue b L =
      decodeFinite b k σ % placeValue b L := by
    simp only [decodeFinite]
    set lo := Finset.filter (fun j : Fin (k + 1) => j.val < L) Finset.univ
    set hi_set := Finset.filter (fun j : Fin (k + 1) => L ≤ j.val) Finset.univ
    have hd : Disjoint lo hi_set :=
      Finset.disjoint_filter.mpr (fun _ _ h1 h2 => by omega)
    have hu : lo ∪ hi_set = Finset.univ := by
      ext j; constructor
      · exact fun _ => Finset.mem_univ _
      · intro _; simp only [lo, hi_set, Finset.mem_union, Finset.mem_filter,
          Finset.mem_univ, true_and]; exact Nat.lt_or_ge j.val L
    have h_hi_zero : ∀ ρ : FiniteRadixSpace b k,
        (∑ j ∈ hi_set, (ρ j : ℕ) * placeValue b j) % placeValue b L = 0 :=
      fun ρ => Nat.mod_eq_zero_of_dvd (Finset.dvd_sum (fun j hj => by
        simp only [hi_set, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        exact Dvd.dvd.mul_left (placeValue.dvd_of_le hj) _))
    have h_lo_eq : ∑ j ∈ lo, (τ j : ℕ) * placeValue b j =
                   ∑ j ∈ lo, (σ j : ℕ) * placeValue b j := by
      apply Finset.sum_congr rfl; intro j hj
      simp only [lo, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      congr 1; exact congrArg Fin.val (h_prefix_eq ⟨j.val, hj⟩)
    conv_lhs => rw [show (∑ j, (τ j : ℕ) * placeValue b j) =
      ∑ j ∈ lo, (τ j : ℕ) * placeValue b j + ∑ j ∈ hi_set, (τ j : ℕ) * placeValue b j from
      by rw [← Finset.sum_union hd, hu]]
    conv_rhs => rw [show (∑ j, (σ j : ℕ) * placeValue b j) =
      ∑ j ∈ lo, (σ j : ℕ) * placeValue b j + ∑ j ∈ hi_set, (σ j : ℕ) * placeValue b j from
      by rw [← Finset.sum_union hd, hu]]
    conv_lhs => rw [Nat.add_mod, h_hi_zero τ]
    conv_rhs => rw [Nat.add_mod, h_hi_zero σ]
    rw [h_lo_eq]
  conv_lhs => rw [Nat.add_mod, h_dec_mod, ← Nat.add_mod]

/--
**Proposition 31**: T̃_k preserves the uniform measure.

On a finite set with the counting measure, any bijection is measure-preserving.
Equivalently: for any function g, ∑_τ g(T̃_k(τ)) = ∑_τ g(τ).

**Proof**: Reindex the sum via the bijection `cyclicTick_bijective`.
-/
-- fdrs.md lines 1234-1240, Proposition 31
theorem cyclicTick_measurePreserving (b : RadixSeq) (k : ℕ)
    {α : Type*} [AddCommMonoid α] (g : FiniteRadixSpace b k → α) :
    ∑ τ, g (cyclicTick b k τ) = ∑ τ, g τ :=
  Fintype.sum_equiv (Equiv.ofBijective _ (cyclicTick_bijective b k))
    (fun τ => g (cyclicTick b k τ)) g (fun _ => rfl)

/--
Tick pullback preserves sums (hence all Lp norms).

**fdrs.md**: ‖T̃_k^* f‖_p = ‖f‖_p since T̃_k is a measure-preserving bijection.

**Proof**: Unfolds to `cyclicTick_measurePreserving`.
-/
-- fdrs.md lines 1234-1240, Proposition 31
theorem tickPullback_isometry (b : RadixSeq) (k : ℕ)
    {α : Type*} [AddCommMonoid α] (f : FiniteRadixSpace b k → α) :
    ∑ τ, tickPullback b k f τ = ∑ τ, f τ := by
  unfold tickPullback; exact cyclicTick_measurePreserving b k f

/-!
## Theorem 10: Commutation with Projections
-/

/--
**Theorem 10**: Tick pullback commutes with all block projections.

T̃_k^* P_L = P_L T̃_k^* for all L.

**fdrs.md proof**: P_L averages on cylinders U_k(s). Since T̃_k permutes cylinders
(by `cyclicTick_preserves_prefix`), the averaging sum is merely reindexed.

**Proof**: We construct an equivalence `cyl(s) ≃ cyl(T̃(s))` via cyclicTick,
then use `Fintype.sum_equiv` to reindex the sum in the block projection.
Bijectivity follows from injectivity (via `cyclicTick_bijective`) between
finite types of equal cardinality (via `finiteCylinder_card`).
-/
theorem tickPullback_commutes_projection (b : RadixSeq) (k L : ℕ) (hLk : L ≤ k + 1)
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : FiniteRadixSpace b k → V) :
    tickPullback b k (finiteBlockProjection b k L hLk f) =
    finiteBlockProjection b k L hLk (tickPullback b k f) := by
  ext τ
  simp only [tickPullback, finiteBlockProjection]
  congr 1
  set s := finitePrefix b L τ hLk
  set s' := finitePrefix b L (cyclicTick b k τ) hLk
  -- cyclicTick maps cyl(s) into cyl(s')
  have h_map : ∀ σ : finiteCylinderSet b k L hLk s,
      cyclicTick b k σ.val ∈ finiteCylinderSet b k L hLk s' := by
    intro ⟨σ_val, hσ⟩
    intro i
    have h_pref : finitePrefix b L σ_val hLk = s := funext hσ
    exact congr_fun (cyclicTick_preserves_prefix b k L hLk σ_val τ h_pref) i
  let φ : finiteCylinderSet b k L hLk s → finiteCylinderSet b k L hLk s' :=
    fun σ => ⟨cyclicTick b k σ.val, h_map σ⟩
  have hφ_inj : Function.Injective φ := by
    intro ⟨a, ha⟩ ⟨b_val, hb⟩ hab
    simp only [φ, Subtype.mk.injEq] at hab
    exact Subtype.ext ((cyclicTick_bijective b k).1 hab)
  have hcard : Fintype.card (finiteCylinderSet b k L hLk s) =
               Fintype.card (finiteCylinderSet b k L hLk s') := by
    rw [finiteCylinder_card, finiteCylinder_card]
  have hφ_bij : Function.Bijective φ := by
    refine ⟨hφ_inj, ?_⟩
    let ε := Fintype.equivOfCardEq hcard
    have hinj' : Function.Injective (φ ∘ ε.symm) := hφ_inj.comp ε.symm.injective
    have hbij' : Function.Bijective (φ ∘ ε.symm) := Finite.injective_iff_bijective.mp hinj'
    exact hbij'.2.of_comp
  exact (Fintype.sum_equiv (Equiv.ofBijective φ hφ_bij)
    (fun σ => f (cyclicTick b k σ.val)) (fun σ' => f σ'.val) (fun _ => rfl)).symm

/--
**Corollary 7**: Tick preserves detail scales.

T̃_k^* Δ_L = Δ_L T̃_k^* for all L, i.e. T̃_k^* preserves each detail scale.

**Proof**: Since Δ_L = P_{L+1} - P_L and T̃_k^* commutes with both P_{L+1} and P_L
(by `tickPullback_commutes_projection`), and T̃_k^* distributes over subtraction
(being pointwise precomposition), the result follows immediately.
-/
theorem tickPullback_preserves_details (b : RadixSeq) (k L : ℕ) (hLk : L < k + 1)
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : FiniteRadixSpace b k → V) :
    tickPullback b k (finiteDetailOperator b k L hLk f) =
    finiteDetailOperator b k L hLk (tickPullback b k f) := by
  unfold finiteDetailOperator
  have h_sub : tickPullback b k
      (finiteBlockProjection b k (L + 1) (by omega) f - finiteBlockProjection b k L (by omega) f) =
      tickPullback b k (finiteBlockProjection b k (L + 1) (by omega) f) -
      tickPullback b k (finiteBlockProjection b k L (by omega) f) := by
    ext τ; simp only [tickPullback, Pi.sub_apply]
  rw [h_sub,
    tickPullback_commutes_projection b k (L + 1) (by omega) f,
    tickPullback_commutes_projection b k L (by omega) f]

end FdrsFormal.FunctionSpaces.Commutant
