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
-/
import FdrsFormal.NumberTheory.FactorizationLens.Definition
import FdrsFormal.NumberTheory.Valuations

/-!
# Divisibility Periodicity

-- fdrs.md lines 2297-2309, Proposition 52

Proves three properties of the divisibility indicator g_{p^e}(n) := 𝟙_{p^e | n}:
1. **Periodicity**: g_{p^e}(n) = g_{p^e}(n + p^e)
2. **Nesting**: g_{p^{e+1}} ≤ g_{p^e} pointwise
3. **Exact-valuation identity**: 𝟙_{v_p(n)=e} = g_{p^e}(n) - g_{p^{e+1}}(n)

## Main Results

* `divisibility_periodic` - periodicity of divisibility indicator
* `divisibility_nesting` - nesting of divisibility levels
* `exactValuation_eq_diff` - exact valuation projector as difference of divisibility projectors
* `divisibilityPeriodicity` - combined statement for spec-item matching

## References

* fdrs.md, Lines 2297-2309: Proposition 52 (periodicity of divisibility)
-/

open FdrsFormal.NumberTheory.Valuations

namespace FdrsFormal.NumberTheory

/-! ### Part (a): Periodicity -/

/-- **Proposition 52(a)**: The divisibility indicator g_{p^e}(n) := 𝟙_{p^e | n}
is periodic mod p^e: p^e | n ↔ p^e | (n + p^e). -/
theorem divisibility_periodic (p e n : ℕ) : p ^ e ∣ n ↔ p ^ e ∣ n + p ^ e := by
  simp only [Nat.dvd_iff_mod_eq_zero, Nat.add_mod_right]

/-! ### Part (b): Nesting -/

/-- **Proposition 52(b)**: g_{p^{e+1}} ≤ g_{p^e} pointwise, i.e.,
p^(e+1) | n → p^e | n. -/
theorem divisibility_nesting (p : ℕ) {e n : ℕ} (h : p ^ (e + 1) ∣ n) : p ^ e ∣ n :=
  dvd_trans (Nat.pow_dvd_pow p (Nat.le_succ e)) h

/-! ### Part (c): Exact-valuation identity -/

/-- Bridge: characterize padicValNat via divisibility.
v_p(n) = e ↔ p^e | n ∧ ¬(p^{e+1} | n). -/
private lemma padicValNat_eq_iff (p e n : ℕ) (hp : Nat.Prime p) (hn : n ≠ 0) :
    padicValNat p n = e ↔ p ^ e ∣ n ∧ ¬ p ^ (e + 1) ∣ n := by
  rw [← Nat.factorization_def n hp]
  constructor
  · intro h
    exact ⟨(hp.pow_dvd_iff_le_factorization hn).mpr (le_of_eq h.symm),
           fun h1 => by have := (hp.pow_dvd_iff_le_factorization hn).mp h1; omega⟩
  · intro ⟨h1, h2⟩
    have hle := (hp.pow_dvd_iff_le_factorization hn).mp h1
    have hlt : ¬(e + 1 ≤ n.factorization p) := by
      intro h; exact h2 ((hp.pow_dvd_iff_le_factorization hn).mpr h)
    omega

/-- **Proposition 52(c)**: The exact-valuation projector equals the difference of
consecutive divisibility projectors:
  Π_{p,=e} f = Π_{p^e} f - Π_{p^{e+1}} f

Equivalently: 𝟙_{v_p(n)=e} = 𝟙_{p^e | n} - 𝟙_{p^{e+1} | n}. -/
theorem exactValuation_eq_diff (p e : ℕ) [hp : Fact p.Prime]
    (f : {n : ℕ // 0 < n} → ℂ) (n : {n : ℕ // 0 < n}) :
    exactValuationProjector p e f n =
    divisibilityProjector p e f n - divisibilityProjector p (e + 1) f n := by
  simp only [exactValuationProjector, divisibilityProjector, padicValuation]
  have hn : n.val ≠ 0 := by omega
  by_cases he : p ^ e ∣ n.val
  · by_cases he1 : p ^ (e + 1) ∣ n.val
    · -- Both divide: v_p(n) > e, so v_p(n) ≠ e
      have hne : ¬(padicValNat p n.val = e) := by
        intro heq
        exact ((padicValNat_eq_iff p e n.val hp.out hn).mp heq).2 he1
      simp [he, he1, hne, sub_self]
    · -- p^e | n but ¬(p^(e+1) | n): v_p(n) = e
      have heq : padicValNat p n.val = e :=
        (padicValNat_eq_iff p e n.val hp.out hn).mpr ⟨he, he1⟩
      simp [he, he1, heq, sub_zero]
  · -- ¬(p^e | n): also ¬(p^(e+1) | n), and v_p(n) ≠ e
    have hne1 : ¬(p ^ (e + 1) ∣ n.val) := fun h => he (divisibility_nesting p h)
    have hne : ¬(padicValNat p n.val = e) := by
      intro heq; exact he (heq ▸ pow_padicValNat_dvd)
    simp [he, hne1, hne]

/-! ### Combined statement for spec-item matching -/

/-- **Proposition 52** (fdrs.md lines 2297-2309): Periodicity of divisibility.

For prime p and e ≥ 1:
1. g_{p^e}(n) = g_{p^e}(n + p^e) (periodicity)
2. g_{p^{e+1}} ≤ g_{p^e} (nesting)
3. 𝟙_{v_p(n)=e} = g_{p^e} - g_{p^{e+1}} (exact-valuation identity)

All three parts are proved as `divisibility_periodic`, `divisibility_nesting`,
and `exactValuation_eq_diff` respectively. -/
theorem divisibilityPeriodicity (p e : ℕ) [hp : Fact p.Prime] :
    -- (a) Periodicity
    (∀ n, p ^ e ∣ n ↔ p ^ e ∣ n + p ^ e) ∧
    -- (b) Nesting
    (∀ n, p ^ (e + 1) ∣ n → p ^ e ∣ n) ∧
    -- (c) Exact-valuation identity (projector form)
    (∀ (f : {n : ℕ // 0 < n} → ℂ) (n : {n : ℕ // 0 < n}),
      exactValuationProjector p e f n =
      divisibilityProjector p e f n - divisibilityProjector p (e + 1) f n) :=
  ⟨divisibility_periodic p e,
   fun _ h => divisibility_nesting p h,
   fun f n => exactValuation_eq_diff p e f n⟩

end FdrsFormal.NumberTheory
