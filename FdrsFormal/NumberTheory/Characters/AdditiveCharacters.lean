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

# Additive Characters

Additive characters on ℤ/Nℤ and their orthogonality properties.

## Mathematical Content (fdrs.md lines 1792-1849)

**Definition**: For m ∈ {0,...,N-1}, the additive character is:
  χ_m(x) = exp(2πi·m·x/N)

**Proposition 38 (orthogonality)**:
  (1/N) ∑_{x ∈ ℤ/Nℤ} χ_m(x) · conj(χ_{m'}(x)) = δ_{m,m'}

**Proposition 42** (residue class projector):
For divisor q | N and residue a (mod q):
  𝟙_{x ≡ a (mod q)} = (1/q) ∑_{t=0}^{q-1} exp(2πi·t·(x-a)/q)

## References

- fdrs.md, Phase 3 Fragment 2, Section 1 (lines 1792-1849)
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Group.AddChar
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

namespace FdrsFormal.NumberTheory.Characters

/-!
## Additive Characters - AddChar Infrastructure (Mathlib bridge)
-/

/--
The standard additive character on ZMod N (via Mathlib's AddChar + zmodChar).

This is the canonical AddChar structure parameterized by m ∈ ZMod N.
Uses Mathlib's group-theoretic character machinery.
-/
noncomputable def standardAddChar (N : ℕ) [NeZero N] (m : ZMod N) : AddChar (ZMod N) ℂ :=
  let ζ := Complex.exp (2 * Real.pi * Complex.I / (N : ℂ))
  have hζ : ζ ^ N = 1 := by
    rw [← Complex.exp_nat_mul]
    have hN_ne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    have : (N : ℕ) * (2 * Real.pi * Complex.I / (N : ℂ)) = 2 * Real.pi * Complex.I := by
      field_simp [hN_ne]
    rw [this, Complex.exp_two_pi_mul_I]
  AddChar.zmodChar N hζ |>.mulShift m

/-!
## Exponential periodicity helper
-/

/--
Helper: exp(2πi · a / N) depends only on a mod N.

This is the key lemma connecting natural-number exponents to ZMod representatives.
-/
private lemma exp_periodic_mod (N a : ℕ) (hN : 0 < N) :
    Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (N : ℂ)) =
    Complex.exp (2 * Real.pi * Complex.I * ((a % N : ℕ) : ℂ) / (N : ℂ)) := by
  have hN_ne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h_decomp : (a : ℂ) = ↑(a % N) + ↑(a / N) * ↑N := by
    have h : a = a % N + a / N * N := by
      have := Nat.div_add_mod a N; rw [mul_comm] at this; omega
    exact_mod_cast h
  conv_lhs => rw [h_decomp]
  rw [show 2 * ↑Real.pi * Complex.I * (↑(a % N) + ↑(a / N) * ↑N) / ↑N =
      2 * ↑Real.pi * Complex.I * ↑(a % N) / ↑N +
      ↑(a / N) * (2 * ↑Real.pi * Complex.I) from by field_simp]
  rw [Complex.exp_add]
  rw [show (↑(a / N) : ℂ) * (2 * ↑Real.pi * Complex.I) =
      ↑(a / N) * (2 * Real.pi * Complex.I) from by push_cast; ring]
  rw [Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow, mul_one]

/--
Helper: exp(n * 2πi) = 1 for any integer n.
-/
private lemma exp_int_mul_two_pi_I (n : ℤ) :
    Complex.exp (↑n * (2 * ↑Real.pi * Complex.I)) = 1 := by
  cases n with
  | ofNat n =>
    simp only [Int.ofNat_eq_coe, Int.cast_natCast]
    rw [Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]
  | negSucc n =>
    simp only [Int.cast_negSucc]
    rw [neg_mul, Complex.exp_neg, Complex.exp_nat_mul,
        Complex.exp_two_pi_mul_I, one_pow, inv_one]

/-!
## FDRS-facing additive character (exp-based definition)
-/

/--
The additive character χ_m on ℤ/Nℤ (FDRS exp-based definition).

χ_m(x) = exp(2πi · m · x / N)

**Note**: Structural lemmas proven via bridge to standardAddChar (AddChar infrastructure).
-/
noncomputable def additiveCharacter (N m : ℕ) (hN : 0 < N) (x : ZMod N) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (ZMod.val x : ℂ) / (N : ℂ))

/-!
## Orthogonality Helper Lemmas
-/

/--
**Lemma**: Additive character respects addition.

χ_m(x + y) = χ_m(x) · χ_m(y)

**Proof**: Use ZMod.val_add, modular arithmetic, and exp_add.
-/
lemma additiveCharacter_add (N m : ℕ) (hN : 0 < N) [NeZero N] (x y : ZMod N) :
    additiveCharacter N m hN (x + y) =
    additiveCharacter N m hN x * additiveCharacter N m hN y := by
  unfold additiveCharacter
  have hN_ne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- Key: (m * (x+y).val) % N = (m * (x.val + y.val)) % N
  have h_key : (m * ZMod.val (x + y)) % N = (m * (ZMod.val x + ZMod.val y)) % N := by
    calc (m * ZMod.val (x + y)) % N
        = (m % N * (ZMod.val (x + y) % N)) % N := Nat.mul_mod _ _ _
      _ = (m % N * ((ZMod.val x + ZMod.val y) % N % N)) % N := by rw [ZMod.val_add]
      _ = (m % N * ((ZMod.val x + ZMod.val y) % N)) % N := by
          rw [Nat.mod_eq_of_lt (Nat.mod_lt _ hN)]
      _ = (m * (ZMod.val x + ZMod.val y)) % N := (Nat.mul_mod _ _ _).symm
  -- Rewrite LHS exp argument to factor out m into ℕ product
  rw [show 2 * ↑Real.pi * Complex.I * ↑m * ↑(ZMod.val (x + y)) / ↑N =
      2 * ↑Real.pi * Complex.I * ↑(m * ZMod.val (x + y)) / ↑N from by push_cast; ring]
  rw [exp_periodic_mod N (m * ZMod.val (x + y)) hN, h_key,
      ← exp_periodic_mod N (m * (ZMod.val x + ZMod.val y)) hN]
  rw [show 2 * ↑Real.pi * Complex.I * ↑(m * (ZMod.val x + ZMod.val y)) / ↑N =
      2 * ↑Real.pi * Complex.I * ↑m * ↑(ZMod.val x) / ↑N +
      2 * ↑Real.pi * Complex.I * ↑m * ↑(ZMod.val y) / ↑N from by
    push_cast; field_simp]
  exact Complex.exp_add _ _

/--
**Lemma**: Product of additive character with its conjugate equals 1.

χ_m(x) · conj(χ_m(x)) = 1

**Proof**: exp(θ*I) has norm 1 for any real θ, so normSq = 1,
and z * conj(z) = normSq z.
-/
lemma additiveCharacter_mul_conj_self (N m : ℕ) (hN : 0 < N) (x : ZMod N) :
    additiveCharacter N m hN x * (starRingEnd ℂ) (additiveCharacter N m hN x) = 1 := by
  unfold additiveCharacter
  rw [starRingEnd_apply, Complex.star_def, Complex.mul_conj]
  -- Show normSq(exp(...)) = 1, using that norm of exp(θ*I) = 1
  rw [Complex.normSq_eq_norm_sq]
  -- Use the fact that exp of purely imaginary has norm 1
  simp only [show (2 : ℂ) * ↑Real.pi * Complex.I * ↑m * ↑(x.val) / ↑N =
                  ((2 * Real.pi * ↑m * ↑(x.val) / ↑N) : ℝ) * Complex.I by
             push_cast; ring,
            Complex.norm_exp_ofReal_mul_I]
  norm_num

/--
**Lemma**: Sum of geometric series of roots of unity.

For ζ = exp(2πik/N) where k ≢ 0 (mod N), we have:
  ∑_{j=0}^{N-1} ζ^j = 0

**Proof**: Use geometric sum formula: (ζ - 1) * Σζ^i = ζ^N - 1.
Since ζ^N = 1 and ζ ≠ 1, the sum equals 0.
-/
lemma geom_sum_primitive_root (N k : ℕ) (hN : 0 < N) (hk : ¬(k % N = 0)) [Fintype (ZMod N)] :
    ∑ x : ZMod N, Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (ZMod.val x : ℂ) / (N : ℂ)) = 0 := by
  -- Let ζ = exp(2πik/N)
  let ζ := Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / (N : ℂ))

  -- Rewrite sum as geometric series in ζ
  have h_rewrite : ∑ x : ZMod N, Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (ZMod.val x : ℂ) / (N : ℂ)) =
                   ∑ x : ZMod N, ζ ^ (ZMod.val x) := by
    congr 1
    ext x
    simp only [show (2 * Real.pi * Complex.I * (k : ℂ) * (ZMod.val x : ℂ) / (N : ℂ)) =
                    (ZMod.val x : ℕ) * (2 * Real.pi * Complex.I * (k : ℂ) / (N : ℂ)) by
               push_cast; ring]
    rw [Complex.exp_nat_mul]

  rw [h_rewrite]

  -- Key fact: ζ^N = 1 (exp is periodic with period 2πi)
  have hζN : ζ ^ N = 1 := by
    simp only [ζ]
    rw [← Complex.exp_nat_mul]
    have h_simplify : (N : ℕ) * (2 * Real.pi * Complex.I * (k : ℂ) / (N : ℂ)) =
                      2 * Real.pi * Complex.I * (k : ℂ) := by
      have hN_ne : (N : ℂ) ≠ 0 := by norm_cast; omega
      field_simp [hN_ne]
    rw [h_simplify]
    -- exp(2πik*I) = exp(k * (2πi*I)) = (exp(2πi*I))^k = 1^k = 1
    rw [show 2 * Real.pi * Complex.I * (k : ℂ) = (k : ℕ) * (2 * Real.pi * Complex.I) by
         push_cast; ring]
    rw [Complex.exp_nat_mul]
    simp [Complex.exp_two_pi_mul_I]

  -- Key fact: ζ ≠ 1 (k % N ≠ 0 means exp(2πik/N*I) ≠ 1)
  have hζ_ne : ζ ≠ 1 := by
    intro h_eq
    simp only [ζ] at h_eq
    -- exp(2πik/N*I) = 1 iff 2πik/N*I = n*(2πi*I) for some integer n
    rw [Complex.exp_eq_one_iff] at h_eq
    obtain ⟨n, hn⟩ := h_eq
    -- From hn: 2πi*k/N = n*2πi
    -- Algebraic manipulation: k = n*N, so k % N = 0, contradicting hk
    -- The extraction from ℂ to ℕ requires careful use of cast injectivity
    have hN_ne : (N : ℂ) ≠ 0 := by norm_cast; omega
    have h_2pi_I_ne : 2 * Real.pi * Complex.I ≠ 0 := by
      apply mul_ne_zero; apply mul_ne_zero
      · norm_num
      · exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      · exact Complex.I_ne_zero
    have h_cleared : (k : ℂ) = (n : ℤ) * (N : ℂ) := by
      field_simp [hN_ne, h_2pi_I_ne] at hn
      linear_combination hn
    have h_int_eq : (k : ℤ) = n * (N : ℤ) := by
      apply @Int.cast_injective ℂ; push_cast
      convert h_cleared using 1 <;> ring
    have h_dvd : (N : ℤ) ∣ (k : ℤ) := ⟨n, by rw [mul_comm]; exact h_int_eq⟩
    have h_dvd_nat : N ∣ k := by
      obtain ⟨m, hm⟩ := h_dvd
      have hm_nonneg : 0 ≤ m := by
        have : 0 ≤ (k : ℤ) := Nat.cast_nonneg k
        rw [hm, mul_comm] at this
        exact Int.nonneg_of_mul_nonneg_left this (by omega : 0 < (N : ℤ))
      use m.toNat
      apply @Nat.cast_injective ℤ; push_cast
      rw [Int.toNat_of_nonneg hm_nonneg, ← hm]
    exact hk (Nat.mod_eq_zero_of_dvd h_dvd_nat)

  -- Apply geometric sum formula
  have h_geom : (ζ - 1) * ∑ i ∈ Finset.range N, ζ ^ i = ζ ^ N - 1 := mul_geom_sum ζ N
  rw [hζN] at h_geom
  simp only [sub_self] at h_geom

  -- Since ζ - 1 ≠ 0, conclude Σ ζ^i = 0
  have h_ζ_sub : ζ - 1 ≠ 0 := sub_ne_zero_of_ne hζ_ne
  have h_sum_zero : ∑ i ∈ Finset.range N, ζ ^ i = 0 := by
    have := mul_eq_zero.mp h_geom
    cases this with
    | inl h => exact absurd h h_ζ_sub
    | inr h => exact h

  -- Convert sum over ZMod N to sum over Finset.range N
  -- This uses that ZMod.val : ZMod N → ℕ is a bijection onto {0,...,N-1}
  haveI : NeZero N := ⟨hN.ne'⟩
  calc ∑ x : ZMod N, ζ ^ (ZMod.val x)
      = ∑ x ∈ Finset.univ, ζ ^ (ZMod.val x) := rfl
    _ = ∑ i ∈ Finset.range N, ζ ^ i := by
        apply Finset.sum_bij (fun x _ => ZMod.val x)
        · intro x _; simp [ZMod.val_lt]
        · intro x₁ x₂ _ _ h; exact ZMod.val_injective N h
        · intro i hi; simp [Finset.mem_range] at hi
          use (i : ZMod N); simp [ZMod.val_natCast, Nat.mod_eq_of_lt hi]
        · intros; rfl
    _ = 0 := h_sum_zero

/-!
## Orthogonality Helper
-/

/--
**Lemma**: Exp periodicity for ZMod difference.

When (m : ZMod N) ≠ (m' : ZMod N), we have exp(2πi(m-m')x/N) = exp(2πi·dm.val·x/N)
where dm = (m : ZMod N) - (m' : ZMod N).

**Justification**: This follows from (m - m') ≡ dm.val (mod N) and periodicity of exp.
-/
theorem exp_zmod_sub_eq (N m m' : ℕ) (hN : 0 < N) (x : ZMod N) :
    let dm := (m : ZMod N) - (m' : ZMod N)
    Complex.exp (2 * Real.pi * Complex.I * ((m : ℂ) - (m' : ℂ)) * (ZMod.val x : ℂ) / (N : ℂ)) =
    Complex.exp (2 * Real.pi * Complex.I * (dm.val : ℂ) * (ZMod.val x : ℂ) / (N : ℂ)) := by
  haveI : NeZero N := ⟨hN.ne'⟩
  simp only
  set dm := (m : ZMod N) - (m' : ZMod N)
  have hN_ne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- Key: N | ((m : ℤ) - m' - dm.val), so exponents differ by 2πi * integer
  have h_dvd : (N : ℤ) ∣ ((m : ℤ) - m' - dm.val) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [Int.cast_sub, Int.cast_natCast]
    have h_cast : ((dm.val : ℕ) : ZMod N) = dm :=
      ZMod.val_injective N (by simp [ZMod.val_natCast, Nat.mod_eq_of_lt (ZMod.val_lt dm)])
    rw [h_cast]; exact sub_self dm
  obtain ⟨k, hk⟩ := h_dvd
  -- (m : ℂ) - m' = dm.val + k * N
  have hk_C : ((m : ℂ) - (m' : ℂ)) = ↑(dm.val : ℕ) + (k : ℂ) * (N : ℂ) := by
    have h_int : ((m : ℤ) - m') = (dm.val : ℤ) + (N : ℤ) * k := by linarith
    have h_c := congr_arg (Int.cast (R := ℂ)) h_int
    push_cast at h_c
    linear_combination h_c
  rw [hk_C]
  -- Split exponent: dm.val part + k * x.val * 2πi part
  rw [show 2 * ↑Real.pi * Complex.I * (↑(dm.val : ℕ) + ↑k * ↑N) * ↑(ZMod.val x) / ↑N =
      2 * ↑Real.pi * Complex.I * ↑(dm.val : ℕ) * ↑(ZMod.val x) / ↑N +
      ↑k * ↑(ZMod.val x) * (2 * ↑Real.pi * Complex.I) from by field_simp]
  rw [Complex.exp_add]
  -- The second factor is exp(k * x.val * 2πi) = 1
  rw [show (↑k : ℂ) * ↑(ZMod.val x) * (2 * ↑Real.pi * Complex.I) =
      ↑(k * ↑(ZMod.val x)) * (2 * ↑Real.pi * Complex.I) from by push_cast; ring]
  rw [exp_int_mul_two_pi_I, mul_one]

/-!
## Orthogonality
-/

/--
**Proposition 38**: Additive characters are orthogonal.

**Statement** (fdrs.md lines 1813-1818):
  (1/N) ∑_{x ∈ ℤ/Nℤ} χ_m(x) · conj(χ_{m'}(x)) = δ_{m,m'}

**Proof**: This is the finite geometric series identity. When m = m',
the product is 1 everywhere, giving sum = N, hence (1/N) · N = 1.
When m ≠ m', the sum is a geometric series with ratio ≠ 1, which sums to 0.
-/
theorem additiveCharacter_orthogonal (N m m' : ℕ) (hN : 0 < N) [Fintype (ZMod N)] :
    (1 / (N : ℂ)) * (∑ x : ZMod N, additiveCharacter N m hN x * (starRingEnd ℂ) (additiveCharacter N m' hN x)) =
    if (m : ZMod N) = (m' : ZMod N) then 1 else 0 := by
  haveI : NeZero N := ⟨hN.ne'⟩
  by_cases h : (m : ZMod N) = (m' : ZMod N)
  · -- Case: (m : ZMod N) = (m' : ZMod N)
    simp only [h, ↓reduceIte]
    -- Use additiveCharacter_add to show χ_m = χ_m' when m ≡ m' (mod N)
    have h_char_eq : ∀ x : ZMod N, additiveCharacter N m hN x = additiveCharacter N m' hN x := by
      intro x; unfold additiveCharacter
      -- m ≡ m' (mod N), so m*x.val ≡ m'*x.val (mod N), so exp values are equal
      rw [show 2 * ↑Real.pi * Complex.I * ↑m * ↑(ZMod.val x) / ↑N =
          2 * ↑Real.pi * Complex.I * ↑(m * ZMod.val x) / ↑N from by push_cast; ring,
        show 2 * ↑Real.pi * Complex.I * ↑m' * ↑(ZMod.val x) / ↑N =
          2 * ↑Real.pi * Complex.I * ↑(m' * ZMod.val x) / ↑N from by push_cast; ring]
      rw [exp_periodic_mod N (m * ZMod.val x) hN, exp_periodic_mod N (m' * ZMod.val x) hN]
      have h_mod : m % N = m' % N := (ZMod.natCast_eq_natCast_iff m m' N).mp h
      have h_key : (m * ZMod.val x) % N = (m' * ZMod.val x) % N := by
        calc (m * ZMod.val x) % N
            = (m % N * (ZMod.val x % N)) % N := Nat.mul_mod m (ZMod.val x) N
          _ = (m' % N * (ZMod.val x % N)) % N := by rw [h_mod]
          _ = (m' * ZMod.val x) % N := (Nat.mul_mod m' (ZMod.val x) N).symm
      rw [h_key]
    have sum_eq_card : ∑ x : ZMod N, additiveCharacter N m hN x * (starRingEnd ℂ) (additiveCharacter N m' hN x) =
                       ∑ x : ZMod N, (1 : ℂ) := by
      congr 1
      funext x
      rw [h_char_eq]
      exact additiveCharacter_mul_conj_self N m' hN x
    rw [sum_eq_card]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [ZMod.card]
    have hN_ne : (N : ℂ) ≠ 0 := by
      norm_cast
      omega
    field_simp [hN_ne]
  · -- Case: m ≠ m'
    simp only [h, ↓reduceIte]
    -- The product χ_m(x) · conj(χ_m'(x)) = exp(2πi(m-m')x/N)
    -- This is a geometric sum with difference k = m - m' ≠ 0
    -- By geom_sum_primitive_root, the sum equals 0
    -- Therefore (1/N) · 0 = 0

    have h_sum_zero : ∑ x : ZMod N, additiveCharacter N m hN x * (starRingEnd ℂ) (additiveCharacter N m' hN x) = 0 := by
      -- Simplify: χ_m(x) * conj(χ_m'(x)) = exp(2πi*m*x/N) * exp(-2πi*m'*x/N) = exp(2πi(m-m')x/N)
      have h_simplify : ∀ x : ZMod N,
          additiveCharacter N m hN x * (starRingEnd ℂ) (additiveCharacter N m' hN x) =
          Complex.exp (2 * Real.pi * Complex.I * ((m : ℂ) - (m' : ℂ)) * (ZMod.val x : ℂ) / (N : ℂ)) := by
        intro x
        unfold additiveCharacter
        rw [starRingEnd_apply, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
        -- Simplify using exp_add and conjugate properties
        -- After exp_conj and exp_add, we need to show the exponents combine correctly
        congr 1
        simp only [map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_I, Complex.conj_natCast]
        have : (starRingEnd ℂ) (2 : ℂ) = 2 := Complex.conj_ofNat 2
        simp [this]; ring

      -- Rewrite sum
      conv_lhs => arg 2; ext x; rw [h_simplify x]

      -- Now apply geom_sum_primitive_root
      -- Need: k = (m - m') with k % N ≠ 0
      set dm : ZMod N := (m : ZMod N) - (m' : ZMod N)
      have hdm : dm ≠ 0 := sub_ne_zero.mpr h
      have hdm_val : dm.val ≠ 0 := by
        intro h0
        have : dm = 0 := (ZMod.val_eq_zero dm).mp h0
        exact hdm this
      have hk_ne : ¬(dm.val % N = 0) := by
        intro h_mod
        have h_lt : dm.val < N := ZMod.val_lt dm
        -- If dm.val < N and dm.val % N = 0, then dm.val = 0
        have : dm.val = 0 := by
          have h_dvd : N ∣ dm.val := Nat.dvd_iff_mod_eq_zero.mpr h_mod
          obtain ⟨k, hk⟩ := h_dvd
          cases k with
          | zero => exact hk
          | succ k =>
            rw [hk] at h_lt
            simp only [Nat.mul_succ] at h_lt
            have : N ≤ N * k + N := Nat.le_add_left N (N * k)
            have : N ≤ N + N * k := by omega
            omega
        exact hdm_val this

      -- Use exp_zmod_sub_eq to link (m - m') to dm.val
      conv_lhs => arg 2; ext x; rw [exp_zmod_sub_eq N m m' hN x]
      exact geom_sum_primitive_root N dm.val hN hk_ne

    rw [h_sum_zero]
    simp

/--
**Proposition 42**: Residue class projector via additive characters.

-- fdrs.md lines 1820-1831, Proposition 42

**Statement**: 𝟙_{x = a in ℤ/qℤ} = (1/q) ∑_{t ∈ ℤ/qℤ} χ_t(x) · conj(χ_t(a))

**Proof**: Swap character index and argument using exp(2πi·t·x/q) = exp(2πi·x·t/q),
then apply column orthogonality (additiveCharacter_orthogonal).
-/
theorem residueClassProjector (q : ℕ) (hq : 0 < q) [Fintype (ZMod q)] (x a : ZMod q) :
    (1 / (q : ℂ)) * ∑ t : ZMod q,
      additiveCharacter q (ZMod.val t) hq x *
      (starRingEnd ℂ) (additiveCharacter q (ZMod.val t) hq a) =
    if x = a then 1 else 0 := by
  haveI : NeZero q := ⟨hq.ne'⟩
  -- Swap indices: χ_{t.val}(x) = χ_{x.val}(t) since t·x = x·t in ℕ
  have h_swap : ∀ t : ZMod q,
      additiveCharacter q (ZMod.val t) hq x *
        (starRingEnd ℂ) (additiveCharacter q (ZMod.val t) hq a) =
      additiveCharacter q (ZMod.val x) hq t *
        (starRingEnd ℂ) (additiveCharacter q (ZMod.val a) hq t) := by
    intro t; congr 1
    · unfold additiveCharacter; congr 1; push_cast; ring
    · congr 1; unfold additiveCharacter; congr 1; push_cast; ring
  simp_rw [h_swap]
  -- Apply column orthogonality
  rw [additiveCharacter_orthogonal q (ZMod.val x) (ZMod.val a) hq]
  -- (val x : ZMod q) = x since val x < q
  have h_cast : ∀ (y : ZMod q), ((ZMod.val y : ℕ) : ZMod q) = y :=
    fun y => ZMod.val_injective q
      (by simp [ZMod.val_natCast, Nat.mod_eq_of_lt (ZMod.val_lt y)])
  rw [h_cast x, h_cast a]

/-!
## Convolution Diagonalization
-/

/--
Fourier transform on ℤ/Nℤ.

F{f}(m) = (1/N) ∑_{x ∈ ℤ/Nℤ} f(x) · conj(χ_m(x))
-/
noncomputable def fourierTransform (N : ℕ) (hN : 0 < N) (f : ZMod N → ℂ) (m : ℕ)
    [Fintype (ZMod N)] : ℂ :=
  (1 / (N : ℂ)) * ∑ x : ZMod N, f x * (starRingEnd ℂ) (additiveCharacter N m hN x)

/--
Cyclic convolution on ℤ/Nℤ.

(f ⊛ g)(x) = (1/N) ∑_{y ∈ ℤ/Nℤ} f(y) · g(x - y)
-/
noncomputable def cyclicConv (N : ℕ) [Fintype (ZMod N)] (f g : ZMod N → ℂ) : ZMod N → ℂ :=
  fun x => (1 / (N : ℂ)) * ∑ y : ZMod N, f y * g (x - y)

/--
**Theorem 16**: Convolution theorem (fdrs.md lines 1840-1848).

Additive characters diagonalize cyclic convolution:
  F{f ⊛ g}(m) = F{f}(m) · F{g}(m)

where F is the discrete Fourier transform and ⊛ is cyclic convolution.

**Proof strategy**: Expand definitions, swap summation order (Finset.sum_comm),
change of variables z = x - y via Fintype.sum_equiv (Equiv.subLeft y),
then use additiveCharacter_add to factorize χ_m(y + z) = χ_m(y) · χ_m(z).

**Justification for axiomatization**: Standard DFT convolution theorem.
The proof requires technical sum manipulations that are straightforward but tedious.
-/
theorem convolutionTheorem (N : ℕ) (hN : 0 < N) [Fintype (ZMod N)] (f g : ZMod N → ℂ) (m : ℕ) :
    fourierTransform N hN (cyclicConv N f g) m =
    fourierTransform N hN f m * fourierTransform N hN g m := by
  haveI : NeZero N := ⟨hN.ne'⟩
  have hN_ne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [fourierTransform, cyclicConv]
  -- Reduce to core sum identity
  suffices key : ∑ x : ZMod N, (∑ y : ZMod N, f y * g (x - y)) *
      (starRingEnd ℂ) (additiveCharacter N m hN x) =
      (∑ x : ZMod N, f x * (starRingEnd ℂ) (additiveCharacter N m hN x)) *
      (∑ x : ZMod N, g x * (starRingEnd ℂ) (additiveCharacter N m hN x)) by
    -- Extract the 1/N factors using algebra
    have h1 : ∀ x : ZMod N,
        (1 / (↑N : ℂ) * ∑ y, f y * g (x - y)) * (starRingEnd ℂ) (additiveCharacter N m hN x) =
        1 / ↑N * ((∑ y, f y * g (x - y)) * (starRingEnd ℂ) (additiveCharacter N m hN x)) := by
      intro x; ring
    simp_rw [h1, ← Finset.mul_sum, key]; ring
  -- Core identity: ∑_x (∑_y f(y)g(x-y)) conj(χ(x)) = (∑ f·conj(χ)) * (∑ g·conj(χ))
  -- First distribute conj(χ(x)) into the inner sum
  simp_rw [Finset.sum_mul]
  -- Now LHS = ∑_x ∑_y f(y) g(x-y) conj(χ(x))
  -- Swap sums: ∑_x ∑_y → ∑_y ∑_x
  rw [Finset.sum_comm]
  -- RHS is already ∑_y (f(y) conj(χ(y)) * ∑_z g(z) conj(χ(z))) after Finset.sum_mul
  congr 1; ext y
  -- For fixed y: ∑_x f(y)g(x-y)conj(χ(x)) = f(y)conj(χ(y)) · ∑_z g(z)conj(χ(z))
  -- Change of variable: x = y + z, so z = x - y
  rw [show ∑ x : ZMod N, f y * g (x - y) * (starRingEnd ℂ) (additiveCharacter N m hN x) =
      ∑ z : ZMod N, f y * g z * (starRingEnd ℂ) (additiveCharacter N m hN (y + z)) from by
    symm; apply Fintype.sum_equiv (Equiv.addLeft y)
    intro z; simp [add_sub_cancel_left]]
  -- Split χ_m(y+z) = χ_m(y) · χ_m(z)
  simp_rw [additiveCharacter_add N m hN, map_mul]
  -- Factor out f(y) · conj(χ_m(y)) from the sum
  simp_rw [show ∀ z : ZMod N, f y * g z *
      ((starRingEnd ℂ) (additiveCharacter N m hN y) *
       (starRingEnd ℂ) (additiveCharacter N m hN z)) =
      f y * (starRingEnd ℂ) (additiveCharacter N m hN y) *
      (g z * (starRingEnd ℂ) (additiveCharacter N m hN z)) from fun z => by ring]
  rw [← Finset.mul_sum]

end FdrsFormal.NumberTheory.Characters
