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

# Pure p-Power Kernels and Valuation-Fiber Action

Dirichlet transforms with kernels supported on prime powers give
lower-triangular convolutions in the valuation coordinate.

## Mathematical Content (fdrs.md lines 2181-2193)

**Definition 43**: Pure p-power kernel (a supported only on p-powers)
**Theorem 21**: Valuation-fiber Toeplitz action

## References

- fdrs.md, Phase 3 Fragment 3, Section 3.2-3.4 (lines 2181-2193)
-/

import FdrsFormal.NumberTheory.FactorizationLens.Definition
import FdrsFormal.NumberTheory.ArithmeticFunctions.Operators

namespace FdrsFormal.NumberTheory.FactorizationLens

open FdrsFormal.NumberTheory.ArithmeticFunctions
open Finset

/-! ## Definition 43: Pure p-power kernel -/

/--
**fdrs.md**: Definition 43 (pure p-power kernel) [§3.3 · Phase 3, Fragment 3] (lines 2181-2183)

An arithmetic function a is a pure p-power kernel if a(d) = 0 unless d = p^j
for some j ≥ 0.

**Axiomatized**: Predicate on arithmetic functions.
-/
def PurePowerKernel (p : ℕ) (a : ArithmeticFunction) : Prop :=
  ∀ n : {n : ℕ // 0 < n}, (¬ ∃ j, n.val = p ^ j) → a n = 0

/-! ## Theorem 21: Valuation-fiber Toeplitz action -/

private lemma j_le_r_of_pow_dvd {p r m j e : ℕ} (hp : Nat.Prime p) (hm : Nat.Coprime m p)
    (hx : p ^ j * e = p ^ r * m) : j ≤ r := by
  have h_dvd_nm : p ^ j ∣ p ^ r * m := ⟨e, hx.symm⟩
  have h_cop : Nat.Coprime (p ^ j) m := hm.symm.pow_left j
  have h_dvd_pr : p ^ j ∣ p ^ r := h_cop.dvd_of_dvd_mul_right h_dvd_nm
  by_contra hle; push_neg at hle
  exact absurd (Nat.le_of_dvd (pow_pos hp.pos r) h_dvd_pr)
    (not_le.mpr (Nat.pow_lt_pow_right hp.one_lt (by omega)))

/--
**fdrs.md**: Theorem 21 (valuation-fiber Toeplitz action) [§3.4 · Phase 3, Fragment 3] (lines 2185-2193)

Let n = p^r · m with gcd(m,p) = 1. If a is supported on p-powers, then:
  (T_a f)(p^r · m) = Σ_{j=0}^{r} a(p^j) · f(p^{r-j} · m)

Equivalently: for each fixed p-free m, T_a acts on the sequence
r ↦ f(p^r · m) by a finite lower-triangular convolution in the valuation coordinate r.

**Proof**: Divisors d | p^r·m that are p-powers are exactly p^j
for 0 ≤ j ≤ r, and (p^r·m)/p^j = p^{r-j}·m.
-/
-- fdrs.md lines 2185-2202, Theorem 21
theorem valuationFiberAction (p : ℕ) (hp : Nat.Prime p)
    (a : ArithmeticFunction) (ha : PurePowerKernel p a)
    (f : ArithmeticFunction) (r : ℕ) (m : ℕ) (hm : Nat.Coprime m p)
    (hm_pos : 0 < m) :
    dirichletTransform a f ⟨p ^ r * m, Nat.mul_pos (pow_pos hp.pos r) hm_pos⟩ =
    ∑ j ∈ Finset.range (r + 1),
      a ⟨p ^ j, pow_pos hp.pos j⟩ *
      f ⟨p ^ (r - j) * m, Nat.mul_pos (pow_pos hp.pos (r - j)) hm_pos⟩ := by
  -- Setup
  set n := p ^ r * m with hn_def
  have hn_pos : 0 < n := Nat.mul_pos (pow_pos hp.pos r) hm_pos
  have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn_pos
  -- Unfold dirichletTransform to the mathlib divisor sum
  have lhs_unfold : dirichletTransform a f ⟨n, hn_pos⟩ =
      ∑ x ∈ n.divisorsAntidiagonal, (toMathlib a) x.1 * (toMathlib f) x.2 := by
    simp only [dirichletTransform, dirichletConv, fromMathlib,
      _root_.ArithmeticFunction.mul_apply]
  rw [lhs_unfold]
  -- Define the injection φ : range(r+1) → divisorsAntidiagonal(n)
  -- mapping j ↦ (p^j, p^(r-j) * m)
  set φ : ℕ → ℕ × ℕ := fun j => (p ^ j, p ^ (r - j) * m) with hφ_def
  -- Step 1: φ maps into divisorsAntidiagonal
  have hφ_mem : ∀ j ∈ Finset.range (r + 1), φ j ∈ n.divisorsAntidiagonal := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [Nat.mem_divisorsAntidiagonal]
    constructor
    · -- p^j * (p^(r-j) * m) = n
      show p ^ j * (p ^ (r - j) * m) = p ^ r * m
      rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' (by omega : j ≤ r)]
    · exact hn_ne
  -- Step 2: φ is injective on range(r+1)
  have hφ_inj : ∀ j₁ ∈ Finset.range (r + 1), ∀ j₂ ∈ Finset.range (r + 1),
      φ j₁ = φ j₂ → j₁ = j₂ := by
    intro j₁ _ j₂ _ heq
    simp only [hφ_def, Prod.mk.injEq] at heq
    exact Nat.pow_right_injective hp.two_le heq.1
  -- Step 3: Elements outside image(φ) contribute zero
  have hzero : ∀ x ∈ n.divisorsAntidiagonal,
      x ∉ (Finset.range (r + 1)).image φ →
      (toMathlib a) x.1 * (toMathlib f) x.2 = 0 := by
    intro ⟨d, e⟩ hx hx_not
    rw [Nat.mem_divisorsAntidiagonal] at hx
    have hde : d * e = n := hx.1
    have hd_pos : 0 < d := by
      rcases Nat.eq_zero_or_pos d with rfl | h
      · simp at hde; exact absurd hde.symm hn_ne
      · exact h
    -- Case split: is d a power of p?
    by_cases hd_pow : ∃ j, d = p ^ j
    · -- d = p^j for some j: show (d, e) IS in image(φ), contradiction
      obtain ⟨j, rfl⟩ := hd_pow
      exfalso; apply hx_not
      rw [Finset.mem_image]
      have hj_le : j ≤ r := j_le_r_of_pow_dvd hp hm hde
      have he_eq : e = p ^ (r - j) * m := by
        have h1 : p ^ j * e = p ^ j * (p ^ (r - j) * m) := by
          rw [hde, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hj_le]
        exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos j) h1
      exact ⟨j, Finset.mem_range.mpr (by omega), by simp [hφ_def, he_eq]⟩
    · -- d is not a p-power: a(d) = 0 by PurePowerKernel
      have : (toMathlib a) d = 0 := by
        show (if h : 0 < d then a ⟨d, h⟩ else 0) = 0
        rw [dif_pos hd_pos]
        exact ha ⟨d, hd_pos⟩ hd_pow
      rw [this, zero_mul]
  -- Step 4: toMathlib converts back to our ArithmeticFunction on positive args
  have hval : ∀ j ∈ Finset.range (r + 1),
      (toMathlib a) (φ j).1 * (toMathlib f) (φ j).2 =
      a ⟨p ^ j, pow_pos hp.pos j⟩ *
      f ⟨p ^ (r - j) * m, Nat.mul_pos (pow_pos hp.pos (r - j)) hm_pos⟩ := by
    intro j _
    simp only [hφ_def]
    show (if h : 0 < p ^ j then a ⟨p ^ j, h⟩ else 0) *
         (if h : 0 < p ^ (r - j) * m then f ⟨p ^ (r - j) * m, h⟩ else 0) =
         a ⟨p ^ j, _⟩ * f ⟨p ^ (r - j) * m, _⟩
    rw [dif_pos (pow_pos hp.pos j),
        dif_pos (Nat.mul_pos (pow_pos hp.pos (r - j)) hm_pos)]
  -- Combine: full sum = sum over image(φ) = sum over range(r+1) = RHS
  calc ∑ x ∈ n.divisorsAntidiagonal, (toMathlib a) x.1 * (toMathlib f) x.2
      = ∑ x ∈ (Finset.range (r + 1)).image φ,
          (toMathlib a) x.1 * (toMathlib f) x.2 := by
        exact (Finset.sum_subset
          (Finset.image_subset_iff.mpr (fun j hj => hφ_mem j hj))
          (fun x hx hx_not => hzero x hx hx_not)).symm
    _ = ∑ j ∈ Finset.range (r + 1),
          (toMathlib a) (φ j).1 * (toMathlib f) (φ j).2 :=
        Finset.sum_image hφ_inj
    _ = ∑ j ∈ Finset.range (r + 1),
          a ⟨p ^ j, pow_pos hp.pos j⟩ *
          f ⟨p ^ (r - j) * m, Nat.mul_pos (pow_pos hp.pos (r - j)) hm_pos⟩ :=
        Finset.sum_congr rfl hval

end FdrsFormal.NumberTheory.FactorizationLens
