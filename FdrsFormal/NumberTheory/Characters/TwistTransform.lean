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

# Twist–Transform Covariance

Dirichlet character twists and their covariance with Dirichlet transforms.

## Mathematical Content (fdrs.md lines 2156-2175)

**Theorem 20**: M_χ T_a = T_{a·χ} M_χ (twist–transform covariance)
**Corollary 15**: M_χ commutes with T_a iff a·χ = a

## References

- fdrs.md, Phase 3 Fragment 3, Section 3 (lines 2156-2175)
-/

import FdrsFormal.NumberTheory.Characters.DirichletCharacters
import FdrsFormal.NumberTheory.ArithmeticFunctions.DirichletConv

namespace FdrsFormal.NumberTheory.Characters

open FdrsFormal.NumberTheory.ArithmeticFunctions

/-! ## Complete multiplicativity of Dirichlet characters -/

/--
Dirichlet characters are completely multiplicative: χ(m·n) = χ(m)·χ(n).

When gcd(m·n, q) > 1, both sides are 0.
When gcd(m·n, q) = 1, follows from the MulChar property on units.
-/
theorem DirichletChar.apply_mul {q : ℕ} (χ : DirichletChar q) (m n : ℕ) :
    χ.apply (m * n) = χ.apply m * χ.apply n := by
  simp only [DirichletChar.apply]
  by_cases hmn : Nat.Coprime (m * n) q
  · have hm : Nat.Coprime m q := Nat.Coprime.coprime_dvd_left (dvd_mul_right m n) hmn
    have hn : Nat.Coprime n q := Nat.Coprime.coprime_dvd_left (dvd_mul_left n m) hmn
    rw [dif_pos hmn, dif_pos hm, dif_pos hn]
    have hunits : ZMod.unitOfCoprime (m * n) hmn =
                  ZMod.unitOfCoprime m hm * ZMod.unitOfCoprime n hn := by
      ext; simp [ZMod.coe_unitOfCoprime, Nat.cast_mul]
    rw [hunits, Units.val_mul, map_mul]
  · rw [dif_neg hmn]
    by_cases hm : Nat.Coprime m q
    · by_cases hn : Nat.Coprime n q
      · exact absurd (hm.mul_left hn) hmn
      · rw [dif_pos hm, dif_neg hn, mul_zero]
    · rw [dif_neg hm, zero_mul]

/-! ## Theorem 20: Twist–transform covariance -/

/--
**fdrs.md**: Theorem 20 (twist–transform covariance) [§3.1 · Phase 3, Fragment 3] (lines 2156-2170)

For any arithmetic function a and Dirichlet character χ:
  M_χ T_a = T_{a·χ} M_χ
where (a·χ)(d) := a(d)χ(d).

**Proof**:
  (M_χ T_a f)(n) = χ(n) Σ_{d|n} a(d) f(n/d)
                  = Σ_{d|n} a(d)χ(d) · χ(n/d) f(n/d)
                  = (T_{a·χ} (M_χ f))(n)
using complete multiplicativity χ(n) = χ(d)χ(n/d).
-/
-- fdrs.md lines 2156-2170, Theorem 20
theorem twistTransformCovariance (q : ℕ) (χ : DirichletChar q)
    (a f : ArithmeticFunction) (n : {n : ℕ // 0 < n}) :
    χ.apply n.val * (dirichletConv a f) n =
    (dirichletConv (fun m => a m * χ.apply m.val)
                   (fun m => χ.apply m.val * f m)) n := by
  -- Unfold dirichletConv to Mathlib divisor sums
  simp only [dirichletConv, fromMathlib, _root_.ArithmeticFunction.mul_apply]
  -- Distribute χ(n) into the sum
  rw [Finset.mul_sum]
  -- Per-summand equality
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨hprod, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hx
  -- Both components are positive since their product n is positive
  have hd0 : 0 < x.1 := by
    by_contra h; push_neg at h
    exact hn0 (by rw [← hprod, Nat.le_zero.mp h, zero_mul])
  have he0 : 0 < x.2 := by
    by_contra h; push_neg at h
    exact hn0 (by rw [← hprod, Nat.le_zero.mp h, mul_zero])
  -- Simplify toMathlib at positive arguments
  simp only [toMathlib_apply hd0, toMathlib_apply he0]
  -- Key step: χ(n) = χ(d) · χ(e) by complete multiplicativity (d·e = n)
  have hmult : χ.apply n.val = χ.apply x.1 * χ.apply x.2 := by
    rw [← hprod]; exact χ.apply_mul x.1 x.2
  rw [hmult]
  ring

/-! ## Corollary 15: True commutation criterion -/

/--
**fdrs.md**: Corollary 15 (true commutation criterion) [§3.2 · Phase 3, Fragment 3] (lines 2172-2175)

M_χ commutes with T_a iff a(d)χ(d) = a(d) for all d,
i.e. a is supported where χ(d) = 1, or more generally a·χ = a.

**Proof**: By Theorem 20, M_χ T_a f = T_{a·χ} M_χ f. If a·χ = a, then T_{a·χ} = T_a,
so M_χ T_a f = T_a M_χ f.
-/
-- fdrs.md lines 2172-2175, Corollary 15
theorem commutationCriterion (q : ℕ) (χ : DirichletChar q)
    (a : ArithmeticFunction)
    (h : ∀ m : {n : ℕ // 0 < n}, a m * χ.apply m.val = a m) :
    ∀ (f : ArithmeticFunction) (n : {n : ℕ // 0 < n}),
      χ.apply n.val * (dirichletConv a f) n =
      (dirichletConv a (fun m => χ.apply m.val * f m)) n := by
  intro f n
  rw [twistTransformCovariance q χ a f n]
  -- Suffices to show a·χ = a as functions
  congr 1
  exact funext h

end FdrsFormal.NumberTheory.Characters
