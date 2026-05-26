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
import FdrsFormal.NumberTheory.FactorizationLens.ExponentConvolution
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Fiber Decomposition

-- fdrs.md lines 2367-2395, Theorem 23

This file proves that Dirichlet transforms with P-smooth kernels act
fiberwise: the divisor sum ∑_{d|n} a(d) f(n/d) reduces to a sum over
divisors of the smooth part s_P(n), never mixing different P-free fibers.

## Main Results

* `factorizationFiberDecomp` - **Theorem 23**: ∑_{d|n} a(d) f(n/d) =
  ∑_{d|s_P(n)} a(d) f(u_P(n) · s_P(n)/d)  when a is P-smooth supported.

## References

* fdrs.md, Lines 2367-2400: Theorem 23 (fiberwise decomposition)
-/

open FdrsFormal.NumberTheory.FactorizationLens
open scoped BigOperators

namespace FdrsFormal.NumberTheory

/--
The factorization fiber: all positive integers with P-free part equal to u.
-/
def FactorizationFiber (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (u : ℕ) : Set ℕ :=
  {m : ℕ | 0 < m ∧ freePart P hP m = u}

private lemma smoothPart_pos (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (n : ℕ) :
    0 < smoothPart P hP n := by
  unfold smoothPart
  apply Finset.prod_pos
  intro p hp
  exact Nat.pow_pos (Nat.Prime.pos (hP p hp))

private lemma smoothPart_dvd' (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (n : ℕ) (hn : 0 < n) :
    smoothPart P hP n ∣ n :=
  ⟨freePart P hP n, by rw [mul_comm]; exact factorization_unique P hP n hn⟩

/-- If d ∣ n and all prime factors of d are in P, then d ∣ smoothPart P hP n.
This is the key divisibility lemma for Theorem 23. -/
private lemma pSmooth_dvd_smoothPart (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (n d : ℕ) (hn : 0 < n) (_hd : 0 < d) (hdn : d ∣ n)
    (h_in_P : ∀ p, Nat.Prime p → p ∣ d → p ∈ P) :
    d ∣ smoothPart P hP n := by
  -- n = freePart * smoothPart
  have h_eq : n = freePart P hP n * smoothPart P hP n := factorization_unique P hP n hn
  -- d is coprime to freePart: any common prime factor p would satisfy
  -- p ∈ P (from h_in_P) yet p ∣ freePart (contradicting freePart_coprime)
  have hcop : Nat.Coprime d (freePart P hP n) := by
    by_contra h
    obtain ⟨p, hp_prime, hp_dvd_gcd⟩ := Nat.exists_prime_and_dvd h
    have hp_dvd_d : p ∣ d := dvd_trans hp_dvd_gcd (Nat.gcd_dvd_left d _)
    have hp_dvd_free : p ∣ freePart P hP n := dvd_trans hp_dvd_gcd (Nat.gcd_dvd_right d _)
    have hp_in_P := h_in_P p hp_prime hp_dvd_d
    have := (Nat.Prime.coprime_iff_not_dvd hp_prime).mp
      (Nat.coprime_comm.mp (freePart_coprime P hP n hn p hp_in_P))
    exact this hp_dvd_free
  -- d ∣ freePart * smoothPart and gcd(d, freePart) = 1, so d ∣ smoothPart
  rw [h_eq] at hdn
  exact Nat.Coprime.dvd_of_dvd_mul_left hcop hdn

/--
**Theorem 23** (fdrs.md lines 2367-2378): Factorization-fiber decomposition.

For a P-smooth supported kernel a (meaning a(d) ≠ 0 only when d is P-smooth),
the Dirichlet divisor sum over n reduces to divisors of the smooth part:

  ∑_{d|n} a(d) f(n/d) = ∑_{d|s_P(n)} a(d) f(u_P(n) · (s_P(n)/d))

**Proof**: If a(d) ≠ 0 then d is P-smooth. A P-smooth divisor of n = u·s
must divide s (since gcd(u,d) = 1). So the sum reduces to d | s.
-/
theorem factorizationFiberDecomp (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (a f : ℕ → ℂ) (n : ℕ) (hn : 0 < n)
    (ha_smooth : ∀ d, a d ≠ 0 → ∀ p, Nat.Prime p → p ∣ d → p ∈ P) :
    ∑ d ∈ n.divisors, a d * f (n / d) =
    ∑ d ∈ (smoothPart P hP n).divisors,
      a d * f (freePart P hP n * (smoothPart P hP n / d)) := by
  -- Step 1: The sums over n.divisors and smoothPart.divisors of (a d * f (n/d)) agree
  have h_subset : (smoothPart P hP n).divisors ⊆ n.divisors := by
    intro d hd
    rw [Nat.mem_divisors] at hd ⊢
    exact ⟨dvd_trans hd.1 (smoothPart_dvd' P hP n hn), by omega⟩
  have h_sum_eq : ∑ d ∈ n.divisors, a d * f (n / d) =
      ∑ d ∈ (smoothPart P hP n).divisors, a d * f (n / d) := by
    symm
    apply Finset.sum_subset h_subset
    intro d hd hnd
    have hdn := (Nat.mem_divisors.mp hd).1
    have hd_pos : 0 < d := Nat.pos_of_ne_zero (fun h => by simp [h] at hdn; omega)
    have hnd_smooth : ¬(d ∣ smoothPart P hP n) := by
      intro h_dvd
      exact hnd (Nat.mem_divisors.mpr ⟨h_dvd, Nat.pos_iff_ne_zero.mp (smoothPart_pos P hP n)⟩)
    suffices a d = 0 by simp [this]
    by_contra had
    exact hnd_smooth (pSmooth_dvd_smoothPart P hP n d hn hd_pos hdn (ha_smooth d had))
  -- Step 2: Rewrite n/d = freePart * (smoothPart / d) for d | smoothPart
  rw [h_sum_eq]
  apply Finset.sum_congr rfl
  intro d hd
  have hd_dvd_s := (Nat.mem_divisors.mp hd).1
  have h_ndiv : n / d = freePart P hP n * (smoothPart P hP n / d) := by
    conv_lhs => rw [factorization_unique P hP n hn]
    exact Nat.mul_div_assoc (freePart P hP n) hd_dvd_s
  rw [h_ndiv]

end FdrsFormal.NumberTheory
