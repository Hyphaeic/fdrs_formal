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

# Squarefree Projection on Valuation Lattice

This file characterizes squarefree projection in valuation coordinates.

## Mathematical Content (fdrs.md lines 2430-2453)

**Proposition 54 (Squarefree constraint on P-valuation lattice)**:

For s = ∏_{p ∈ P} p^{e_p} ∈ S_P:
  μ²(s) = 1 ⟺ e_p ∈ {0,1} ∀ p ∈ P

Hence squarefree projection on P-smooth fibers is exactly restriction
to "{0,1}^P" hypercube inside ℕ^P.

**Proposition 55 (Möbius on P-smooth numbers)**:

For s = ∏_{p ∈ P} p^{e_p}:
  μ(s) = (-1)^{∑_p e_p} if e_p ∈ {0,1} ∀ p
  μ(s) = 0 otherwise

## References

- fdrs.md, Phase 3, Fragment 4, Section 6 (lines 2430-2453)
-/

import FdrsFormal.NumberTheory.FactorizationLens.Definition
import FdrsFormal.NumberTheory.ArithmeticFunctions.MobiusInversion

namespace FdrsFormal.NumberTheory.FactorizationLens

/-!
## Squarefree on Lattice
-/

/--
Squarefree constraint in exponent coordinates.

**fdrs.md Proposition 54 (lines 2431-2437)**: Squarefree ⟺ all factorization exponents ≤ 1.

**Proof**: Delegates to Mathlib's `Nat.squarefree_iff_factorization_le_one`.
-/
theorem squarefree_iff_boolean_exponents (n : ℕ) (hn : n ≠ 0) :
    Squarefree n ↔ ∀ p, n.factorization p ≤ 1 :=
  Nat.squarefree_iff_factorization_le_one hn

/--
Squarefree projection as hypercube restriction on P-smooth numbers.

**fdrs.md line 2436**: For P-smooth n (all prime factors in P),
squarefree ↔ all P-exponents are in {0,1}.

**Proof**: Specialization of `squarefree_iff_boolean_exponents`: for P-smooth n,
exponents at primes outside P are zero, so the condition reduces to primes in P.
-/
theorem squarefree_as_hypercube (P : Finset ℕ) (_hP : ∀ p ∈ P, Nat.Prime p)
    (n : ℕ) (hn : n ≠ 0) (hsmooth : ∀ p, Nat.Prime p → p ∣ n → p ∈ P) :
    Squarefree n ↔ ∀ p ∈ P, n.factorization p ≤ 1 := by
  rw [squarefree_iff_boolean_exponents n hn]
  exact ⟨fun h p _ => h p, fun h p => by
    by_cases hp : Nat.Prime p
    · by_cases hpn : p ∣ n
      · exact h p (hsmooth p hp hpn)
      · simp [Nat.factorization_eq_zero_of_not_dvd hpn]
    · simp [Nat.factorization_eq_zero_of_not_prime n hp]⟩

/-!
## Möbius on P-Smooth
-/

/--
Möbius function characterization.

**fdrs.md Proposition 55 (lines 2441-2450)**:
- μ(n) = (-1)^{Ω(n)} if n is squarefree (where Ω = number of prime factors with multiplicity)
- μ(n) = 0 otherwise

**Proof**: Delegates to Mathlib's `ArithmeticFunction.moebius_apply_of_squarefree`
and `ArithmeticFunction.moebius_eq_zero_of_not_squarefree`.
-/
theorem moebius_on_smooth (n : ℕ) :
    ArithmeticFunction.moebius n =
      if Squarefree n then (-1 : ℤ) ^ ArithmeticFunction.cardFactors n else 0 := by
  split_ifs with h
  · exact ArithmeticFunction.moebius_apply_of_squarefree h
  · exact ArithmeticFunction.moebius_eq_zero_of_not_squarefree h

end FdrsFormal.NumberTheory.FactorizationLens
