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

# Factorization Lens

Decomposition n = u_P(n) · s_P(n) into P-free and P-smooth parts.

## Mathematical Content (fdrs.md lines 2228-2513)

**Definition**: For finite prime set P and n ∈ ℕ≥1:
- Valuation vector: v_P(n) = (v_p(n))_{p ∈ P} ∈ ℕ^P
- P-smooth part: s_P(n) = ∏_{p ∈ P} p^{v_p(n)}
- P-free part: u_P(n) = n / s_P(n) (coprime to all p ∈ P)

**Key property**: n = u_P(n) · s_P(n) uniquely.

**Theorem 23** (fiberwise decomposition):
Dirichlet transforms with P-smooth kernels act fiberwise:
  (T_a f)(n) = ∑_{d | s_P(n)} a(d) · f(u_P(n) · s_P(n)/d)

Each u-fiber evolves independently under P-smooth operations.

## References

- fdrs.md, Phase 3 Fragment 4 (lines 2228-2476), Phase 4 Fragment 1 (lines 2488-2513)
- Paper §8.1-8.2, Definition 8.2
-/

import FdrsFormal.NumberTheory.Valuations
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Factorization.Basic

namespace FdrsFormal.NumberTheory.FactorizationLens

/-!
## Factorization Lens Definitions
-/

/--
The valuation vector v_P(n) for finite prime set P.

v_P(n) = (v_p(n))_{p ∈ P}

This is the "program space coordinate" inside an integer.
-/
def valuationVector (P : Finset ℕ) (_hP : ∀ p ∈ P, Nat.Prime p) (n : ℕ) : P → ℕ :=
  fun ⟨p, _⟩ => Nat.factorization n p

/--
The P-smooth part s_P(n) = ∏_{p ∈ P} p^{v_p(n)}.

This is the "largest P-smooth divisor" of n.
-/
def smoothPart (P : Finset ℕ) (_hP : ∀ p ∈ P, Nat.Prime p) (n : ℕ) : ℕ :=
  P.prod fun p => p ^ (Nat.factorization n p)

/--
The P-free part u_P(n) = n / s_P(n).

This is coprime to all primes in P.
-/
def freePart (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (n : ℕ) : ℕ :=
  n / smoothPart P hP n

/-!
## Helper Lemmas
-/

/-- If m is coprime to each f(x) for x ∈ s, then m is coprime to ∏_{x ∈ s} f(x). -/
private lemma coprime_of_coprime_prod (m : ℕ) (s : Finset ℕ) (f : ℕ → ℕ)
    (h : ∀ x ∈ s, Nat.Coprime m (f x)) :
    Nat.Coprime m (s.prod f) := by
  induction s using Finset.induction with
  | empty => simp [Nat.Coprime]
  | insert a s' ha ih =>
    rw [Finset.prod_insert ha]
    apply Nat.Coprime.mul_right
    · exact h a (Finset.mem_insert_self a s')
    · exact ih (fun x hx => h x (Finset.mem_insert_of_mem hx))

/-- The smooth part divides n. -/
private theorem smoothPart_dvd (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (n : ℕ) :
    smoothPart P hP n ∣ n := by
  by_cases hn : n = 0
  · simp [hn, smoothPart]
  · unfold smoothPart
    induction P using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      · apply Nat.Coprime.pow_left
        apply coprime_of_coprime_prod
        intro q hqs
        apply Nat.Coprime.pow_right
        apply (Nat.coprime_primes (hP a (Finset.mem_insert_self a s))
                                  (hP q (Finset.mem_insert_of_mem hqs))).mpr
        intro heq
        subst heq
        exact ha hqs
      · rw [(hP a (Finset.mem_insert_self a s)).pow_dvd_iff_le_factorization hn]
      · exact ih (fun p hp' => hP p (Finset.mem_insert_of_mem hp'))

/-- The smooth part captures exactly the p-adic valuation for p ∈ P. -/
private theorem smoothPart_valuation (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (n : ℕ)
    (_hn : n ≠ 0) (p : ℕ) (hp : p ∈ P) :
    (smoothPart P hP n).factorization p = n.factorization p := by
  unfold smoothPart
  have hprime := hP p hp
  have hne : ∀ q ∈ P, q ^ (n.factorization q) ≠ 0 := by
    intro q hq
    exact pow_ne_zero _ (Nat.Prime.ne_zero (hP q hq))
  rw [Nat.factorization_prod hne]
  simp only [Finsupp.coe_finset_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single p]
  · rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
        Nat.Prime.factorization_self hprime, mul_one]
  · intro q hq hqp
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    have hndvd : ¬(p ∣ q) := by
      have hcoprime : Nat.Coprime p q := (Nat.coprime_primes hprime (hP q hq)).mpr (Ne.symm hqp)
      exact hprime.coprime_iff_not_dvd.mp hcoprime
    rw [Nat.factorization_eq_zero_of_not_dvd hndvd]
    ring
  · intro hnp
    exact absurd hp hnp

/-!
## Factorization Properties
-/

/--
**Unique factorization**: n = u_P(n) · s_P(n).

**Proof**: By construction of smooth and free parts.
-/
theorem factorization_unique (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (n : ℕ) (_hn : 0 < n) :
    n = freePart P hP n * smoothPart P hP n := by
  unfold freePart
  exact (Nat.div_mul_cancel (smoothPart_dvd P hP n)).symm

/--
**P-free property**: u_P(n) is coprime to all p ∈ P.

**Proof**: All p-adic valuations at p ∈ P are concentrated in s_P(n).
-/
theorem freePart_coprime (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (n : ℕ) (hn : 0 < n)
    (p : ℕ) (hp : p ∈ P) :
    Nat.Coprime (freePart P hP n) p := by
  unfold freePart
  have hsmooth_dvd := smoothPart_dvd P hP n
  have hsmooth_pos : 0 < smoothPart P hP n := by
    unfold smoothPart
    apply Finset.prod_pos
    intro q hq
    exact Nat.pow_pos (Nat.Prime.pos (hP q hq))
  have hval := smoothPart_valuation P hP n (Nat.pos_iff_ne_zero.mp hn) p hp
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (hP p hp)]
  intro hdvd
  have hrough_pos : 0 < n / smoothPart P hP n := by
    exact Nat.div_pos (Nat.le_of_dvd (by omega) hsmooth_dvd) hsmooth_pos
  have hrough_ne : n / smoothPart P hP n ≠ 0 := Nat.pos_iff_ne_zero.mp hrough_pos
  have h1 : 1 ≤ (n / smoothPart P hP n).factorization p := by
    exact ((hP p hp).dvd_iff_one_le_factorization hrough_ne).mp hdvd
  have h2 : (n / smoothPart P hP n).factorization p =
      n.factorization p - (smoothPart P hP n).factorization p := by
    have := Nat.factorization_div hsmooth_dvd
    exact congr_fun (congrArg DFunLike.coe this) p
  rw [h2, hval] at h1
  omega

-- Theorem 23 (fiberwise decomposition) is proved in
-- FdrsFormal.NumberTheory.FactorizationLens.FiberDecomposition
-- as `factorizationFiberDecomp`.

end FdrsFormal.NumberTheory.FactorizationLens
