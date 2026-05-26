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

# Möbius Inversion Operator

This file defines the Möbius inversion operator T_μ (MobiusUnmix).

## Mathematical Content (fdrs.md Phase 4)

**Möbius Inversion**: The operator `T_μ` applies Möbius inversion, converting
between multiplicative and additive views.

**Key Identity**: `MobiusUnmix ∘ DivisorSum = I` (Möbius inversion formula)

## References

- fdrs.md, Phase 4, Section 4.2 (ANT Primitives)
- fdrs.md, Phase 3, Section 3.2 (Möbius Function)
-/

import FdrsFormal.Core
import FdrsFormal.NumberTheory
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

namespace FdrsFormal.Integration.Primitives

variable {V : Type*} [AddCommGroup V]

/-!
## Divisor Sum and Möbius Inversion
-/

/--
Divisor sum operator: `(DivisorSum f)(n) = Σ_{d|n} f(d)`

**fdrs.md**: Standard divisor sum from ANT
-/
def divisorSum (f : ℕ → V) : ℕ → V :=
  fun n => (Nat.divisors n).sum (fun d => f d)

/--
Möbius inversion operator: `(MobiusUnmix g)(n) = Σ_{d|n} μ(n/d) g(d)`

**fdrs.md**: `T_μ` - the Möbius unmixing transform
-/
def mobiusUnmix (g : ℕ → V) : ℕ → V :=
  fun n => (Nat.divisors n).sum (fun d =>
    (ArithmeticFunction.moebius (n / d) : ℤ) • g d)

/--
Helper: for p ∈ divisorsAntidiagonal n, n / p.1 = p.2.

**Proof**: By definition of divisorsAntidiagonal, p.1 * p.2 = n, so n / p.1 = p.2.
-/
private lemma divisorsAntidiagonal_snd (n : ℕ) (hn : n ≠ 0) (p : ℕ × ℕ)
    (hp : p ∈ Nat.divisorsAntidiagonal n) : n / p.1 = p.2 := by
  rw [Nat.mem_divisorsAntidiagonal] at hp
  have hpos : 0 < p.1 := by
    rcases Nat.eq_zero_or_pos p.1 with h | h
    · simp only [h, zero_mul] at hp
      exact absurd hp.1.symm hn
    · exact h
  rw [Nat.div_eq_iff_eq_mul_left hpos (hp.1.symm ▸ dvd_mul_right _ _)]
  rw [mul_comm]; exact hp.1.symm

/--
Convert from divisorsAntidiagonal sum to divisors sum form.

**Proof**: Bijection between divisorsAntidiagonal n and divisors n via p ↦ p.1.
-/
private lemma divisorsAntidiagonal_sum_eq_divisors_sum (n : ℕ) (hn : n ≠ 0) (g : ℕ → V) :
    (Nat.divisorsAntidiagonal n).sum (fun p => (ArithmeticFunction.moebius p.1 : ℤ) • g p.2) =
    (Nat.divisors n).sum (fun d => (ArithmeticFunction.moebius d : ℤ) • g (n / d)) := by
  apply Finset.sum_bij' (fun p _ => p.1) (fun d _ => (d, n / d))
  · intro p hp
    rw [Nat.mem_divisorsAntidiagonal] at hp
    rw [Nat.mem_divisors]
    exact ⟨hp.1.symm ▸ dvd_mul_right _ _, hn⟩
  · intro d hd
    rw [Nat.mem_divisors] at hd
    rw [Nat.mem_divisorsAntidiagonal]
    exact ⟨Nat.mul_div_cancel' hd.1, hn⟩
  · intro p hp
    ext
    · rfl
    · exact divisorsAntidiagonal_snd n hn p hp
  · intro d _
    rfl
  · intro p hp
    rw [← divisorsAntidiagonal_snd n hn p hp]

/--
Our mobiusUnmix equals the Mathlib antidiagonal form up to the bijection d ↔ n/d.

**Proof**: The bijection d ↔ n/d on divisors of n is an involution.
-/
private lemma mobiusUnmix_eq_antidiagonal_form (g : ℕ → V) (n : ℕ) (hn : n ≠ 0) :
    mobiusUnmix g n =
    (Nat.divisors n).sum (fun d => (ArithmeticFunction.moebius d : ℤ) • g (n / d)) := by
  unfold mobiusUnmix
  apply Finset.sum_bij' (fun d _ => n / d) (fun d _ => n / d)
  · intro d hd
    rw [Nat.mem_divisors] at hd ⊢
    exact ⟨Nat.div_dvd_of_dvd hd.1, hn⟩
  · intro d hd
    rw [Nat.mem_divisors] at hd ⊢
    exact ⟨Nat.div_dvd_of_dvd hd.1, hn⟩
  · intro d hd
    rw [Nat.mem_divisors] at hd
    exact Nat.div_div_self hd.1 hn
  · intro d hd
    rw [Nat.mem_divisors] at hd
    exact Nat.div_div_self hd.1 hn
  · intro d hd
    rw [Nat.mem_divisors] at hd
    rw [Nat.div_div_self hd.1 hn]

/--
Möbius inversion formula: MobiusUnmix ∘ DivisorSum = I

**fdrs.md**: Core identity `MobiusUnmix ∘ DivisorSum = I`

**Mathematical Proof**: This is the classical Möbius inversion formula.
If g(n) = Σ_{d|n} f(d), then f(n) = Σ_{d|n} μ(n/d) g(d).
The proof uses the fact that Σ_{d|n} μ(d) = [n = 1].

Uses Mathlib's `ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq` after
translating between divisor sums and divisorAntidiagonal forms.
-/
theorem mobiusInversion (f : ℕ → V) (n : ℕ) (hn : n ≠ 0) :
    mobiusUnmix (divisorSum f) n = f n := by
  have hpos : 0 < n := Nat.pos_of_ne_zero hn
  have hdiv : ∀ m > 0, (m.divisors).sum (fun d => f d) = divisorSum f m := fun _ _ => rfl
  have hinv := ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq.mp hdiv
  have h := hinv n hpos
  rw [divisorsAntidiagonal_sum_eq_divisors_sum n hn] at h
  rw [mobiusUnmix_eq_antidiagonal_form (divisorSum f) n hn]
  exact h

/--
Dual: DivisorSum ∘ MobiusUnmix = I

**Mathematical Proof**: The dual direction of Möbius inversion.
If f(n) = Σ_{d|n} μ(n/d) g(d), then g(n) = Σ_{d|n} f(d).
-/
theorem mobiusInversion_dual (g : ℕ → V) (n : ℕ) (hn : n ≠ 0) :
    divisorSum (mobiusUnmix g) n = g n := by
  have hpos : 0 < n := Nat.pos_of_ne_zero hn
  have hmob : ∀ m > 0, (Nat.divisorsAntidiagonal m).sum
      (fun p => (ArithmeticFunction.moebius p.1 : ℤ) • g p.2) = mobiusUnmix g m := by
    intro m hm
    rw [divisorsAntidiagonal_sum_eq_divisors_sum m (Nat.pos_iff_ne_zero.mp hm)]
    rw [← mobiusUnmix_eq_antidiagonal_form g m (Nat.pos_iff_ne_zero.mp hm)]
  have hinv := ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq.mpr hmob
  exact hinv n hpos

/-!
## Squarefree Projection
-/

/--
Squarefree projection: filters to squarefree integers.

**fdrs.md**: `SquarefreeProject(f)(n) = f(n) if n squarefree, else 0`
-/
def squarefreeProject (f : ℕ → V) : ℕ → V :=
  fun n => if Squarefree n then f n else 0

/--
Squarefree projection is idempotent.
-/
theorem squarefreeProject_idempotent (f : ℕ → V) :
    squarefreeProject (squarefreeProject f) = squarefreeProject f := by
  ext n
  simp only [squarefreeProject]
  split_ifs <;> rfl

/--
Möbius function is supported on squarefrees.

**fdrs.md**: μ(n) = 0 unless n is squarefree
-/
theorem moebius_squarefree_support (n : ℕ) (hn : ¬Squarefree n) :
    ArithmeticFunction.moebius n = 0 := by
  exact ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn

end FdrsFormal.Integration.Primitives
