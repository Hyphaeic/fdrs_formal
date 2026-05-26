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

# Integers as Programs

This file defines the semantic map from integers to programs.

## Mathematical Content (fdrs.md Phase 4)

**Semantic Map**: `n ↦ ⟦n⟧_k = T_{δ_n}` where δ_n is the indicator of {n}.

**Key Property**: Multiplication ↔ Composition
  `⟦a⟧ ∘ ⟦b⟧ = ⟦ab⟧`

This establishes integers as a "programming language" where multiplication
is program composition.

## References

- fdrs.md, Phase 4, Section 4.3 (Integers as Programs)
- fdrs.md, Phase 4, Theorem 24 (Multiplication ↔ Composition)
-/

import FdrsFormal.Core
import FdrsFormal.Topology
import FdrsFormal.NumberTheory

namespace FdrsFormal.Integration.Programs

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Block size at depth L: B_L = ∏_{i=0}^{L-1} b_i -/
def blockSize (b : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => blockSize b n * b n

/-!
## Integer Program Semantics
-/

/--
The semantic map: integer n becomes the Dirichlet transform by δ_n.

**fdrs.md**: `⟦n⟧_k = T_{δ_n}` where δ_n(m) = 1 if m = n, else 0
-/
def integerProgram (n : ℕ) (f : ℕ → V) : ℕ → V :=
  fun m => if n ∣ m then f (m / n) else 0

/--
The identity program is ⟦1⟧.

**fdrs.md**: `⟦1⟧ = I` (identity operator)
-/
theorem integerProgram_one (f : ℕ → V) :
    integerProgram 1 f = f := by
  ext m
  simp only [integerProgram, Nat.one_dvd, Nat.div_one, ite_true]

/--
Multiplication becomes composition.

**fdrs.md Theorem 24**: `⟦a⟧ ∘ ⟦b⟧ = ⟦ab⟧`

This is the core semantic identity that makes integers a programming language.
-/
theorem integerProgram_mul (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (f : ℕ → V) :
    integerProgram a (integerProgram b f) = integerProgram (a * b) f := by
  ext m
  simp only [integerProgram]
  -- Case split on whether a*b divides m
  by_cases hab_dvd : (a * b) ∣ m
  · -- If a*b | m, then a | m and b | (m/a)
    have ha_dvd : a ∣ m := dvd_trans (dvd_mul_right a b) hab_dvd
    simp only [ha_dvd, ↓reduceIte, hab_dvd]
    -- Need to show b | (m/a) and (m/a)/b = m/(a*b)
    have hb_dvd : b ∣ (m / a) := by
      rw [Nat.dvd_div_iff_mul_dvd ha_dvd]
      exact (mul_comm a b) ▸ hab_dvd
    simp only [hb_dvd, ↓reduceIte]
    -- (m/a)/b = m/(a*b)
    congr 1
    rw [Nat.div_div_eq_div_mul]
  · -- If a*b ∤ m, then either a ∤ m or (a | m but b ∤ m/a)
    simp only [hab_dvd, ↓reduceIte]
    by_cases ha_dvd : a ∣ m
    · -- a | m but a*b ∤ m, so b ∤ m/a
      simp only [ha_dvd, ↓reduceIte]
      have hb_not_dvd : ¬(b ∣ (m / a)) := by
        intro hb_dvd
        apply hab_dvd
        exact Nat.mul_dvd_of_dvd_div ha_dvd hb_dvd
      simp only [hb_not_dvd, ↓reduceIte]
    · -- a ∤ m
      simp only [ha_dvd, ↓reduceIte]

/-!
## Prime Power Decomposition
-/

/-- Product of nonzero natural numbers is nonzero. -/
private lemma list_prod_ne_zero (l : List ℕ) (hl : ∀ p ∈ l, p ≠ 0) : l.prod ≠ 0 := by
  induction l with
  | nil => simp
  | cons p l' ih =>
    simp only [List.prod_cons]
    exact Nat.mul_ne_zero (hl _ List.mem_cons_self)
      (ih (fun q hq => hl _ (List.mem_cons_of_mem p hq)))

/-- Composing integerProgram over a list equals integerProgram of their product. -/
private theorem integerProgram_list_prod (l : List ℕ) (hl : ∀ p ∈ l, p ≠ 0) (f : ℕ → V) :
    integerProgram l.prod f =
      List.foldr (fun p g => integerProgram p g) f l := by
  induction l with
  | nil => simp [integerProgram_one]
  | cons p l' ih =>
    simp only [List.prod_cons, List.foldr_cons]
    have hp : p ≠ 0 := hl _ List.mem_cons_self
    have hl' : ∀ q ∈ l', q ≠ 0 := fun q hq => hl _ (List.mem_cons_of_mem p hq)
    rw [← integerProgram_mul p l'.prod hp (list_prod_ne_zero l' hl') f, ih hl']

/--
Integer programs factor through prime factors.

**fdrs.md**: `⟦n⟧ = ⟦p₁⟧ ∘ ⟦p₂⟧ ∘ ... ∘ ⟦pₖ⟧` where n = p₁ · p₂ · ... · pₖ
is the prime factorization (with multiplicity).
-/
theorem integerProgram_factorization (n : ℕ) (hn : n ≠ 0) (f : ℕ → V) :
    integerProgram n f =
      List.foldr (fun p g => integerProgram p g) f n.primeFactorsList := by
  conv_lhs => rw [← Nat.prod_primeFactorsList hn]
  exact integerProgram_list_prod n.primeFactorsList
    (fun p hp => by have := Nat.pos_of_mem_primeFactorsList hp; omega) f

/-!
## Rhythm Gates
-/

/--
Rhythm gate: the set of positions where n divides the natural encoding.

**fdrs.md**: `E_n = {τ : n | nat_k(τ)}`
-/
def rhythmGate (b : ℕ → ℕ) (k : ℕ) (n : ℕ) : Set (Fin (blockSize b k)) :=
  {τ | n ∣ τ.val}

/--
Rhythm gates for coprime integers are independent.

**fdrs.md**: `E_{ab} = E_a ∩ E_b` when gcd(a,b) = 1

**Mathematical Proof**: For coprime a,c: (a*c) | n ↔ a | n ∧ c | n.
This is a standard number theory fact: when gcd(a,c) = 1,
the divisibility by a*c is equivalent to divisibility by both.
The forward direction uses that a | (a*c) and c | (a*c).
The reverse uses that coprime divisors combine: if a | n and c | n
with gcd(a,c) = 1, then (a*c) | n.
-/
theorem rhythmGate_coprime (b : ℕ → ℕ) (k : ℕ) (a c : ℕ)
    (hcoprime : Nat.Coprime a c) :
    rhythmGate b k (a * c) = rhythmGate b k a ∩ rhythmGate b k c := by
  ext τ
  simp only [rhythmGate, Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · -- Forward: (a*c) | τ implies a | τ and c | τ
    intro h
    exact ⟨dvd_trans (dvd_mul_right a c) h, dvd_trans (dvd_mul_left c a) h⟩
  · -- Backward: a | τ and c | τ implies (a*c) | τ when gcd(a,c) = 1
    intro ⟨ha, hc⟩
    exact hcoprime.mul_dvd_of_dvd_of_dvd ha hc

end FdrsFormal.Integration.Programs
