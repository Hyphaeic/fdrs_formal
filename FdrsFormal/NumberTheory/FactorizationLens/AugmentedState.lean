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
import FdrsFormal.NumberTheory.FactorizationLens.FiberDecomposition

/-!
# Augmented Factorization State

This file defines the augmented state space (u, e) combining the unit part
and exponent vector, which forms the complete factorization lens state.

## Main Definitions

* `AugmentedFactorizationState` - The product space (unit × exponent vector)
* `augmentedLens` - The projection n ↦ (u_P(n), v_P(n))

## Main Results

* `augmentedLens_injective` - The augmented lens is injective on positive naturals
* `markovProperty` - **Prop 5.2**: Markov property on the augmented state

## References

* fdrs.md, Lines 2402-2428: Def 5.1 and Prop 5.2 (augmented state Markov property)
* THEOREM_MAPPING.md: Def 5.1-Prop 5.2 → augmentedFactorizationState
-/

open FdrsFormal

namespace FdrsFormal.NumberTheory

open FactorizationLens

/--
The augmented factorization state (u, e) where:
- u is the unit part (coprime to all primes in P)
- e is the exponent vector in ℕ^P

**fdrs.md Reference:** Lines 2402-2428, Definition 45
-/
def AugmentedFactorizationState (P : Finset Nat) :=
  {u : ℕ // ∀ p ∈ P, ¬(p ∣ u)} × (P → ℕ)

/--
The augmented lens projection: n ↦ (u_P(n), v_P(n)).

Maps a positive natural number to its P-free part and P-valuation vector.

**fdrs.md Reference:** Lines 2402-2428
-/
def augmentedLens (P : Finset Nat) (hP : ∀ p ∈ P, Nat.Prime p) (n : ℕ) (hn : 0 < n) :
    AugmentedFactorizationState P :=
  (⟨freePart P hP n, fun p hp =>
    (hP p hp).coprime_iff_not_dvd.mp
      (Nat.coprime_comm.mp (freePart_coprime P hP n hn p hp))⟩,
   valuationVector P hP n)

/--
The augmented lens is injective on positive naturals: if two positive numbers
have the same P-free part and P-valuation vector, they are equal.

**fdrs.md Reference:** Lines 2402-2428

**Proof**: n = freePart(n) × smoothPart(n), and smoothPart is determined by
the valuation vector. So equal (freePart, valuationVector) implies equal n.
-/
theorem augmentedLens_injective (P : Finset Nat) (hP : ∀ p ∈ P, Nat.Prime p)
    (n₁ n₂ : ℕ) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (heq : augmentedLens P hP n₁ hn₁ = augmentedLens P hP n₂ hn₂) :
    n₁ = n₂ := by
  -- Extract components from the product equality
  have h_free : freePart P hP n₁ = freePart P hP n₂ :=
    congrArg Subtype.val (congrArg Prod.fst heq)
  have h_val : valuationVector P hP n₁ = valuationVector P hP n₂ :=
    congrArg Prod.snd heq
  -- The smooth parts are equal because they depend only on the valuation vector
  have h_smooth : smoothPart P hP n₁ = smoothPart P hP n₂ := by
    simp only [smoothPart]
    apply Finset.prod_congr rfl
    intro p hp; congr 1
    have := congrFun h_val ⟨p, hp⟩
    simp only [valuationVector] at this
    exact this
  -- n = freePart * smoothPart, so equal parts imply equal n
  calc n₁ = freePart P hP n₁ * smoothPart P hP n₁ :=
        factorization_unique P hP n₁ hn₁
    _ = freePart P hP n₂ * smoothPart P hP n₂ := by rw [h_free, h_smooth]
    _ = n₂ := (factorization_unique P hP n₂ hn₂).symm

/--
**Proposition 53**: Markov property on the augmented state space.

The augmented state (u_P(n), v_P(n)) determines the augmented state of n * d:
transitions depend only on the current state, not the full history.

**fdrs.md Reference:** Lines 2402-2428, Proposition 53

**Proof**: By injectivity of the augmented lens, the state uniquely determines n.
Therefore n * d (and hence its augmented state) depends only on the state and d.
-/
theorem markovProperty (P : Finset Nat) (hP : ∀ p ∈ P, Nat.Prime p)
    (d : ℕ) (hd : 0 < d) (state : AugmentedFactorizationState P) :
    ∃ (nextState : AugmentedFactorizationState P),
      ∀ n : ℕ, ∀ hn : 0 < n, augmentedLens P hP n hn = state →
        augmentedLens P hP (n * d) (Nat.mul_pos hn hd) = nextState := by
  by_cases h : ∃ (n₀ : ℕ) (hn₀ : 0 < n₀), augmentedLens P hP n₀ hn₀ = state
  · obtain ⟨n₀, hn₀, heq₀⟩ := h
    exact ⟨augmentedLens P hP (n₀ * d) (Nat.mul_pos hn₀ hd), fun n hn hstate => by
      have hinj := augmentedLens_injective P hP n n₀ hn hn₀ (hstate.trans heq₀.symm)
      subst hinj; rfl⟩
  · exact ⟨augmentedLens P hP d hd, fun n hn hstate => absurd ⟨n, hn, hstate⟩ h⟩

end FdrsFormal.NumberTheory
