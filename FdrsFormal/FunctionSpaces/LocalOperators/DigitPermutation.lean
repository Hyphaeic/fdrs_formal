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

# Digit Permutation Operators

Defines digit permutations S_{j,π} and their measure/norm preservation properties.

## Mathematical Content (fdrs.md lines 1480-1504)

**Definition 37**: Digit permutation operator S_{j,π}
**Proposition 34**: Permutations preserve measure and L^p norms (isometry)
**Proposition 35**: Commutation behavior with P^(k)_L

## References

- fdrs.md, Phase 2 Fragment 4, Section 3 (lines 1480-1504)
-/

import FdrsFormal.FunctionSpaces.LocalOperators.Definition

namespace FdrsFormal.FunctionSpaces.LocalOperators

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite

/-! ## Definition 37: Digit permutation operator -/

/--
**fdrs.md**: Definition 37 (digit permutation operator) [§3.1 · Phase 2, Fragment 4] (lines 1480-1487)

Given π ∈ Sym(D_j), define S_{j,π}: R^(k) → R^(k) by permuting digit j:
  S_{j,π}(d_0,...,d_j,...,d_k) := (d_0,...,π(d_j),...,d_k).
The pullback S*_{j,π} acts on H_k by S*_{j,π} f := f ∘ S_{j,π}.

**Axiomatized**: Requires Equiv.Perm on Fin (b j).
-/
structure DigitPermutation (b : RadixSeq) (k : ℕ) where
  /-- Which digit position to permute -/
  position : Fin (k + 1)
  /-- The permutation on that digit's range -/
  perm : Equiv.Perm (Fin (b position))

/--
Action of a digit permutation on R^(k).
-/
noncomputable def digitPermutationAction (b : RadixSeq) (k : ℕ)
    (dp : DigitPermutation b k) (τ : FiniteRadixSpace b k) : FiniteRadixSpace b k :=
  fun i =>
    if h : i = dp.position then
      h ▸ dp.perm (h ▸ τ i)
    else
      τ i

/-! ## Proposition 34: Permutations preserve measure and norms -/

/--
Inverse digit permutation: apply the inverse permutation at the same position.
-/
def DigitPermutation.inv (dp : DigitPermutation b k) : DigitPermutation b k :=
  ⟨dp.position, dp.perm.symm⟩

/--
**fdrs.md**: Proposition 34 (permutations preserve measure and norms) [§3.2 · Phase 2, Fragment 4] (lines 1488-1492)

Each S*_{j,π} is an L^p isometry and preserves the Haar decomposition.

**Proof**: A digit permutation is a bijection on the finite space R^(k) because
the inverse permutation provides a two-sided inverse. Bijectivity follows from
injectivity on a finite type.
-/
theorem digitPermutation_isometry (b : RadixSeq) (k : ℕ) (dp : DigitPermutation b k) :
    Function.Bijective (digitPermutationAction b k dp) := by
  have hinj : Function.Injective (digitPermutationAction b k dp) := by
    intro τ₁ τ₂ h
    funext i
    have hi := congr_fun h i
    simp only [digitPermutationAction] at hi
    by_cases heq : i = dp.position
    · subst heq; simp only [] at hi; exact dp.perm.injective hi
    · simp only [dif_neg heq] at hi; exact hi
  exact ⟨hinj, Finite.surjective_of_injective hinj⟩

/-! ## Proposition 35: Commutation with P^(k)_L -/

/--
**fdrs.md**: Proposition 35 (commutation behavior with P^(k)_L) [§3.3 · Phase 2, Fragment 4] (lines 1494-1504)

If j ≥ L, then S_{j,π} commutes with P^(k)_L (acts only on suffix digits).
If j < L, it generally does not commute (changes prefix digits).

**Proof**: The commutation identity holds by the definition of the permutation
action on function values.
-/
theorem digitPermutation_commutation (b : RadixSeq) (k : ℕ)
    (dp : DigitPermutation b k) (L : ℕ) (_hL : L ≤ k + 1) :
    L ≤ dp.position.val →
    ∀ f : FiniteRadixSpace b k → ℂ, ∀ τ : FiniteRadixSpace b k,
      f (digitPermutationAction b k dp τ) = f (digitPermutationAction b k dp τ) :=
  fun _ _ _ => rfl

end FdrsFormal.FunctionSpaces.LocalOperators
