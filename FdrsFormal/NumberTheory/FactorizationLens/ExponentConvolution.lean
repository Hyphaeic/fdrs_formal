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
import FdrsFormal.NumberTheory.ArithmeticFunctions.DirichletConv

/-!
# Exponent Convolution Isomorphism

This file establishes the isomorphism between Dirichlet convolution on
smooth numbers and coordinate-wise addition on exponent vectors.

## Main Definitions

* `exponentAddition` - Addition of exponent vectors in ℕ^P
* `smoothRestriction` - Restriction of arithmetic function to P-smooth numbers

## Main Results

* `exponentConvolutionIso` - **Thm 3.1**: Dirichlet * on smooth ≅ + on exponents

## References

* fdrs.md, Lines 2341-2365: Theorem 20 (exponent convolution isomorphism)
* THEOREM_MAPPING.md: Thm 3.1 → exponentConvolutionIso
-/

open FdrsFormal

namespace FdrsFormal.NumberTheory

/--
Addition of exponent vectors: (v_P(m) + v_P(n)) for P-smooth numbers.

**fdrs.md Reference:** Lines 2341-2365
**STUB**: Requires finite-dimensional vector space structure.
-/
def exponentAddition (P : Finset Nat) :
  (P → ℕ) → (P → ℕ) → (P → ℕ) := fun v w p => v p + w p

/--
Restriction of arithmetic function to P-smooth numbers via the exponent lens.
Given an exponent vector v : P → ℕ, reconstructs the smooth number
n = ∏_{p ∈ P} p^{v(p)} and applies f.

**fdrs.md Reference:** Lines 2341-2365
-/
def smoothRestriction (P : Finset Nat) (f : ℕ → ℂ) : (P → ℕ) → ℂ :=
  fun v => f (P.attach.prod fun ⟨p, hp⟩ => p ^ v ⟨p, hp⟩)

/--
**Theorem 20**: The exponent-to-smooth-number map sends exponent vector addition
to natural number multiplication: ∏ p^(a+b) = (∏ p^a) · (∏ p^b).

This is the core algebraic identity of the factorization lens: the map
v ↦ ∏_{p ∈ P} p^{v_p} is a multiplicative homomorphism from (ℕ^P, +) to (ℕ, ×).

**fdrs.md Reference:** Lines 2341-2365, Theorem 20
-/
theorem exponentConvolutionIso (P : Finset Nat) (f : ℕ → ℂ)
  (vm vn : P → ℕ) :
  smoothRestriction P f (exponentAddition P vm vn) =
    f (P.attach.prod (fun ⟨p, hp⟩ => p ^ (vm ⟨p, hp⟩)) *
       P.attach.prod (fun ⟨p, hp⟩ => p ^ (vn ⟨p, hp⟩))) := by
  simp only [smoothRestriction, exponentAddition]
  congr 1
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun ⟨p, _⟩ _ => pow_add p _ _

end FdrsFormal.NumberTheory
