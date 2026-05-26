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

# Dirichlet Convolution

Defines Dirichlet convolution (a * b)(n) = ∑_{d|n} a(d) b(n/d) and proves
it forms a commutative, associative, unital algebra.

## Mathematical Content (fdrs.md lines 1616-1629)

**Definition 42 (Dirichlet convolution)**:
For arithmetic functions a, b : ℕ≥1 → ℂ, define:
  (a * b)(n) := ∑_{d|n} a(d) · b(n/d)

**Theorem 14 (Dirichlet algebra)**:
(𝒜, *) is a commutative associative unital algebra with identity ε.

**Proof**:
- Closure: Divisor sums are finite
- Associativity: ((a*b)*c)(n) = ∑_{d|n} ∑_{e|n/d} a(d)b(e)c(n/de)
                               = ∑_{de|n} a(d)b(e)c(n/de) = (a*(b*c))(n)
- Commutativity: d ↔ n/d symmetry
- Identity: ε * a = a (only d=1 contributes)

## References

- fdrs.md, Phase 3 Fragment 1, Section 2 (lines 1616-1629)
- Mathlib: Nat.ArithmeticFunction has similar structures
-/

import FdrsFormal.NumberTheory.ArithmeticFunctions.Definition
import Mathlib.NumberTheory.ArithmeticFunction.Defs

namespace FdrsFormal.NumberTheory.ArithmeticFunctions

open FdrsFormal.NumberTheory.ArithmeticFunctions

/-!
## Type Conversion Infrastructure

We bridge between our custom ArithmeticFunction ({n : ℕ // 0 < n} → ℂ) and
mathlib's Nat.ArithmeticFunction ℂ (ZeroHom ℕ ℂ).
-/

/--
Convert our ArithmeticFunction to mathlib's.

Our type: {n : ℕ // 0 < n} → ℂ
Mathlib: ℕ → ℂ with f(0) = 0 (implemented as ZeroHom)
-/
noncomputable def toMathlib (f : FdrsFormal.NumberTheory.ArithmeticFunctions.ArithmeticFunction) :
    _root_.ArithmeticFunction ℂ where
  toFun n := if h : 0 < n then f ⟨n, h⟩ else 0
  map_zero' := by simp

/--
Convert mathlib's ArithmeticFunction to ours.

We restrict to positive naturals and use the zero-preserving property.
-/
noncomputable def fromMathlib (f : _root_.ArithmeticFunction ℂ) :
    FdrsFormal.NumberTheory.ArithmeticFunctions.ArithmeticFunction :=
  fun n => f n.val

/--
Extensionality lemma for ArithmeticFunction.
-/
@[ext]
theorem ArithmeticFunction.ext {f g : ArithmeticFunction}
    (h : ∀ n, f n = g n) : f = g :=
  funext h

/--
Round-trip property: fromMathlib ∘ toMathlib = id
-/
theorem fromMathlib_toMathlib (f : FdrsFormal.NumberTheory.ArithmeticFunctions.ArithmeticFunction) :
    fromMathlib (toMathlib f) = f := by
  ext n
  unfold fromMathlib toMathlib
  simp [n.property]

/--
Conversion preserves function values at positive integers.
-/
theorem toMathlib_apply {f : FdrsFormal.NumberTheory.ArithmeticFunctions.ArithmeticFunction}
    {n : ℕ} (hn : 0 < n) :
    toMathlib f n = f ⟨n, hn⟩ := by
  unfold toMathlib
  simp [hn]

/-!
## Dirichlet Convolution Definition
-/

/--
**Dirichlet convolution**: (a * b)(n) = ∑_{d|n} a(d) · b(n/d).

**fdrs.md Definition** (lines 1617-1618):
For a, b ∈ 𝒜 (arithmetic functions), the Dirichlet convolution is defined by
summing over all divisors of n.

**Implementation**: Convert to mathlib's ArithmeticFunction, use mathlib's
multiplication (which is Dirichlet convolution), convert back.
-/
noncomputable def dirichletConv (a b : ArithmeticFunction) : ArithmeticFunction :=
  fromMathlib (toMathlib a * toMathlib b)

-- Notation for Dirichlet convolution
local infixl:70 " ⋆ " => dirichletConv

/--
Dirichlet convolution preserves function values.
-/
theorem dirichletConv_apply {a b : FdrsFormal.NumberTheory.ArithmeticFunctions.ArithmeticFunction}
    {n : ℕ} (hn : 0 < n) :
    (a ⋆ b) ⟨n, hn⟩ = (toMathlib a * toMathlib b) n := by
  unfold dirichletConv fromMathlib
  rfl

/--
Converting to mathlib and back is identity.
-/
theorem toMathlib_fromMathlib_mul (a b : FdrsFormal.NumberTheory.ArithmeticFunctions.ArithmeticFunction) :
    toMathlib (fromMathlib (toMathlib a * toMathlib b)) = toMathlib a * toMathlib b := by
  ext n
  unfold toMathlib fromMathlib
  by_cases h : 0 < n
  · simp [h]
  · have : n = 0 := Nat.eq_zero_of_not_pos h
    simp [this]

/-!
## Dirichlet Algebra Structure
-/

/--
**Theorem 14(a)**: Dirichlet convolution is commutative.

**Proof**: Uses mathlib's `mul_comm` for Nat.ArithmeticFunction, which has a
CommSemiring instance.
-/
theorem dirichletConv_comm (a b : FdrsFormal.NumberTheory.ArithmeticFunctions.ArithmeticFunction) :
    a ⋆ b = b ⋆ a := by
  ext n
  unfold dirichletConv fromMathlib
  congr 1
  exact mul_comm (toMathlib a) (toMathlib b)

/--
**Theorem 14(b)**: Dirichlet convolution is associative.

**Proof**: Uses mathlib's `mul_assoc` for Nat.ArithmeticFunction.
-/
theorem dirichletConv_assoc (a b c : FdrsFormal.NumberTheory.ArithmeticFunctions.ArithmeticFunction) :
    (a ⋆ b) ⋆ c = a ⋆ (b ⋆ c) := by
  unfold dirichletConv
  rw [toMathlib_fromMathlib_mul, toMathlib_fromMathlib_mul]
  congr 1
  exact mul_assoc (toMathlib a) (toMathlib b) (toMathlib c)

/--
Helper lemma: Our ε corresponds to mathlib's 1.

ε is defined as: ε(1) = 1, ε(n) = 0 for n > 1
Mathlib's 1 is: 1(1) = 1, 1(n) = 0 for n ≠ 1

**Proof**: Case analysis on n.
-/
theorem toMathlib_epsilon : toMathlib ε = 1 := by
  ext n
  unfold toMathlib epsilon
  rw [_root_.ArithmeticFunction.one_apply]
  by_cases h0 : 0 < n
  · -- Case: n > 0
    simp [h0]
  · -- Case: n = 0
    have h1 : ¬n = 1 := by
      intro heq
      rw [heq] at h0
      exact h0 (by norm_num : 0 < 1)
    simp [h0, h1]

/--
**Theorem 14(c)**: ε is the identity for Dirichlet convolution (left).

**Proof**: Uses mathlib's `one_mul` and the fact that toMathlib(ε) = 1.
-/
theorem dirichletConv_identity_left (a : FdrsFormal.NumberTheory.ArithmeticFunctions.ArithmeticFunction) :
    ε ⋆ a = a := by
  ext n
  unfold dirichletConv fromMathlib
  rw [toMathlib_epsilon, one_mul]
  simp [toMathlib, n.property]

/--
**Theorem 14(c)**: ε is the identity for Dirichlet convolution (right).

**Proof**: Follows from commutativity and left identity.
-/
theorem dirichletConv_identity_right (a : FdrsFormal.NumberTheory.ArithmeticFunctions.ArithmeticFunction) :
    a ⋆ ε = a := by
  rw [dirichletConv_comm, dirichletConv_identity_left]

/--
The Dirichlet algebra is a commutative monoid.
-/
noncomputable instance : CommMonoid ArithmeticFunction where
  mul := dirichletConv
  mul_assoc := dirichletConv_assoc
  one := ε
  one_mul := dirichletConv_identity_left
  mul_one := dirichletConv_identity_right
  mul_comm := dirichletConv_comm
end FdrsFormal.NumberTheory.ArithmeticFunctions
