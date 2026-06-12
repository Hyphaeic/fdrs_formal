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

# Arithmetic Functions

Basic theory of arithmetic functions f : ℕ≥1 → ℂ.

## Mathematical Content (fdrs.md lines 1612-1648)

**Definition**: An arithmetic function is a function f : ℕ≥1 → ℂ.

Key examples:
- Identity ε: ε(1) = 1, ε(n) = 0 for n > 1
- Constant 1: 𝟙(n) ≡ 1
- Möbius function μ
- Euler totient φ
- Divisor function τ

## References

- fdrs.md, Phase 3 Fragment 1, Section 2.1 (lines 1612-1620)
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Squarefree

namespace FdrsFormal.NumberTheory.ArithmeticFunctions

/-!
## Basic Definitions
-/

/-- An arithmetic function is a function from positive integers to complex numbers. -/
def ArithmeticFunction := {n : ℕ // 0 < n} → ℂ

/-- Coercion from ArithmeticFunction to function on ℕ (extending by 0 at n=0). -/
def ArithmeticFunction.toFun (a : ArithmeticFunction) : ℕ → ℂ
  | 0 => 0
  | n + 1 => a ⟨n + 1, Nat.succ_pos n⟩

instance : CoeFun ArithmeticFunction (fun _ => {n : ℕ // 0 < n} → ℂ) where
  coe := id

/-!
## Standard Arithmetic Functions
-/

/--
The identity function ε in the Dirichlet algebra.

ε(1) = 1, ε(n) = 0 for n > 1.

This is the identity element for Dirichlet convolution.
-/
def epsilon : ArithmeticFunction :=
  fun n => if n.val = 1 then 1 else 0

notation "ε" => epsilon

/--
The constant function 𝟙(n) ≡ 1.
-/
def constantOne : ArithmeticFunction :=
  fun _ => 1

notation "𝟙" => constantOne

/--
The Möbius function μ : ℕ≥1 → {-1, 0, 1}.

**Definition** (fdrs.md lines 1655-1659):
- μ(1) = 1
- μ(n) = (-1)^r if n is a product of r distinct primes
- μ(n) = 0 if p² | n for some prime p

**Implementation**: We use mathlib's `ArithmeticFunction.moebius` and convert
from ℤ to ℂ.
-/
def moebius : ArithmeticFunction :=
  fun n => (ArithmeticFunction.moebius n.val : ℂ)

notation "μ" => moebius

/--
**Theorem**: μ(1) = 1

**Proof**: Direct from mathlib's `ArithmeticFunction.moebius_apply_one`.
-/
theorem moebius_one : μ ⟨1, Nat.one_pos⟩ = 1 := by
  unfold moebius
  simp only [ArithmeticFunction.moebius_apply_one]
  norm_cast

/--
The squarefree indicator μ² : ℕ≥1 → {0, 1}.

μ²(n) = 1 iff n is squarefree (no prime appears with exponent ≥ 2).

**Implementation**: We use the fact that μ²(n) = |μ(n)|² for the Möbius function.
-/
def squarefreeIndicator : ArithmeticFunction :=
  fun n => if Squarefree n.val then 1 else 0

notation "μ²" => squarefreeIndicator

/--
**Theorem**: μ²(1) = 1 (1 is squarefree)

**Proof**: 1 is squarefree by mathlib's `squarefree_one`.
-/
theorem squarefreeIndicator_one : μ² ⟨1, Nat.one_pos⟩ = 1 := by
  unfold squarefreeIndicator
  simp only [ite_eq_left_iff]
  intro h
  -- 1 is squarefree
  exfalso
  apply h
  -- Show Squarefree (1 : ℕ)
  exact squarefree_one

end FdrsFormal.NumberTheory.ArithmeticFunctions
