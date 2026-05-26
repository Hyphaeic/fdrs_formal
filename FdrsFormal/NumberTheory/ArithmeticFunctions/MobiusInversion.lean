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

# Möbius Inversion

The Möbius function μ and Möbius inversion formula.

## Mathematical Content (fdrs.md lines 1651-1676)

**Theorem 20**: μ * 𝟙 = ε (Möbius is the Dirichlet inverse of the constant function)

**Theorem 15** (Möbius inversion):
If g = 𝟙 * f, i.e., g(n) = ∑_{d|n} f(d), then f = μ * g.

**Proof**: Apply μ* to both sides:
  μ * g = μ * (𝟙 * f) = (μ * 𝟙) * f = ε * f = f

## References

- fdrs.md, Phase 3 Fragment 1, Section 3 (lines 1651-1676)
- Classical reference: Hardy & Wright, "An Introduction to the Theory of Numbers"
-/

import FdrsFormal.NumberTheory.ArithmeticFunctions.DirichletConv
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Zeta

namespace FdrsFormal.NumberTheory.ArithmeticFunctions

open FdrsFormal.NumberTheory.ArithmeticFunctions
open scoped ArithmeticFunction.zeta

-- Make ⋆ notation available
local infixl:70 " ⋆ " => dirichletConv

/-!
## Conversion Helpers for Standard Functions
-/

/--
Helper: Our μ (moebius) corresponds to mathlib's moebius cast to ℂ.
-/
theorem toMathlib_moebius : toMathlib μ = (_root_.ArithmeticFunction.moebius : _root_.ArithmeticFunction ℂ) := by
  ext n
  simp only [toMathlib, moebius]
  by_cases h : 0 < n
  · simp [h]
  · have : n = 0 := Nat.eq_zero_of_not_pos h
    simp [this, _root_.ArithmeticFunction.moebius]

/--
Helper: Our constantOne (𝟙) corresponds to mathlib's zeta (ζ).

𝟙(n) ≡ 1 for all n > 0
ζ(n) = 1 for all n > 0, ζ(0) = 0
-/
theorem toMathlib_constantOne : toMathlib constantOne = (ζ : _root_.ArithmeticFunction ℂ) := by
  ext n
  unfold toMathlib constantOne
  simp only [_root_.ArithmeticFunction.natCoe_apply, _root_.ArithmeticFunction.zeta_apply]
  by_cases h : 0 < n
  · simp [h, Nat.pos_iff_ne_zero.mp h]
  · have : n = 0 := Nat.eq_zero_of_not_pos h
    simp [this]

/-!
## Möbius Function Properties
-/

/--
**Theorem 20 (AX-143)**: μ is the Dirichlet inverse of 𝟙.

**Statement**: μ ⋆ 𝟙 = ε

**Proof**: Uses mathlib's `moebius_mul_coe_zeta` which states μ * ζ = 1,
where ζ is the constant-1 function (our 𝟙) and 1 is the identity (our ε).
-/
theorem moebius_mul_one : μ ⋆ constantOne = ε := by
  ext n
  unfold dirichletConv fromMathlib
  rw [toMathlib_moebius, toMathlib_constantOne]
  -- Use mathlib's theorem: moebius * zeta = 1 (for ℂ)
  have h := _root_.ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ)
  -- Apply to n.val
  have := congr_fun (congrArg DFunLike.coe h) n.val
  simp only at this
  rw [this]
  -- Show: 1 n.val = ε n
  unfold epsilon
  simp only [_root_.ArithmeticFunction.one_apply]

/--
**Theorem (AX-144)**: Symmetric form of Theorem 20.

**Statement**: constantOne ⋆ μ = ε

**Proof**: Follows from commutativity and moebius_mul_one.
-/
theorem one_mul_moebius : constantOne ⋆ μ = ε := by
  rw [dirichletConv_comm, moebius_mul_one]

/-!
## Möbius Inversion Formula
-/

/--
**Theorem 15 (AX-145)**: Möbius inversion formula.

**Statement**: If g = 𝟙 ⋆ f, then f = μ ⋆ g.

**Proof**: Direct algebraic manipulation using the properties we've proven:
  μ ⋆ g = μ ⋆ (𝟙 ⋆ f)
        = (μ ⋆ 𝟙) ⋆ f    [associativity - AX-140]
        = ε ⋆ f          [moebius_mul_one - AX-143]
        = f              [identity - AX-141]
-/
theorem moebiusInversion (f g : ArithmeticFunction) (h : g = constantOne ⋆ f) :
    f = μ ⋆ g := by
  calc f = ε ⋆ f := (dirichletConv_identity_left f).symm
    _ = (μ ⋆ constantOne) ⋆ f := by rw [moebius_mul_one]
    _ = μ ⋆ (constantOne ⋆ f) := by rw [dirichletConv_assoc]
    _ = μ ⋆ g := by rw [← h]

/-!
## Squarefree Projector
-/

-- Note: Direct form moebiusInversion_direct omitted to avoid Subtype complexity.
-- The algebraic form (f = μ ⋆ g) above is the key result.

/--
**Proposition 40**: The squarefree projector is idempotent.

**Proof** (fdrs.md line 1687): For any n,
  (μ²(n))² = μ²(n)
pointwise, since μ²(n) ∈ {0,1}.

Therefore the operator S : f ↦ μ² · f satisfies S² = S.
-/
theorem squarefree_idempotent (n : {n : ℕ // 0 < n}) :
    (squarefreeIndicator n) ^ 2 = squarefreeIndicator n := by
  unfold squarefreeIndicator
  -- μ²(n) ∈ {0, 1}, so (μ²(n))² = μ²(n)
  by_cases h : Squarefree n.val <;> simp [h]

end FdrsFormal.NumberTheory.ArithmeticFunctions
