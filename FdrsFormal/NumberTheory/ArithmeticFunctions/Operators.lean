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

# Arithmetic Operators (Dirichlet Transform, Multiplication, Character Twist)

Defines the operator-algebraic layer for arithmetic functions:
- T_a (Dirichlet transform): convolution with a fixed function
- M_g (multiplication operator): pointwise multiplication
- M_χ (character twist): pointwise multiplication by a Dirichlet character

## Mathematical Content (fdrs.md lines 1690-1737)

**Definition 44 (Dirichlet transform)**:
For an arithmetic function a, the Dirichlet transform T_a acts on functions via:
  (T_a f)(n) = ∑_{d|n} a(d) f(n/d) = (a * f)(n)

**Proposition 47**: T_a ∘ T_b = T_{a*b} (Dirichlet composition)
**Corollary 9**: T_ε = id (identity transform)
**Corollary 10**: T_μ ∘ T_𝟙 = id (Möbius inversion)

**Theorem 20**: M_χ T_a = T_{a·χ} M_χ (twist–transform covariance)

## References

- fdrs.md, Phase 3 Fragment 1, Section 3 (lines 1690-1737)
- fdrs.md, Phase 3 Fragment 3, Section 3 (lines 2156-2175)
- THEOREM_MAPPING.md, NumberTheory/ArithmeticFunctions section
-/

import FdrsFormal.NumberTheory.ArithmeticFunctions.DirichletConv
import FdrsFormal.NumberTheory.ArithmeticFunctions.MobiusInversion

namespace FdrsFormal.NumberTheory.ArithmeticFunctions

open FdrsFormal.NumberTheory.ArithmeticFunctions

/-!
## Dirichlet Transform

The operator T_a f := a ⋆ f (Dirichlet convolution with a fixed function a).
-/

/--
**Definition 44**: The Dirichlet transform operator T_a.

(T_a f)(n) = ∑_{d|n} a(d) f(n/d) = (a * f)(n)
-/
noncomputable def dirichletTransform (a : ArithmeticFunction) : ArithmeticFunction → ArithmeticFunction :=
  fun f => dirichletConv a f

/--
**Proposition 47**: Dirichlet transforms compose via convolution.

T_a ∘ T_b = T_{a*b}

This is the operator-algebraic form of associativity of Dirichlet convolution.
-/
theorem dirichletTransform_comp (a b : ArithmeticFunction) (f : ArithmeticFunction) :
    dirichletTransform a (dirichletTransform b f) = dirichletTransform (dirichletConv a b) f := by
  unfold dirichletTransform
  exact (dirichletConv_assoc a b f).symm

/--
**Corollary 9**: T_ε = id (the identity transform).
-/
theorem dirichletTransform_identity (f : ArithmeticFunction) :
    dirichletTransform ε f = f := by
  unfold dirichletTransform
  exact dirichletConv_identity_left f

/--
**Corollary 10**: T_μ ∘ T_𝟙 = id (Möbius inversion at the operator level).

Proof: T_μ(T_𝟙 f) = T_{μ*𝟙} f = T_ε f = f, using μ * 𝟙 = ε.
-/
theorem dirichletTransform_moebius_one (f : ArithmeticFunction) :
    dirichletTransform moebius (dirichletTransform constantOne f) = f := by
  rw [dirichletTransform_comp, moebius_mul_one, dirichletTransform_identity]

/-!
## Multiplication Operator

The pointwise multiplication operator M_g.
-/

/--
Multiplication operator: (M_g f)(n) = g(n) · f(n).
-/
noncomputable def multiplicationOp (g : ArithmeticFunction) : ArithmeticFunction → ArithmeticFunction :=
  fun f n => g n * f n

/--
Multiplication operators compose pointwise.

M_g ∘ M_h = M_{g·h}
-/
theorem multiplicationOp_comp (g h : ArithmeticFunction) (f : ArithmeticFunction) :
    multiplicationOp g (multiplicationOp h f) =
    multiplicationOp (fun n => g n * h n) f := by
  ext n
  simp only [multiplicationOp, mul_assoc]

/--
M_ε restricted to n=1 is the identity; in general M_ε zeros out n > 1.
-/
theorem multiplicationOp_epsilon (f : ArithmeticFunction) (n : {n : ℕ // 0 < n}) :
    multiplicationOp ε f n = if n.val = 1 then f n else 0 := by
  simp only [multiplicationOp, epsilon]
  split_ifs with h
  · simp
  · simp

/--
M_𝟙 is the identity operator.
-/
theorem multiplicationOp_constantOne (f : ArithmeticFunction) :
    multiplicationOp constantOne f = f := by
  ext n
  simp only [multiplicationOp, constantOne, one_mul]

/-!
## Character Twist Operator

M_χ: pointwise multiplication by a Dirichlet character.
-/

-- Note: charMultiplyOp is defined using DirichletChar.apply in Characters/TwistTransform.lean
-- Here we provide the abstract version for arithmetic functions.

/--
Pointwise product of two arithmetic functions.
-/
noncomputable def pointwiseMul (a b : ArithmeticFunction) : ArithmeticFunction :=
  fun n => a n * b n

/--
Pointwise multiplication is commutative.
-/
theorem pointwiseMul_comm (a b : ArithmeticFunction) :
    pointwiseMul a b = pointwiseMul b a := by
  ext n; simp only [pointwiseMul, mul_comm]

/--
Pointwise multiplication is associative.
-/
theorem pointwiseMul_assoc (a b c : ArithmeticFunction) :
    pointwiseMul (pointwiseMul a b) c = pointwiseMul a (pointwiseMul b c) := by
  ext n; simp only [pointwiseMul, mul_assoc]

/--
M_g distributes over T_a: M_g(T_a f) rewrites as a twisted Dirichlet sum.

More precisely, for completely multiplicative g:
  (M_g ∘ T_a) f (n) = g(n) · ∑_{d|n} a(d) f(n/d)
                     = ∑_{d|n} a(d) g(d) · g(n/d) f(n/d)  [using g(n)=g(d)g(n/d)]
                     = (T_{a·g} ∘ M_g) f (n)

This is the abstract form of twist-transform covariance (Theorem 20).
-/
theorem multiplicationOp_dirichletTransform_comm_of_multiplicative
    (g a : ArithmeticFunction) (f : ArithmeticFunction)
    (hg_mult : ∀ (m n : {n : ℕ // 0 < n}), g ⟨m.val * n.val, Nat.mul_pos m.property n.property⟩ = g m * g n) :
    multiplicationOp g (dirichletTransform a f) =
    dirichletTransform (pointwiseMul a g) (multiplicationOp g f) := by
  ext n
  simp only [multiplicationOp, dirichletTransform, dirichletConv, fromMathlib,
             _root_.ArithmeticFunction.mul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨hprod, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hx
  have hd0 : 0 < x.1 := by
    by_contra h; push_neg at h
    exact hn0 (by rw [← hprod, Nat.le_zero.mp h, zero_mul])
  have he0 : 0 < x.2 := by
    by_contra h; push_neg at h
    exact hn0 (by rw [← hprod, Nat.le_zero.mp h, mul_zero])
  simp only [toMathlib_apply hd0, toMathlib_apply he0, pointwiseMul, multiplicationOp]
  have hmult : g n = g ⟨x.1, hd0⟩ * g ⟨x.2, he0⟩ := by
    have := hg_mult ⟨x.1, hd0⟩ ⟨x.2, he0⟩
    rwa [show (⟨x.1 * x.2, Nat.mul_pos hd0 he0⟩ : {n : ℕ // 0 < n}) = n from
      Subtype.ext hprod] at this
  rw [hmult]
  ring

end FdrsFormal.NumberTheory.ArithmeticFunctions
