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
import FdrsFormal.NumberTheory.ArithmeticFunctions.MobiusInversion
import FdrsFormal.NumberTheory.ArithmeticFunctions.Operators
import FdrsFormal.FunctionSpaces.Basic

/-!
# Tensor Pullback of Dirichlet Algebra

This file defines the pullback of Dirichlet convolution to mixed-radix
tensor spaces via the shifted arithmetic index nat_k, and proves the
tensor Dirichlet algebra composition law (Theorem 23) and tensor Möbius
inversion (Corollary 10).

## Main Definitions

* `natK` - The shifted arithmetic index nat_k(τ) = dec_k(τ) + 1
* `liftToArith` - Lifts a tensor function to an arithmetic function
* `tensorTransform` - The tensor Dirichlet transform T_a^{(k)}

## Main Results

-- fdrs.md lines 1710-1737, Theorem 23 and Corollary 10
* `tensorDirichletAlgebra` - **Theorem 23**: T_a^{(k)} ∘ T_b^{(k)} = T_{a*b}^{(k)}
* `tensorMobiusInversion` - **Corollary 10**: G = T_1^{(k)}F ⟹ F = T_μ^{(k)}G

## References

* fdrs.md, Lines 1710-1737: Theorem 23 and Corollary 10
-/

open FdrsFormal.Core.Finite FdrsFormal.Core.Primitives
open FdrsFormal.NumberTheory.ArithmeticFunctions

namespace FdrsFormal.NumberTheory

variable {b : RadixSeq} {k : ℕ}

/-! ## Shifted Arithmetic Index -/

/-- The shifted arithmetic index nat_k(τ) = dec_k(τ) + 1 ∈ {1,...,N}. -/
def natK (b : RadixSeq) (k : ℕ) (τ : FiniteRadixSpace b k) : {n : ℕ // 0 < n} :=
  ⟨decodeFinite b k τ + 1, Nat.succ_pos _⟩

/-- nat_k(τ) ≤ B_{k+1}. -/
theorem natK_le (τ : FiniteRadixSpace b k) :
    (natK b k τ).val ≤ placeValue b (k + 1) :=
  decodeFinite_lt k τ

/-- Round-trip: nat_k(enc_k(n-1)) = n for n ∈ {1,...,N}. -/
theorem natK_encodeFinite (n : {n : ℕ // 0 < n}) (hn : n.val ≤ placeValue b (k + 1)) :
    natK b k (encodeFinite b k ⟨n.val - 1, by omega⟩) = n := by
  ext
  simp only [natK]
  rw [decodeFinite_encodeFinite, Fin.val_mk]
  exact Nat.sub_add_cancel n.property

/-! ## Lifting and Transform Definitions -/

/-- Lift a tensor function to an arithmetic function via nat_k.
    For n ∈ {1,...,N}: f(n) = F(enc_k(n-1)). For n > N: f(n) = 0. -/
noncomputable def liftToArith (b : RadixSeq) (k : ℕ)
    (F : FiniteRadixSpace b k → ℂ) : ArithmeticFunction :=
  fun n => if h : n.val ≤ placeValue b (k + 1) then
    F (encodeFinite b k ⟨n.val - 1, by omega⟩)
  else 0

/-- Evaluating liftToArith at nat_k(τ) recovers F(τ). -/
theorem liftToArith_natK (F : FiniteRadixSpace b k → ℂ) (τ : FiniteRadixSpace b k) :
    liftToArith b k F (natK b k τ) = F τ := by
  unfold liftToArith
  rw [dif_pos (natK_le τ)]
  congr 1
  show encodeFinite b k ⟨(natK b k τ).val - 1, _⟩ = τ
  have : (natK b k τ).val - 1 = decodeFinite b k τ := by simp [natK]
  exact encodeFinite_decodeFinite k τ

/-- The tensor Dirichlet transform T_a^{(k)}.
    (T_a^{(k)} F)(τ) = (T_a (liftToArith F))(nat_k(τ)) -/
noncomputable def tensorTransform (b : RadixSeq) (k : ℕ) (a : ArithmeticFunction)
    (F : FiniteRadixSpace b k → ℂ) : FiniteRadixSpace b k → ℂ :=
  fun τ => dirichletTransform a (liftToArith b k F) (natK b k τ)

/-! ## Key Lemmas -/

/-- T_ε^{(k)} = id: the identity transform on tensors. -/
theorem tensorTransform_identity (F : FiniteRadixSpace b k → ℂ)
    (τ : FiniteRadixSpace b k) :
    tensorTransform b k ε F τ = F τ := by
  unfold tensorTransform
  rw [dirichletTransform_identity]
  exact liftToArith_natK F τ

/-- Dirichlet convolution locality: if f and g agree on {1,...,m},
    then (a ⋆ f)(m) = (a ⋆ g)(m). -/
theorem dirichletConv_congr_right (a f g : ArithmeticFunction)
    (m : {n : ℕ // 0 < n})
    (h : ∀ n : {n : ℕ // 0 < n}, n.val ≤ m.val → f n = g n) :
    dirichletConv a f m = dirichletConv a g m := by
  unfold dirichletConv fromMathlib
  simp only [_root_.ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨hprod, hne⟩ := Nat.mem_divisorsAntidiagonal.mp hx
  have hd_pos : 0 < x.1 := by
    by_contra h0; push_neg at h0
    exact hne (by rw [← hprod, Nat.le_zero.mp h0, zero_mul])
  have he_pos : 0 < x.2 := by
    by_contra h0; push_neg at h0
    exact hne (by rw [← hprod, Nat.le_zero.mp h0, mul_zero])
  have he_le : x.2 ≤ m.val := hprod ▸ Nat.le_mul_of_pos_left _ hd_pos
  congr 1
  rw [toMathlib_apply he_pos, toMathlib_apply he_pos]
  exact h ⟨x.2, he_pos⟩ he_le

/-- liftToArith(T_c F) agrees with T_c(liftToArith F) on {1,...,N}. -/
theorem liftToArith_tensorTransform (c : ArithmeticFunction)
    (F : FiniteRadixSpace b k → ℂ) (n : {n : ℕ // 0 < n})
    (hn : n.val ≤ placeValue b (k + 1)) :
    liftToArith b k (tensorTransform b k c F) n =
    dirichletTransform c (liftToArith b k F) n := by
  unfold liftToArith
  rw [dif_pos hn]
  unfold tensorTransform
  congr 1
  exact natK_encodeFinite n hn

/-! ## Main Results -/

/--
**Theorem 23**: Tensor Dirichlet algebra respects composition.

T_a^{(k)} ∘ T_b^{(k)} = T_{a*b}^{(k)}

fdrs.md lines 1710-1723, Theorem 23

**Proof**: Transport Dirichlet composition through the bijection nat_k.
-/
theorem tensorDirichletAlgebra (b : RadixSeq) (k : ℕ)
    (a c : ArithmeticFunction) (F : FiniteRadixSpace b k → ℂ)
    (τ : FiniteRadixSpace b k) :
    tensorTransform b k a (tensorTransform b k c F) τ =
    tensorTransform b k (dirichletConv a c) F τ := by
  unfold tensorTransform
  -- LHS: T_a(liftToArith(T_c F))(natK τ)
  -- RHS: T_{a⋆c}(liftToArith F)(natK τ)
  -- Step 1: liftToArith(T_c F) agrees with T_c(liftToArith F) on {1,...,N}
  -- Step 2: By Dirichlet locality, T_a applied to either gives the same at natK τ
  -- Step 3: T_a(T_c(liftToArith F)) = T_{a⋆c}(liftToArith F) by composition
  have h_agree : ∀ n : {n : ℕ // 0 < n}, n.val ≤ (natK b k τ).val →
      liftToArith b k (tensorTransform b k c F) n =
      dirichletTransform c (liftToArith b k F) n := by
    intro n hn_le
    exact liftToArith_tensorTransform c F n (le_trans hn_le (natK_le τ))
  calc dirichletTransform a (liftToArith b k (tensorTransform b k c F)) (natK b k τ)
      = dirichletConv a (liftToArith b k (tensorTransform b k c F)) (natK b k τ) := rfl
    _ = dirichletConv a (dirichletTransform c (liftToArith b k F)) (natK b k τ) :=
        dirichletConv_congr_right a _ _ (natK b k τ) h_agree
    _ = dirichletTransform a (dirichletTransform c (liftToArith b k F)) (natK b k τ) := rfl
    _ = dirichletTransform (dirichletConv a c) (liftToArith b k F) (natK b k τ) := by
        rw [dirichletTransform_comp]

/--
**Corollary 10**: Tensor Möbius inversion.

If G = T_1^{(k)} F, then F = T_μ^{(k)} G.

fdrs.md lines 1735-1737, Corollary 10

**Proof**: Transport Theorem 15 (Möbius inversion) through nat_k.
  T_μ^{(k)} G = T_μ^{(k)}(T_1^{(k)} F) = T_{μ⋆1}^{(k)} F = T_ε^{(k)} F = F.
-/
theorem tensorMobiusInversion (b : RadixSeq) (k : ℕ)
    (F G : FiniteRadixSpace b k → ℂ)
    (h : G = tensorTransform b k constantOne F) :
    F = tensorTransform b k moebius G := by
  subst h
  ext τ
  rw [tensorDirichletAlgebra, moebius_mul_one, tensorTransform_identity]

end FdrsFormal.NumberTheory
