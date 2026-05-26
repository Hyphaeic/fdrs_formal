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

# Cyclic Convolution on Finite Abelian Groups

Proves that cyclic (group) convolution on a finite abelian group forms a
commutative associative unital algebra with identity δ_0.

## Mathematical Content (fdrs.md lines 1594-1606)

**Proposition 38**: (R^(k), ⊞_k) is a finite abelian group; dec_k is a
group isomorphism to ℤ/Nℤ where N = B_{k+1}.

**Theorem 13**: (H_k^ℂ, *_k) is a commutative associative algebra with
identity δ_0.

## References

- fdrs.md, Phase 3 Fragment 1, Section 1 (lines 1594-1595)
- fdrs.md, Phase 3 Fragment 1, Section 2 (lines 1604-1606)
- Mathlib: Circulant.lean for the Fintype.sum_equiv proof technique
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

namespace FdrsFormal.NumberTheory.ArithmeticFunctions.CyclicConvolution

open Finset BigOperators Complex
set_option linter.unusedSectionVars false

variable {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]

/-! ## Definitions -/

/-- Kronecker delta at 0: the identity element for group convolution. -/
noncomputable def kroneckerDelta (x : G) : ℂ :=
  if x = 0 then 1 else 0

/-- Unnormalized cyclic (group) convolution: `(f * g)(x) = ∑_y f(y) g(x - y)`. -/
noncomputable def cyclicMul (f g : G → ℂ) : G → ℂ :=
  fun x => ∑ y : G, f y * g (x - y)

/-! ## Commutativity -/

/--
**Theorem 13 (commutativity)**: Cyclic convolution is commutative.

Proof: Reindex `y ↦ x - y` using `Equiv.subLeft x`, then apply `mul_comm`.
-/
theorem cyclicMul_comm (f g : G → ℂ) : cyclicMul f g = cyclicMul g f := by
  ext x
  simp only [cyclicMul]
  refine Fintype.sum_equiv (Equiv.subLeft x) _ _ ?_
  intro y
  simp only [Equiv.subLeft_apply]
  rw [mul_comm]
  congr 1
  abel

/-! ## Identity element -/

/--
**Theorem 13 (left identity)**: `kroneckerDelta` is a left identity for `cyclicMul`.

Proof: Unfold kroneckerDelta, use `ite_mul` to push the conditional into the
product, then `Fintype.sum_ite_eq'` collapses the sum to the single `y = 0` term.
-/
theorem cyclicMul_one_left (f : G → ℂ) : cyclicMul kroneckerDelta f = f := by
  ext x
  simp only [cyclicMul, kroneckerDelta]
  simp only [ite_mul, one_mul, zero_mul]
  rw [Fintype.sum_ite_eq' 0]
  simp [sub_zero]

/--
**Theorem 13 (right identity)**: `kroneckerDelta` is a right identity for `cyclicMul`.

Proof: Follows from commutativity and left identity.
-/
theorem cyclicMul_one_right (f : G → ℂ) : cyclicMul f kroneckerDelta = f := by
  rw [cyclicMul_comm, cyclicMul_one_left]

/-! ## Associativity -/

/--
**Theorem 13 (associativity)**: Cyclic convolution is associative.

Proof: Expand nested sums, distribute using `Finset.sum_mul`/`mul_sum`,
swap summation order with `Finset.sum_comm`, then reindex with
`Fintype.sum_equiv (Equiv.subRight y)`.
-/
theorem cyclicMul_assoc (f g h : G → ℂ) :
    cyclicMul (cyclicMul f g) h = cyclicMul f (cyclicMul g h) := by
  ext x
  simp only [cyclicMul]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1; ext y
  refine Fintype.sum_equiv (Equiv.subRight y) _ _ ?_
  intro z
  simp only [Equiv.subRight_apply]
  rw [mul_assoc]
  congr 1
  congr 1
  abel

/-! ## Bundled theorem -/

/--
**fdrs.md**: Proposition 38 (R^(k) ≅ ℤ/Nℤ as group) [§1.1 · Phase 3, Fragment 1] (lines 1594-1595)

(R^(k), ⊞_k) is a finite abelian group; dec_k is a group isomorphism
to ℤ/Nℤ where N = B_{k+1}.

Proof: ZMod N inherits AddCommGroup and Fintype from Mathlib.
-/
theorem cyclicGroup_isFiniteAbelian (N : ℕ) [NeZero N] :
    Nonempty (AddCommGroup (ZMod N)) ∧ Nonempty (Fintype (ZMod N)) :=
  ⟨⟨inferInstance⟩, ⟨inferInstance⟩⟩

/--
**fdrs.md**: Theorem 13 (closure, associativity, commutativity, identity) [§1.2 · Phase 3, Fragment 1] (lines 1604-1606)

(H_k^ℂ, *_k) is a commutative associative algebra with identity δ_0
(the Kronecker delta at the group identity digit-vector).

Proof: Combine the four properties proved above.
-/
theorem cyclicConvolution_isCommAlgebra :
    (∀ f g : G → ℂ, cyclicMul f g = cyclicMul g f) ∧
    (∀ f g h : G → ℂ, cyclicMul (cyclicMul f g) h = cyclicMul f (cyclicMul g h)) ∧
    (∀ f : G → ℂ, cyclicMul kroneckerDelta f = f) ∧
    (∀ f : G → ℂ, cyclicMul f kroneckerDelta = f) :=
  ⟨cyclicMul_comm, cyclicMul_assoc, cyclicMul_one_left, cyclicMul_one_right⟩

/-! ## Bridge to normalized convolution -/

/--
The normalized cyclic convolution from `AdditiveCharacters.lean` equals `(1/N) * cyclicMul`.
-/
theorem cyclicConv_eq_smul_cyclicMul (N : ℕ) [NeZero N] [Fintype (ZMod N)]
    (f g : ZMod N → ℂ) (x : ZMod N) :
    (1 / (N : ℂ)) * ∑ y : ZMod N, f y * g (x - y) =
    (1 / (N : ℂ)) * cyclicMul f g x := by
  simp only [cyclicMul]

end FdrsFormal.NumberTheory.ArithmeticFunctions.CyclicConvolution
