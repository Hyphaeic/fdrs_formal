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

# NumberTheory Module (Tier 10-13)

Analytic number theory integrated with mixed-radix systems.

## Overview

This module imports arithmetic functions, Dirichlet convolution, characters,
valuations, and factorization lens theory into the mixed-radix framework.

**Key results**:
- Dirichlet algebra: Commutative, associative, unital
- Möbius inversion: Classical inversion formula
- Character orthogonality: Additive and multiplicative
- CRT factorization: Projectors factor under coprimality
- Factorization lens: Fiberwise locality of Dirichlet transforms

## Module Structure

```
NumberTheory/
├── ArithmeticFunctions/
│   ├── Definition.lean         # Basic arithmetic function type
│   ├── DirichletConv.lean      # Dirichlet convolution ⋆
│   ├── MobiusInversion.lean    # Möbius μ and inversion formula
│   └── ArithmeticFunctions.lean  # Aggregator
│
├── Characters/
│   ├── AdditiveCharacters.lean    # χ_m on ℤ/Nℤ, orthogonality
│   ├── DirichletCharacters.lean   # Multiplicative characters mod q
│   ├── CRT.lean                   # Character factorization via CRT
│   └── Characters.lean            # Aggregator
│
├── Valuations/
│   ├── Definition.lean         # v_p(n), Π_{p^e}, Π_{p,=e}
│   ├── Squarefree.lean         # μ² and product formula
│   └── Valuations.lean         # Aggregator
│
├── FactorizationLens/
│   ├── Definition.lean         # n = u_P(n) · s_P(n), fiberwise locality
│   └── FactorizationLens.lean  # Aggregator
│
├── CylinderMeasurability.lean  # Bridge: when congruences → cylinders
│
└── NumberTheory.lean (this file)
```

## Mathematical Content

Implements **Phase 3** from fdrs.md (lines 1594-2476):
- Fragment 1: Dirichlet algebra and Möbius inversion
- Fragment 2: Characters (additive and multiplicative) with CRT
- Fragment 3: Valuations and squarefree projectors
- Fragment 4: Factorization lens and dual filtrations

## Dependencies

**Requires**: Core, Operations, FunctionSpaces. **Enables**: the Integration module
(runtime algebra and programs).

## Status

Built and machine-checked against Mathlib. The early "axiomatized/STUB" labels are
obsolete — these results are proved (see, e.g., Proposition 51 below). Run
`python3 scripts/fdrs-summary` for the live, authoritative status (axioms, sorries,
scaffold); counts are intentionally not hard-coded here.

## References

- fdrs.md, Phase 3 (lines 1594-2476)
-/

import FdrsFormal.NumberTheory.ArithmeticFunctions
import FdrsFormal.NumberTheory.Characters
import FdrsFormal.NumberTheory.Valuations
import FdrsFormal.NumberTheory.FactorizationLens
import FdrsFormal.NumberTheory.CylinderMeasurability

-- fdrs.md lines 2203-2214, Proposition 51
namespace FdrsFormal.NumberTheory.Proposition51

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite
open FdrsFormal.NumberTheory.ArithmeticFunctions
open FdrsFormal.NumberTheory

variable {b : RadixSeq}

/--
**Proposition 51** (generic failure of commutation with additive block projections).
[§4.1 · Phase 3, Fragment 3]

Fix L ≥ 1. In general, T_a^{(k)} P_L^{(k)} ≠ P_L^{(k)} T_a^{(k)}.

**Proof**: For N = B_L + 1, define a = δ_N (the Dirac function at N). The transform
T_a maps the constant function 1 to 0 at all-zeros (since no divisor of 1 equals N ≥ 3)
and to 1 at the element with digit L = 1 (since N divides itself). These two elements
share an L-prefix, so T_a(1) is not L-block-constant, hence T_a does not commute with P_L.
-/
theorem genericFailure_dirichletTransform_blockProjection (b : RadixSeq) (k L : ℕ)
    (hL : 0 < L) (hLk : L ≤ k) :
    ∃ (a : ArithmeticFunction) (F : FiniteRadixSpace b k → ℂ),
      -- F is L-block-constant
      (∀ τ σ : FiniteRadixSpace b k,
        (∀ i : Fin (k + 1), i.val < L → τ i = σ i) → F τ = F σ) ∧
      -- T_a^{(k)} F is NOT L-block-constant
      ¬(∀ τ σ : FiniteRadixSpace b k,
        (∀ i : Fin (k + 1), i.val < L → τ i = σ i) →
        tensorTransform b k a F τ = tensorTransform b k a F σ) := by
  -- N = B_L + 1 ≥ 3
  set N := placeValue b L + 1 with hN_def
  have hBL_ge : 2 ≤ placeValue b L := by
    have h_pv1 : placeValue b 1 = b 0 := by show 1 * b 0 = b 0; exact one_mul _
    have h_ge : 2 ≤ placeValue b 1 := by rw [h_pv1]; exact b.ge_two 0
    have h_le : placeValue b 1 ≤ placeValue b L :=
      Nat.le_of_dvd (placeValue.pos L) (placeValue.dvd_of_le hL)
    omega
  have hN_ge : 3 ≤ N := by omega
  have hN_pos : 0 < N := by omega
  -- N ≤ B_{k+1}
  have hN_le : N ≤ placeValue b (k + 1) := by
    have h_step : placeValue b L * 2 ≤ placeValue b (L + 1) := by
      show placeValue b L * 2 ≤ placeValue b L * b L
      exact Nat.mul_le_mul_left _ (b.ge_two L)
    have h_mono : placeValue b (L + 1) ≤ placeValue b (k + 1) :=
      Nat.le_of_dvd (placeValue.pos _) (placeValue.dvd_of_le (by omega))
    omega
  -- Witness: a = Dirac at N, F = constant 1
  let a : ArithmeticFunction := fun n => if n.val = N then 1 else 0
  refine ⟨a, fun _ => 1, fun _ _ _ => rfl, ?_⟩
  intro h_block
  -- τ₀ = all zeros, τ₁ = digit L = 1, rest zeros
  let τ₀ : FiniteRadixSpace b k := fun _ => ⟨0, b.pos _⟩
  let τ₁ : FiniteRadixSpace b k :=
    fun i => if i.val = L then ⟨1, by have := b.ge_two i; omega⟩ else ⟨0, b.pos i⟩
  -- They agree on the first L digits
  have h_agree : ∀ i : Fin (k + 1), i.val < L → τ₀ i = τ₁ i := by
    intro i hi; simp only [τ₁]; rw [if_neg (by omega)]
  have h_eq := h_block τ₀ τ₁ h_agree
  -- Compute decodeFinite
  have h_dec₀ : decodeFinite b k τ₀ = 0 := by
    simp only [decodeFinite, τ₀, Nat.zero_mul, Finset.sum_const_zero]
  have h_dec₁ : decodeFinite b k τ₁ = placeValue b L := by
    simp only [decodeFinite, τ₁]
    rw [Finset.sum_eq_single ⟨L, by omega⟩]
    · simp only [ite_true, Fin.val_mk, one_mul]
    · intro j _ hj
      have hne : j.val ≠ L := fun h => hj (Fin.ext h)
      simp only [Fin.val_mk, hne, ite_false, Nat.zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  -- natK values
  have h_natK₀ : (natK b k τ₀).val = 1 := by simp [natK, h_dec₀]
  have h_natK₁ : (natK b k τ₁).val = N := by
    show decodeFinite b k τ₁ + 1 = N; rw [h_dec₁]
  -- Key computation: tensorTransform unfolds to Dirichlet sum
  -- For any τ: tensorTransform b k a F τ = (toMathlib a * toMathlib (liftToArith b k F)) (natK b k τ).val
  have unfold_tensor : ∀ τ : FiniteRadixSpace b k,
      tensorTransform b k a (fun _ => 1) τ =
      (toMathlib a * toMathlib (liftToArith b k (fun _ => (1 : ℂ)))) (natK b k τ).val := by
    intro τ; rfl
  -- At τ₀: sum over divisorsAntidiagonal 1, only element is (1,1), a(1) = 0
  have h_val₀ : tensorTransform b k a (fun _ => 1) τ₀ = 0 := by
    rw [unfold_tensor, h_natK₀, _root_.ArithmeticFunction.mul_apply]
    rw [Nat.divisorsAntidiagonal_one]
    simp only [Finset.sum_singleton]
    rw [toMathlib_apply (show 0 < 1 by omega)]
    show (a ⟨1, Nat.one_pos⟩) * _ = 0
    simp only [a, show (1 : ℕ) ≠ N by omega, ite_false, zero_mul]
  -- At τ₁: sum over divisorsAntidiagonal N, only (N,1) contributes
  have h_val₁ : tensorTransform b k a (fun _ => 1) τ₁ = 1 := by
    rw [unfold_tensor, h_natK₁, _root_.ArithmeticFunction.mul_apply]
    -- Use Finset.sum_eq_single to extract the (N, 1) term
    rw [Finset.sum_eq_single_of_mem (N, 1)
      (Nat.mem_divisorsAntidiagonal.mpr ⟨mul_one N, by omega⟩)]
    · -- The term at (N, 1) equals 1
      rw [toMathlib_apply hN_pos, toMathlib_apply (show 0 < 1 by omega)]
      show a ⟨N, hN_pos⟩ * liftToArith b k (fun _ => (1 : ℂ)) ⟨1, Nat.one_pos⟩ = 1
      simp only [a, ite_true, liftToArith,
        show (1 : ℕ) ≤ placeValue b (k + 1) from placeValue.one_le _, dite_true]
      simp
    · -- All other terms are 0
      intro ⟨d, e⟩ hde hne
      have ⟨hprod, hne_zero⟩ := Nat.mem_divisorsAntidiagonal.mp hde
      have hd_pos : 0 < d := by
        by_contra h; push_neg at h
        rw [Nat.le_zero.mp h, zero_mul] at hprod; omega
      rw [toMathlib_apply hd_pos]
      show a ⟨d, hd_pos⟩ * _ = 0
      -- d ≠ N: if d = N then e = 1 (from d * e = N), contradicting hne
      have hd_ne : d ≠ N := by
        intro h_eq
        rw [h_eq] at hprod
        have he1 : e = 1 := mul_left_cancel₀ (by omega : N ≠ 0)
          (hprod.trans (mul_one N).symm)
        exact hne (Prod.ext h_eq he1)
      simp only [a, hd_ne, ite_false, zero_mul]
  -- Contradiction: 0 = 1
  rw [h_val₀, h_val₁] at h_eq
  exact zero_ne_one h_eq

end FdrsFormal.NumberTheory.Proposition51
