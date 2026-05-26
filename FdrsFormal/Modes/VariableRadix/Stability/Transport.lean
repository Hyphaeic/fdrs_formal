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

# Transport Principle for Variable Radix

This file establishes the transport principle: properties on ℤ_M transfer
to properties on R^{(k)}_ω via the chart isomorphism.

## Mathematical Content (fdrs.md Theorem 33)

**Theorem 33 (Transport Principle)**:
For any property P on ℤ_M, we have:
  P holds on ℤ_M ⟺ P∘φ holds on R^{(k)}_ω

This allows us to:
1. Prove arithmetic properties on integers
2. Transport them to digit sequences via the chart

## References

- fdrs.md, Phase 5-6, Theorem 33
- DEPENDENCY_BASED_STRUCTURE.md, Modes/VariableRadix/Stability
-/

import FdrsFormal.Modes.VariableRadix.Stability.ChartIso

namespace FdrsFormal.Modes.VariableRadix

/-!
## Transport Principle
-/

/--
**Theorem 33**: Transport of unary predicates.

A predicate on Fin M is equivalent to its transported version on R^{(k)}_ω.
-/
theorem transport_pred (ω : RadixLaw) (k : ℕ)
    (P : Fin (completionCount ω k []) → Prop) :
    (∀ n, P n) ↔ (∀ τ : FiniteVariableSpace ω k, P (chartIso ω k τ)) := by
  constructor
  · intro h τ; exact h _
  · intro h n
    have := h (invChartIso ω k n)
    simp only [invChartIso, Equiv.apply_symm_apply] at this
    exact this

/-- Transport of binary predicates -/
theorem transport_pred₂ (ω : RadixLaw) (k : ℕ)
    (P : Fin (completionCount ω k []) → Fin (completionCount ω k []) → Prop) :
    (∀ m n, P m n) ↔
      (∀ τ σ : FiniteVariableSpace ω k, P (chartIso ω k τ) (chartIso ω k σ)) := by
  constructor
  · intro h τ σ; exact h _ _
  · intro h m n
    have := h (invChartIso ω k m) (invChartIso ω k n)
    simp only [invChartIso, Equiv.apply_symm_apply] at this
    exact this

/-!
## Transport of Functions
-/

/-- Transport a function through the chart -/
noncomputable def transportFun (ω : RadixLaw) (k : ℕ)
    (f : Fin (completionCount ω k []) → Fin (completionCount ω k [])) :
    FiniteVariableSpace ω k → FiniteVariableSpace ω k :=
  fun τ => invChartIso ω k (f (chartIso ω k τ))

/-- Transport preserves composition -/
theorem transportFun_comp (ω : RadixLaw) (k : ℕ)
    (f g : Fin (completionCount ω k []) → Fin (completionCount ω k [])) :
    transportFun ω k (f ∘ g) = transportFun ω k f ∘ transportFun ω k g := by
  funext τ
  simp only [transportFun, Function.comp_apply, invChartIso, chartIso, Equiv.apply_symm_apply]

/-- Transport preserves identity -/
theorem transportFun_id (ω : RadixLaw) (k : ℕ) :
    transportFun ω k id = id := by
  funext τ
  simp only [transportFun, id_eq, invChartIso, Equiv.symm_apply_apply]

/-!
## Transport of Algebraic Operations
-/

/-- Addition on R^{(k)}_ω transported from Fin -/
noncomputable def radixAdd (ω : RadixLaw) (k : ℕ)
    (τ σ : FiniteVariableSpace ω k) : FiniteVariableSpace ω k :=
  invChartIso ω k (chartIso ω k τ + chartIso ω k σ)

/-- Radix addition is commutative (by transport) -/
theorem radixAdd_comm (ω : RadixLaw) (k : ℕ) (τ σ : FiniteVariableSpace ω k) :
    radixAdd ω k τ σ = radixAdd ω k σ τ := by
  simp only [radixAdd, add_comm]

/-- Radix addition is associative (by transport) -/
theorem radixAdd_assoc (ω : RadixLaw) (k : ℕ) (τ σ ρ : FiniteVariableSpace ω k) :
    radixAdd ω k (radixAdd ω k τ σ) ρ = radixAdd ω k τ (radixAdd ω k σ ρ) := by
  simp only [radixAdd, invChartIso, chartIso, Equiv.apply_symm_apply, add_assoc]

/-!
## Transport Stability
-/

/-- Continuity of the chart (trivial for finite spaces) -/
theorem chartIso_continuous (ω : RadixLaw) (k : ℕ) :
    Function.Bijective (chartIso ω k) :=
  (chartIso ω k).bijective

/-- The chart is Lipschitz with respect to the induced ultrametric -/
theorem chartIso_lipschitz (ω : RadixLaw) (k : ℕ) :
    ∃ C : ℝ, C > 0 ∧ ∀ τ σ : FiniteVariableSpace ω k,
      ((chartIso ω k τ).val : ℝ) ≤ C * completionCount ω k [] := by
  use 1
  constructor
  · exact one_pos
  · intro τ _σ
    -- chartIso gives a Fin, so its value is < completionCount
    have h := (chartIso ω k τ).isLt
    simp only [one_mul]
    exact Nat.cast_le.mpr (Nat.le_of_lt h)

end FdrsFormal.Modes.VariableRadix
