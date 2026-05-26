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

# Chart Isomorphism for Variable Radix

This file establishes the chart isomorphism between variable radix spaces
and their integer representations.

## Mathematical Content (fdrs.md Fragment 5.2)

The chart isomorphism connects:
1. The geometric/combinatorial view (digit sequences in R_ω)
2. The arithmetic view (integers in ℤ_M where M = |R^{(k)}_ω|)

Under sibling uniformity, this isomorphism preserves:
- Group structure (addition mod M)
- Metric structure (induced ultrametric)
- Measure structure (counting measure)

## References

- fdrs.md, Phase 5-6, Fragment 5.2
- DEPENDENCY_BASED_STRUCTURE.md, Modes/VariableRadix/Stability
-/

import FdrsFormal.Modes.VariableRadix.Encoding.Encoding
import FdrsFormal.Modes.VariableRadix.VariableTick.Definition

namespace FdrsFormal.Modes.VariableRadix

/-!
## Chart Isomorphism
-/

/--
The chart isomorphism: the bijection φ^{(k)}_ω viewed as a structure-preserving map.
-/
noncomputable def chartIso (ω : RadixLaw) (k : ℕ) :
    FiniteVariableSpace ω k ≃ Fin (completionCount ω k []) :=
  finiteVariableRadixEquiv ω k

/-- Chart isomorphism is the decode function -/
theorem chartIso_apply (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k) :
    (chartIso ω k τ).val = variableRadixDecode ω k τ := by
  rfl

/-!
## Chart Preserves Order
-/

/-- Chart isomorphism is an order isomorphism -/
theorem chartIso_orderIso (ω : RadixLaw) (k : ℕ) (τ σ : FiniteVariableSpace ω k) :
    chartIso ω k τ < chartIso ω k σ ↔ τ.digits < σ.digits := by
  -- chartIso applies decode and wraps in Fin
  -- Fin ordering is the natural number ordering
  simp only [chartIso, finiteVariableRadixEquiv, Equiv.ofBijective_apply, Fin.lt_def]
  exact decode_lt_iff ω k τ σ

/-!
## Chart and Tick
-/

/-- Chart intertwines Tick and +1: φ(T(τ)).val = (φ(τ).val + 1) mod M -/
theorem chartIso_tick (ω : RadixLaw) (k : ℕ) (τ : FiniteVariableSpace ω k) :
    (chartIso ω k (cyclicVariableTick ω k τ)).val =
      ((chartIso ω k τ).val + 1) % completionCount ω k [] := by
  rw [chartIso_apply, chartIso_apply]
  exact cyclicVariableTick_decode ω k τ

/-!
## Inverse Chart
-/

/-- The inverse chart: encode -/
noncomputable def invChartIso (ω : RadixLaw) (k : ℕ) :
    Fin (completionCount ω k []) ≃ FiniteVariableSpace ω k :=
  (chartIso ω k).symm

/-- Inverse chart is the encode function -/
theorem invChartIso_apply (ω : RadixLaw) (k : ℕ) (n : Fin (completionCount ω k [])) :
    invChartIso ω k n = variableRadixEncode ω k n.val n.isLt := by
  simp only [invChartIso, chartIso]
  -- finiteVariableRadixEquiv.symm n = variableRadixEncode n
  -- Since finiteVariableRadixEquiv is Equiv.ofBijective of the decode function,
  -- its inverse is the encode function
  apply (finiteVariableRadixEquiv ω k).injective
  rw [Equiv.apply_symm_apply]
  -- Goal: finiteVariableRadixEquiv ω k (variableRadixEncode ω k n.val n.isLt) = n
  -- finiteVariableRadixEquiv applies decode and wraps in Fin
  simp only [finiteVariableRadixEquiv, Equiv.ofBijective_apply]
  ext
  exact (variableRadixDecode_encode ω k n.val n.isLt).symm

end FdrsFormal.Modes.VariableRadix
