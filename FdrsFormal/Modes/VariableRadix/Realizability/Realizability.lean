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

# Realizability Module (THEOREM B)

Aggregator for ultrametric realizability theory.

## Contents

- `Conditions`: The three realizability conditions
- `Necessity`: δ = δ_ω ⟹ conditions (forward direction)
- `Sufficiency`: Conditions ⟹ ∃ω: δ = δ_ω (backward direction)
- `Spectrum`: Spec(R̂) preordered set
- `Extremal`: p-adic as minimal
- `Examples`: Engineered ultrametrics

## Main Result

**THEOREM B (Realizability Classification)**:
An ultrametric δ on ∏_{i≥0} D_i is realizable as δ = δ_ω for some SU radix function ω
if and only if:
1. Cylinder correspondence: Every ball is a finite union of cylinders
2. Monotone refinement: U(s) ⊆ U(t) ⟹ rad(U(s)) ≤ rad(U(t))
3. Finite branching: Each cylinder has finitely many immediate sub-cylinders

## References

- fdrs.md, Phase 6, Section 6.6 (lines 5381-5402)
- Paper (external draft): Theorem B (§6.3), Theorem 6.14
-/

import FdrsFormal.Modes.VariableRadix.Realizability.Conditions
import FdrsFormal.Modes.VariableRadix.Realizability.Necessity
import FdrsFormal.Modes.VariableRadix.Realizability.Sufficiency
import FdrsFormal.Modes.VariableRadix.Realizability.Spectrum
import FdrsFormal.Modes.VariableRadix.Realizability.Extremal
import FdrsFormal.Modes.VariableRadix.Realizability.Examples

namespace FdrsFormal.Modes.VariableRadix

/-!
## THEOREM B: Realizability

**Mathematical Theorem B** (Theorem 43):
An ultrametric δ on ∏_{i≥0} D_i is realizable as δ = δ_ω for some SU radix function ω
if and only if the three realizability conditions hold.

**Formalization Notes**:

The mathematical theorem is about abstract ultrametrics, but this formalization works
directly with RadixLaws. This creates a subtlety:

1. `RealizabilityConditions ω` is formulated in terms of ω's induced ultrametric
2. Any RadixLaw ω satisfies these conditions (see `radixLaw_satisfies_conditions`)
3. Therefore, the backward direction "conditions → SU" cannot distinguish SU from non-SU

The correct statement is:
- **Forward (necessity)**: SU → conditions (proven in `theoremB_necessity`)
- **Backward (sufficiency)**: Given an abstract ultrametric δ satisfying conditions,
  construct an SU ω with δ = δ_ω (requires abstract ultrametric formalization)

For practical purposes, we provide:
- `theoremB_necessity`: SU implies conditions
- `radixLaw_satisfies_conditions`: Any RadixLaw satisfies the conditions

The key insight is that the conditions characterize which ultrametrics ARISE from
SU radix laws, not which RadixLaws are SU.
-/

/--
**THEOREM B (Necessity)**: SU radix laws induce ultrametrics satisfying the conditions.

This is the forward direction of Theorem B: if ω is SU at all levels,
then the induced ultrametric δ_ω satisfies the three realizability conditions.
-/
theorem theoremB_forward (ω : RadixLaw) :
    (∀ k, isSiblingUniform ω k) → RealizabilityConditions ω :=
  theoremB_necessity ω

/--
Any RadixLaw satisfies the realizability conditions.

This follows from the fact that the conditions are formulated in terms of the
induced ultrametric δ_ω, which automatically has the required properties.
-/
theorem any_radixLaw_satisfies_conditions (ω : RadixLaw) :
    RealizabilityConditions ω :=
  radixLaw_satisfies_conditions ω

/-!
## Corollaries
-/

/-- Every RadixLaw gives a well-defined ultrametric (SU or not) -/
theorem radixLaw_gives_ultrametric (ω : RadixLaw) :
    ∀ x y z : InfiniteVariableSpace ω,
      ultrametricDist x z ≤ max (ultrametricDist x y) (ultrametricDist y z) := by
  intro x y z
  exact ultrametricDist_triangle x y z

/-- SU radix laws have stronger properties -/
theorem su_gives_ultrametric (ω : RadixLaw) (_hsu : ∀ k, isSiblingUniform ω k) :
    ∀ x y z : InfiniteVariableSpace ω,
      ultrametricDist x z ≤ max (ultrametricDist x y) (ultrametricDist y z) :=
  radixLaw_gives_ultrametric ω

/--
Classification of RadixLaws: either non-SU at some level, or satisfies conditions.

Since all RadixLaws satisfy the conditions, this is a tautology, but it illustrates
the structure of Theorem B's mathematical content.
-/
theorem spectrum_classification :
    ∀ ω : RadixLaw, (∃ k, ¬isSiblingUniform ω k) ∨ RealizabilityConditions ω := by
  intro ω
  by_cases h : ∀ k, isSiblingUniform ω k
  · right; exact theoremB_necessity ω h
  · left; push_neg at h; exact h

end FdrsFormal.Modes.VariableRadix
