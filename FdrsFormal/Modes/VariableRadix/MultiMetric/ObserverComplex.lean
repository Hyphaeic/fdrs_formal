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

# Multi-Metric Observer Complex

This file defines observer complexes with custom ultrametrics on each timeline.

## Mathematical Content (fdrs.md lines 5340-5382)

**Definition 82 (Multi-metric observer complex)**:

An observer complex with custom ultrametrics is:
  𝒪 := (A, B; σ; ω_A, ω_B, ω_I)

where:
- ω_A defines δ_{ω_A} on ℛ_A (timeline A's ultrametric)
- ω_B defines δ_{ω_B} on ℛ_B (timeline B's ultrametric)
- ω_I defines δ_{ω_I} on ℛ_I (interpreter/composite ultrametric)

**Key property**: Each timeline measures information distance differently.

## References

- fdrs.md, Phase 6, Section 6.5 (lines 5340-5366)
-/

import FdrsFormal.Modes.VariableRadix.Basic.RadixLaw
import FdrsFormal.Modes.VariableRadix.InducedUltrametric.Definition

namespace FdrsFormal.Modes.VariableRadix.MultiMetric

/-!
## Multi-Metric Observer Structure
-/

/--
Observer complex with independent ultrametrics on each timeline.

**fdrs.md Definition 82 (lines 5342-5354)**: Each timeline has its own radix law.

**Components**:
- Timeline A with radix law ω_A
- Timeline B with radix law ω_B
- Interpreter I with radix law ω_I
- Schedule σ determining execution order

**Axiomatized**: Full structure requires timeline state spaces and schedule formalization.
-/
structure MultiMetricObserver where
  /-- Radix law for timeline A -/
  ω_A : RadixLaw
  /-- Radix law for timeline B -/
  ω_B : RadixLaw
  /-- Radix law for interpreter timeline -/
  ω_I : RadixLaw
  /-- Schedule (simplified - full version requires more structure) -/
  schedule : ℕ → Bool  -- True = A, False = B

/--
Key property: timelines measure distance differently.

**fdrs.md line 5353**: Each timeline's δ_ω is independent.

**Axiomatized**: Formalization of independent metric structures.
-/
def timelines_independent_metrics (obs : MultiMetricObserver) : Prop :=
  obs.ω_A ≠ obs.ω_B ∨ obs.ω_A ≠ obs.ω_I ∨ obs.ω_B ≠ obs.ω_I

end FdrsFormal.Modes.VariableRadix.MultiMetric
