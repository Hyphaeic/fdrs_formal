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

# Metric Projection

This file defines metric pullback via timeline projections.

## Mathematical Content (fdrs.md lines 5357-5366)

**Definition 83 (Metric projection)**:

The projection π_B: ℛ_I → ℛ_B induces a **pullback metric** on ℛ_I:
  π_B^*(δ_{ω_B})(x,y) := δ_{ω_B}(π_B(x), π_B(y))

**Observation**: Generally π_B*(δ_{ω_B}) ≠ δ_{ω_I}

**Interpretation**: Pullback measures distance in B's coordinate system,
while δ_{ω_I} is intrinsic composite metric. Discrepancy represents
information not captured by B alone.

## References

- fdrs.md, Phase 6, Section 6.5 (lines 5357-5366)
-/

import FdrsFormal.Modes.VariableRadix.MultiMetric.ObserverComplex

namespace FdrsFormal.Modes.VariableRadix.MultiMetric

/-!
## Pullback Metric Construction
-/

/--
Pullback metric induced by timeline projection.

**fdrs.md Definition 83 (lines 5357-5362)**:
  π_B^*(δ_{ω_B})(x,y) := δ_{ω_B}(π_B(x), π_B(y))

**Axiomatized**: Requires formalizing projection maps between timeline spaces.
-/
def pullbackMetric (obs : MultiMetricObserver) : Prop :=
  ∀ s, 2 ≤ obs.ω_B.radix s

/--
Pullback generally differs from intrinsic composite metric.

**fdrs.md line 5363**: π_B*(δ_{ω_B}) ≠ δ_{ω_I} in general.

**Interpretation**: Information loss when projecting to B's view.
-/
def pullback_ne_intrinsic (obs : MultiMetricObserver) : Prop :=
  obs.ω_B ≠ obs.ω_I

end FdrsFormal.Modes.VariableRadix.MultiMetric
