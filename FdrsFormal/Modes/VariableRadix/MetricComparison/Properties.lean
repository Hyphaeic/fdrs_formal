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

# Metric Spectrum Properties

This file proves the ultrametric spectrum forms a preorder under dominance.

## Mathematical Content (fdrs.md lines 5228-5238)

**Theorem 41 (Metric spectrum forms a preorder)**:
The relation ⪰ on Spec($\widehat{\mathcal{R}}$) satisfies:
- **Reflexivity**: δ_ω ⪰ δ_ω
- **Transitivity**: δ_{ω₁} ⪰ δ_{ω₂} ⪰ δ_{ω₃} ⟹ δ_{ω₁} ⪰ δ_{ω₃}

But not necessarily antisymmetric (distinct ω can induce same metric).

## References

- fdrs.md, Phase 6, Section 6.3 (lines 5228-5238)
-/

import FdrsFormal.Modes.VariableRadix.MetricComparison.Definition

namespace FdrsFormal.Modes.VariableRadix

/-!
## Preorder Properties
-/

/--
Metric dominance is reflexive.

**fdrs.md line 5232**: δ_ω ⪰ δ_ω trivially.

**Proof**: For all prefixes s, prefixWeight ω s ≤ prefixWeight ω s by reflexivity of ≤.
-/
theorem metricDominance_refl (ω : RadixLaw) : metricDominance ω ω := by
  unfold metricDominance
  intro s
  exact le_refl _

/--
Metric dominance is transitive.

**fdrs.md line 5233**: δ_{ω₁} ⪰ δ_{ω₂} ⪰ δ_{ω₃} ⟹ δ_{ω₁} ⪰ δ_{ω₃}.

**Proof**: By transitivity of ≤ on prefix weights:
If β_{ω₁}(s) ≤ β_{ω₂}(s) and β_{ω₂}(s) ≤ β_{ω₃}(s), then β_{ω₁}(s) ≤ β_{ω₃}(s).
-/
theorem metricDominance_trans (ω₁ ω₂ ω₃ : RadixLaw)
  (h₁₂ : metricDominance ω₁ ω₂) (h₂₃ : metricDominance ω₂ ω₃) :
  metricDominance ω₁ ω₃ := by
  unfold metricDominance at *
  intro s
  exact le_trans (h₁₂ s) (h₂₃ s)

/--
The ultrametric spectrum equipped with dominance forms a preorder.

**fdrs.md Theorem 41**: Combines reflexivity and transitivity.

**Note**: Not antisymmetric - different radix laws can induce the same metric.

**Proof**: We construct the Preorder instance using metricDominance as ≤.
-/
noncomputable instance ultrametricSpectrum_preorder : Preorder RadixLaw where
  le := metricDominance
  le_refl := metricDominance_refl
  le_trans := fun _ _ _ => metricDominance_trans _ _ _

end FdrsFormal.Modes.VariableRadix
