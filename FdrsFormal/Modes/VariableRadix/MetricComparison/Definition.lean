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

# Metric Dominance

This file defines the dominance relation on ultrametric spectra.

## Mathematical Content (fdrs.md lines 5214-5240)

**Definition 81 (Metric dominance)**:
For two radix functions ω₁, ω₂, we say δ_{ω₁} **dominates** δ_{ω₂} (written δ_{ω₁} ⪰ δ_{ω₂}) if:
  ∀ x,y: δ_{ω₁}(x,y) ≥ δ_{ω₂}(x,y)

Equivalently: β_{ω₁}(s) ≤ β_{ω₂}(s) for all prefixes s.

**Interpretation**: ω₁ provides finer resolution (smaller cylinder volumes) than ω₂.

## References

- fdrs.md, Phase 6, Section 6.3 (lines 5214-5240)
- Paper: Part of custom ultrametric design framework
-/

import FdrsFormal.Modes.VariableRadix.InducedUltrametric.Definition
import FdrsFormal.Modes.VariableRadix.PrefixWeights.Definition

namespace FdrsFormal.Modes.VariableRadix

/-!
## Metric Dominance Relation
-/

/--
Metric dominance: δ_{ω₁} dominates δ_{ω₂} if distances are everywhere larger.

**fdrs.md lines 5214-5224**: Dominance means finer resolution (smaller prefix weights).

**Definition**: We define dominance via prefix weight comparison, which is the
concrete implementation of "distances are everywhere ≥".
-/
def metricDominance (ω₁ ω₂ : RadixLaw) : Prop :=
  ∀ s : PrefixWord, prefixWeight ω₁ s ≤ prefixWeight ω₂ s

/--
Notation for metric dominance.

δ_{ω₁} ⪰ δ_{ω₂} means ω₁ provides finer or equal resolution everywhere.
-/
notation δ₁ " ⪰ " δ₂ => metricDominance δ₁ δ₂

/--
Dominance is equivalent to prefix weight comparison.

**fdrs.md line 5222**: δ_{ω₁} ⪰ δ_{ω₂} ⟺ β_{ω₁}(s) ≤ β_{ω₂}(s) for all s.

**Proof**: By definition.
-/
theorem metricDominance_iff_prefixWeight (ω₁ ω₂ : RadixLaw) :
  metricDominance ω₁ ω₂ ↔ ∀ s : PrefixWord, prefixWeight ω₁ s ≤ prefixWeight ω₂ s := by
  rfl

/--
Interpretation of dominance in terms of resolution.

**fdrs.md line 5224**: ω₁ dominates means finer resolution (smaller cylinders).

**Proof**: Immediate from the definition of metricDominance.
-/
theorem dominance_implies_finer_resolution (ω₁ ω₂ : RadixLaw)
  (h : metricDominance ω₁ ω₂) (s : PrefixWord) :
  prefixWeight ω₁ s ≤ prefixWeight ω₂ s :=
  h s

end FdrsFormal.Modes.VariableRadix
