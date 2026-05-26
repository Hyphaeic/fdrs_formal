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

# Spectrum of Ultrametrics

This file studies the spectrum Spec(R̂) of ultrametrics on the profinite completion.

## Mathematical Content (fdrs.md lines 5450-5454)

**P6.3** (Spectrum forms preorder):
The ultrametric dominance relation ⪰ is reflexive and transitive on Spec(R̂).

The spectrum is the collection of all SU-realizable ultrametrics, ordered
by the dominance relation: δ₁ ⪰ δ₂ iff balls of δ₁ are unions of balls of δ₂.

## References

- fdrs.md, Phase 6, Summary (lines 5450-5454)
- DEPENDENCY_BASED_STRUCTURE.md, Modes/VariableRadix/Realizability
- Paper: Theorem B (§6.3)
-/

import FdrsFormal.Modes.VariableRadix.Realizability.Sufficiency

namespace FdrsFormal.Modes.VariableRadix

/-!
## The Spectrum
-/

/-- The spectrum: the set of SU-realizable ultrametrics -/
def UltrametricSpectrum : Type :=
  {ω : RadixLaw // ∀ k, isSiblingUniform ω k}

/-- Coercion to RadixLaw -/
instance : CoeOut UltrametricSpectrum RadixLaw :=
  ⟨Subtype.val⟩

/-!
## Dominance Relation
-/

/--
Ultrametric dominance: δ₁ ⪰ δ₂ iff every ball of δ₁ is a union of balls of δ₂.

Intuitively, δ₁ is "coarser" than δ₂.

Note: The formal definition requires embedding both spaces in a common space
(the profinite completion) or using a transport map. For this stub, we use
a placeholder definition based on radii comparison.
-/
def ultrametricDominance (ω₁ ω₂ : UltrametricSpectrum) : Prop :=
  ∀ (s : PrefixWord),
    variableRadixRadius ω₁.val s ≤ variableRadixRadius ω₂.val s

/-- Notation for dominance -/
scoped infix:50 " ⪰ᵤ " => ultrametricDominance

/-!
## Preorder Structure
-/

/-- Dominance is reflexive -/
theorem dominance_refl (ω : UltrametricSpectrum) : ω ⪰ᵤ ω := by
  intro s
  exact le_refl _

/-- Dominance is transitive -/
theorem dominance_trans (ω₁ ω₂ ω₃ : UltrametricSpectrum)
    (h₁₂ : ω₁ ⪰ᵤ ω₂) (h₂₃ : ω₂ ⪰ᵤ ω₃) : ω₁ ⪰ᵤ ω₃ := by
  intro s
  exact le_trans (h₁₂ s) (h₂₃ s)

/--
**P6.3**: The spectrum forms a preorder under dominance.
-/
instance : Preorder UltrametricSpectrum where
  le := ultrametricDominance
  le_refl := dominance_refl
  le_trans := dominance_trans

/-!
## Spectrum Properties
-/

/-- The spectrum is nonempty (constant radix law) -/
theorem spectrum_nonempty : Nonempty UltrametricSpectrum := by
  constructor
  refine ⟨{radix := fun _ => 2, radix_ge_two := fun _ => Nat.le_refl 2}, ?_⟩
  intro k
  exact positionOnly_siblingUniform _ k (fun _ _ _ => rfl)

/-- Position-only radix laws are in the spectrum (they satisfy SU at all depths) -/
theorem positionOnly_in_spectrum (ω : RadixLaw)
    (h_pos : ∀ s t : PrefixWord, s.length = t.length → ω.radix s = ω.radix t) :
    ∃ spec : UltrametricSpectrum, (spec : RadixLaw) = ω :=
  ⟨⟨ω, fun k => positionOnly_siblingUniform ω k h_pos⟩, rfl⟩

/-!
## Extremal Elements
-/

/-- Characterization of minimal elements in the spectrum -/
def isMinimalInSpectrum (ω : UltrametricSpectrum) : Prop :=
  ∀ ω' : UltrametricSpectrum, ω' ≤ ω → ω ≤ ω'

/-- Characterization of maximal elements in the spectrum -/
def isMaximalInSpectrum (ω : UltrametricSpectrum) : Prop :=
  ∀ ω' : UltrametricSpectrum, ω ≤ ω' → ω' ≤ ω

end FdrsFormal.Modes.VariableRadix
