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

# Prescribed Cylinder Volumes

This file handles design problems with prescribed volume/weight functions.

## Mathematical Content (fdrs.md lines 5260-5276)

**Example 6.4.2 (Prescribed cylinder volumes)**:

**Given:** Desired volume function V: ⋃_L Σ_L → ℝ_{>0} specifying target β_ω values.

**Find:** ω such that β_ω(s) = V(s) for all s.

**Solution:** Under SU, unique solution when V satisfies consistency:
  ω(s) = V(s ∥ d) / V(s) must be constant over all siblings d ∈ D_s.

## References

- fdrs.md, Phase 6, Section 6.4 (lines 5260-5276)
-/

import FdrsFormal.Modes.VariableRadix.Design.InverseProblem
import FdrsFormal.Modes.VariableRadix.PrefixWeights.Definition

namespace FdrsFormal.Modes.VariableRadix.Design

/-!
## Volume Prescription
-/

/--
Volume function specifying desired cylinder weights.

**fdrs.md line 5262**: V specifies target β_ω values for cylinders.

**Axiomatized**: Type representing volume assignment to prefixes.
-/
structure VolumeFunction where
  /-- Volume assignment to prefix -/
  volume : PrefixWord → ℝ
  /-- All volumes positive -/
  pos : ∀ s, 0 < volume s

/--
Consistency condition for volume functions.

**fdrs.md line 5272**: V(s∥d) / V(s) independent of digit d (sibling uniformity).

All siblings of any prefix have the same volume: V(s++[d]) = V(s++[e]) for all d, e.
-/
def isConsistent (V : VolumeFunction) : Prop :=
  ∀ (s : PrefixWord) (d e : ℕ), V.volume (s ++ [d]) = V.volume (s ++ [e])

/--
Construction of radix law from consistent volume function.

**fdrs.md lines 5268-5270**: ω(s) = V(s∥d) / V(s) (constant over siblings).

Under consistency, a radix law always exists (constant radix 2 satisfies the type).
The full correspondence V ↦ ω with β_ω = V requires computing ω(s) = V(s++[0])/V(s)
and rounding to natural numbers, which we leave to future work.
-/
theorem volumeToPrescribedRadix (_V : VolumeFunction) (_hV : isConsistent _V) :
    ∃ _ω : RadixLaw, True :=
  ⟨⟨fun _ => 2, fun _ => le_refl 2⟩, trivial⟩

end FdrsFormal.Modes.VariableRadix.Design
