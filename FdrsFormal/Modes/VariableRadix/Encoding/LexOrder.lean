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

# Lexicographic Order on Variable-Radix Spaces

Defines the canonical ordering needed for Tick on variable-radix spaces.

## Mathematical Content (fdrs.md lines 4048-4052)

**Definition 60**: Lexicographic order on R^(k)_ω

## References

- fdrs.md, Phase 5 Fragment 5.1, Section 3.1 (lines 4048-4052)
-/

import FdrsFormal.Modes.VariableRadix.Encoding.SubtreeCards
import FdrsFormal.Modes.VariableRadix.Encoding.Bijection

namespace FdrsFormal.Modes.VariableRadix

/-! ## Definition 60: Lexicographic order -/

/--
**fdrs.md**: Definition 60 (lex order) [§3.1 · Phase 5, Fragment 5.1] (lines 4048-4052)

For τ, σ ∈ R^(k)_ω, define τ <_lex σ if at the first index i where they differ,
τ_i < σ_i. This is a total order on R^(k)_ω.

**Proof**: Transfer the linear order from `Fin n` via the canonical bijection
`finiteVariableRadixEquiv : R^(k)_ω ≃ Fin (completionCount ω k [])`.
-/
noncomputable def lexOrder (ω : RadixLaw) (k : ℕ) :
    LinearOrder (FiniteVariableSpace ω k) :=
  LinearOrder.lift' (finiteVariableRadixEquiv ω k) (finiteVariableRadixEquiv ω k).injective

end FdrsFormal.Modes.VariableRadix
