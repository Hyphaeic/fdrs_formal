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
-/
import FdrsFormal.FunctionSpaces.Haar.ContrastBasis
import FdrsFormal.FunctionSpaces.Haar.Definition
import FdrsFormal.FunctionSpaces.Haar.Orthonormality
import FdrsFormal.FunctionSpaces.Haar.SupportLevel
import FdrsFormal.FunctionSpaces.Haar.ProjectionAction
import FdrsFormal.FunctionSpaces.Haar.DiagonalStructure
import FdrsFormal.FunctionSpaces.Haar.WaveletPacket

/-!
# Haar Wavelet Basis for Mixed-Radix Spaces

This module develops the Haar wavelet basis for finite mixed-radix function spaces,
providing a multi-resolution analysis adapted to the mixed-radix structure.

## Main Components

* `ContrastBasis` - Mean-zero orthonormal vectors for each digit alphabet
* `Definition` - Haar atoms as tensor products of contrast vectors
* `Orthonormality` - Proof that Haar atoms form orthonormal basis
* `SupportLevel` - Support level ℓ(α) indicating finest scale
* `ProjectionAction` - How block projections act on Haar atoms
* `DiagonalStructure` - Commutant algebra diagonal-by-scale structure
* `WaveletPacket` - Ultrametric-adapted wavelet packet trees

## Mathematical Content

Phase 2.4 from fdrs.md (Lines 1279-1564) - Mixed-radix Haar wavelets:
- Orthonormal contrast basis construction
- Tensor product Haar atoms h_α
- Scale decomposition D_L = span{h_α : ℓ(α) = L}
- Commutant algebra as product of matrix algebras

## Status

The full module — contrast basis, Haar orthonormality, and the wavelet-packet tree
(`WaveletPacket`, including the closed-form `basisEval_eq_prod` and the
`packetBasis_orthogonal` / `packetBasis_norm_sq` lemmas) — is fully proved and
axiom-clean, and is part of the default `lake build`. Run
`python3 scripts/fdrs-summary` for the live, authoritative status.

## References

* fdrs.md, Phase 2.4 (Lines 1279-1564): Haar basis construction
-/
