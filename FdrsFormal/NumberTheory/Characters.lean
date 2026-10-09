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

# Characters Module

Additive and multiplicative (Dirichlet) characters with orthogonality and CRT.

## Contents

1. **AdditiveCharacters**: Characters on ℤ/Nℤ, orthogonality, residue projectors
2. **DirichletCharacters**: Multiplicative characters, dual orthogonality
3. **CRT**: Factorization of characters and projectors under Chinese Remainder Theorem
4. **MixedRadixFFT**: The pulled-back character as Vilenkin character × twiddle kernel
   (Phase 3 §1.4 addendum: Theorem 119, Corollary 32, Propositions 154–155)
5. **MixedRadixStages**: The staged FFT is the DFT; reads per output (§1.5)
6. **GoodThomas**: The residue chart is untwisted; a chart iff coprime (§1.6)
7. **FourierCircuit** / **FFTCircuit**: Family 130's gate model; exact gate counts for
   the staged, dense, and binary circuits (§1.7)
8. **FFTButterfly**: The binary stage is a butterfly; `(3/2) N log₂ N` gates (§1.8)
9. **FFTTwiddleSkip**: Trivial twiddles skipped; exactly `(3/2) N log₂ N − N + 1` gates (§1.9)
10. **PairKernel**: Odd lengths in `n² − 1` gates by mirror pairing (§1.10)
11. **CircuitCompose**: Positional and residue splits for arbitrary circuits; plans are
    circuits (§1.11)
12. **SearchCertificates** (generated): every search count for `N ≤ 512` as a theorem

## Mathematical References

- fdrs.md, Phase 3 Fragment 2 (lines 1769-1942)

## Status

Built and machine-checked against Mathlib; the early "axiomatized/STUB" labels are
obsolete (this module has no axioms). Run `python3 scripts/fdrs-summary` for the live,
authoritative status — axioms, sorries, and any remaining scaffold declarations —
rather than relying on counts written here.
-/

import FdrsFormal.NumberTheory.Characters.AdditiveCharacters
import FdrsFormal.NumberTheory.Characters.DirichletCharacters
import FdrsFormal.NumberTheory.Characters.CRT
import FdrsFormal.NumberTheory.Characters.TwistTransform
import FdrsFormal.NumberTheory.Characters.MixedRadixFFT
import FdrsFormal.NumberTheory.Characters.MixedRadixStages
import FdrsFormal.NumberTheory.Characters.GoodThomas
import FdrsFormal.NumberTheory.Characters.FourierCircuit
import FdrsFormal.NumberTheory.Characters.FFTCircuit
import FdrsFormal.NumberTheory.Characters.FFTButterfly
import FdrsFormal.NumberTheory.Characters.FFTTwiddleSkip
import FdrsFormal.NumberTheory.Characters.PairKernel
import FdrsFormal.NumberTheory.Characters.CircuitCompose
import FdrsFormal.NumberTheory.Characters.SearchCertificates
import FdrsFormal.NumberTheory.Characters.RaderBluestein
import FdrsFormal.NumberTheory.Characters.SearchCertificatesExt
import FdrsFormal.NumberTheory.Characters.ResidueConvolution
