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

# Variable Radix Module (MODE I)

Main aggregator for variable radix systems.

## Overview

This module formalizes **variable radix systems** where the radix at each position
can depend on the prefix of digits chosen so far:

  ω : Σ* → ℕ≥2

This generalizes the fixed radix systems from Core to allow content-dependent branching.

## Contents

### Basic Definitions
- `Basic/`: RadixLaw, digit alphabets, tree structure, variable spaces

### Topology
- `InducedUltrametric/`: The induced ultrametric δ_ω from variable radix
- `PrefixWeights/`: The prefix weight function β_ω

### Encoding (THEOREM A)
- `Encoding/`: Subtree cardinalities, ranking, bijection φ_ω: R_ω ≅ ℕ

### Operations
- `VariableTick/`: Tick operator with variable carry

### Structure Conditions
- `SiblingUniformity/`: The SU condition for well-behaved odometer charts
- `Stability/`: Chart isomorphism and transport principle

### Classification (THEOREM B)
- `Realizability/`: Characterization of realizable ultrametrics

## Main Theorems

**THEOREM A** (Canonical Bijection): For any radix law ω, there exists a canonical
order-preserving bijection φ_ω: R^{(∞)}_ω → ℕ.
See: `Encoding/Bijection.lean`

**THEOREM B** (Realizability Classification, corrected form — Theorem 43): An
ultrametric δ is realizable as δ_ω for an SU radix law iff every open ball is a
prefix cylinder AND every cylinder has the canonical reciprocal-place-value
diameter. (The original three-condition form is provably insufficient; see the
erratum in fdrs.md §6.6.)
See: `Realizability/MetricRealizability.lean`

## Phase 13 (Generated Timelines)

The subshift gauge, the CF ultrametric, carry frequency, the Parry measure on the
golden-mean shift, and the certified Gosper engine cluster
(homographic/bihomographic/hyper) — fdrs.md Phase 13, Definitions 178–191,
Theorems 70–82.

## References

- fdrs.md, Phase 5-6 (Variable Radix Systems), Phase 13 (Generated Timelines)
- Paper (external draft): §6.3, Theorems A and B
-/

-- Basic definitions
import FdrsFormal.Modes.VariableRadix.Basic.Basic

-- Topology
import FdrsFormal.Modes.VariableRadix.InducedUltrametric.InducedUltrametric
import FdrsFormal.Modes.VariableRadix.PrefixWeights.PrefixWeights

-- Encoding (THEOREM A)
import FdrsFormal.Modes.VariableRadix.Encoding.Encoding

-- Operations
import FdrsFormal.Modes.VariableRadix.VariableTick.VariableTick

-- Structure conditions
import FdrsFormal.Modes.VariableRadix.SiblingUniformity.SiblingUniformity
import FdrsFormal.Modes.VariableRadix.Stability.Stability

-- Classification (THEOREM B)
import FdrsFormal.Modes.VariableRadix.Realizability.Realizability

-- Advanced Phase 6 content
import FdrsFormal.Modes.VariableRadix.MetricComparison
import FdrsFormal.Modes.VariableRadix.Design
import FdrsFormal.Modes.VariableRadix.MultiMetric

-- Phase 13: generated (continued-fraction) timelines — the subshift gauge,
-- the CF ultrametric, carry frequency, the Parry measure, and the certified
-- Gosper engine cluster
import FdrsFormal.Modes.VariableRadix.SubshiftWeight
import FdrsFormal.Modes.VariableRadix.SubshiftMetric
import FdrsFormal.Modes.VariableRadix.CarryFrequency
import FdrsFormal.Modes.VariableRadix.SubshiftParry
import FdrsFormal.Modes.VariableRadix.HomographicCarry
import FdrsFormal.Modes.VariableRadix.Bihomographic
import FdrsFormal.Modes.VariableRadix.BihomographicSound
import FdrsFormal.Modes.VariableRadix.BihomographicDriver
import FdrsFormal.Modes.VariableRadix.HyperGosper
