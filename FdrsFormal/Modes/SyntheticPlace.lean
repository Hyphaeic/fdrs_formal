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

# Synthetic Place Complex Module (Phase 14)

Aggregates the synthetic place complex: the gauge keystone (SU0), coupling and the
ragged regime (SU1), the admissibility trap (SU2), zoom-out restriction (SU3),
conservation / interface balance / rigidity (SU4), network geometry (SU5), the
digit-coupling axes — grading, currencies, windows, nested charts, the non-abelian
arc (SU6), and the SU7 network machine (`Config` + `complexStep`: balance,
couplability, traps, determinacy, liveness) with the Phase-8 concretization bridge.

## References

- fdrs.md Phase 14 (Definitions 192–211, Theorems 83–112, Propositions 147–152)
- Design records: `docs/synthetic-place/00-thesis.md` … `04-network-config.md`
-/

-- SU0–SU5: the statics
import FdrsFormal.Modes.SyntheticPlace.GaugeUltrametric
import FdrsFormal.Modes.SyntheticPlace.Composition
import FdrsFormal.Modes.SyntheticPlace.AdmissibilityTrap
import FdrsFormal.Modes.SyntheticPlace.Restriction
import FdrsFormal.Modes.SyntheticPlace.Conservation
import FdrsFormal.Modes.SyntheticPlace.InterfaceBalance
import FdrsFormal.Modes.SyntheticPlace.ConservationRigidity
import FdrsFormal.Modes.SyntheticPlace.TraceGeometry
import FdrsFormal.Modes.SyntheticPlace.NetworkGauge

-- SU6: digit coupling — grading, currencies, windows, nested charts
import FdrsFormal.Modes.SyntheticPlace.Grading
import FdrsFormal.Modes.SyntheticPlace.CurrencyBalance
import FdrsFormal.Modes.SyntheticPlace.WindowAccountability
import FdrsFormal.Modes.SyntheticPlace.WindowBoundary
import FdrsFormal.Modes.SyntheticPlace.NestedChain
import FdrsFormal.Modes.SyntheticPlace.NestedDilation

-- SU6′: the non-abelian arc
import FdrsFormal.Modes.SyntheticPlace.GroupGrading
import FdrsFormal.Modes.SyntheticPlace.CircleEmit
import FdrsFormal.Modes.SyntheticPlace.SE2Pose
import FdrsFormal.Modes.SyntheticPlace.SE2Engine
import FdrsFormal.Modes.SyntheticPlace.SE2Tight

-- SU7: the network machine (§14.12)
import FdrsFormal.Modes.SyntheticPlace.NetworkConfig
import FdrsFormal.Modes.SyntheticPlace.NetworkComplexStep
import FdrsFormal.Modes.SyntheticPlace.NetworkBalance
import FdrsFormal.Modes.SyntheticPlace.NetworkCouplability
import FdrsFormal.Modes.SyntheticPlace.NetworkTraps
import FdrsFormal.Modes.SyntheticPlace.NetworkDeterminacy
import FdrsFormal.Modes.SyntheticPlace.NetworkLiveness

-- The Phase-8 concretization bridge (§14.13)
import FdrsFormal.Modes.SyntheticPlace.NetworkBridge

-- The dimension of a designed gauge (§14.15)
import FdrsFormal.Modes.SyntheticPlace.Dimension
