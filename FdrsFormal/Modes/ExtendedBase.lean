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

# Extended Base Module (Mode III)

Aggregator for the extended base mode with distinguished 0/1 digits.

## Contents

- **Definition**: ExtendedDigit, ExtendedRep, decode, subset encoding
- **IndexSets**: Active/capacity index sets, effective base
- **PlaceValues**: Generalized place values with monotonicity
- **ExtendedTick**: Tick semantics with wall/wire/standard carry

## References

- fdrs.md, Phase 6 Section 6.3, Phase 9 (lines 6890-7035)
-/

import FdrsFormal.Modes.ExtendedBase.Definition
import FdrsFormal.Modes.ExtendedBase.IndexSets
import FdrsFormal.Modes.ExtendedBase.PlaceValues
import FdrsFormal.Modes.ExtendedBase.ExtendedTick
import FdrsFormal.Modes.ExtendedBase.Instantiate
import FdrsFormal.Modes.ExtendedBase.ArithmeticCylinder
import FdrsFormal.Modes.ExtendedBase.OdometerWeight
import FdrsFormal.Modes.ExtendedBase.SigmaAlgebra
import FdrsFormal.Modes.ExtendedBase.SpatialThermometer
import FdrsFormal.Modes.ExtendedBase.CarryRouteUnification
