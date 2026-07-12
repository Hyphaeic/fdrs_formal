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

# Adelic Complex Module

Aggregates the adelic machine: heterogeneous place engines (p-adic ledgers and
certified emission traps) under one scheduler with proven confluence, the product
formula on ℚˣ in exact arithmetic, the finite-precision gauge bound, the rigidity
boundary (no synthetic places on ℚ), and the function-field keystone.

## References

- Design records: `docs/archive/adelic-machine/` (superseded), `docs/function-field/`
- fdrs.md Phase 13 (the emission-certificate family; `padic_emit_traps` is the
  congruence certificate cited by Theorem 100's four-certificate accounting)
-/

import FdrsFormal.Modes.Adelic.PlaceEngine
import FdrsFormal.Modes.Adelic.PadicEmission
import FdrsFormal.Modes.Adelic.PadicHomographic
import FdrsFormal.Modes.Adelic.PadicEmitTraps
import FdrsFormal.Modes.Adelic.PadicBihEmission
import FdrsFormal.Modes.Adelic.ValuationStream
import FdrsFormal.Modes.Adelic.Complex
import FdrsFormal.Modes.Adelic.ProductFormula
import FdrsFormal.Modes.Adelic.ProductFormulaRat
import FdrsFormal.Modes.Adelic.GaugeBound
import FdrsFormal.Modes.Adelic.DriverCorrect
import FdrsFormal.Modes.Adelic.Rigidity
import FdrsFormal.Modes.Adelic.AdelicInterface
import FdrsFormal.Modes.Adelic.FunctionFieldDegree
