/-
FdrsFormal - Function-Defined Radix Systems

Formalization of the fdrs.md specification, organized by mathematical dependencies.

## Structure

- **Core/**: Foundation (radix sequences, finite/infinite spaces, bijections)
- **Operations/**: Arithmetic operations (Tick, addition, subtraction, predecessor)
- **Topology/**: Ultrametric structure, continuity, locality
- **FunctionSpaces/**: Mixed-radix complexes (𝕋(V), projections P_L, details Δ_L)
- **NumberTheory/**: Analytic number theory (Dirichlet, characters, factorization)
- **Integration/**: Combined topology + ANT (dual filtrations, complexity bounds)
- **Modes/**: Modes of application (VariableRadix, ContextDependent, ExtendedBase, BaseZeroSea)
- **Analysis/**: Digit-conditional signal analysis (imported transitively via Modes)
- **Composition/**: Multi-timeline routing and composition

For live status (file/theorem counts, sorries, stubs) run
`python3 scripts/fdrs-summary`; counts are intentionally not hard-coded here.
-/

-- Foundation layer
import FdrsFormal.Core

-- Operations layer
import FdrsFormal.Operations

-- Topology layer
import FdrsFormal.Topology

-- Function Spaces layer (Tier 6-9)
import FdrsFormal.FunctionSpaces

-- Number Theory layer (Tier 10-13) - NEW 2026-01-21
import FdrsFormal.NumberTheory

-- Integration layer (Phase 4) - NEW 2026-01-30
import FdrsFormal.Integration

-- Modes layer (Phases 5-6) - NEW 2026-01-30
import FdrsFormal.Modes

-- Composition layer (Phase 5) - NEW 2026-01-30
import FdrsFormal.Composition
