# FDRS Notation Reference

Auto-generated from Lean source files.

## Lean Notations

| Symbol | Expansion | File | Line | Scoped |
|--------|-----------|------|------|--------|
| `:50 c " ⟶[" e "] " Γ` | `ContextDynamics.step Γ c e` | FdrsFormal/Modes/ContextDependent/Evolution/ContextDynamics.lean | 74 |  |
| `:max Ω "[" c "]` | `ExtendedOracle.atContext Ω c` | FdrsFormal/Modes/ContextDependent/Basic/ExtendedOracle.lean | 70 |  |
| `c₀` | `InitialContext.initial` | FdrsFormal/Modes/ContextDependent/Basic/ContextSpace.lean | 62 |  |
| `P[" k "," L "]` | `finiteBlockProjection _ k L _` | FdrsFormal/FunctionSpaces/Commutant/FiniteProjection.lean | 84 | ✓ |
| `P_" L` | `blockProjection _ L` | FdrsFormal/FunctionSpaces/Projections/Definition.lean | 83 | ✓ |
| `pred` | `predecessor` | FdrsFormal/Operations/Predecessor/Correctness.lean | 52 |  |
| `r_" L` | `prefixValue _ L` | FdrsFormal/Core/PrefixValue.lean | 73 | ✓ |
| `r_" L` | `prefixResidue _ L` | FdrsFormal/Topology/PrefixCongruence/Definition.lean | 181 |  |
| `v_" p` | `padicValuation p` | FdrsFormal/NumberTheory/Valuations/Definition.lean | 63 |  |
| `Δ[" k "," L "]` | `finiteDetailOperator _ k L _` | FdrsFormal/FunctionSpaces/Commutant/FiniteProjection.lean | 97 | ✓ |
| `Δ_" L` | `detailOperator _ L` | FdrsFormal/FunctionSpaces/Projections/Details.lean | 70 | ✓ |
| `δ₁ " ⪰ " δ₂` | `metricDominance δ₁ δ₂` | FdrsFormal/Modes/VariableRadix/MetricComparison/Definition.lean | 61 |  |
| `ε` | `epsilon` | FdrsFormal/NumberTheory/ArithmeticFunctions/Definition.lean | 74 |  |
| `μ` | `moebius` | FdrsFormal/NumberTheory/ArithmeticFunctions/Definition.lean | 98 |  |
| `μ_" b` | `uniformProductMeasure b` | FdrsFormal/FunctionSpaces/Measure/ProductMeasure.lean | 144 | ✓ |
| `μ_k[" k "]` | `finiteUniformMeasure _ k` | FdrsFormal/FunctionSpaces/Commutant/FiniteHorizon.lean | 326 | ✓ |
| `μ²` | `squarefreeIndicator` | FdrsFormal/NumberTheory/ArithmeticFunctions/Definition.lean | 120 |  |
| `π_" L` | `prefixProjection _ L` | FdrsFormal/Topology/PrefixCongruence/Definition.lean | 174 |  |
| `ℱ_" L` | `cylinderAlgebra _ L` | FdrsFormal/Topology/Filtration/Definition.lean | 62 |  |
| `⊕ (infixl:65)` | `add` | FdrsFormal/Operations/Addition/Correctness.lean | 52 |  |
| `⊖ (infixl:65)` | `subtract` | FdrsFormal/Operations/Subtraction/Correctness.lean | 53 |  |
| `⋆ (local infixl:70)` | `dirichletConv` | FdrsFormal/NumberTheory/ArithmeticFunctions/DirichletConv.lean | 121 |  |
| `⋆ (local infixl:70)` | `dirichletConv` | FdrsFormal/NumberTheory/ArithmeticFunctions/MobiusInversion.lean | 46 |  |
| `𝟙` | `constantOne` | FdrsFormal/NumberTheory/ArithmeticFunctions/Definition.lean | 82 |  |

## Key Mathematical Symbols

| Symbol | Meaning | fdrs.md Ref |
|--------|---------|-------------|
| b_i | Radix at position i | Phase 1, Section 1 |
| D_i | Digit alphabet {0,...,b_i-1} | Phase 1, Section 1 |
| B_m | Cumulative radix product | Phase 1, Section 1 |
| R^(k) | Finite mixed-radix space | Def 1 |
| R^(∞)_fin | Direct-limit space | Def 3 |
| R̂ | Completed mixed-radix space | Def 7 |
| dec | Decoding map (ℛ → ℕ) | Def 2, 4 |
| enc | Encoding map (ℕ → ℛ) | Def 2, 4 |
| T(x) | Tick operator (successor) | Def 5, 6 |
| ⊕ | Addition on ℛ | Def 14, Prop 10 |
| ⊖ | Subtraction on ℛ (partial) | Def 13, Prop 9 |
| pred | Predecessor on ℛ | Def 12 |
| δ(x,y) | Ultrametric distance | Def 9, Prop 3 |
| U(s) | Cylinder set at prefix s | Def 8 |
| π_L | Prefix projection to depth L | Def 10 |
| r_L | Prefix residue / value | Def 11 |
| P_L | Block projection operator | Def 22, Prop 16 |
| Δ_L | Detail operator | Def 23, Prop 18 |
| 𝕋(V) | Mixed-radix tensor space | Phase 2 |
| ε | Dirichlet identity | Phase 3 |
| μ | Möbius function | Phase 3 |
| μ² | Squarefree indicator | Phase 3, Prop 40 |
| ⋆ | Dirichlet convolution | Phase 3 |
| v_p | p-adic valuation | Phase 3 |
| ω | Radix function (variable) | Phase 5, Def 57 |
| β_ω(s) | Odometer weight | Phase 5, Def 75-76 |
| δ_ω | Radix-induced ultrametric | Phase 6, Def 79 |
| Ω | Extended radix oracle | Phase 7, Def 85 |
| 𝒢 | Timeline graph | Phase 8, Def 108 |
| ρ | Routing function | Phase 8, Def 112 |
