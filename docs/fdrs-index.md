# FDRS Specification Index

Auto-generated from `data/fdrs-index.yaml` (2026-10-07T01:51:03.598833)

**532 items** from `docs/fdrs.md` (9146 lines)

Status: missing: 2 | proven: 528 | scaffold: 2

## Phase 1

| ID | Type | Number | Title | Line | Status | Lean File |
|---|---|---|---|---|---|---|
| definition_1 | definition | 1 | finite horizon space | 20 | ✅ proven | FdrsFormal/Core/Finite/Bijection.lean |
| definition_2 | definition | 2 | finite decoding / encoding | 28 | ✅ proven | FdrsFormal/Core/Finite/Bijection.lean |
| proposition_1 | proposition | 1 | representation theorem, finite case | 36 | ✅ proven | FdrsFormal/Core/Finite/Bijection.lean |
| definition_3 | definition | 3 | direct-limit space | 61 | ✅ proven | FdrsFormal/Core/Infinite/DirectLimit.lean |
| definition_4 | definition | 4 | unbounded decoding | 77 | ✅ proven | FdrsFormal/Core/Infinite/DirectLimit.lean |
| theorem_1 | theorem | 1 | order-theoretic isomorphism with (\mathbb N | 85 | ✅ proven | FdrsFormal/Core/Infinite/DirectLimit.lean |
| definition_5 | definition | 5 | Tick on finite horizon; partial successor | 101 | ✅ proven | FdrsFormal/Modes/VariableRadix/VariableTick/CarryAlgorithm.lean |
| proposition_2 | proposition | 2 | Tick corresponds to (+1 | 118 | ✅ proven | FdrsFormal/Composition/TimingBounds/Definition.lean |
| definition_6 | definition | 6 | Tick on the direct-limit space; total successor | 137 | ✅ proven | FdrsFormal/Core/Infinite/DirectLimit.lean |
| theorem_2 | theorem | 2 | Tick is total and matches successor on (\mathbb N | 145 | ✅ proven | FdrsFormal/Modes/ExtendedBase/CarryRouteUnification.lean |
| definition_7 | definition | 7 | completed mixed-radix space | 161 | ✅ proven | FdrsFormal/FunctionSpaces/Measure/ProductMeasure.lean |
| definition_8 | definition | 8 | cylinder sets | 169 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| definition_9 | definition | 9 | ultrametric | 176 | ✅ proven | FdrsFormal/Modes/VariableRadix/InducedUltrametric/Axioms.lean |
| proposition_3 | proposition | 3 | (\delta | 188 | ✅ proven | FdrsFormal/Topology/Ultrametric/Definition.lean |
| proposition_4 | proposition | 4 | open balls are cylinders; cylinders form a clopen  | 208 | ✅ proven | FdrsFormal/Topology/Ultrametric/Definition.lean |
| proposition_5 | proposition | 5 | cylinders correspond to congruence classes under d | 223 | ✅ proven | FdrsFormal/FunctionSpaces/LocalOperators/Definition.lean |
| definition_10 | definition | 10 | prefix projection | 274 | ✅ proven | FdrsFormal/Topology/PrefixCongruence/Definition.lean |
| definition_11 | definition | 11 | prefix residue map | 282 | ✅ proven | FdrsFormal/Core/PrefixValue.lean |
| proposition_6 | proposition | 6 | prefix–congruence equivalence on (\mathcal R | 291 | ✅ proven | FdrsFormal/Core/PrefixValue.lean |
| definition_12 | definition | 12 | predecessor on (\mathcal R | 310 | ✅ proven | FdrsFormal/Operations/Predecessor/Correctness.lean |
| proposition_7 | proposition | 7 | decoded correctness | 318 | ✅ proven | FdrsFormal/Operations/Predecessor/Correctness.lean |
| proposition_8 | proposition | 8 | borrow algorithm equals (\operatorname{pred} | 327 | ✅ proven | FdrsFormal/Operations/Predecessor/Correctness.lean |
| definition_13 | definition | 13 | subtraction; partial | 365 | ✅ proven | FdrsFormal/Operations/Subtraction/Correctness.lean |
| proposition_9 | proposition | 9 | correctness + basic laws | 372 | ✅ proven | FdrsFormal/Operations/Subtraction/Correctness.lean |
| definition_14 | definition | 14 | addition on (\mathcal R | 391 | ✅ proven | FdrsFormal/Operations/Addition/Correctness.lean |
| proposition_10 | proposition | 10 | decoded correctness | 398 | ✅ proven | FdrsFormal/Operations/Addition/Correctness.lean |
| theorem_3 | theorem | 3 | ((\mathcal R,\oplus | 407 | ✅ proven | FdrsFormal/Operations/Addition/Correctness.lean |
| proposition_11 | proposition | 11 | carry locality at depth (L | 420 | ✅ proven | FdrsFormal/Integration/Complexity/Definition.lean |
| proposition_12 | proposition | 12 | Tick preserves prefixes | 451 | ✅ proven | FdrsFormal/Topology/Continuity/Operations.lean |
| corollary_1 | corollary | 1 | Tick is 1-Lipschitz | 458 | ✅ proven | FdrsFormal/Topology/Continuity/Operations.lean |
| proposition_13 | proposition | 13 | predecessor is 1-Lipschitz on its domain | 468 | ✅ proven | FdrsFormal/Operations/Predecessor/Locality.lean |
| proposition_14 | proposition | 14 | translation invariance on prefixes | 479 | ✅ proven | FdrsFormal/Topology/Continuity/Operations.lean |
| corollary_2 | corollary | 2 | addition is 1-Lipschitz in each input | 491 | ✅ proven | FdrsFormal/Topology/Continuity/Operations.lean |
| corollary_3 | corollary | 3 | finite dependence / multi-rate execution | 510 | ✅ proven | FdrsFormal/Topology/Locality/Properties.lean |
## Phase 2

| ID | Type | Number | Title | Line | Status | Lean File |
|---|---|---|---|---|---|---|
| definition_15 | definition | 15 | prefix index set | 549 | ✅ proven | FdrsFormal/FunctionSpaces/Basic/PrefixSet.lean |
| definition_16 | definition | 16 | cylinders | 557 | ✅ proven | FdrsFormal/FunctionSpaces/Basic/Cylinder.lean |
| definition_17 | definition | 17 | filtration of (\sigma | 565 | ✅ proven | FdrsFormal/Topology/Filtration/Definition.lean |
| definition_18 | definition | 18 | mixed-radix tensor space | 581 | ✅ proven | FdrsFormal/FunctionSpaces/Basic/TensorSpace.lean |
| definition_19 | definition | 19 | block-constant subspaces | 589 | ✅ proven | FdrsFormal/FunctionSpaces/Basic/BlockConstant.lean |
| proposition_15 | proposition | 15 | finite block coordinate representation | 597 | ✅ proven | FdrsFormal/FunctionSpaces.lean |
| definition_20 | definition | 20 | refinement embeddings | 607 | ✅ proven | FdrsFormal/FunctionSpaces/Basic/Refinement.lean |
| definition_21 | definition | 21 | uniform product measure | 621 | ✅ proven | FdrsFormal/FunctionSpaces/Measure/ProductMeasure.lean |
| definition_22 | definition | 22 | block projection (P_L | 628 | ✅ proven | FdrsFormal/FunctionSpaces/Projections/Definition.lean |
| proposition_16 | proposition | 16 | projection / tower properties | 640 | ✅ proven | FdrsFormal/FunctionSpaces.lean |
| proposition_17 | proposition | 17 | compatibility with block coordinates | 650 | ✅ proven | FdrsFormal/FunctionSpaces.lean |
| definition_23 | definition | 23 | detail operators | 660 | ✅ proven | FdrsFormal/FunctionSpaces.lean |
| proposition_18 | proposition | 18 | telescoping identity | 668 | ✅ proven | FdrsFormal/FunctionSpaces.lean |
| theorem_4 | theorem | 4 | convergence to (f | 681 | ✅ proven | FdrsFormal/FunctionSpaces.lean |
| definition_24 | definition | 24 | prefix locality of an operator | 705 | ✅ proven | FdrsFormal/FunctionSpaces.lean |
| proposition_19 | proposition | 19 | basic examples | 714 | ✅ proven | FdrsFormal/FunctionSpaces.lean |
| proposition_20 | proposition | 20 | phase-locked activation as clopen gating | 726 | ✅ proven | FdrsFormal/FunctionSpaces/LocalOperators/Definition.lean |
| definition_25 | definition | 25 | finite prefix sets and cylinders | 794 | ✅ proven | FdrsFormal/FunctionSpaces/Commutant/FiniteHorizon.lean |
| definition_26 | definition | 26 | uniform measure on (\mathcal R^{(k | 805 | ✅ proven | FdrsFormal/FunctionSpaces/Commutant/FiniteHorizon.lean |
| definition_27 | definition | 27 | finite block projection | 824 | ✅ proven | FdrsFormal/FunctionSpaces/Commutant/FiniteProjection.lean |
| definition_28 | definition | 28 | finite detail operator | 834 | ✅ proven | FdrsFormal/FunctionSpaces/Commutant/FiniteProjection.lean |
| proposition_21 | proposition | 21 | projection algebra | 841 | ✅ proven | FdrsFormal/FunctionSpaces.lean |
| proposition_22 | proposition | 22 | coordinate split into prefix/suffix | 855 | ✅ proven | FdrsFormal/FunctionSpaces/Projections/CoordinateSplit.lean |
| proposition_23 | proposition | 23 | explicit fiberwise averaging | 863 | ✅ proven | FdrsFormal/FunctionSpaces/Projections/CoordinateSplit.lean |
| theorem_5 | theorem | 5 | (P^{(k | 877 | ✅ proven | FdrsFormal/FunctionSpaces.lean |
| corollary_4 | corollary | 4 | detail operator bound | 896 | ✅ proven | FdrsFormal/FunctionSpaces.lean |
| proposition_24 | proposition | 24 | gates are contractions | 903 | ✅ proven | FdrsFormal/FunctionSpaces.lean |
| proposition_25 | proposition | 25 | (L^2 | 914 | ✅ proven | FdrsFormal/FunctionSpaces.lean |
| lemma_1 | lemma | 1 | eigenspace decomposition | 942 | ✅ proven | FdrsFormal/FunctionSpaces/Projections/CoordinateSplit.lean |
| theorem_6 | theorem | 6 | commutation ⇔ invariance of coarse/detail subspace | 955 | ✅ proven | FdrsFormal/FunctionSpaces.lean |
| corollary_5 | corollary | 5 | block form | 978 | ✅ proven | FdrsFormal/FunctionSpaces.lean |
| definition_29 | definition | 29 | truncation / embedding | 1009 | ✅ proven | FdrsFormal/FunctionSpaces.lean |
| proposition_26 | proposition | 26 | projection compatibility | 1014 | ✅ proven | FdrsFormal/FunctionSpaces.lean |
| definition_30 | definition | 30 | coarse subspaces | 1054 | ✅ proven | FdrsFormal/FunctionSpaces.lean |
| definition_31 | definition | 31 | detail subspaces | 1068 | ✅ proven | FdrsFormal/FunctionSpaces.lean |
| proposition_27 | proposition | 27 | orthogonal increment projection | 1076 | ✅ proven | FdrsFormal/FunctionSpaces.lean |
| theorem_7 | theorem | 7 | multiresolution decomposition | 1086 | ✅ proven | FdrsFormal/FunctionSpaces.lean |
| corollary_6 | corollary | 6 | dimensions | 1099 | ✅ proven | FdrsFormal/FunctionSpaces.lean |
| lemma_2 | lemma | 2 | commutation ⇔ invariance of each (C_L | 1116 | ✅ proven | FdrsFormal/FunctionSpaces.lean |
| theorem_8 | theorem | 8 | multi-level commutation ⇔ block diagonal on the mu | 1125 | ✅ proven | FdrsFormal/FunctionSpaces.lean |
| definition_32 | definition | 32 | linear (L | 1163 | ✅ proven | FdrsFormal/FunctionSpaces.lean |
| proposition_28 | proposition | 28 | matrix/kernel characterization of (L | 1170 | ✅ proven | FdrsFormal/FunctionSpaces.lean |
| proposition_29 | proposition | 29 | commutation with (P^{(k | 1181 | ✅ proven | FdrsFormal/FunctionSpaces.lean |
| proposition_30 | proposition | 30 | (L | 1187 | ✅ proven | FdrsFormal/FunctionSpaces.lean |
| theorem_9 | theorem | 9 | intersection: (L | 1198 | ✅ proven | FdrsFormal/FunctionSpaces.lean |
| definition_33 | definition | 33 | cyclic Tick on (\mathcal R^{(k | 1219 | ✅ proven | FdrsFormal/FunctionSpaces.lean |
| definition_34 | definition | 34 | pullback on functions | 1227 | ✅ proven | FdrsFormal/FunctionSpaces.lean |
| proposition_31 | proposition | 31 | measure preservation and isometries | 1234 | ✅ proven | FdrsFormal/FunctionSpaces.lean |
| proposition_32 | proposition | 32 | cylinders are permuted | 1243 | ✅ proven | FdrsFormal/FunctionSpaces.lean |
| theorem_10 | theorem | 10 | Tick pullback commutes with all block projections | 1253 | ✅ proven | FdrsFormal/FunctionSpaces.lean |
| corollary_7 | corollary | 7 | scale invariance under Tick | 1266 | ✅ proven | FdrsFormal/FunctionSpaces.lean |
| lemma_3 | lemma | 3 | existence of a mean-zero orthonormal contrast basi | 1306 | ✅ proven | FdrsFormal/FunctionSpaces/Haar.lean |
| definition_35 | definition | 35 | global mixed-radix Haar atoms | 1330 | ✅ proven | FdrsFormal/FunctionSpaces/Haar.lean |
| theorem_11 | theorem | 11 | orthonormal basis | 1346 | ✅ proven | FdrsFormal/FunctionSpaces/Haar.lean |
| definition_36 | definition | 36 | support level of a basis atom | 1358 | ✅ proven | FdrsFormal/FunctionSpaces/Haar.lean |
| proposition_33 | proposition | 33 | how (P^{(k | 1366 | ✅ proven | FdrsFormal/FunctionSpaces/Haar.lean |
| corollary_8 | corollary | 8 | explicit description of scale subspaces (D_L | 1379 | ✅ proven | FdrsFormal/FunctionSpaces/Haar.lean |
| theorem_12 | theorem | 12 | diagonal-by-scale structure in Haar coordinates | 1405 | ✅ proven | FdrsFormal/FunctionSpaces/Haar.lean |
| corollary_9 | corollary | 9 | commutant algebra is a direct product of full matr | 1415 | ✅ proven | FdrsFormal/FunctionSpaces/Haar.lean |
| gate_1 | gate | 1 | Scale projections | 1440 | ✅ proven | FdrsFormal/FunctionSpaces/Commutant/OperatorAlgebra.lean |
| gate_2 | gate | 2 | Cylinder gates (phase-locked activation | 1448 | ✅ proven | FdrsFormal/FunctionSpaces/Commutant/OperatorAlgebra.lean |
| definition_37 | definition | 37 | digit permutation operator | 1480 | ✅ proven | FdrsFormal/FunctionSpaces/LocalOperators/DigitPermutation.lean |
| proposition_34 | proposition | 34 | permutations preserve measure and norms | 1488 | ✅ proven | FdrsFormal/FunctionSpaces/LocalOperators/DigitPermutation.lean |
| proposition_35 | proposition | 35 | commutation behavior with (P^{(k | 1494 | ✅ proven | FdrsFormal/FunctionSpaces/LocalOperators/DigitPermutation.lean |
| definition_38 | definition | 38 | generated operator algebra | 1510 | ✅ proven | FdrsFormal/FunctionSpaces/Commutant/OperatorAlgebra.lean |
| proposition_36 | proposition | 36 | basic closure and stability | 1521 | ✅ proven | FdrsFormal/FunctionSpaces/Commutant/OperatorAlgebra.lean |
| proposition_37 | proposition | 37 | multi-rate determinism | 1533 | ✅ proven | FdrsFormal/FunctionSpaces/Commutant/OperatorAlgebra.lean |
## Phase 3

| ID | Type | Number | Title | Line | Status | Lean File |
|---|---|---|---|---|---|---|
| proposition_38 | proposition | 38 | (\mathcal R^{(k | 1594 | ✅ proven | FdrsFormal/NumberTheory/ArithmeticFunctions/CyclicConvolution.lean |
| theorem_13 | theorem | 13 | closure, associativity, commutativity, identity | 1604 | ✅ proven | FdrsFormal/NumberTheory/ArithmeticFunctions/CyclicConvolution.lean |
| theorem_14 | theorem | 14 | Dirichlet algebra | 1622 | ✅ proven | FdrsFormal/NumberTheory.lean |
| proposition_39 | proposition | 39 | representation | 1637 | ✅ proven | FdrsFormal/NumberTheory.lean |
| theorem_15 | theorem | 15 | Möbius inversion | 1667 | ✅ proven | FdrsFormal/NumberTheory.lean |
| proposition_40 | proposition | 40 | idempotence | 1687 | ✅ proven | FdrsFormal/NumberTheory.lean |
| corollary_10 | corollary | 10 | tensor Möbius inversion | 1735 | ✅ proven | FdrsFormal/NumberTheory.lean |
| proposition_41 | proposition | 41 | additive orthogonality | 1812 | ✅ proven | FdrsFormal/NumberTheory.lean |
| proposition_42 | proposition | 42 | residue-class projector via additive characters | 1820 | ✅ proven | FdrsFormal/NumberTheory.lean |
| theorem_16 | theorem | 16 | convolution theorem | 1840 | ✅ proven | FdrsFormal/NumberTheory.lean |
| theorem_119 | theorem | 119 | the triangular phase | 1862 | ✅ proven | FdrsFormal/NumberTheory/Characters/MixedRadixFFT.lean |
| corollary_32 | corollary | 32 | Vilenkin character × twiddle kernel | 1874 | ✅ proven | FdrsFormal/NumberTheory/Characters/MixedRadixFFT.lean |
| proposition_154 | proposition | 154 | the twiddle boundary | 1887 | ✅ proven | FdrsFormal/NumberTheory/Characters/MixedRadixFFT.lean |
| proposition_155 | proposition | 155 | stage locality | 1896 | ✅ proven | FdrsFormal/NumberTheory/Characters/MixedRadixFFT.lean |
| proposition_43 | proposition | 43 | orthogonality over units | 1923 | ✅ proven | FdrsFormal/NumberTheory.lean |
| proposition_44 | proposition | 44 | orthogonality over characters gives residue projec | 1931 | ✅ proven | FdrsFormal/NumberTheory.lean |
| proposition_45 | proposition | 45 | character expansion of residue projectors | 1954 | ✅ proven | FdrsFormal/NumberTheory.lean |
| proposition_46 | proposition | 46 | residue projectors factor | 1975 | ✅ proven | FdrsFormal/NumberTheory.lean |
| proposition_47 | proposition | 47 | Dirichlet characters factor | 1990 | ✅ proven | FdrsFormal/NumberTheory.lean |
| corollary_11 | corollary | 11 | projectors factor | 1999 | ✅ proven | FdrsFormal/NumberTheory.lean |
| definition_39 | definition | 39 | radix depth of a modulus | 2014 | ✅ proven | FdrsFormal/NumberTheory.lean |
| theorem_17 | theorem | 17 | additive residue classes are (\mathcal F_{k,L} | 2024 | ✅ proven | FdrsFormal/NumberTheory.lean |
| corollary_12 | corollary | 12 | same for (\mathrm{nat}_k | 2043 | ✅ proven | FdrsFormal/NumberTheory.lean |
| theorem_18 | theorem | 18 | Dirichlet characters become cylinder-measurable wh | 2049 | ✅ proven | FdrsFormal/NumberTheory.lean |
| definition_40 | definition | 40 | divisibility projector | 2114 | ✅ proven | FdrsFormal/NumberTheory.lean |
| definition_41 | definition | 41 | exact valuation projector | 2121 | ✅ proven | FdrsFormal/NumberTheory.lean |
| proposition_48 | proposition | 48 | orthogonal idempotents; partition of unity | 2129 | ✅ proven | FdrsFormal/NumberTheory.lean |
| proposition_49 | proposition | 49 | cylinder measurability criterion | 2143 | ✅ proven | FdrsFormal/NumberTheory.lean |
| corollary_13 | corollary | 13 | valuation gates at finite depth | 2153 | ✅ proven | FdrsFormal/NumberTheory.lean |
| definition_42 | definition | 42 |  | 2169 | ✅ proven | FdrsFormal/NumberTheory.lean |
| proposition_50 | proposition | 50 | idempotence | 2177 | ✅ proven | FdrsFormal/NumberTheory.lean |
| theorem_19 | theorem | 19 | squarefree projector as finite product of divisibi | 2187 | ✅ proven | FdrsFormal/NumberTheory.lean |
| corollary_14 | corollary | 14 | when squarefree is cylinder-measurable at some dep | 2201 | ✅ proven | FdrsFormal/NumberTheory.lean |
| theorem_20 | theorem | 20 | twist–transform covariance | 2220 | ✅ proven | FdrsFormal/NumberTheory/Characters/TwistTransform.lean |
| corollary_15 | corollary | 15 | true commutation criterion | 2236 | ✅ proven | FdrsFormal/NumberTheory/Characters/TwistTransform.lean |
| definition_43 | definition | 43 | pure (p | 2245 | ✅ proven | FdrsFormal/NumberTheory/FactorizationLens/PowerKernel.lean |
| theorem_21 | theorem | 21 | valuation-fiber Toeplitz action | 2249 | ✅ proven | FdrsFormal/NumberTheory/FactorizationLens/PowerKernel.lean |
| proposition_51 | proposition | 51 | generic failure of commutation with additive block | 2269 | ✅ proven | FdrsFormal/NumberTheory/CylinderMeasurability.lean |
| definition_44 | definition | 44 | multiplicative sigma-algebra at depth (E | 2343 | ✅ proven | FdrsFormal/NumberTheory/FactorizationLens/ValuationAlgebra.lean |
| proposition_52 | proposition | 52 | periodicity of divisibility | 2363 | ✅ proven | FdrsFormal/NumberTheory.lean |
| theorem_22 | theorem | 22 | exponent convolution isomorphism | 2407 | ✅ proven | FdrsFormal/NumberTheory.lean |
| theorem_23 | theorem | 23 | factorization-fiber decomposition | 2433 | ✅ proven | FdrsFormal/NumberTheory.lean |
| corollary_16 | corollary | 16 | explicit valuation-lattice update rule | 2446 | ✅ proven | FdrsFormal/NumberTheory.lean |
| definition_45 | definition | 45 | augmented factorization state | 2468 | ✅ proven | FdrsFormal/NumberTheory/FactorizationLens/MarkovProperty.lean |
| proposition_53 | proposition | 53 | Dirichlet transforms are local/Markov on (\Lambda_ | 2478 | ✅ proven | FdrsFormal/NumberTheory/FactorizationLens/MarkovProperty.lean |
| proposition_54 | proposition | 54 | squarefree constraint on the (P | 2498 | ✅ proven | FdrsFormal/NumberTheory/FactorizationLens/SquarefreeOnLattice.lean |
| proposition_55 | proposition | 55 | Möbius on (P | 2508 | ✅ proven | FdrsFormal/NumberTheory/FactorizationLens/SquarefreeOnLattice.lean |
## Phase 4

| ID | Type | Number | Title | Line | Status | Lean File |
|---|---|---|---|---|---|---|
| definition_46 | definition | 46 | prime-set lens | 2570 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| lemma_4 | lemma | 4 | multiplication inside the Dirichlet basis | 2593 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| proposition_56 | proposition | 56 | representation of Dirichlet convolution | 2621 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| theorem_24 | theorem | 24 | monoid homomorphism: multiplication ↔ composition | 2647 | ✅ proven | FdrsFormal/Integration/Programs/IntegerSemantics.lean |
| corollary_17 | corollary | 17 | prime-power instruction set | 2665 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| definition_47 | definition | 47 | (P | 2681 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| theorem_25 | theorem | 25 | lens-locality: (P | 2689 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| definition_48 | definition | 48 | execution set / rhythm of (n | 2712 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| proposition_57 | proposition | 57 | periodicity on the integer line | 2720 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| proposition_58 | proposition | 58 | finite-depth cylinder realization when (n\mid B_L | 2729 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| definition_49 | definition | 49 | truncated Dirichlet product | 2781 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| proposition_59 | proposition | 59 | algebra laws | 2789 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| definition_50 | definition | 50 | compiled program operator | 2817 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| proposition_60 | proposition | 60 | representation / homomorphism | 2824 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| proposition_61 | proposition | 61 | multiplication = composition on basis programs | 2861 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| definition_51 | definition | 51 | divisor gate / rhythm | 2893 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| theorem_26 | theorem | 26 | compiled execution law | 2900 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| corollary_18 | corollary | 18 | causality / triangularity | 2912 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| theorem_27 | theorem | 27 | fiberwise locality of (P | 2932 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| corollary_19 | corollary | 19 | valuation-lattice convolution form | 2950 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| proposition_62 | proposition | 62 | finite-depth cylinder criterion | 2970 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| proposition_63 | proposition | 63 | projection algebra for a fixed modulus | 3039 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| proposition_64 | proposition | 64 | character expansion = Fourier probe form | 3052 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| theorem_28 | theorem | 28 | Möbius inversion as operator inverse | 3081 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| proposition_65 | proposition | 65 | projection + prime-square factorization | 3105 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| theorem_29 | theorem | 29 | CRT identity | 3132 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| definition_52 | definition | 52 | general sieve filter | 3149 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| proposition_66 | proposition | 66 | idempotence + monotonic refinement | 3160 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| example_1 | example | 1 | squarefree as a sieve | 3172 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| proposition_67 | proposition | 67 | diagonal subalgebra closure | 3188 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| proposition_68 | proposition | 68 | Dirichlet core closure | 3196 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| proposition_69 | proposition | 69 | spectral interaction law with multiplicative probe | 3204 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| definition_53 | definition | 53 | lift to cylinder-constant functions | 3287 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| definition_54 | definition | 54 | restriction as conditional expectation / block ave | 3295 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| proposition_70 | proposition | 70 | lift/restrict coherence | 3309 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| definition_55 | definition | 55 | coherent hierarchical memory | 3330 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| proposition_71 | proposition | 71 | equivalence with a single fine state | 3341 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| proposition_72 | proposition | 72 | depth-(L | 3363 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| corollary_20 | corollary | 20 | induced block operator | 3378 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| proposition_73 | proposition | 73 | closure under products and linear combinations | 3412 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| corollary_21 | corollary | 21 | CRTCompose is depth-max | 3426 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| definition_56 | definition | 56 | support of a gate at depth (L | 3443 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| proposition_74 | proposition | 74 | sparse update on block memory | 3450 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| proposition_75 | proposition | 75 | prefix odometer | 3480 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| proposition_76 | proposition | 76 | block-lift evaluation cost | 3537 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| proposition_77 | proposition | 77 | active block count | 3555 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| proposition_78 | proposition | 78 | per-fiber update cost | 3690 | ✅ proven | FdrsFormal/Integration/Complexity/Definition.lean |
| corollary_22 | corollary | 22 | global valuation-local cost | 3701 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| gate_3 | gate | 3 | Diagonal gates (constraints / phase | 3816 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| gate_4 | gate | 4 | Dirichlet transforms (compiled programs | 3829 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| proposition_79 | proposition | 79 | closure of guarded instructions | 3916 | ✅ proven | FdrsFormal/Integration/BlockMemory/Definition.lean |
| corollary_23 | corollary | 23 | Markov locality | 3990 | ✅ proven | FdrsFormal/Modes/VariableRadix/Basic/Basic.lean |
## Phase 5

| ID | Type | Number | Title | Line | Status | Lean File |
|---|---|---|---|---|---|---|
| definition_57 | definition | 57 | branching function / radix law | 4024 | ✅ proven | FdrsFormal/Modes/VariableRadix/Basic/RadixLaw.lean |
| definition_58 | definition | 58 | cylinder sets | 4068 | ✅ proven | FdrsFormal/Modes/VariableRadix/InducedUltrametric/CylinderBalls.lean |
| definition_59 | definition | 59 | prefix metric | 4078 | ✅ proven | FdrsFormal/Modes/VariableRadix/Encoding/Encoding.lean |
| proposition_80 | proposition | 80 | ultrametric | 4089 | ✅ proven | FdrsFormal/Modes/VariableRadix/Encoding/Bijection.lean |
| corollary_24 | corollary | 24 | cylinders are clopen and form a basis | 4102 | ✅ proven | FdrsFormal/Modes/VariableRadix/VariableTick/Definition.lean |
| definition_60 | definition | 60 | lex order | 4116 | ✅ proven | FdrsFormal/Modes/VariableRadix/Encoding/LexOrder.lean |
| definition_61 | definition | 61 | completion counts | 4124 | ✅ proven | FdrsFormal/Modes/VariableRadix/Encoding/SubtreeCards.lean |
| definition_62 | definition | 62 | variable-base rank / decoding | 4139 | ✅ proven | FdrsFormal/Modes/VariableRadix/Encoding/Ranking.lean |
| theorem_30 | theorem | 30 | order-isomorphism to an integer interval | 4148 | ✅ proven | FdrsFormal/Modes/VariableRadix/VariableTick/Termination.lean |
| definition_63 | definition | 63 | finite-depth Tick, partial form | 4167 | ✅ proven | FdrsFormal/Modes/VariableRadix/VariableTick/Definition.lean |
| definition_64 | definition | 64 | finite-depth cyclic Tick | 4175 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/CoupledSystem.lean |
| theorem_31 | theorem | 31 | Tick equals +1 in rank coordinates | 4204 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/CoupledSystem.lean |
| definition_65 | definition | 65 | maximal path | 4223 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/CoupledSystem.lean |
| definition_66 | definition | 66 | infinite Tick, partial | 4231 | ✅ proven | FdrsFormal/Modes/VariableRadix/VariableTick/Definition.lean |
| proposition_81 | proposition | 81 | no infinite carry | 4235 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/CoupledSystem.lean |
| corollary_25 | corollary | 25 | well-founded tick index from a start state | 4243 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/CoupledSystem.lean |
| proposition_82 | proposition | 82 | Tick computability | 4263 | ✅ proven | FdrsFormal/Integration/Complexity/Definition.lean |
| definition_67 | definition | 67 | prefix-determined radix law | 4317 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/CoupledSystem.lean |
| theorem_32 | theorem | 32 | well-defined successor; no carry loops | 4323 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/CoupledSystem.lean |
| definition_68 | definition | 68 | chart / reindexing isomorphism | 4345 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/CoupledSystem.lean |
| theorem_33 | theorem | 33 | transport principle | 4359 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/CoupledSystem.lean |
| definition_69 | definition | 69 | rechart map | 4380 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/CoupledSystem.lean |
| proposition_83 | proposition | 83 | coherent composition across changing radices | 4389 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/CoupledSystem.lean |
| definition_70 | definition | 70 | augmented state for variable-radix time | 4418 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/CoupledSystem.lean |
| theorem_34 | theorem | 34 | Markov property | 4439 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/CoupledSystem.lean |
| proposition_84 | proposition | 84 | finite-horizon DP always works | 4454 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/CoupledSystem.lean |
| proposition_85 | proposition | 85 | infinite-horizon contraction condition | 4468 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/CoupledSystem.lean |
| definition_71 | definition | 71 | radix chart | 4532 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/CoupledSystem.lean |
| definition_72 | definition | 72 | chart-invariant Tick | 4545 | ✅ proven | FdrsFormal/Modes/VariableRadix/Basic/VariableSpace.lean |
| theorem_35 | theorem | 35 | semantic stability under radix changes | 4558 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/CoupledSystem.lean |
| definition_73 | definition | 73 | arithmetic-cylinder property at depth (L | 4593 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/CoupledSystem.lean |
| proposition_86 | proposition | 86 | prefix-relative modulus appearance | 4606 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/CoupledSystem.lean |
| corollary_26 | corollary | 26 | global modulus-by-depth | 4640 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/CoupledSystem.lean |
| theorem_36 | theorem | 36 | Markov property | 4667 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/CoupledSystem.lean |
| theorem_37 | theorem | 37 | STOK/DP recursion viability under variable radices | 4689 | ✅ proven | FdrsFormal/Modes/VariableRadix/SiblingUniformity/Definition.lean |
| definition_74 | definition | 74 | Sibling-uniform suffix counts, SU | 4760 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/CoupledSystem.lean |
| proposition_87 | proposition | 87 | SU ⇔ constant block sizes at each node | 4771 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/CoupledSystem.lean |
| definition_75 | definition | 75 | local modulus / place value along a prefix | 4790 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/CoupledSystem.lean |
| definition_76 | definition | 76 | odometer decoding | 4803 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/CoupledSystem.lean |
| theorem_38 | theorem | 38 | SU ⇒ arithmetic cylinders with modulus (\beta_\ome | 4819 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/CoupledSystem.lean |
| corollary_27 | corollary | 27 | prefix-relative modulus appearance | 4853 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/CoupledSystem.lean |
| proposition_88 | proposition | 88 | level-only bases ⇒ (\beta_\omega(s | 4869 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/CoupledSystem.lean |
| definition_77 | definition | 77 | Dual-Filtration Machine state | 4993 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/CoupledSystem.lean |
| definition_78 | definition | 78 | one step of Dual-Filtration Machine | 5087 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/CoupledSystem.lean |
| theorem_39 | theorem | 39 | combined locality bound | 5120 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/CoupledSystem.lean |
| proposition_89 | proposition | 89 | closure under composition | 5154 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/CoupledSystem.lean |
## Phase 6

| ID | Type | Number | Title | Line | Status | Lean File |
|---|---|---|---|---|---|---|
| definition_79 | definition | 79 | Radix-induced ultrametric | 5203 | ✅ proven | FdrsFormal/Modes/ExtendedBase/Definition.lean |
| definition_80 | definition | 80 | Ultrametric spectrum | 5220 | ✅ proven | FdrsFormal/Modes/VariableRadix/MetricComparison.lean |
| theorem_40 | theorem | 40 | SU implies proper ultrametric | 5234 | ✅ proven | FdrsFormal/Modes/VariableRadix/MetricComparison.lean |
| proposition_90 | proposition | 90 | Cylinders are ultrametric balls | 5261 | ✅ proven | FdrsFormal/Modes/VariableRadix/Design.lean |
| definition_81 | definition | 81 | Metric dominance | 5284 | ✅ proven | FdrsFormal/Modes/VariableRadix/Design.lean |
| theorem_41 | theorem | 41 | Metric spectrum forms a preorder | 5296 | ✅ proven | FdrsFormal/Modes/VariableRadix/MetricComparison/Properties.lean |
| definition_82 | definition | 82 | Multi-metric observer complex | 5415 | ✅ proven | FdrsFormal/Modes/VariableRadix/MultiMetric/ObserverComplex.lean |
| definition_83 | definition | 83 | Metric projection | 5430 | ✅ proven | FdrsFormal/Modes/VariableRadix/MultiMetric/Projection.lean |
| theorem_42 | theorem | 42 | Residual as metric discrepancy | 5442 | ✅ proven | FdrsFormal/Modes/VariableRadix/MultiMetric/Residual.lean |
| theorem_43 | theorem | 43 | Realizability criterion for ultrametrics | 5458 | ✅ proven | FdrsFormal/Modes/ExtendedBase/Definition.lean |
| corollary_28 | corollary | 28 | Non-realizable ultrametrics | 5514 | ✅ proven | FdrsFormal/Modes/ContextDependent/Basic/Basic.lean |
| theorem_44 | theorem | 44 | Locality bounds under designed metrics | 5525 | ✅ proven | FdrsFormal/Modes/ContextDependent/Basic/Basic.lean |
| proposition_91 | proposition | 91 | SU ⟹ proper ultrametric | 5550 | ✅ proven | FdrsFormal/Modes/ContextDependent/Evolution/ContextDynamics.lean |
| proposition_92 | proposition | 92 | Cylinders are balls | 5552 | ✅ proven | FdrsFormal/Modes/ContextDependent/Evolution/Evolution.lean |
| proposition_93 | proposition | 93 | Spectrum forms preorder | 5554 | ✅ proven | FdrsFormal/Modes/ContextDependent/Evolution/Evolution.lean |
| proposition_94 | proposition | 94 | Volume prescription | 5556 | ✅ proven | FdrsFormal/Modes/ContextDependent/Evolution/Evolution.lean |
| proposition_95 | proposition | 95 | Multi-metric observers | 5558 | ✅ proven | FdrsFormal/Modes/ContextDependent/Evolution/Evolution.lean |
| proposition_96 | proposition | 96 | Realizability criterion | 5560 | ✅ proven | FdrsFormal/Modes/ContextDependent/Evolution/Evolution.lean |
| proposition_97 | proposition | 97 | Custom locality | 5562 | ✅ proven | FdrsFormal/Modes/ContextDependent/Evolution/Evolution.lean |
## Phase 7

| ID | Type | Number | Title | Line | Status | Lean File |
|---|---|---|---|---|---|---|
| definition_84 | definition | 84 | Context space | 5589 | ✅ proven | FdrsFormal/Modes/ContextDependent/Evolution/Evolution.lean |
| definition_85 | definition | 85 | Extended radix oracle | 5607 | ✅ proven | FdrsFormal/Modes/ContextDependent/Realization/Realization.lean |
| definition_86 | definition | 86 | Contextual sibling uniformity - CSU | 5619 | ✅ proven | FdrsFormal/Modes/ContextDependent/Realization/Realization.lean |
| definition_87 | definition | 87 | Context-indexed mixed-radix family | 5631 | ✅ proven | FdrsFormal/Modes/ContextDependent/Basic/ExtendedOracle.lean |
| definition_88 | definition | 88 | Context dynamics | 5648 | ✅ proven | FdrsFormal/Modes/ContextDependent/Preservation/DepthL.lean |
| definition_89 | definition | 89 | Stateful context-dependent system | 5660 | ✅ proven | FdrsFormal/Modes/ContextDependent/Preservation/OperatorPreserved.lean |
| definition_90 | definition | 90 | Trace of a stateful system | 5684 | ✅ proven | FdrsFormal/Modes/ContextDependent/Preservation/MonotoneRefinement.lean |
| theorem_45 | theorem | 45 | Context-switching preserves SU | 5697 | ✅ proven | FdrsFormal/Modes/ContextDependent/Evolution/Preservation.lean |
| definition_91 | definition | 91 | Operational semantic modes | 5709 | ✅ proven | FdrsFormal/Modes/ContextDependent/Realization/SemanticModes.lean |
| definition_92 | definition | 92 | Lazy vs eager realization | 5721 | ✅ proven | FdrsFormal/Modes/ContextDependent/Variations/MultiAgent.lean |
| theorem_46 | theorem | 46 | Lazy-eager semantic equivalence | 5737 | ✅ proven | FdrsFormal/Modes/ContextDependent/Variations/MultiAgent.lean |
| definition_93 | definition | 93 | Structure-preserving context transition | 5749 | ✅ proven | FdrsFormal/Modes/ContextDependent/Variations/MultiAgent.lean |
| theorem_47 | theorem | 47 | Depth-L operators preserved | 5759 | ✅ proven | FdrsFormal/Modes/ContextDependent/Variations/MultiAgent.lean |
| definition_94 | definition | 94 | Monotone context refinement | 5780 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/Definition.lean |
| proposition_98 | proposition | 98 | Metric dominance under refinement | 5790 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/Definition.lean |
| definition_95 | definition | 95 | Multi-context observer complex | 5804 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/Definition.lean |
| definition_96 | definition | 96 | Context-dependent schedule | 5817 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/Definition.lean |
| definition_97 | definition | 97 | Context coupling maps | 5829 | ✅ proven | FdrsFormal/Modes/ContextDependent/Variations/Stochastic.lean |
| theorem_48 | theorem | 48 | Independent context evolution | 5843 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/Definition.lean |
| definition_98 | definition | 98 | Coupled context evolution | 5855 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/Definition.lean |
| definition_99 | definition | 99 | Computable oracle | 5872 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/Definition.lean |
| definition_100 | definition | 100 | Finitely-supported oracle | 5878 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/Definition.lean |
| proposition_99 | proposition | 99 | Finite-depth realizability | 5884 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/Definition.lean |
| definition_101 | definition | 101 | Stable oracle | 5898 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/Definition.lean |
| definition_102 | definition | 102 | Context-independent prefix | 5910 | ❌ missing | FdrsFormal/Composition.lean |
| definition_103 | definition | 103 | Deterministic context system | 5920 | ✅ proven | FdrsFormal/Composition.lean |
| definition_104 | definition | 104 | Stochastic context system | 5928 | ✅ proven | FdrsFormal/Composition.lean |
| theorem_49 | theorem | 49 | Stochastic SU preservation | 5940 | ✅ proven | FdrsFormal/Composition.lean |
| definition_105 | definition | 105 | Oracle embedding | 5950 | ❌ missing | FdrsFormal/Composition.lean |
| definition_106 | definition | 106 | Oracle equivalence | 5963 | ✅ proven | FdrsFormal/Composition.lean |
| theorem_50 | theorem | 50 | Equivalence preserves all structural properties | 5976 | ✅ proven | FdrsFormal/Composition.lean |
| proposition_100 | proposition | 100 | Context-switching preserves SU | 5989 | ✅ proven | FdrsFormal/Composition.lean |
| proposition_101 | proposition | 101 | Lazy-eager equivalence | 5991 | ✅ proven | FdrsFormal/Composition.lean |
| proposition_102 | proposition | 102 | Structure-preserving transitions | 5993 | ✅ proven | FdrsFormal/Composition.lean |
| proposition_103 | proposition | 103 | Refinement induces metric dominance | 5995 | ✅ proven | FdrsFormal/Composition.lean |
| proposition_104 | proposition | 104 | Independent factorization | 5997 | ✅ proven | FdrsFormal/Composition.lean |
| proposition_105 | proposition | 105 | Finite realizability | 5999 | ✅ proven | FdrsFormal/Composition.lean |
| proposition_106 | proposition | 106 | Stochastic SU preservation | 6001 | ✅ proven | FdrsFormal/Composition.lean |
| proposition_107 | proposition | 107 | Oracle equivalence invariance | 6003 | ✅ proven | FdrsFormal/Composition.lean |
## Phase 8

| ID | Type | Number | Title | Line | Status | Lean File |
|---|---|---|---|---|---|---|
| definition_107 | definition | 107 | Timeline identifier space | 6028 | ✅ proven | FdrsFormal/Composition/TimelineGraphs/Identifiers.lean |
| definition_108 | definition | 108 | Timeline graph structure | 6042 | ✅ proven | FdrsFormal/Composition/TimelineGraphs/Identifiers.lean |
| definition_109 | definition | 109 | Junction point types | 6059 | ✅ proven | FdrsFormal/Composition/Junctions/Types.lean |
| definition_110 | definition | 110 | Active cylinder in timeline | 6072 | ✅ proven | FdrsFormal/Composition/Junctions/Types.lean |
| definition_111 | definition | 111 | Event space for timeline graphs | 6084 | ✅ proven | FdrsFormal/Composition/Routing/Events.lean |
| definition_112 | definition | 112 | Routing function | 6097 | ✅ proven | FdrsFormal/Composition/Routing/Events.lean |
| definition_113 | definition | 113 | Transfer types | 6119 | ✅ proven | FdrsFormal/Composition/Junctions/TransferSemantics.lean |
| definition_114 | definition | 114 | Payload transform | 6140 | ✅ proven | FdrsFormal/Composition/Junctions/PayloadTransform.lean |
| definition_115 | definition | 115 | Static routing table | 6155 | ✅ proven | FdrsFormal/Composition.lean |
| definition_116 | definition | 116 | Injection operation | 6170 | 🟠 scaffold | FdrsFormal/Composition/Injection/Definition.lean |
| definition_117 | definition | 117 | Injection locality | 6180 | ✅ proven | FdrsFormal/Composition/Injection/Locality.lean |
| definition_118 | definition | 118 | Injection queue for asynchrony | 6192 | ✅ proven | FdrsFormal/Composition/Injection/Queue.lean |
| theorem_51 | theorem | 51 | Injection preserves CSU | 6206 | ✅ proven | FdrsFormal/Composition/Injection/Preservation.lean |
| definition_119 | definition | 119 | Routing dependency graph | 6220 | ✅ proven | FdrsFormal/Composition/RoutingGraph/Graph.lean |
| definition_120 | definition | 120 | Acyclic routing | 6231 | ✅ proven | FdrsFormal/Composition/RoutingGraph/Graph.lean |
| theorem_52 | theorem | 52 | Acyclic routing implies deadlock-freedom | 6239 | ✅ proven | FdrsFormal/Composition/RoutingGraph/Graph.lean |
| definition_121 | definition | 121 | Routing depth | 6259 | ✅ proven | FdrsFormal/Composition/TimingBounds/RoutingAnalysis.lean |
| proposition_108 | proposition | 108 | Finite routing depth | 6269 | ✅ proven | FdrsFormal/Composition/TimingBounds/RoutingAnalysis.lean |
| definition_122 | definition | 122 | Local timeline operation cost | 6281 | ✅ proven | FdrsFormal/Composition/TimingBounds/RoutingAnalysis.lean |
| definition_123 | definition | 123 | Routing operation overhead | 6291 | ✅ proven | FdrsFormal/Composition/RoutingGraph/Graph.lean |
| theorem_53 | theorem | 53 | Composite timing bound - Main Result | 6304 | ✅ proven | FdrsFormal/Composition/TimingBounds/RoutingAnalysis.lean |
| corollary_29 | corollary | 29 | Static routing compile-time bound | 6325 | ✅ proven | FdrsFormal/Composition/TimingBounds/RoutingAnalysis.lean |
| definition_124 | definition | 124 | Timeline lifecycle states | 6347 | ✅ proven | FdrsFormal/Composition/Lifecycle/States.lean |
| definition_125 | definition | 125 | Spawn operation | 6359 | ✅ proven | FdrsFormal/Composition/Lifecycle/Spawn.lean |
| definition_126 | definition | 126 | Terminate operation | 6373 | ✅ proven | FdrsFormal/Composition/Lifecycle/Terminate.lean |
| definition_127 | definition | 127 | Bounded spawn system | 6386 | ✅ proven | FdrsFormal/Composition/Lifecycle/BoundedSpawn.lean |
| theorem_54 | theorem | 54 | Bounded spawn preserves global timing bounds | 6398 | ✅ proven | FdrsFormal/Composition/Lifecycle/BoundedSpawn.lean |
| definition_128 | definition | 128 | Multicast routing | 6424 | ✅ proven | FdrsFormal/Composition/Synchronization/Multicast.lean |
| definition_129 | definition | 129 | Synchronization point | 6436 | ✅ proven | FdrsFormal/Composition/Synchronization/Join.lean |
| definition_130 | definition | 130 | Join semantics | 6446 | ✅ proven | FdrsFormal/Composition/Synchronization/Join.lean |
| theorem_55 | theorem | 55 | Multicast-join duality | 6463 | ✅ proven | FdrsFormal/Composition/Synchronization/Duality.lean |
| definition_131 | definition | 131 | Routing specification language | 6473 | ✅ proven | FdrsFormal/Composition/Verification/Specification.lean |
| definition_132 | definition | 132 | Compiled routing table | 6490 | ✅ proven | FdrsFormal/Composition/Verification/Specification.lean |
| proposition_109 | proposition | 109 | Compile-time decidable properties | 6500 | ✅ proven | FdrsFormal/Composition/Verification/CompileTime.lean |
| definition_133 | definition | 133 | Verified routing specification | 6516 | ✅ proven | FdrsFormal/Composition/Verification/Verified.lean |
| definition_134 | definition | 134 | Routed observer complex | 6528 | ✅ proven | FdrsFormal/Composition/ObserverIntegration/RoutedObserver.lean |
| theorem_56 | theorem | 56 | Observer complex as special case of routing | 6543 | ✅ proven | FdrsFormal/Composition/ObserverIntegration/Embedding.lean |
| theorem_57 | theorem | 57 | Residual payload as junction accumulation | 6555 | ✅ proven | FdrsFormal/Composition/ObserverIntegration/ResidualPayload.lean |
| example_2 | example | 2 | Multi-Timeline RTOS Architecture | 6571 | ✅ proven | FdrsFormal/Composition/DeadlockAnalysis/Definition.lean |
| example_3 | example | 3 | Interrupt as Timeline Injection | 6598 | ✅ proven | FdrsFormal/Composition/DeadlockAnalysis/Definition.lean |
| example_4 | example | 4 | Dynamic Task Spawning | 6633 | ✅ proven | FdrsFormal/Composition/DeadlockAnalysis/Definition.lean |
| proposition_110 | proposition | 110 | Injection preserves CSU | 6658 | ✅ proven | FdrsFormal/Composition/DeadlockAnalysis/Definition.lean |
| proposition_111 | proposition | 111 | Acyclic routing ⟹ deadlock-free | 6660 | ✅ proven | FdrsFormal/Composition/DeadlockAnalysis/Definition.lean |
| proposition_112 | proposition | 112 | Finite depth under acyclicity | 6662 | ✅ proven | FdrsFormal/Composition/DeadlockAnalysis/Definition.lean |
| proposition_113 | proposition | 113 | Composite timing bound | 6664 | ✅ proven | FdrsFormal/Composition/DeadlockAnalysis/Definition.lean |
| proposition_114 | proposition | 114 | Static routing compile-time bound | 6666 | ✅ proven | FdrsFormal/Composition/DeadlockAnalysis/Definition.lean |
| proposition_115 | proposition | 115 | Bounded spawn timing preservation | 6668 | ✅ proven | FdrsFormal/Composition/DeadlockAnalysis/Definition.lean |
| proposition_116 | proposition | 116 | Multicast-join duality | 6670 | ✅ proven | FdrsFormal/Composition/DeadlockAnalysis/Definition.lean |
| proposition_117 | proposition | 117 | Observer complex embedding | 6672 | ✅ proven | FdrsFormal/Composition/DeadlockAnalysis/Definition.lean |
| proposition_118 | proposition | 118 | Compile-time verification | 6674 | ✅ proven | FdrsFormal/Composition/DeadlockAnalysis/Definition.lean |
| proposition_119 | proposition | 119 | Residual as undelivered accumulation | 6676 | ✅ proven | FdrsFormal/Composition/DeadlockAnalysis/Definition.lean |
## Phase 9

| ID | Type | Number | Title | Line | Status | Lean File |
|---|---|---|---|---|---|---|
| definition_135 | definition | 135 | Extended radix sequence | 6989 | ✅ proven | FdrsFormal/Modes/ExtendedBase.lean |
| definition_136 | definition | 136 | Extended digit alphabets | 6993 | ✅ proven | FdrsFormal/Modes/ExtendedBase.lean |
| definition_137 | definition | 137 | Active and capacity index sets | 7002 | ✅ proven | FdrsFormal/Modes/ExtendedBase/IndexSets.lean |
| definition_138 | definition | 138 | Effective base | 7008 | ✅ proven | FdrsFormal/Modes/ExtendedBase/IndexSets.lean |
| definition_139 | definition | 139 | Generalized cumulative radix products | 7021 | ✅ proven | FdrsFormal/Modes/ExtendedBase/PlaceValues.lean |
| proposition_120 | proposition | 120 | Monotonicity preserved | 7029 | ✅ proven | FdrsFormal/Modes/ExtendedBase/PlaceValues.lean |
| proposition_121 | proposition | 121 | Recovery of original | 7035 | ✅ proven | FdrsFormal/Modes/ExtendedBase/PlaceValues.lean |
| definition_140 | definition | 140 | Representable subspace | 7043 | ✅ proven | FdrsFormal/Modes/ExtendedBase/Definition.lean |
| definition_141 | definition | 141 | Extended decode | 7050 | ✅ proven | FdrsFormal/Modes/ExtendedBase/Definition.lean |
| definition_142 | definition | 142 | Extended encode | 7059 | ✅ proven | FdrsFormal/Modes/ExtendedBase/Definition.lean |
| proposition_122 | proposition | 122 | Bijection on representable subspace | 7066 | ✅ proven | FdrsFormal/Modes/ExtendedBase/Definition.lean |
| definition_143 | definition | 143 | Tick with extended bases | 7078 | ✅ proven | FdrsFormal/Modes/ExtendedBase/ExtendedTick.lean |
| theorem_58 | theorem | 58 | Wire transparency | 7088 | ✅ proven | FdrsFormal/Modes/ExtendedBase/ExtendedTick.lean |
| theorem_59 | theorem | 59 | Barrier wrap | 7098 | ✅ proven | FdrsFormal/Modes/ExtendedBase/ExtendedTick.lean |
| proposition_123 | proposition | 123 | Sigma-algebra contribution by base type | 7108 | ✅ proven | FdrsFormal/Modes/ExtendedBase/SigmaAlgebra.lean |
| proposition_124 | proposition | 124 | Extended β_ω(s | 7115 | ✅ proven | FdrsFormal/Modes/ExtendedBase/OdometerWeight.lean |
| proposition_125 | proposition | 125 | Arithmetic-cylinder property extension | 7124 | ✅ proven | FdrsFormal/Modes/ExtendedBase/ArithmeticCylinder.lean |
| definition_144 | definition | 144 | Instantiation API | 7137 | ✅ proven | FdrsFormal/Modes/ExtendedBase/Instantiate.lean |
| definition_145 | definition | 145 | Spatial digit capacity | 7194 | ✅ proven | FdrsFormal/Modes/ExtendedBase/SpatialThermometer.lean |
| definition_146 | definition | 146 | Spatial tick | 7204 | ✅ proven | FdrsFormal/Modes/ExtendedBase/SpatialThermometer.lean |
| definition_147 | definition | 147 | Spatial radix wall | 7213 | ✅ proven | FdrsFormal/Modes/ExtendedBase/SpatialThermometer.lean |
| theorem_60 | theorem | 60 | Spatial-algebraic isomorphism | 7223 | ✅ proven | FdrsFormal/Modes/ExtendedBase/SpatialThermometer.lean |
| definition_148 | definition | 148 | Carry event classification | 7244 | ✅ proven | FdrsFormal/Modes/BaseZeroSea.lean |
| definition_149 | definition | 149 | Carry-as-route | 7253 | ✅ proven | FdrsFormal/Modes/ExtendedBase/CarryRouteUnification.lean |
| definition_150 | definition | 150 | Unified spatial tick | 7264 | ✅ proven | FdrsFormal/Modes/ExtendedBase/CarryRouteUnification.lean |
| theorem_61 | theorem | 61 | Fractal unification — carry is overflow route | 7268 | ✅ proven | FdrsFormal/Modes/BaseZeroSea.lean |
## Phase 10

| ID | Type | Number | Title | Line | Status | Lean File |
|---|---|---|---|---|---|---|
| definition_151 | definition | 151 | Base-zero sea | 7305 | ✅ proven | FdrsFormal/Modes/BaseZeroSea/Basic.lean |
| definition_152 | definition | 152 | Observation windows and radix walls | 7316 | ✅ proven | FdrsFormal/Modes/BaseZeroSea/Basic.lean |
| definition_153 | definition | 153 | Legacy thread | 7330 | ✅ proven | FdrsFormal/Modes/BaseZeroSea/Basic.lean |
| definition_154 | definition | 154 | Deterministic creation step | 7340 | ✅ proven | FdrsFormal/Modes/BaseZeroSea/Dynamics.lean |
| definition_155 | definition | 155 | Consumption target rule | 7358 | ✅ proven | FdrsFormal/Modes/BaseZeroSea/Dynamics.lean |
| definition_156 | definition | 156 | Consumption schedule | 7371 | ✅ proven | FdrsFormal/Modes/BaseZeroSea/Dynamics.lean |
| definition_157 | definition | 157 | Unified deterministic sea tick | 7379 | ✅ proven | FdrsFormal/Modes/BaseZeroSea/Dynamics.lean |
| proposition_126 | proposition | 126 | Deterministic totality | 7396 | ✅ proven | FdrsFormal/Modes/BaseZeroSea/Properties.lean |
| proposition_127 | proposition | 127 | Closure and validity invariants | 7404 | ✅ proven | FdrsFormal/Modes/BaseZeroSea/Properties.lean |
| proposition_128 | proposition | 128 | Legacy-length balance law | 7412 | ✅ proven | FdrsFormal/Modes/BaseZeroSea/Properties.lean |
| theorem_62 | theorem | 62 | Deterministic sea dynamics is a well-defined trans | 7423 | ✅ proven | FdrsFormal/Modes/BaseZeroSea/Properties.lean |
| definition_158 | definition | 158 | Window-to-digit projection | 7437 | ✅ proven | FdrsFormal/Modes/BaseZeroSea/Projection.lean |
| definition_159 | definition | 159 | Phase-9 constraint profile | 7445 | ✅ proven | FdrsFormal/Modes/BaseZeroSea/Projection.lean |
| theorem_63 | theorem | 63 | Phase 9 is a special case of Phase 10 | 7454 | ✅ proven | FdrsFormal/Modes/BaseZeroSea/Projection.lean |
| definition_160 | definition | 160 | Digit module in a base-zero sea | 7479 | ✅ proven | FdrsFormal/Modes/BaseZeroSea/Modules.lean |
| definition_161 | definition | 161 | Sustainment and resistance functional | 7495 | ✅ proven | FdrsFormal/Modes/BaseZeroSea/Modules.lean |
| proposition_129 | proposition | 129 | Deterministic persistence criterion | 7511 | ✅ proven | FdrsFormal/Modes/BaseZeroSea/Modules.lean |
| definition_162 | definition | 162 | Emergent effective base | 7520 | ✅ proven | FdrsFormal/Modes/BaseZeroSea/Modules.lean |
| proposition_130 | proposition | 130 | Resistance-base monotonicity under fixed observati | 7536 | ✅ proven | FdrsFormal/Modes/BaseZeroSea/Modules.lean |
| definition_163 | definition | 163 | Coupled-digit sea network | 7544 | ✅ proven | FdrsFormal/Modes/BaseZeroSea/Modules.lean |
| theorem_64 | theorem | 64 | Classical mixed-radix line as a single-lineage spe | 7568 | ✅ proven | FdrsFormal/Modes/BaseZeroSea/Modules.lean |
## Phase 11

| ID | Type | Number | Title | Line | Status | Lean File |
|---|---|---|---|---|---|---|
| definition_164 | definition | 164 | Non-stationary radix tree | 7607 | ✅ proven | FdrsFormal/Analysis/DigitConditional/Tree.lean |
| definition_165 | definition | 165 | Depth and heterogeneity | 7619 | ✅ proven | FdrsFormal/Analysis/DigitConditional/Tree.lean |
| proposition_131 | proposition | 131 | Leaf count identity | 7629 | ✅ proven | FdrsFormal/Analysis/DigitConditional/Tree.lean |
| proposition_132 | proposition | 132 | Homogeneous recovery | 7638 | ✅ proven | FdrsFormal/Analysis/DigitConditional/Tree.lean |
| definition_166 | definition | 166 | Tree-adapted signal | 7650 | ✅ proven | FdrsFormal/Analysis/DigitConditional/Decomposition.lean |
| definition_167 | definition | 167 | Node projection and layer | 7659 | ✅ proven | FdrsFormal/Analysis/DigitConditional/Decomposition.lean |
| lemma_5 | lemma | 5 | Within-node layer properties | 7677 | ✅ proven | FdrsFormal/Analysis/DigitConditional/Decomposition.lean |
| theorem_65 | theorem | 65 | Orthogonal decomposition | 7688 | ✅ proven | FdrsFormal/Analysis/DigitConditional/Decomposition.lean |
| corollary_30 | corollary | 30 | Exact adapted signals | 7702 | ✅ proven | FdrsFormal/Analysis/DigitConditional/Decomposition.lean |
| definition_168 | definition | 168 | Signal taxonomy | 7712 | ✅ proven | FdrsFormal/Analysis/DigitConditional/SignalClass.lean |
| proposition_133 | proposition | 133 | Strict class hierarchy | 7724 | ✅ proven | FdrsFormal/Analysis/DigitConditional/SignalClass.lean |
| definition_169 | definition | 169 | Root-periodic energy fraction | 7734 | ✅ proven | FdrsFormal/Analysis/DigitConditional/FourierCeiling.lean |
| theorem_66 | theorem | 66 | Fourier ceiling | 7744 | ✅ proven | FdrsFormal/Analysis/DigitConditional/FourierCeiling.lean |
| proposition_134 | proposition | 134 | Homogeneous ceiling trivial | 7754 | ✅ proven | FdrsFormal/Analysis/DigitConditional/FourierCeiling.lean |
| definition_170 | definition | 170 | Minimum uniform cells | 7764 | ✅ proven | FdrsFormal/Analysis/DigitConditional/RepresentationGap.lean |
| definition_171 | definition | 171 | Representation gap | 7772 | ✅ proven | FdrsFormal/Analysis/DigitConditional/RepresentationGap.lean |
| proposition_135 | proposition | 135 | Representation gap: collapse and strict gap | 7780 | ✅ proven | FdrsFormal/Analysis/DigitConditional/RepresentationGap.lean |
| theorem_67 | theorem | 67 | Depth-2 gap formula | 7790 | ✅ proven | FdrsFormal/Analysis/DigitConditional/RepresentationGap.lean |
| corollary_31 | corollary | 31 | Compensated heterogeneity | 7800 | ✅ proven | FdrsFormal/Analysis/DigitConditional/RepresentationGap.lean |
| definition_172 | definition | 172 | Tree block projection | 7810 | ✅ proven | FdrsFormal/Analysis/DigitConditional/Projection.lean |
| proposition_136 | proposition | 136 | Projection properties | 7818 | ✅ proven | FdrsFormal/Analysis/DigitConditional/Projection.lean |
| theorem_68 | theorem | 68 | Connection to FDRS filtration | 7830 | ✅ proven | FdrsFormal/Analysis/DigitConditional/Projection.lean |
| definition_173 | definition | 173 | F-statistic for radix selection | 7844 | ✅ proven | FdrsFormal/Analysis/DigitConditional/Detection.lean |
| proposition_137 | proposition | 137 | Detection power scaling | 7857 | ✅ proven | FdrsFormal/Analysis/DigitConditional/Detection.lean |
| definition_174 | definition | 174 | DCC | 7871 | 🟠 scaffold | FdrsFormal/Analysis/DigitConditional/Complexity.lean |
| proposition_138 | proposition | 138 | DCC characterizes taxonomy | 7879 | ✅ proven | FdrsFormal/Analysis/DigitConditional/Complexity.lean |
| theorem_69 | theorem | 69 | Vilenkin is special case | 7896 | ✅ proven | FdrsFormal/Analysis/DigitConditional/SpecialCase.lean |
## Phase 12

| ID | Type | Number | Title | Line | Status | Lean File |
|---|---|---|---|---|---|---|
| definition_175 | definition | 175 | unit complement | 7929 | ✅ proven | FdrsFormal/Core/UnitComplement.lean |
| definition_176 | definition | 176 | unit pair and parts | 7937 | ✅ proven | FdrsFormal/Core/UnitComplement.lean |
| proposition_139 | proposition | 139 | complement properties | 7945 | ✅ proven | FdrsFormal/Core/UnitComplement.lean |
| proposition_140 | proposition | 140 | ordering split | 7960 | ✅ proven | FdrsFormal/Core/UnitComplement.lean |
| definition_177 | definition | 177 | fit count, completion residue, overflow carry | 7987 | ✅ proven | FdrsFormal/Core/UnitCarry.lean |
| proposition_141 | proposition | 141 | basic carry arithmetic | 7997 | ✅ proven | FdrsFormal/Core/UnitCarry.lean |
| proposition_142 | proposition | 142 | irrational sharpening | 8010 | ✅ proven | FdrsFormal/Core/UnitCarry.lean |
| proposition_143 | proposition | 143 | greater/lesser part specialization | 8022 | ✅ proven | FdrsFormal/Core/UnitCarry.lean |
## Phase 13

| ID | Type | Number | Title | Line | Status | Lean File |
|---|---|---|---|---|---|---|
| definition_178 | definition | 178 | Product radix and the observer-line mediator | 8077 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/Definition.lean |
| proposition_144 | proposition | 144 | Mediator ≅ A × B: the round-trip identities | 8083 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/Definition.lean |
| theorem_70 | theorem | 70 | Place value and overflow rate factor under the pro | 8093 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/Definition.lean |
| definition_179 | definition | 179 | Coupling, the coupled system, and manifest instant | 8108 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/Definition.lean |
| proposition_145 | proposition | 145 | Independence of coupling and radix; manifestation  | 8114 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/Definition.lean |
| proposition_146 | proposition | 146 | Overflow-rate ratio and the discrete → real compar | 8120 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/Definition.lean |
| definition_180 | definition | 180 | Subshift / transfer-matrix prefix gauge | 8132 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/Definition.lean |
| theorem_71 | theorem | 71 | Defensive perimeter: the free `d = 1` gauge recove | 8138 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/Definition.lean |
| definition_181 | definition | 181 | The convergent-pair ledger | 8148 | ✅ proven | FdrsFormal/Modes/VariableRadix/SubshiftWeight.lean |
| theorem_72 | theorem | 72 | The bracket invariant | 8154 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/Definition.lean |
| theorem_73 | theorem | 73 | Gauge growth: `q_k > 0` and `q_k → ∞`, even for `φ | 8162 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/Definition.lean |
| definition_182 | definition | 182 | Admissible point, prefix, and the gauge at depth | 8174 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/Definition.lean |
| definition_183 | definition | 183 | The gauge-induced continued-fraction distance | 8180 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/Definition.lean |
| theorem_74 | theorem | 74 | `cfDist` is a genuine ultrametric | 8186 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/Definition.lean |
| theorem_75 | theorem | 75 | `ball = cylinder` | 8194 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/Definition.lean |
| definition_184 | definition | 184 | Carry frequency of a generated timeline | 8211 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/Definition.lean |
| theorem_76 | theorem | 76 | `cfOverflowRate` is positive, antitone, and vanish | 8217 | ✅ proven | FdrsFormal/Modes/VariableRadix/CarryFrequency.lean |
| definition_185 | definition | 185 | Parry transition kernel of the golden-mean shift | 8233 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/Definition.lean |
| theorem_77 | theorem | 77 | Mass conservation and the Markov kernel | 8239 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/Definition.lean |
| definition_186 | definition | 186 | Parry stationary law | 8247 | ✅ proven | FdrsFormal/Modes/VariableRadix/SubshiftParry.lean |
| theorem_78 | theorem | 78 | Stationarity | 8253 | ✅ proven | FdrsFormal/Modes/VariableRadix/SubshiftParry.lean |
| definition_187 | definition | 187 | Parry path measure via Ionescu–Tulcea | 8261 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/Definition.lean |
| theorem_79 | theorem | 79 | Lévy upward convergence — "Group G" — on the golde | 8267 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/Definition.lean |
| definition_188 | definition | 188 | Homographic emission — single stream | 8281 | ✅ proven | FdrsFormal/Modes/VariableRadix/HomographicCarry.lean |
| theorem_80 | theorem | 80 | Exactness and channel independence | 8287 | ✅ proven | FdrsFormal/Modes/VariableRadix/HomographicCarry.lean |
| definition_189 | definition | 189 | The bihomographic tensor — two-stream mediator, Ti | 8295 | ✅ proven | FdrsFormal/Integration/ThreeLineMediator/Definition.lean |
| theorem_81 | theorem | 81 | Channel commutations | 8301 | ✅ proven | FdrsFormal/Modes/VariableRadix/Bihomographic.lean |
| theorem_82 | theorem | 82 | Emission soundness — the four-corner trap | 8309 | ✅ proven | FdrsFormal/Modes/VariableRadix/BihomographicSound.lean |
| definition_190 | definition | 190 | The two-stream driver | 8317 | ✅ proven | FdrsFormal/Modes/VariableRadix/BihomographicDriver.lean |
| definition_191 | definition | 191 | The hyper-Gosper clock | 8325 | ✅ proven | FdrsFormal/Modes/VariableRadix/HyperGosper.lean |
## Phase 14

| ID | Type | Number | Title | Line | Status | Lean File |
|---|---|---|---|---|---|---|
| definition_192 | definition | 192 | prefix gauge | 8366 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| theorem_83 | theorem | 83 | gauge ⇒ ultrametric; ball = cylinder | 8373 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| proposition_147 | proposition | 147 | the corpus instances | 8381 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| definition_193 | definition | 193 | coupled fiber law; coupled completion counts | 8390 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| theorem_84 | theorem | 84 | level-only coupling preserves SU | 8397 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| proposition_148 | proposition | 148 | the ragged witness, machine-checked | 8402 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| theorem_85 | theorem | 85 | geometry survives raggedness | 8409 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| definition_194 | definition | 194 | transfer structure; uncertainty ledger; trap gate | 8418 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| theorem_86 | theorem | 86 | admissibility-trap soundness | 8425 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| definition_195 | definition | 195 | depth-decided observables | 8439 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| theorem_87 | theorem | 87 | indistinguishability below the gauge; strict hiera | 8443 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| definition_196 | definition | 196 | completion mass and observed flux | 8455 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| theorem_88 | theorem | 88 | the partition law; zero leak | 8460 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| definition_197 | definition | 197 | the coupled interface machine; balance | 8470 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| theorem_89 | theorem | 89 | the interface balance law | 8477 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| definition_198 | definition | 198 | place-local transfer rules | 8485 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| theorem_90 | theorem | 90 | conservation rigidity: factorization, no-go, bound | 8490 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| proposition_149 | proposition | 149 | witnesses on both sides of the boundary | 8504 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| definition_199 | definition | 199 | schedules, trace equivalence, projections | 8514 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| theorem_91 | theorem | 91 | the scalar trace-gauge no-go, machine-checked | 8522 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| definition_200 | definition | 200 | the observer-glued network distance | 8534 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| theorem_92 | theorem | 92 | the glued network ultrametric | 8539 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| definition_201 | definition | 201 | coupling graph; size as an edge cocycle | 8590 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| theorem_93 | theorem | 93 | the holonomy dichotomy — the full iff | 8604 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| proposition_150 | proposition | 150 | witnesses on both sides | 8611 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| definition_202 | definition | 202 | currency; transport vs trigger | 8624 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| theorem_94 | theorem | 94 | currency-generic interface balance | 8635 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| definition_203 | definition | 203 | windows; the length window; grant uniformity | 8644 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| theorem_95 | theorem | 95 | the shared clock; clock windows are accountable | 8655 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| theorem_96 | theorem | 96 | the window boundary, CLOSED for the alternating ma | 8663 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| definition_204 | definition | 204 | the exact splice | 8674 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| theorem_97 | theorem | 97 | synthetic fractions; the gauge half of dilation | 8683 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| theorem_98 | theorem | 98 | dilation, dynamic half — exact nesting is conserva | 8695 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| definition_205 | definition | 205 | group-valued coupling graph | 8713 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| theorem_99 | theorem | 99 | group holonomy dichotomy — gain-graph balance | 8721 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| proposition_151 | proposition | 151 | non-abelian frustrated witnesses, discrete and con | 8731 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| definition_206 | definition | 206 | sector emission — the floor-free trap | 8739 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| theorem_100 | theorem | 100 | sector-trap soundness — the fourth certificate | 8747 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| definition_207 | definition | 207 | exact SE2 motions; pose regions; tractable engines | 8756 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| theorem_101 | theorem | 101 | the certified non-commutative engine: soundness an | 8766 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| theorem_102 | theorem | 102 | the tight tractable engine | 8779 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| definition_208 | definition | 208 | the network machine; the latency discipline | 8820 | ✅ proven | FdrsFormal/Modes/SyntheticPlace/NetworkConfig.lean |
| theorem_103 | theorem | 103 | the probe gate: the two-node network IS the SU4b m | 8831 | ✅ proven | FdrsFormal/Modes/SyntheticPlace/NetworkConfig.lean |
| definition_209 | definition | 209 | `complexStep` — the three-clause firing | 8840 | ✅ proven | FdrsFormal/Modes/SyntheticPlace/NetworkComplexStep.lean |
| theorem_104 | theorem | 104 | conservative extension, twice; the fan-out witness | 8855 | ✅ proven | FdrsFormal/Modes/SyntheticPlace/NetworkComplexStep.lean |
| theorem_105 | theorem | 105 | causality must not be frustrated — well-formedness | 8864 | ✅ proven | FdrsFormal/Modes/SyntheticPlace/NetworkComplexStep.lean |
| theorem_106 | theorem | 106 | network balance: SU6b's generic law, per edge | 8874 | ✅ proven | FdrsFormal/Modes/SyntheticPlace/NetworkBalance.lean |
| definition_210 | definition | 210 | non-blocking couplability; the decidable fixpoint  | 8890 | ✅ proven | FdrsFormal/Modes/SyntheticPlace/NetworkCouplability.lean |
| theorem_107 | theorem | 107 | couplability certificate soundness | 8900 | ✅ proven | FdrsFormal/Modes/SyntheticPlace/NetworkCouplability.lean |
| proposition_152 | proposition | 152 | witnesses on both sides of couplability | 8907 | ✅ proven | FdrsFormal/Modes/SyntheticPlace/NetworkCouplability.lean |
| theorem_108 | theorem | 108 | per-node traps on the network — Theorem 86 transpo | 8915 | ✅ proven | FdrsFormal/Modes/SyntheticPlace/NetworkTraps.lean |
| theorem_109 | theorem | 109 | the conditional Kahn diamond — determinacy, local  | 8928 | ✅ proven | FdrsFormal/Modes/SyntheticPlace/NetworkDeterminacy.lean |
| theorem_110 | theorem | 110 | network liveness — the factored guarantee | 8943 | ✅ proven | FdrsFormal/Modes/SyntheticPlace/NetworkLiveness.lean |
| theorem_111 | theorem | 111 | a timeline graph IS a network shape; time-ordering | 8967 | ✅ proven | FdrsFormal/Modes/SyntheticPlace/NetworkBridge.lean |
| definition_211 | definition | 211 | the queue-backed edge register | 8981 | ✅ proven | FdrsFormal/Modes/SyntheticPlace/NetworkBridge.lean |
| theorem_112 | theorem | 112 | queue balance at every capacity; capacity-one IS t | 8988 | ✅ proven | FdrsFormal/Modes/SyntheticPlace/NetworkBridge.lean |
| definition_212 | definition | 212 | the 25519 digit ring | 9011 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| theorem_113 | theorem | 113 | a carry is a value-preserving redistribution | 9021 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| theorem_114 | theorem | 114 | the wrap has holonomy 19, not 1 | 9030 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| theorem_115 | theorem | 115 | the schedule restores the bound — lazy reduction l | 9038 | ✅ proven | FdrsFormal/Applications/Field25519Carry.lean |
| definition_213 | definition | 213 | position gauge; the gauged completion | 9071 | ✅ proven | FdrsFormal/Modes/SyntheticPlace/Dimension.lean |
| theorem_116 | theorem | 116 | the Moran frame — dimension squeezed by count agai | 9087 | ✅ proven | FdrsFormal/Modes/SyntheticPlace/Dimension.lean |
| theorem_117 | theorem | 117 | every number line is one-dimensional | 9100 | ✅ proven | FdrsFormal/Modes/SyntheticPlace/Dimension.lean |
| theorem_118 | theorem | 118 | the gauge programs the dimension | 9110 | ✅ proven | FdrsFormal/Modes/SyntheticPlace/Dimension.lean |
| proposition_153 | proposition | 153 | the §6.4.3 growth regimes, computed | 9118 | ✅ proven | FdrsFormal/Modes/SyntheticPlace/Dimension.lean |
