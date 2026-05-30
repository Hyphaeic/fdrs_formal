# FDRS Formal

A Lean 4 formalization of **Function-Defined Radix Systems** (FDRS) — a mathematical
framework generalizing classical positional notation by allowing the radix at each
digit position to be determined by a *function* rather than fixed data.

The mathematical specification lives in [`docs/fdrs.md`](docs/fdrs.md) (the aggreate of concepts). The Lean code in [`FdrsFormal/`](FdrsFormal/) is a machine-checked
formalization of that specification against [Mathlib](https://github.com/leanprover-community/mathlib4).

## Status

This is an actively developed formalization, refined over time rather than a sealed
artifact — expect it to keep evolving. The default `lake build` compiles cleanly; a few
`sorry`s remain in work-in-progress modules (currently the wavelet-packet experiments
under `FunctionSpaces/Haar/`).

For the current state of the Lean code, ask the tooling rather than relying on numbers
written in prose:

```bash
python3 scripts/fdrs-summary        # axioms, sorries, stubs, per-phase coverage
```

Building the work-in-progress modules that aren't part of the default target is covered
in [`docs/TESTING.md`](docs/TESTING.md).

## Building

Requires the Lean toolchain pinned in [`lean-toolchain`](lean-toolchain)
(`leanprover/lean4:v4.27.0-rc1`) via [elan](https://github.com/leanprover/elan), and
Mathlib (fetched automatically by Lake; the revision is pinned in
[`lake-manifest.json`](lake-manifest.json)).

```bash
# Fetch the prebuilt Mathlib cache (recommended — avoids compiling Mathlib from source)
lake exe cache get

# Build the formalization
lake build
```

## Module structure

```
FdrsFormal/
├── Core/           # Radix sequences, finite/infinite spaces, canonical bijections
├── Operations/     # Tick, predecessor, addition, subtraction
├── Topology/       # Ultrametric structure, continuity, compactness, filtration
├── FunctionSpaces/ # Tensor spaces, projections, detail operators, Haar/contrast bases
├── NumberTheory/   # Arithmetic functions, Dirichlet convolution, characters,
│                   #   valuations, the factorization lens
├── Integration/    # Block memory, dual filtrations, runtime algebra, complexity bounds
├── Modes/          # The three modes of application:
│                   #   VariableRadix, ContextDependent, ExtendedBase, BaseZeroSea
├── Analysis/       # Digit-conditional signal analysis (radix trees, orthogonal
│                   #   decomposition, Fourier ceiling, detection power)
└── Composition/    # Multi-timeline routing, synchronization, lifecycle management
```

`FdrsFormal.lean` is the root module aggregating the development; `Main.lean` is a
trivial executable entry point.

## What this formalizes

The specification develops the theory of radix systems where the base at each digit
position is computed by a function evaluated during representation. The function's
domain and evaluation semantics define three principal **modes of application**:

- **Mode I — Prefix-Pure**: the radix depends only on the prefix of digits already
  determined (`w : S* → ℕ_{≥2}`). Yields static tree structures with canonical
  ultrametrics and a classification of realizable ultrametrics (Theorem B).
- **Mode II — Context-Dependent**: the radix depends on prefix and evolving external
  context (`O : S* × C → ℕ_{≥2}`). Yields context-parameterized ultrametrics with
  representation independence (Theorem E) and structure-preserving transitions (Theorem F).
- **Mode III — Extended-Base**: the codomain extends to include 0 (walls) and 1 (wires),
  enabling dynamic structure discovery and explicit routing.

Across all modes the formalization establishes canonical bijections with ℕ (Theorem A),
arithmetic continuity (Tick is 1-Lipschitz, Theorem C), orthogonal dual filtrations
(topological vs. multiplicative, Theorem D), mixed-radix complexes (a discrete
ultrametric analogue of wavelet multiresolution analysis), analytic number theory on
radix coordinates, and multi-timeline composition.

## Tooling

A small Python toolchain (requires `pyyaml`, see [`requirements.txt`](requirements.txt))
maintains the spec ⇄ Lean correspondence and regenerates the metadata in `data/`:

```bash
python3 scripts/fdrs-summary                 # Status dashboard (scans live .lean source)
python3 scripts/fdrs-summary --check         # Verify the index matches live code
python3 scripts/fdrs-summary --sorries       # List every sorry
python3 scripts/fdrs-summary --stubs         # List every declaration stub
python3 scripts/fdrs-summary --phase 11      # Items in a specific phase
python3 scripts/fdrs-rebuild                 # Regenerate all derived metadata + graphs
```

See [`docs/GENERAL_CONTEXT.md`](docs/GENERAL_CONTEXT.md) for the canonical-source trust
hierarchy and how the metadata is generated, and [`docs/TESTING.md`](docs/TESTING.md)
for build/check workflows.

## Documentation

- [`docs/fdrs.md`](docs/fdrs.md) — the mathematical specification (single source of truth).
- [`docs/fdrs-index.md`](docs/fdrs-index.md) — auto-generated spec-item → Lean index.
- [`docs/notation.md`](docs/notation.md) — symbol/notation reference extracted from live code.
- `data/*.yaml` — machine-readable index and dependency graphs (regenerated by the tooling).

The rendered dependency-graph images (`*.svg`/`*.dot`) are not committed; regenerate
them locally with `scripts/fdrs-rebuild` (requires Graphviz).

## Scope of this repository

This repository contains **only** the Lean formalization, its build configuration, the
maintenance tooling, and the documentation needed to build and check it. It intentionally
excludes the SageMath experiments, ML experiments, paper drafts, teaching material,
archived planning documents, and generated media that lived alongside the formalization
during development.

It is the canonical Lean artifact of the Hyphaeic **variable-representation** research
program (registry id `project-fdrs-formal`), and is built within the
`workspace-math-proof-env` toolchain (Lean 4 + Python + SageMath).

## License

Licensed under the [Hyphaeic Public License, Version 1.0](https://github.com/hyphaeic/hpl).
See [LICENSE](LICENSE) and [NOTICE](NOTICE). Third-party components (Lean 4, Mathlib) are
under their own licenses, as noted in [NOTICE](NOTICE).
