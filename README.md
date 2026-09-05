<div align="center">
  <img src="https://src.hyphaeic.com/website/img/logo.png" alt="Hyphaeic" width="80"/>

  # FDRS Formal

  [![Hyphaeic](https://img.shields.io/badge/HYPHAEIC-research-41efa4?style=flat-square&labelColor=1a1a1a)](https://github.com/Hyphaeic)
  [![Lean 4](https://img.shields.io/badge/Lean_4-v4.27.0--rc1-purple?style=flat-square&labelColor=1a1a1a)](https://github.com/leanprover/lean4)
  [![Build](https://img.shields.io/badge/lake_build-passing-41efa4?style=flat-square&labelColor=1a1a1a)](docs/TESTING.md)
  [![License](https://img.shields.io/badge/license-HPL-41efa4?style=flat-square&labelColor=1a1a1a)](https://github.com/hyphaeic/hpl)

  **A machine-checked mathematical corpus on Function-Defined Radix Systems —
  from positional notation as algebra, through certified digit-emission engines,
  to the geometry and conservation laws of coupled radix networks.**

  [The spec](docs/fdrs.md) · [Item index](docs/fdrs-index.md) · [Design records](docs/synthetic-place/) · [Tooling](scripts/)

</div>

---

## The idea

You already use a number system whose base changes with position: 60 seconds
to a minute, 60 minutes to an hour, 24 hours to a day. That is *mixed radix*,
and it is classical — fix a list of bases `b₀, b₁, b₂, …` and the place value
at position `m` is the running product `Bₘ = b₀·b₁ ⋯ bₘ₋₁`.

This corpus asks what number representation becomes when that list is replaced
by a **function**. The central object is the *radix law*

```
b : prefix ⟶ {2, 3, 4, …}
```

— the base at each position is *computed*: from the position, from the digits
already written, from an external context, or from the live state of another
number line entirely. The digit space stops being a grid and becomes a rooted
tree whose branching factor varies node by node; the "numbers" are its paths.

A surprising amount of classical structure survives the generalization: the
bijection with ℕ, the carry dynamics of `+1` (the odometer), the prefix
ultrametric in which balls are exactly cylinders. The subject of the corpus is
*where each survival ends* — and the boundary is in every case proven, not
asserted. The specification, [`docs/fdrs.md`](docs/fdrs.md), has grown through
fourteen phases of numbered definitions, theorems, and propositions, and is
machine-checked item by item in Lean 4 against
[Mathlib](https://github.com/leanprover-community/mathlib4).

## Five results, as a sampler

Chosen for range; the [index](docs/fdrs-index.md) maps every numbered item to
its proof.

**Which geometries can be numbered.** An ultrametric space is realizable by a
sibling-uniform radix law **iff** every open ball is a prefix cylinder and
every cylinder has canonical diameter (Theorem 43, Phase 6) — both directions
proven, and the two conditions do provably separate work: the first pins the
tree, the second pins the gauge
([`MetricRealizability.lean`](FdrsFormal/Modes/VariableRadix/Realizability/MetricRealizability.lean)).

**A digit is emitted only when it is forced.** On continued-fraction timelines
(Phase 13) the gauge is generated rather than multiplied out, and Gosper-style
homographic/bihomographic engines emit a digit only when *every* possible
continuation of the unread input forces it — the four-corner order trap at the
Archimedean place, the congruence trap at p-adic places, the admissibility trap
on finite grammars. Exact integer ledgers, no floating point anywhere;
`√2·√2` emits nothing, honestly.

**You cannot counterfeit a prime.** Heterogeneous place-engines run under one
scheduler with proven confluence, and the product formula on ℚˣ holds in exact
arithmetic — but an FDRS gauge reproduces a p-adic place value **iff** its base
is constantly p. There are no synthetic places on ℚ; a function-field keystone
stakes the genuinely synthetic instance
([`docs/function-field/`](docs/function-field/)).

**When number lines couple, they stop being numbers — lawfully.** Coupling
generically destroys the odometer while the geometry survives (Phase 14).
Conservation migrates from product formulas — impossible for genuinely coupled
systems, by a machine-checked separability no-go — to interface balance laws
(`issued = consumed + pending`, proven for arbitrary coupling in any
commutative monoid of carries). No scalar gauge can metrize a concurrent
network, forcing the observer-glued construction; and "bigger digit" exists
**iff** every coupling loop has trivial holonomy, with a verified three-digit
Penrose staircase on the other side of the boundary. Together with ragged
fibers and bilateral coupling, three independent machine-checked obstructions
separate coupled radix complexes from number systems.

**The vocabulary is load-bearing in production arithmetic.** GF(2²⁵⁵ − 19)
under Ed25519, read as a ten-digit variable-radix ring: carries are
ledger-balanced redistributions, the wrap has holonomy 19 — a digit ring on the
frustrated side of the grading dichotomy — and the eleven-carry schedule
provably restores the digit bound, licensing the lazy reduction used in
deployed Rust kernels
([`Field25519Carry.lean`](FdrsFormal/Applications/Field25519Carry.lean)).

Beyond the sampler: a discrete multiresolution analysis with a commutant
theorem, the cylinder-measurability bridge between the additive and
multiplicative filtrations, and a verified abstract machine for coupled radix
networks (the SU7 arc, §14.12–14.13) whose firing rule, balance laws, Kahn
determinacy, and liveness are all proven — with the Phase-8 timeline-graph
layer shown to be an instance of it.

## How to trust it

The default `lake build` target compiles the entire tree — **zero axioms and
zero sorries** — against Mathlib at the revision pinned in the manifest. The
spec contains **523 numbered items** across the fourteen phases, and the
correspondence between items and Lean proofs is maintained by tooling, not by
prose:

```bash
python3 scripts/fdrs-summary   # live status: axioms, sorries, scaffolds, coverage
```

At this writing the scanner matches 520 of the 523 items (99.4%) to proofs and
names the residue explicitly — one open Phase-7 item and three scaffold
declarations it flags as such. Numbers printed in documentation, including this
file, are treated as stale by default; the scanner reads the live source.

House rules, as working practice:

- **Spec first.** `docs/fdrs.md` is the single source of truth; Lean modules
  cite the numbered items they prove, and an erratum is preferred over a
  silent fix when the spec is wrong.
- **Honest scope.** Every module carries an honest-scope banner; design
  documents carry anti-confabulation ledgers.
- **Kernel `decide`.** Finite witnesses are checked by the kernel, never by
  `native_decide`.
- **Classical is cited as classical.** The contribution is the connection and
  the verified artifact, not a claim of novelty over the ingredients.

## The fourteen phases

| Phase | Name | What lands there |
|:--|:--|:--|
| 1 | Foundations | Mixed-radix spaces; decode/encode bijections with ℕ; the Tick; the prefix ultrametric |
| 2 | Mixed-Radix Complexes | Cylinders and filtration; block projections as conditional expectations; the Haar/contrast MRA; the commutant theorem |
| 3 | Import Analytic Number Theory | Dirichlet convolution, characters, valuations; the cylinder-measurability bridge |
| 4 | Integers as Programs | Computation primitives from ANT; the factorization lens |
| 5 | Function-Defined Radices | The radix law; variable-radix trees; Tick with variable carry; no-infinite-carry conditions |
| 6 | Custom Ultrametric Design | Radix engineering; the realizability criterion (Theorem 43) |
| 7 | Context-Dependent Radix Systems | Radix laws that consult an external context or oracle |
| 8 | Multi-Timeline Routing | Composition of timelines; the dependency-grading deadlock certificate; timing bounds |
| 9 | Extended Base Support | Base-0 walls and base-1 wires; spatialized digits; the spatial thermometer |
| 10 | Base-Zero Sea Dynamics | Deterministic substrate dynamics; the linear-chain bridge |
| 11 | Digit-Conditional Signal Analysis | The projection algebra; the Fourier ceiling |
| 12 | Unit Complement Structure | The complement `x ↦ 1 − x` as a uniform frame for the corpus's normalized quantities |
| 13 | Generated Timelines | Continued-fraction gauges, generated rather than multiplied out; the certified Gosper emission engines |
| 14 | The Synthetic Place Complex | Coupled radix networks: geometry, conservation, obstructions; the SU7 network machine; applications |

## Layout

```
docs/            # the spec (fdrs.md), the item index, design records, notation
FdrsFormal/      # the Lean corpus (tree below)
scripts/         # maintenance tooling — fdrs-summary and the index builder
data/            # generated: the item index (YAML) and per-phase item graphs
explorations/    # small Python sketches; exploratory, non-evidentiary
```

```
FdrsFormal/
├── Core/            # Radix sequences, bijections, finite/infinite spaces
├── Operations/      # Tick, predecessor, addition, subtraction
├── Topology/        # Ultrametric, compactness, filtration, odometer dynamics
├── FunctionSpaces/  # Projections, detail operators, Haar/contrast bases, commutant
├── NumberTheory/    # Dirichlet convolution, characters, valuations,
│                    #   the factorization lens, the measurability bridge
├── Integration/     # Dual filtrations, mediator lines, runtime algebra
├── Analysis/        # Digit-conditional signal analysis, the Fourier ceiling
├── Composition/     # Multi-timeline routing, deadlock-freedom, timing bounds
├── Applications/    # Corpus theory governing deployed systems (Field25519Carry)
└── Modes/
    ├── VariableRadix/    # Mode I, realizability (Theorem 43), subshift gauges,
    │                     #   the Gosper engine cluster
    ├── ContextDependent/ # Mode II oracles
    ├── ExtendedBase/     # Mode III: walls, wires, the spatial thermometer
    ├── BaseZeroSea/      # Phase 10 substrate dynamics, the linear-chain bridge
    ├── Adelic/           # Place engines, product formula (ℚˣ), gauge bound,
    │                     #   rigidity, the AdelicLaw interface, function-field keystone
    └── SyntheticPlace/   # Phase 14: gauge keystone, coupling, certificates,
                          #   conservation + rigidity, network geometry, grading,
                          #   the SU7 network machine + Phase-8 bridge
```

`FdrsFormal.lean` is the root module aggregating the development, and every
module above is imported (transitively) by it, so the default `lake build`
compiles the whole tree. `Main.lean` is a trivial executable entry point. A
generated module dependency graph lives at
[`docs/dependency-graph.svg`](docs/dependency-graph.svg). Design records for
the newer complexes are in [`docs/synthetic-place/`](docs/synthetic-place/) and
[`docs/function-field/`](docs/function-field/); superseded design documents are
archived under [`docs/archive/`](docs/archive/).

## Building

Requires the toolchain pinned in [`lean-toolchain`](lean-toolchain) via
[elan](https://github.com/leanprover/elan); Mathlib is fetched by Lake at the
revision pinned in [`lake-manifest.json`](lake-manifest.json). The maintenance
tooling needs Python with `pyyaml` ([`requirements.txt`](requirements.txt)).

```bash
lake exe cache get             # prebuilt Mathlib (recommended)
lake build                     # the formalization
python3 scripts/fdrs-summary   # live status: axioms, sorries, coverage
```

[`docs/TESTING.md`](docs/TESTING.md) covers work-in-progress modules outside
the default target; [`docs/GENERAL_CONTEXT.md`](docs/GENERAL_CONTEXT.md)
documents the trust hierarchy of the generated metadata;
[`docs/notation.md`](docs/notation.md) is the symbol reference extracted from
live code.

## Scope

This repository contains the Lean formalization, its build configuration, the
maintenance tooling, and the documentation needed to build and check it. It
intentionally excludes the SageMath and ML experiments, paper drafts, and
generated media that live alongside the formalization during development. It
is the canonical Lean artifact of the Hyphaeic variable-representation
research program (registry id `project-fdrs-formal`), built within the
`workspace-math-proof-env` toolchain (Lean 4 + Python + SageMath).

## License

Licensed under the [Hyphaeic Public License, Version 1.0](https://github.com/hyphaeic/hpl).
See [LICENSE](LICENSE) and [NOTICE](NOTICE). Third-party components (Lean 4,
Mathlib) are under their own licenses, as noted in [NOTICE](NOTICE).
