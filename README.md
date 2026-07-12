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

  [Specification](docs/fdrs.md) · [Index](docs/fdrs-index.md) · [Design records](docs/synthetic-place/) · [Toolchain](scripts/)

</div>

---

## What this is

This repository is a long-form mathematical research program carried out
spec-first in a single document and machine-checked item by item in Lean 4
against [Mathlib](https://github.com/leanprover-community/mathlib4). The
specification ([`docs/fdrs.md`](docs/fdrs.md)) has grown through **fourteen
phases** of numbered definitions, theorems, and propositions; every numbered
item has a Lean proof, and the correspondence is maintained by tooling rather
than by prose claims. The default build carries **zero axioms and zero
sorries**.

The subject is *what number representation becomes when its structure is a
free parameter*. Classical positional notation fixes a base; FDRS lets the
radix at each position be computed by a function — of the position, the prefix
already written, an external context, or the state of another number line
entirely. The corpus develops what survives each generalization and what
breaks, with the boundary in every case proven, not asserted.

**The arc:** foundations (canonical bijections with ℕ, the odometer, the
prefix ultrametric, a conditional-expectation multiresolution analysis on
mixed-radix cylinders, and the bridge to analytic number theory) → the three
modes of function-defined radices and the design space of engineered
ultrametrics → multi-timeline routing and spatialized digits → generated
gauges, where continued-fraction timelines replace base products and digit
emission becomes a *certified* act → the synthetic place complex: coupled
radix networks, their geometry, their conservation laws, and the precise
obstructions separating them from numbers.

## Selected results

A sample chosen to show the range; the [index](docs/fdrs-index.md) maps every
item to its proof.

**Foundations and bridges.**
- Canonical bijections between digit spaces and ℕ; the tick is `+1` under
  decode and `1`-Lipschitz in the ultrametric; balls are exactly cylinders.
- A discrete multiresolution analysis: block projections as conditional
  expectations, detail operators, L² Pythagoras, and the commutant theorem —
  an operator commutes with every scale projection iff it is
  scale-block-diagonal in the Haar/contrast basis.
- The cylinder-measurability bridge: a congruence condition is decidable from a
  positional prefix **iff** the modulus divides the place value (both
  directions, with the sharp converse) — the exact interface between the
  additive and multiplicative filtrations, including a constructive witness of
  their generic non-commutation.

**Realizability.** The full characterization of which ultrametrics are
realizable by sibling-uniform radix laws (Theorem 43): an ultrametric is
realizable **iff** every open ball is a prefix cylinder and every cylinder has
canonical diameter — proven in both directions, with the two conditions doing
provably separate work (the first pins the tree, the second pins the gauge)
([`MetricRealizability.lean`](FdrsFormal/Modes/VariableRadix/Realizability/MetricRealizability.lean)).

**Certified emission engines (Phase 13).** Continued-fraction timelines where
the gauge is generated rather than multiplied out, with Gosper-style
homographic/bihomographic engines that emit a digit only when *every* possible
continuation of the unread input forces it — the four-corner order trap at the
Archimedean place, the congruence trap at p-adic places, the admissibility
trap on finite grammars. Exact integer ledgers, no floating point anywhere;
`√2·√2` emits nothing, honestly.

**The adelic complex.** Heterogeneous place-engines under one scheduler with
proven confluence; the product formula on ℚˣ in exact arithmetic; the
finite-precision gauge bound; and the rigidity boundary — an FDRS gauge
reproduces a p-adic place value **iff** its base is constantly p, so there are
no synthetic places on ℚ. A function-field keystone stakes the genuinely
synthetic instance ([`docs/function-field/`](docs/function-field/)).

**The synthetic place complex (Phase 14).** What survives when number lines
couple: any positive monotone prefix gauge induces an ultrametric with
ball = cylinder (both prior corpus metrics become instances); coupling
generically destroys the odometer while the geometry survives; conservation
migrates from product formulas — impossible for genuinely coupled systems, by
a machine-checked separability no-go — to interface balance laws
(`issued = consumed + pending`, proven for arbitrary coupling in any
commutative monoid of carries); no scalar gauge can metrize a concurrent
network (proven), forcing the observer-glued construction; and "bigger digit"
exists iff every coupling loop has trivial holonomy — with a verified
three-digit Penrose staircase on the other side of the boundary. Together with
ragged fibers and bilateral coupling, that gives three independent,
machine-checked obstructions separating coupled radix complexes from number
systems.

**The SU7 network machine (Phase 14, §14.12–14.13).** The coupled radix network
as a verified abstract machine: a three-clause firing rule whose fan-out
lawfulness is a guard (declared carry mass partitioned exactly across transport
edges), whose well-formedness *is* dependency grading (Phase 8's deadlock
certificate reused verbatim), with per-edge balance laws, a decidable
couplability certificate (witnessed live and blocked), per-node emission traps
transported unchanged, a conditional Kahn diamond whose independence
side-condition is **derived** from the capacity-one latency discipline rather
than assumed, and liveness in honest factored form. A concretization bridge
proves the Phase-8 timeline-graph layer is an instance of this machine (a
timeline graph IS a network shape; time-ordering IS grading; queue registers
balance at every capacity).

**Applications (§14.14).** The corpus vocabulary load-bearing in production
arithmetic: GF(2^255 − 19) under Ed25519 read as a ten-digit variable-radix
ring — carries are ledger-balanced redistributions, the wrap has holonomy 19
(a digit ring on the frustrated side of the grading dichotomy), and the
eleven-carry schedule provably restores the digit bound, licensing the Rust
kernel's lazy reduction
([`Field25519Carry.lean`](FdrsFormal/Applications/Field25519Carry.lean)).

## Method

- **Spec first.** `docs/fdrs.md` is the single source of truth; Lean modules
  cite the numbered items they prove, and an erratum is preferred over a
  silent fix when the spec is wrong.
- **Ask the tooling, not the prose.** `python3 scripts/fdrs-summary` scans the
  live source for axioms, sorries, stubs, and per-phase coverage; numbers in
  documentation are treated as stale by default.
- **Honest scope, as working practice.** Every module carries an honest-scope
  banner; design documents carry anti-confabulation ledgers; finite witnesses
  use kernel `decide` (never `native_decide`); classical results are cited as
  classical — the contribution is the connection and the verified artifact.

## Layout

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

The default `lake build` target compiles the entire tree — every module above is
imported (transitively) by the root module (wiring pass of 2026-07-12).

`FdrsFormal.lean` is the root module aggregating the development; `Main.lean`
is a trivial executable entry point. Design records for the newer complexes
live in [`docs/synthetic-place/`](docs/synthetic-place/) and
[`docs/function-field/`](docs/function-field/); superseded design documents
are archived under [`docs/archive/`](docs/archive/).

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

[`docs/TESTING.md`](docs/TESTING.md) covers the work-in-progress modules
outside the default target; [`docs/GENERAL_CONTEXT.md`](docs/GENERAL_CONTEXT.md)
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
