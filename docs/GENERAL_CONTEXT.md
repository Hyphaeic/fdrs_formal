# Contributor & Maintenance Guide

This document explains how the FDRS Formal repository is organized, which sources are
authoritative, and how the generated metadata is produced. For build and status-check
commands, see [`TESTING.md`](TESTING.md).

## What this project is

FDRS Formal is a Lean 4 formalization of **Function-Defined Radix Systems** — a
mathematical framework for mixed-radix number systems in which the base at each digit
position is determined by a function. The specification lives in a single document,
[`fdrs.md`](fdrs.md), organized into 14 phases spanning foundations (radix sequences,
bijections, ultrametric topology) through analytic number theory, digit-conditional
signal analysis, multi-timeline composition, generated (continued-fraction) timelines
with certified emission engines, and the synthetic place complex (coupled radix
networks: gauges, conservation, and their machine-checked boundaries). Satellite
complexes (the adelic machine, the function-field keystone) live under
`Modes/Adelic/` with design records in `docs/`.

Every spec item carries a **global monotonic ID** (e.g. "Definition 47", "Theorem 12")
with an annotation preserving its original section number, e.g. `[§2.1.3 · Phase 3,
Fragment 1]`.

## Canonical sources (trust hierarchy)

| Priority | Source | What it is |
|---|---|---|
| 1 | `docs/fdrs.md` | The mathematical specification. Single source of truth for what must be proven. Hand-authored. |
| 2 | `FdrsFormal/**/*.lean` | The formalization itself. Ground truth for what *has been* proven. |
| 3 | `data/fdrs-index.yaml` | Machine-generated master index mapping every spec item to its status and Lean location. Regenerated, never hand-edited. |
| 4 | `data/item-deps-lean.yaml` | Dependency graph extracted from the compiled Lean environment via `getUsedConstants` — what each declaration actually uses. |
| 5 | `data/item-deps.yaml` | Supplementary dependency graph parsed from prose references in `fdrs.md`. Fills gaps for items with no Lean code yet. |
| 6 | `docs/fdrs-index.md` | Human-readable rendering of the index (auto-generated). |
| 7 | `data/file-deps.yaml` | Lean module-level import graph (auto-generated). |
| 8 | `docs/notation.md` | Symbol reference extracted from live code (auto-generated). |

**Trust rule**: everything in `data/` and the generated docs is computed from `fdrs.md`
plus the live Lean code by the scripts below. Treat them as authoritative metadata — but
if something looks wrong, verify against the source files (`fdrs.md`, the `.lean`
sources), not the generated output. The Lean-derived dependencies (`item-deps-lean.yaml`)
are the most reliable, since they come from what the proofs actually reference.

## The tooling pipeline

The scripts in [`../scripts/`](../scripts) maintain the spec ⇄ Lean correspondence. They
require only Python 3.10+ and `pyyaml` (see `requirements.txt`); the Lean-dependency step
additionally requires a compiled build.

```
scripts/fdrs-rebuild        # runs the full pipeline below in order
  ├─ fdrs_index.py          # scan .lean sources       → data/fdrs-index.yaml
  ├─ fdrs_deps.py           # parse fdrs.md references  → data/item-deps.yaml, file-deps.yaml
  ├─ fdrs_lean_deps.py      # introspect compiled env   → data/item-deps-lean.yaml  (needs `lake build`)
  ├─ fdrs_graph.py          # render dependency graphs  → data/item-graph*.{dot,svg}  (needs Graphviz)
  └─ fdrs_notation.py       # extract notation table    → docs/notation.md
```

Other entry points:

- `scripts/fdrs-summary` — the status dashboard and query CLI (`--sorries`, `--stubs`,
  `--axioms`, `--check`, `--phase N`, `--rebuild`, `--spec-index`, …). It scans the live
  `.lean` sources, so it works without a build.
- `scripts/fdrs-check` — consistency check used by CI: verifies the generated index is
  current and warns about declaration stubs.

The rendered dependency-graph images are **not committed** (they are large and fully
regenerable). Run `scripts/fdrs-rebuild` locally to produce them.

## Status model

`fdrs-summary` classifies each spec item by the state of its matched Lean declarations:

| Status | Meaning |
|---|---|
| `proven` | All matched declarations are genuine proofs. |
| `partial` | A mix of genuine proofs and stubs. |
| `stub` | All matched declarations are placeholders (e.g. `True := trivial`). |
| `axiom` | Backed by an `axiom`. |
| `sorry` | Contains a `sorry`. |
| `missing` | No Lean declaration found for the item. |

At the **declaration** level the tooling also counts raw `sorry`s and stub kinds
(`True := trivial`, `Prop := True`, `fun _ => 0`) independently of item matching. These
declaration-level counts (`--sorries`, `--stubs`) are the reliable signal for the state
of the code.

The item-level classification, by contrast, is a rough navigation aid, not a scorecard.
It matches spec-item titles to declaration names heuristically and **falls back to
`proven` when it finds no match**, so the item-level coverage percentage tends to
over-report. Don't treat it as a pass/fail headline: a high "proven" count does not mean
every prose claim is fully formalized — a theorem can compile while stating a weaker or
building-block form of its spec item. When it matters, read the `.lean` source and check
`#print axioms` on the specific result.

## Conventions when contributing

- Add or update the mathematics in `fdrs.md` first; it defines what the Lean code must
  establish.
- Keep Lean module paths aligned with the spec structure (`FdrsFormal/<Area>/...`).
- After changing `.lean` files, regenerate the index (`fdrs-summary --rebuild`) and run
  `fdrs-summary --check` before committing.
- Never hand-edit anything under `data/` or the auto-generated docs — regenerate them.
