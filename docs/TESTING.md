# Building & Checking the Formalization

This guide covers building the Lean development and checking its formal status. For the
canonical-source layout and how the metadata is produced, see
[`GENERAL_CONTEXT.md`](GENERAL_CONTEXT.md).

## Prerequisites

- [elan](https://github.com/leanprover/elan) — installs the Lean toolchain pinned in
  [`../lean-toolchain`](../lean-toolchain) (`leanprover/lean4:v4.27.0-rc1`).
- Python 3.10+ with `pyyaml` (`pip install -r ../requirements.txt`) for the status tooling.
- Graphviz (`dot`) — optional, only needed to render dependency-graph images.

## Building

```bash
# Fetch the prebuilt Mathlib cache first — without this, Lake compiles Mathlib
# from source, which takes a very long time.
lake exe cache get

# Build the default target: the FdrsFormal root module and everything it imports.
lake build
```

The default `lake build` target compiles the root module `FdrsFormal` and its transitive
imports (the main development). It should finish with no errors and no `sorry` warnings.

### Building a specific module

```bash
lake build FdrsFormal.Core
lake build FdrsFormal.Analysis.DigitConditional
lake build FdrsFormal.FunctionSpaces.Projections.Details
```

### Coverage of the default target

Since the 2026-07-12 wiring pass, **every module in the tree is imported
(transitively) by the root module**, so a bare `lake build` compiles the entire
formalization — including the Phase-13 Gosper cluster, the adelic complex
(`Modes/Adelic/`), the synthetic place complex and SU7 network machine
(`Modes/SyntheticPlace/`), and the applications layer (`Applications/`). There is
no separate "unwired modules" step. If a new leaf module is added, wire it into
its directory aggregator (e.g. `Modes/SyntheticPlace.lean`) so the default target
keeps this property; `python3 scripts/fdrs-summary` reports any modules that fall
outside the default build.

The corpus carries no outstanding `sorry`s and no axiom declarations; the build
should finish with no errors and no `sorry` warnings (historical note: the last
`sorry`s, in `FunctionSpaces/Haar/WaveletPacket.lean`, were eliminated in the
2026-05/06 proof-completion pass).

### Clean rebuild

```bash
lake clean && lake exe cache get && lake build
```

## Checking formal status

The status tooling scans the live `.lean` sources directly (no build required) and
reports axioms, `sorry`s, declaration stubs, and spec-item coverage:

```bash
python3 scripts/fdrs-summary            # Dashboard: files, theorems, axioms, sorries, stubs
python3 scripts/fdrs-summary --sorries  # Every sorry, with file:line
python3 scripts/fdrs-summary --stubs    # Every declaration stub (e.g. `True := trivial`)
python3 scripts/fdrs-summary --axioms   # Every axiom declaration
python3 scripts/fdrs-summary --check    # Verify the generated index matches live code
```

`--check` is also what CI runs (after `lake build`); see
[`../.github/workflows/lean_action_ci.yml`](../.github/workflows/lean_action_ci.yml).

## Interactive checks inside Lean

```lean
#check placeValue binaryRadix 0   -- inspect a type
#eval  placeValue binaryRadix 5   -- evaluate a computable definition (def, not theorem)
example : placeValue binaryRadix 3 = 8 := rfl   -- prove a concrete instance
```

`#eval` works only for computable `def`s, not `theorem`s or `noncomputable` definitions.

## IDE integration

- **VS Code**: install the official *Lean 4* extension; open the repository root so it
  picks up `lakefile.toml` and the toolchain.
- **Neovim**: [`lean.nvim`](https://github.com/Julian/lean.nvim).

Hover shows types and docstrings; the infoview shows the goal state at the cursor.

## Resources

- Lean 4 manual — <https://lean-lang.org/lean4/doc/>
- Mathlib docs — <https://leanprover-community.github.io/mathlib4_docs/>
- The specification — [`fdrs.md`](fdrs.md) (the mathematical source of truth)
