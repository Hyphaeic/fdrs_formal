# The Adelic Complex — design notes & build guide

*A coupled, exact, floor-free machine that tracks a quantity across the places of
the adele ring, built from the FDRS Lean corpus. Design documents only — the
machine is **not built**; this folder is the context and plan for building it.*

---

## What this is

The FDRS corpus already has an exact "clock" at the **Archimedean place**: the
Gosper / bihomographic engine (Phase 13.6) that combines continued-fraction
streams in exact `ℤ`, emitting a digit only when a four-corner **floor trap**
certifies it. The *adelic complex* asks: extend that idea off the real line.
Track one quantity simultaneously at the Archimedean place **and** at the
non-Archimedean (p-adic) places, couple those positions, and never fall back on
floats or a coerced common clock.

The thesis, in one breath:

> Each **place** `v` of `ℚ` is a **timeline** running the numeration native to
> that place — continued fractions at `∞`, Hensel p-adic digits at each prime
> `p`. Both kinds of timeline are exact integer-ledger transducers of the *same
> flat-`ℤ` homographic shape*, but they differ in three ways: their **recurrence**
> (CF inversion `[[a,1],[1,0]]` vs. Hensel shift `[[p,α],[0,1]]`), their
> **within-place invariant** (`|det|=1`, `SL₂(ℤ)`, vs. the non-unimodular
> `det=±pᵏ`), and — the crux — their **emission certificate**. At `∞` a digit
> is forced by an **order trap** (`emit_traps`, the floor pinned between interval
> endpoints). At `p` a digit is forced by a **congruence** (the residue pinned
> mod `pᵏ` — FDRS's `residue_depends_on_prefix`). The adelic complex couples
> these heterogeneous timelines, and the global invariant that ties one quantity
> across its positions is the **product formula** `∏_v |x|_v = 1` — the adelic
> *analogue* of `|det|=1` (a structural rhyme, not the same invariant; `04` §3.1).

Both emission certificates **already exist in the corpus, axiom-clean.** The
machine is the *coupling* of two engines we have, under a conservation law we can
state. That is the whole content, and the whole honesty: no new mathematics is
claimed — the deliverable is a *verified, unified artifact*.

---

## The honest frame (read before believing anything here)

This project's discipline (see `../gosper-fdrs-handoff.md` §0) is to separate
**substantiated** from **confabulated**. The handoff explicitly flags two things
this folder must not paper over:

- *"The adelic machine — not built; coupling two places is a two-place toy, not
  the adele ring."*
- *"The `BihTensor` is metric-agnostic algebra, but its correctness (`emit_traps`)
  is Archimedean (requires `IsStrictOrderedRing`, which `ℚ_p` lacks). So the
  engine is **not** adelic."*

Both are true and both are load-bearing for the design. The Archimedean engine
does **not** extend to `ℚ_p` for free — and that is the *point*, not a bug: the
p-adic places need a *different* certificate (congruence, not order), which the
corpus also already has. Every claim below carries a provenance tag:

| tag | meaning |
|---|---|
| ✅ **BUILT** | formalized in Lean, axiom-clean (`propext`/`Classical.choice`/`Quot.sound` only); module cited |
| 🟡 **BUILT-THIN** | in Lean but abstract/scaffold (e.g. payload-agnostic, or proven over a toy) |
| 📐 **MATHLIB** | exists in Mathlib, importable, not yet wired into FDRS |
| 📜 **SPEC** | described in `fdrs.md` prose, not in Lean |
| 🔬 **CONJECTURE** | plausible design hypothesis, unproven |
| 🔨 **TO-BUILD** | must be written for the machine |

If you find a claim here without a tag, treat it as 🔬 until grounded.

---

## Reading order

| # | file | what it gives you |
|---|---|---|
| 0 | [`00-thesis-and-scope.md`](00-thesis-and-scope.md) | the idea, the two coupling axes, the central obstruction & its resolution, the no-floats discipline, the honest scope ladder |
| 1 | [`01-mathematical-background.md`](01-mathematical-background.md) | adeles, places, valuations, the product formula, p-adic vs CF expansions, the two ultrametrics — all classical, cited |
| 2 | [`02-corpus-leverage.md`](02-corpus-leverage.md) | the exact Lean tools to build from, leg by leg, with signatures, provenance, and the order-dependence map (what transfers to `ℚ_p`, what doesn't) |
| 3 | [`03-architecture.md`](03-architecture.md) | the machine: places as nodes, per-place engines, the two-certificate emission table, state format, step semantics, coupling fabric |
| 4 | [`04-coupling-invariant.md`](04-coupling-invariant.md) | the real math / open problem: product formula as adelic `|det|=1`, the adelic emission-soundness conjecture, the test plan + scratch results |
| 5 | [`05-build-roadmap.md`](05-build-roadmap.md) | staged Lean build: milestones, acceptance criteria, each generalizing an existing result, Mathlib import decisions, verification gates |
| 6 | [`06-anti-confabulation.md`](06-anti-confabulation.md) | the scope ledger: what is NOT done, what's conjecture, what *looks* adelic but isn't, the failure modes |

Scratch validation (exact arithmetic, no floats) lives in
[`scratch/adelic_validation.py`](scratch/adelic_validation.py) — run it; its output
grounds the claims in `04`.

---

## Status

**Design only.** Nothing in this folder is machine-checked machine code; it is the
context and plan for an *eventual* build. The corpus pieces it leans on **are**
machine-checked, and are cited as such. The one genuinely new mathematical
obligation — the cross-place coupling invariant (`04`) — is flagged 🔬 throughout
and is the first thing the build (`05`, milestone M4) must either prove or retreat
from.
