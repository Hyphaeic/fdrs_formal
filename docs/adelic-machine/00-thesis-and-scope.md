# 00 — Thesis & Scope

*The idea, the two coupling axes, the central obstruction and its resolution, the
no-floats discipline, and an honest scope ladder. Provenance tags per the README.*

---

## 1. The idea

The adele ring of `ℚ` is `𝔸_ℚ = ℝ × ∏'_p ℚ_p` — a quantity viewed *at once*
through every metric "place": the Archimedean place `∞` (ordinary magnitude) and
one non-Archimedean place per prime `p` (p-adic valuation). FDRS already has an
exact, density-free engine at `∞`: the Gosper bihomographic transducer
(Phase 13.6, `Bihomographic.lean`) — `SL₂(ℤ)` ledgers, `|det|=1`, emitting a
continued-fraction digit only when a four-corner floor trap certifies it
(`emit_traps`, ✅).

The **adelic complex** is the machine that runs *the same idea at every place and
couples the places*:

- a quantity `x` is represented not by one stream but by a **family of streams**,
  one per place — its continued fraction at `∞`, its Hensel digits at each `p`;
- each place's stream is produced by an **exact integer ledger** of the same
  flat-integer homographic/bihomographic *shape* — that ledger algebra is pure `ℤ`
  and already place-agnostic (✅). (It is the *shape* that is shared, not the group:
  at `∞` the read is the unimodular CF step `[[a,1],[1,0]]`; at `p` it is the
  non-unimodular Hensel shift `[[p,α],[0,1]]` — same `ℤ`-tuple algebra, different
  recurrence and different determinant law, `03` §3.);
- the places are **coupled** — combined, compared, and constrained — with the
  **product formula** `∏_v |x|_v = 1` as the conserved global invariant;
- **nothing ever becomes a float**, and there is no coerced common clock.

This is the "adelic direction" named as aspirational in the handoff (§2, the
adelic north-star) and as open frontier #2 ("the second place / p-adic lane:
emit without a floor, concretely"). This folder turns that aspiration into a
build plan grounded in code that exists.

---

## 2. Two coupling axes (keep them distinct)

The word "coupling" hides two genuinely different operations. Conflating them is
the easiest way to confabulate, so we name both:

**Axis I — intra-place, inter-stream (combine).**
At a *fixed* place `v`, combine two streams `x_v, y_v` into `z_v = x_v ⊕ y_v`
(`⊕ ∈ {+, ×, …}`). This is the bihomographic tensor `BihTensor` (✅): one node,
8 integers, two inputs, one output, exact. The hyper-Gosper tree (`coupleAll`, ✅)
scales this to `N` streams at one place without exponential blowup. **This already
works at `∞`.** At `p` it needs a p-adic emission certificate (see §3).

**Axis II — inter-place, intra-quantity (the adelic axis).**
For a *single* quantity `x`, couple its positions `x_∞, x_2, x_3, …` across
*different* places. The conserved invariant here is the product formula. **This
is the new axis** — the literal "coupling between separate adelic positions within
the adelic ring." It is what makes the complex *adelic* rather than just a pile of
per-place clocks.

A full machine uses both: within a place you may combine streams (Axis I); across
places you track one quantity under the product formula (Axis II). The handoff's
open frontier #1 ("is there a `|det|=1`-style quantity conserved across a node's
two inputs and its output?") is an **Axis-I** question; the product formula is an
**Axis-II** answer. They are not the same invariant and must not be sold as such.

---

## 3. The central obstruction — and its resolution

**Obstruction.** The Archimedean soundness certificate does not transfer to
`ℚ_p`. Concretely (verified by reading the source, `02` §3): `emit_traps`,
`emitReady_traps`, and `bilinear_ge_const` (`BihomographicSound.lean`) all carry
`[CommRing K] [LinearOrder K] [IsStrictOrderedRing K]`. They *need* an order: the
"four corners" are the order-endpoints `{1,∞}²` of the input tail, and the trap is
proved by monotonicity (`mul_nonneg`, `sub_nonneg`). `ℚ_p` has **no order**. So
the Gosper *engine algebra* transfers verbatim (it is pure `ℤ`), but its
*certificate of correctness does not*. **This is exactly why "the engine is not
adelic."**

**Resolution.** The non-Archimedean places do not *want* a floor. The p-adic
digit `a_i` of a value is determined by a **congruence** — the residue `mod
p^{i+1}` — not by an order comparison. And FDRS already proves the corresponding
certificate, axiom-clean:

> `residue_depends_on_prefix` (✅, `NumberTheory/CylinderMeasurability.lean`):
> when `q ∣ placeValue b L`, the residue `dec(τ) mod q` depends only on the first
> `L` digits — with sufficiency `congruenceSet_is_cylinder_union` and a *sharp*
> necessity `congruenceSet_not_cylinder_union_of_not_dvd`.

Specialized to constant base `p` (so `placeValue = pᴸ`), this says: **the next
p-adic digit is forced once a finite prefix of the input is known** — the precise
non-Archimedean dual of `emit_traps`. The scratch script (`scratch/`, Demo B)
exhibits it numerically: for a homographic map over `ℤ₅`, output digit `aᵢ` is
frozen as soon as the input is known `mod 5^{i+1}`. No order, no floor, no float.

So the obstruction *resolves into the design*: the adelic complex is the coupling
of **two emission engines with two certificates** —

| | Archimedean `∞` | p-adic `p` |
|---|---|---|
| tail domain | `[1,∞]` | `ℤ_p` |
| "corners" | `{1,∞}` (order endpoints) | residue-disks `{0,…,p−1} mod p` |
| digit rule | `⌊N/D⌋` (floor) | `N/D mod p` (residue; needs `v_p(D)=0`) |
| **certificate** | `emit_traps` (order trap) ✅ | core `residue_depends_on_prefix` (congruence) ✅ → ledger-level `padic_emit_traps` 🔨 |
| typeclass | `[IsStrictOrderedRing K]` | discrete valuation / `[Valued K …]` 📐 |
| within-node invariant | `\|det\|=1` (`SL₂ ℤ`) ✅ | `v_p(det)=#steps` / `det=±pᵏ`, **not** `SL₂ ℤ` 🔨-easy |

The **Archimedean certificate is built** (`emit_traps`, ✅); the **p-adic
congruence certificate's *core* is built** (`residue_depends_on_prefix`, ✅) but the
**ledger-level `padic_emit_traps` is still to build** (🔨, M0). The machine is the
*unification of the two under one "emit-when-forced" abstraction* plus the Axis-II
coupling. That unification — not any new theorem — is the deliverable's novelty.
Note the within-node invariant is **not** the same at both places: the Hensel shift
recurrence is non-unimodular (`det ↦ p·det`), so the p-adic ledger is **not**
`SL₂(ℤ)` (see `03` §3b, `04` §2).

---

## 4. The no-floats / no-clock-coercion discipline

The user constraint ("we do not want to fall back onto floats or other clock-based
coercion") is not cosmetic; it is the design's spine, and the corpus already
honors it on the `∞` side. Made precise:

1. **No reals in the engine.** The Archimedean engine is pure `ℤ`; `ℝ` appears
   *only* in soundness statements (`emit_traps`'s `K`, the metric `cfDist`), never
   in any computation (✅, confirmed in `02` §3). The adelic complex keeps this:
   `ℝ` and `ℚ_p` appear only as the *semantic targets* against which soundness is
   stated, never as runtime values.
2. **No materialized p-adic floats either.** The p-adic side stays in exact
   integer ledgers + digit streams (lists of residues in `{0,…,p−1}`); a `ℚ_p`
   element is never approximated. "No floats" extends to "no p-adic truncation
   masquerading as a value."
3. **No coerced common clock.** Places are *incommensurable* timelines (this is
   the `ThreeLineMediator` philosophy, ✅): there is no shared tick that all
   places advance by. Coupling is by *integer/rational identities* (the product
   formula; the `SL₂(ℤ)` ledgers), not by aligning clocks.

The litmus test for any proposed mechanism: *does it stay exact and integer-driven,
and does it avoid presupposing a single global clock?* If it reaches for a float or
a common tick, it is the wrong mechanism.

---

## 5. Honest scope ladder

"The adele ring" is an infinitary object (a *restricted* product over **all**
primes, with almost-all components constrained to `ℤ_p`). A machine cannot run
infinitely many places. So the scope is a ladder, and we say exactly which rung
any claim lives on:

- **L0 — single place.** `∞` alone is the existing Gosper engine (✅). One prime
  `p` alone is the p-adic engine to be built (🔨, M0 in `05`).
- **L1 — two-place toy `S = {∞, p}`.** Couple one Archimedean and one p-adic
  timeline. This is the honest first "adelic" artifact (🔨, M1). The handoff's
  warning lives here: *this is a two-place toy, not the adele ring.* We will say so.
- **L2 — finite `S`-adeles `S = {∞, p₁,…,p_k}`.** A finite set of places; the
  product formula becomes checkable as a finite identity over `S` *only when `x`
  is `S`-integral* (no places outside `S`). Most engineering lives here (🔨, M2).
- **L3 — restricted product (genuine adeles).** Almost-all components in `ℤ_p`,
  encoded by the "support is finite" condition. This is where it earns the name
  *adelic* (🔨/🔬, M3). The `freePart`/`smoothPart` factorization (✅) is the
  corpus's existing handle on "all places at once via factorization."
- **L4 — the coupling-invariant theorem.** A machine-checked statement that the
  complex's per-place streams jointly satisfy the product formula / an adelic
  emission-soundness law (🔬, M4). This is the open math (`04`).

A claim tagged "adelic" without naming its rung is a confabulation. Default
target for the *first buildable* artifact is **L1**, designed so it extends to
L2/L3 without redesign.

---

## 6. What success looks like

A staged, machine-checked artifact in which:

1. a p-adic place runs an **exact, floor-free** homographic/bihomographic engine
   whose emissions are **certified by congruence** (the p-adic dual of
   `emit_traps`), reusing `residue_depends_on_prefix` (M0);
2. an Archimedean place (the existing Gosper engine) and a p-adic place are
   **coupled into one complex** representing a single quantity, exact, no floats
   (M1);
3. the coupling carries a **conserved invariant** — at minimum the product formula
   as a checkable identity on the emitted data — proven in Lean (M4);

with every rung's scope stated, every `🔬` discharged or retracted, and the whole
thing free of floats and coerced clocks. Anything less is a partial result, and
`06` records which part.

Next: [`01-mathematical-background.md`](01-mathematical-background.md) for the
classical objects, or jump to [`02-corpus-leverage.md`](02-corpus-leverage.md) for
the exact tools.
