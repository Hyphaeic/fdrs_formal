# 06 — Anti-Confabulation Ledger

*The honest-broker backstop for this sub-project. Carries forward the handoff's
anti-confabulation list (§6 there) and extends it for the adelic complex. If a
future write-up, commit message, or claim contradicts this file, this file is
right until the code says otherwise. Tags per README.*

---

## 1. The one-line truth

**Nothing in `adelic-machine/` is built.** It is a design + research notes + a
scratch validator. The corpus pieces it leans on **are** machine-checked and are
tagged ✅ with module names; everything tagged 🔨/🔬 is to-build/unproven. The
deliverable, *if built*, is a **verified unified artifact**, not new mathematics —
the math (Ostrowski, Hensel, product formula, valuations, `SL₂(ℤ)`) is all
classical.

---

## 2. Do NOT claim (each with the correction)

- ❌ *"The adelic machine exists / the Gosper engine is adelic."*
  → The engine's soundness (`emit_traps`) is **Archimedean** (`[IsStrictOrderedRing
  K]`, which `ℚ_p` lacks — verified in source, `02` §3). The engine *algebra* is
  place-agnostic `ℤ`; its *certificate* is not. The p-adic certificate
  (`padic_emit_traps`) is **🔨 to build** (its combinatorial core
  `residue_depends_on_prefix` is ✅, but it is not yet wired to a ledger).

- ❌ *"`|det|=1` is the coupling invariant."*
  → `|det|=1` is the **within-place** exactness invariant at `∞`, and at `p` it is
  even replaced by `v_p(det)=#steps` (a p-power det, `04` §2). The **cross-place**
  invariant is the **product formula** `∏_v|x|_v=1`. They *rhyme* (both "a
  determinant is a unit," local vs. idelic) but are **not the same invariant**
  (`04` §3.1). Asserting identity is confabulation.

- ❌ *"The complex couples all places of the adele ring."*
  → Only a **finite** set `S` of places runs (L0–L2). The restricted product over
  *all* primes (L3) is 🔨/🔬 and infinitary. Always state the rung (`00` §5). A
  two-place `{∞,p}` artifact is a **toy**, said so in its own module banner (`05`,
  M1).

- ❌ *"Additive coupling is conserved across places."*
  → **False.** `|x+y|_v` is not a local function of `|x|_v,|y|_v`, and `x+y` can
  acquire new places (validated, scratch Demo D). Only **multiplicative** (idele)
  coupling composes locally. The build targets the multiplicative axis; additive
  is the boundary (strong-approximation territory), not a solved feature.

- ❌ *"The running product `∏_v|x|_v` equals 1 at every step."*
  → At **finite precision** it does **not** — the Archimedean factor only
  *converges* (CF convergent ≈ `x`), while p-adic factors stabilize finitely
  (`04` §3.3). The honest invariant is a **gauge-controlled bound** (🔬,
  possibly with no effective constant — the likeliest stall point).

- ❌ *"Phase 8 routing gives the coupling law."*
  → `Composition/` routing **is** in Lean (🟡, contra the handoff's spec-prose
  framing) but is **payload-agnostic** (routes `ℕ`, proves acyclicity/timing). It
  is coupling **topology**, not coupling **arithmetic**. It supplies wiring, never
  a conserved quantity.

- ❌ *"`productMediator` already couples places."*
  → It couples **radix sizes** via a product law that **does not extend** to the
  generated/CF gauge (`fdrs.md` §13.4: "`overflowRate_product` has no analogue
  here"; handoff anti-confab). It is a structural ancestor, not the adelic coupler.

- ❌ *"We use Mathlib's adele ring."*
  → Not unless/until M3 needs the object. The design deliberately stays in exact
  `ℤ` ledgers + digit streams (no-floats discipline, `00` §4); `Padic`/`Valued`
  appear only as **soundness targets** (📐), as `ℝ` does in `emit_traps`.

---

## 3. Inherited anti-confabulation (still in force from the handoff §6)

- *"Tree coarsening → Gauss/Parry measure (thermodynamic limit)"* — **CONJECTURE**;
  the operator-algebra/multiresolution link is analogy. Unchanged here.
- *"Future affects past / temporal acausality"* — **not formalized**; only
  *structural* rollback (`Sea.revert`, wall-wrap) exists. The adelic complex adds
  no acausality.
- *"Source separation / scope resolution / fuzzy gaps / tree-contrast encodings"* —
  **not in the corpus**; do not introduce them via the adelic framing either.
- The CF ultrametric (`cfDist`, gauge `q_n`) is **not** a p-adic valuation
  (`01` §4). The Archimedean place uses it; p-adic places use the genuine p-adic
  metric (base-`p` cylinder, ✅). Do not blur them.

---

## 4. Status of every load-bearing claim in this folder

| claim | where | status |
|---|---|---|
| `emit_traps` needs an order; doesn't transfer to `ℚ_p` | `02`§3, `03`§3 | ✅ (read source) |
| `residue_depends_on_prefix` pins the next p-adic digit by a finite prefix | `02`§2, `03`§3 | ✅ (read source) + validated (Demo B) |
| `CompletedSpace`(const `p`) = `ℤ_p`; cylinder metric = `\|·\|_p` | `01`§3–4, `02`§4 | ✅ (identity, from defs) |
| product formula `∏_v\|x\|_v=1` | `01`§2, `04`§3 | ✅ classical + validated (Demo A) |
| multiplicative coupling composes, additive doesn't | `04`§3.2 | ✅ classical + validated (Demo D) |
| p-adic ledger has `det=±pᵏ`, not `\|det\|=1` | `03`§3b, `04`§2 | 🔨-easy (det-induction template ✅) |
| `padic_emit_traps` (the p-adic soundness theorem) | `03`§3c, `05` M0 | 🔨 (core ✅, wiring to do) |
| `p²`-corner bihomographic at `p` (Axis I) | `03`§3d | 🔬/🔨 |
| place-parametric `PlaceEngine` + generic scheduler | `03`§2, `05` M0.5 | ✅ BUILT (`PlaceEngine.lean`) |
| two-place complex `{∞,p}`, scheduler-independent | `05` M1 | ✅ BUILT (`Complex.lean`, `run_eq_of_counts`) |
| `S`-product-formula for `S`-integral `x` | `05` M2, `04`§4 | ✅ BUILT (`product_formula_nat`, factorization) |
| read `v_p` off the emitted stream (`padic_valuation_from_stream`) | `06`(this), bridge | ✅ BUILT (`ValuationStream.lean`) |
| restricted product / genuine adeles | `05` M3 | 🔨/🔬 (optional, after M2/M4a) |
| **M4a** exact soundness (value identified) | `04`§4, `05` M4a | ✅ BUILT (`product_formula_place`) |
| **M4b** `gauge_bound` (finite live prefixes) | `04`§3.3, `05` M4b | 📊 CONFIRMED classical (probe: `C=1`, `Θ(1/q_n²)`, Hurwitz) → reachable, mechanical Lean, NOT a stall |
| p²-corner p-adic bihomographic *soundness* (Axis I at `p`) | `03`§3d | 🔨 (algebra ✅ M0a; congruence-trap soundness next) |
| `ProductFormulaResidual` is symbolic-exponent, **not** `log p` | `03`§6 | 🔨 (NF1: `log p ∉ ℚ`) |

---

## 5. The failure modes (name them so they can't masquerade as success)

1. **Two bookkeeping systems, not one law — TESTED, DID NOT OCCUR.** The worry: if
   `gauge_bound` (`04`§3.3) had no effective constant, the Archimedean and
   non-Archimedean data would never reconcile at finite precision; the "coupling"
   would be two side-by-side ledgers, Axis-II "indistinguishable from noise." The
   scratch probe (`gauge_bound_probe.py`, item 4, run **before** Lean as the gate)
   **refuted this**: effective constant `C = 1`, deviation `Θ(1/q_n²)`, strictly
   decreasing — one conserved law. (The honest residue: the law is the *classical* CF
   convergent bound, so the coupling is real but the bound is not new mathematics.)
2. **Toy mistaken for adele ring.** Shipping L1/L2 and calling it "the adelic
   machine." Mitigation: per-module honesty banners (`05`), the scope ladder
   (`00`§5), this ledger.
3. **Order or non-rationals smuggled in.** Reaching for a floor / `ℝ` / `<` in the
   p-adic engine (because the `∞` template uses one), **or** a non-rational like
   `log p` in the coupling residual (a real bug in an earlier draft of `03`§6, now
   fixed to a symbolic-exponent `ProductFormulaResidual`). Mitigation: NF1–NF3
   (`03`§7) as lemmas; the p-adic `ready`/`sound` must be pure congruence/
   divisibility, and the residual must be exact `ℤ`/`ℚ` + finite exponents (logs
   only as an optional *interpretation* theorem, never the stored value).
4. **Additive overreach.** Presenting additive cross-place combination as conserved.
   Mitigation: `04`§3.2 + Demo D; build multiplicative-axis-first.
5. **Mathlib adele import as a shortcut that hides the work.** Importing
   `AdeleRing` and declaring victory without the exact-stream engine. Mitigation:
   the no-floats discipline and the explicit "bespoke encoding default" (`05` M3).

---

## 6. What would make this real (the bar)

The adelic complex is "real" when there is a machine-checked, 0-`sorry`,
axiom-clean Lean artifact in which (a) a p-adic place emits exact, congruence-
certified streams (M0), (b) it is coupled to the `∞` Gosper engine into one
complex with no floats and no global clock (M1), and (c) at least the *exact,
value-identified* `S`-integral multiplicative product-formula soundness is proven
(M4a). Until then, the truthful description is: *"a grounded design and build plan
for an adelic coupling machine, leaning on an already-verified Archimedean engine
and an already-verified congruence certificate, with the cross-place conservation
law still a conjecture."*

**And the first thing built should not be called "the adelic machine."** The
honest name for the first publishable artifact (M0–M2 + M4a) is *"a p-adic
congruence-certified transducer plus a finite-place coupling scaffold with
value-identified product-formula soundness."* "The adelic machine / the adele ring"
is earned only at L3+ (M3) with the cross-place *live-prefix* law (M4b) — both of
which may not land. Use the modest name until the code says otherwise; anything
stronger is ahead of the proof.
