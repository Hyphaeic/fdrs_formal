# 05 — Build Roadmap

*The staged Lean plan. Front-load the ✅ pieces, isolate the 🔬 to the last
milestone, gate on scratch checks. Each milestone names the existing corpus result
it generalizes (the FDRS habit: every new result extends a verified one), its
acceptance criteria, and its risk. Build discipline per the handoff §0.*

---

## 0. Discipline (non-negotiable, from the handoff)

- **Leaf modules.** New work goes in standalone modules nothing else imports →
  zero blast radius. Target directory: `FdrsFormal/Modes/Adelic/` (new).
- **Verify every commit.** `lake build <Module>`; axiom-check with `lake env lean`
  + `#print axioms <thm>` (clean = `[propext, Classical.choice, Quot.sound]`;
  constructive ones drop `Classical.choice`). **0 `sorry`.**
- **Flat integer-tuple `structure`s, not `Matrix`** — so `ring`/`omega`/`decide`
  see through them (the reason `BihTensor` is 8 flat `ℤ` fields).
- **Branch; fast-forward merge when asked. Do not push to `origin` unprompted.**
  **No `Co-Authored-By: Claude` / `noreply@anthropic.com` / "Generated with Claude
  Code" in any commit or PR.**
- **Provenance honesty in docstrings:** mark `CONJECTURE`/`STUB`/`ASPIRATIONAL`
  where they apply, exactly as Phase 13 / Theorem 64 do.

---

## 1. Milestone map

```
 M0  p-adic single-place engine        ──┐  (the second place; emit without a floor)
 M0.5 PlaceEngine refactor (∞ ∪ p)       │  (scheduler/hyper-tree go engine-generic)
 M1  two-place complex  S = {∞, p}     ──┤  (L1: the honest first "adelic" artifact)
 M2  finite S-adeles  {∞,p₁,…,p_k}      │  (L2: freePart/smoothPart; S-product-formula)
 M4a coupling theorem, exact (value-identified) ─┐ (L4: S_product_formula; reachable prize)
 M3  restricted product (genuine 𝔸)    ──────────┤ (L3: "almost all in ℤ_p"; OPTIONAL, after M2/M4a)
 M4b gauge bound, finite live prefixes ──────────┘ (L4: the 🔬 research; may stall)
```

First publishable artifact = **M0–M2 + M4a** (an honest "finite-place exact coupled
machine, with value-identified product-formula soundness"). M3 and M4b are *after*
that, and explicitly may not land. Run scratch `04`§5 items 4–6 **between M2 and
M4b** — they gate M4b (not M4a, which is exact, not a bound).

---

## 2. M0 — the p-adic single-place engine (no floats, emit by congruence)

**Goal.** An exact homographic transducer over `ℤ_p` that emits Hensel digits,
certified by congruence. The non-Archimedean dual of `HomographicCarry` +
`BihomographicSound`.

**Build (leaf module `Modes/Adelic/PadicHomographic.lean`) — a tight proof
sub-ladder, to avoid getting stuck in Mathlib valuation abstractions too early:**

- **M0a — ledger + recurrence (pure `ℤ`, no `K`).** `structure PadicLedger where
  a b c d : ℤ` (+ the 8-field `PadicBihTensor` for Axis I) — *reuse the shape; the
  algebra is pure `ℤ`* (`02` §1). `absorb (α p)` = shift `[[p,α],[0,1]]`, `emit (β p)`
  (`03` §3a). `det`, and `det_absorb`/`det_emit`: `(absorb …).det = p · L.det`
  ⟹ `v_p(det) = #steps` (the exactness invariant — **`det=±pᵏ`, not `|det|=1`**,
  `04` §2). *Template: corpus `det_step`/`det_steps` (✅).*
- **M0b — `candidate` + `ready` (pure `ℤ` congruence, no `K`).** `candidate :
  PadicLedger → Fin p` (the residue digit); a **named prerequisite lemma
  `denom_unit_on_disk`** (`c ≡ 0 ∧ d ≢ 0 (mod p)`, `03` §3c) with the explicit
  **pole/disk-refinement** branch when it fails; `ready : PadicLedger → Bool` =
  the `p`-corner congruence check gated on `denom_unit_on_disk` (decidable,
  `omega`/`decide`; **no `<`, no floor**).
- **M0c — concrete soundness over `ZMod p` first.** Prove `ready_sound_mod_p` for a
  single `PadicLedger` over `ZMod p`: `ready = true ⟹ value ≡ β (mod p)`, using only
  `ZMod`/divisibility (no `Valued`). This is the load-bearing combinatorial step and
  must be stable *before* any valued-field abstraction.
- **M0d — general statement over a valued field.** Only now state
  `padic_emit_traps {K} [Field K] [Valued K Γ] …` (`ready = true ⟹ ∀ tail ∈ 𝒪_K,
  value ≡ β mod 𝔪`), reducing it to M0c. **Core already proven:**
  `residue_depends_on_prefix` + `congruenceSet_is_cylinder_union` (✅) and the sharp
  `congruenceSet_not_cylinder_union_of_not_dvd` (✅, "don't emit early"). M0's
  novelty is *wiring* these to the ledger, not a new hard proof.

**Generalizes:** `HomographicCarry.emit`/`emitDigit`/`emitReady` (✅) — same role,
congruence certificate instead of floor; and `CylinderMeasurability`'s
prefix-pinning (✅) — applied to a homographic value at constant base `p`.

**Acceptance:** `lake build` green; `#print axioms` clean on M0c **and** M0d; 0
`sorry`. `#eval` demo: emit the leading Hensel digits of a Hensel-root quadratic
irrational in `ℤ_p` (e.g. `√6 ∈ ℤ₅`), matching the scratch `padic_digits`
(`scratch/`, Demo B numbers).

**Risk:** low-moderate, *and the sub-ladder front-loads the risk*: M0a/M0b/M0c are
elementary `ℤ`/`ZMod` work; only M0d touches Mathlib `Valued`/`Padic`, and by then
the math is already proven concretely (M0c), so M0d is a restatement, not a new
proof.

---

## 3. M0.5 — `PlaceEngine` refactor (make the scheduler place-agnostic)

**Goal.** Factor emission into the `PlaceEngine` interface (`03` §2) so `run` /
`coupleAll` / `coupleTree` become *engine-generic* (they already never touch order
— `02` §3). Provide two instances: `∞` (= existing `BihTensor` + `emitReady_traps`,
✅) and `p` (= M0).

**Build (`Modes/Adelic/PlaceEngine.lean`):** the class + the two instances + a
generic `runEngine` mirroring `run` but calling `PlaceEngine.ready/candidate/…`.

**Generalizes:** `BihomographicDriver.run` and `HyperGosper.coupleAll` (✅) — same
control flow, abstracted over the engine.

**Acceptance:** the `∞` instance reproduces the existing `run` demos (`φ+φ`, etc.)
*verbatim* (regression guard); the `p` instance reproduces M0's demos. 0 `sorry`,
axiom-clean.

**Risk:** low. Pure refactor; the regression guard catches divergence.

---

## 4. M1 — the two-place complex `S = {∞, p}` (L1)

**Goal.** The first honest "adelic" artifact: one quantity, two coupled exact
streams, no floats.

**Build (`Modes/Adelic/Complex.lean`):**
- `AdelicConfig` over `S = {∞, p}` (`03` §1), `PlaceState`, `step` (`03` §5).
- The **no-floats invariants** NF1–NF3 (`03` §7) as lemmas: ledgers are `ℤ`-tuples,
  values are streams, `step` takes an explicit place (no global counter).
- **Scheduler-independence, as confluence (not hand-waved).** Two theorems, in
  order: (1) a **local diamond lemma** — for `v ≠ w`, `step v ∘ step w = step w ∘
  step v` (distinct places touch disjoint state); *core:* the channel commutations
  `emit_absorbX_comm`/`absorbX_absorbY_comm` (✅) lifted to `step`. (2) the
  **downstream theorem** — any two *fair* schedules produce per-place
  prefix-equal emitted streams (up to fuel), derived from the diamond. State which
  notion of "fair" (every starved-but-ready place eventually stepped) explicitly.

**Generalizes:** `ThreeLineMediator.CoupledSystem` (✅) — but coupling *places*
(with their own valuations) rather than *radix sizes*; this is exactly the
handoff's open frontier #3 ("give `ObserverLine` its own metric/valuation
identity"). And `CoupledDigitNetwork` (✅ shell) — supplied with operational
semantics (`Config + step + value`), the memory's "radix complex as a verified
machine" goal, now place-aware.

**Acceptance:** `#eval` a rational `x` (e.g. `12/35`) represented at `∞` (CF) and
`p` (Hensel) simultaneously; both streams exact and matching scratch; the
scheduler-independence lemma proven. 0 `sorry`, axiom-clean.

**Honest banner (in the module docstring):** *"This is the two-place toy `S={∞,p}`,
NOT the adele ring (handoff anti-confab). It establishes coupling mechanics; the
restricted product is M3 and the conserved cross-place law is M4."*

**Risk:** low-moderate. Mechanics are assembly; the diamond/confluence pair is the
one real proof, and its core commutations exist (✅).

---

## 5. M2 — finite `S`-adeles `{∞, p₁,…,p_k}` (L2)

**Goal.** Generalize M1 to a finite set of places, and make the `S`-product-formula
a *decidable identity* for `S`-integral quantities.

**Build (`Modes/Adelic/FiniteS.lean`):**
- `AdelicConfig` over an arbitrary `S : Finset Place`; one p-adic engine per prime.
- `S_product_formula` (for `S`-integral `x`): `∏_{v∈S} |x|_v = 1` as a `ℚ`/`ℤ`
  identity. *Core:* `factorization_unique` + `freePart`/`smoothPart` (✅) — the
  product formula for `S`-integral rationals **is** unique factorization;
  `padicValRat` (📐) for the statement.
- `multiplicativeSigmaAlgebra` (✅) gives the valuation-filtration view if a
  statistical layer is wanted later.

**Generalizes:** the `FactorizationLens` (`u_P`,`v_P`) machinery (✅) — from a
*passive* coordinate to the *active* per-place stream support of the complex.

**Acceptance:** `S_product_formula` proven for `S`-integral inputs (decidable
`#eval` checks against scratch Demo A); engine runs at `k ≥ 2` primes
simultaneously. 0 `sorry`, axiom-clean.

**Risk:** moderate. The product-formula-as-factorization proof is routine in
Mathlib; the work is the bookkeeping connecting *emitted* valuations to `v_p(x)`
(`padic_valuation_from_stream`, `04`§6, core ✅ `residue_depends_on_prefix`).

---

## 6. M3 — restricted product (genuine adeles, L3)

**Goal.** The "almost all components in `ℤ_p`" condition — the finite-support
encoding that earns the name *adelic*.

**Do not start M3 before M2 and M4a are clean.** M3 is **explicitly optional** for
the first publishable artifact (which is M0–M2 + M4a, `06` §6); it is the first rung
with no FDRS ancestor and moderate-high risk, so it should not block — or precede —
the finite-`S` story.

**Build (`Modes/Adelic/Restricted.lean`):**
- Encode a quantity as `S`-data + a proof that *outside `S` it is a p-adic unit*
  (`v_p = 0`) — the finite-support / `freePart` condition (✅ handle).
- Decide here whether to import `DedekindDomain.FiniteAdeleRing` /
  `NumberField.AdeleRing` (📐) as the semantic target, or keep the bespoke
  finite-support encoding. **Default: bespoke**, per the no-floats discipline
  (the Mathlib adele ring drags in topology/measure not needed for exact
  streams); import only if M4 genuinely needs the restricted-product *object*.

**Generalizes:** nothing in FDRS directly — this is the first piece with no
single-result ancestor, hence the first that is partly 🔬.

**Acceptance:** a represented `x` with explicit finite support `S`; a lemma that
the complex's behavior at places outside `S` is the trivial (unit) stream. 0
`sorry`.

**Risk:** moderate-high. The infinitary "almost all" condition is where the toy
becomes real; expect this to be where scope is most tempting to overstate (`06`).

---

## 7. M4 — the coupling-invariant theorem (L4, the 🔬 prize)

**Gate:** run scratch `04`§5 items 4–6 first. If the gauge-bound check (item 4)
fails, **stop and revise `04` §3.3** before any Lean effort — do not formalize a
false bound.

**Two distinct theorems — do not conflate** (the finite-precision split, `04` §4):

**M4a — `S_product_formula_from_exact_value` (the reachable prize).** For
`S`-integral `x` with **identified** value (terminating/pinned Archimedean stream,
so `|x|_∞` is *exact*) on the multiplicative axis: the emitted data satisfies
`∏_{v∈S}|x|_v = 1` **exactly**, a decidable `ℚ` statement.
- *Build (`Modes/Adelic/Soundness.lean`):* assemble `padic_valuation_from_stream`
  (🔨, core ✅) + `idele_norm_multiplicative` (🔨, 📐) + the factorization identity
  (M2; `freePart`/`smoothPart`, ✅).
- *Generalizes:* `emit_traps` (✅, single-place) → cross-place soundness — the
  Axis-II analogue of the four-corner trap, exact because the value is known.
- *Acceptance:* M4a proven, axiom-clean, 0 `sorry`.

**M4b — `prefix_residual_bound` / `gauge_bound` (the stretch / research).** For
**finite live prefixes** (value *not* identified, `|x|_∞` only a convergent): only
`|∏_v|x|_v − 1| ≤ C/q_n` (`04` §3.3). *Core:* `steps_qCur_unbounded` (✅);
effectivity of `C` open. **Not an acceptance condition** — it is the genuinely
uncertain piece; if it stalls, the artifact still ships M4a and `06` §6 records the
boundary.

**Gate:** run scratch `04`§5 items 4–6 first. The item-4 gauge-bound tabulation
decides whether M4b is worth attempting; if it shows no `O(1/q_n)` envelope,
**stop M4b and revise `04` §3.3** rather than formalize a false bound. M4a does not
depend on this gate (it is exact, not a bound).

**Risk:** M4a is plausibly reachable (bottoms out in unique factorization + the ✅
congruence certificate, exact only via value-identification). M4b, and any
additive/full-adelic version, are genuinely open (`04` §7) — the research
contribution or the stall point.

---

## 8. Dependency & import summary

| milestone | new Mathlib imports | builds on (✅ corpus) | new status |
|---|---|---|---|
| M0 | `Padic`/`PadicInt`/`Valued` (statement only) 📐 | HomographicCarry, CylinderMeasurability | 🔨 |
| M0.5 | — | Driver, HyperGosper, BihTensor | 🔨 |
| M1 | — | ThreeLineMediator, CoupledDigitNetwork, channel commutations | 🔨 |
| M2 | `padicValRat` 📐 | FactorizationLens, Valuations | 🔨 |
| M4a | `padicNorm`/`padicValRat` 📐 | emit_traps (as analogy), M0–M2, factorization | 🔬 (reachable) |
| M3 | (maybe `FiniteAdeleRing` 📐) | freePart/smoothPart | 🔨/🔬 (optional) |
| M4b | — | steps_qCur_unbounded, M4a | 🔬 (may stall) |

**The shape of the whole build:** M0–M2 are assembly of verified parts (low-moderate
risk, high confidence); **M4a** is the reachable exact coupling theorem; **M3** (the
infinitary restricted product) and **M4b** (the finite-precision gauge bound) are the
research, are optional for the first artifact, and may not land. Ship **M0–M2 + M4a**
as the honest "finite-place exact coupled machine with value-identified soundness,"
then attempt M3/M4b — and let `06` keep the scope claims truthful at every rung.

Next: [`06-anti-confabulation.md`](06-anti-confabulation.md) — the scope ledger that
guards all of the above.
