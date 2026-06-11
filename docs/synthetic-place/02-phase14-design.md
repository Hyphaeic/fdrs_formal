# Phase 14 design note — the coupled radix complex (SPS → foundation)

**Status:** EXECUTED. SU0–SU5 are BUILT (`FdrsFormal/Modes/SyntheticPlace/`, ten
modules, 0 sorries, axiom-clean), the §4 scalar no-go is **machine-checked**
(`TraceGeometry.lean`, stronger than the sketch — no positivity/swap-invariance
premises), the observer-glued network ultrametric is proven (`NetworkGauge.lean`),
and **Phase 14 is in the corpus**: `docs/fdrs.md` §Phase 14 (Definitions 192–200,
Theorems 83–92, Propositions 147–149) with the index block in `docs/fdrs-index.md`.
This note remains the design record and decision log.

---

## 1. The architectural result (the Phase 14 thesis)

> The radix complex has no global product formula in the classical adelic sense,
> because genuine coupling destroys separability. Its replacement is a sheaf of
> interface balances: local issued/consumed/pending ledgers living on edges, glued
> across the network. Conservation survives, but it migrates from node-local
> valuation to edge-local transport.

The coupled object is **not a generalized adele; it is a networked transport
object** — a *gauge-indexed transport geometry*. The classical adelic complex is the
degenerate case in which all places are mutually blind, which is precisely when
separable (sum/product-over-places) invariants can exist.

One-line form, which the rest of this note instantiates three times:

> **In the network regime, every global scalar dies, and every law survives by
> becoming indexed and glued.**

- *Value* (global integer decode) dies with sibling uniformity (SU1's ragged
  witness); it survives as **gauge-graded observables** (SU3).
- *Conservation* (product formula) dies with separability (SU4c's no-go); it
  survives as the **balance sheaf over edges** (SU4b).
- *Geometry* (a single scalar depth) dies with concurrency (§4 below — new); it
  survives as the **observer-indexed gauge family glued by sup** (Definition 82's
  shape).

## 2. The separability boundary (proven; the load-bearing import)

What SU4c established, in Phase-14 language:

- **Factorization** (`placeLocal_factors`): any charge with place-local transfer
  rules is additively separable on reachables, `Φ = Φ₀ + f(sA) + g(sB)` — it cannot
  see "in flight", "pending", "issued but not consumed", or "jointly forced".
- **No-go** (`issued_not_placeLocal`): for a bilateral coupling the carry charge
  admits no place-local accounting (rectangle `5+5 ≠ 6+6`, kernel-checked).
- **Boundary** (`issued_placeLocal_of_blind`): B-blind couplings ARE one-side
  accountable; SU1's ragged witness sits inside the boundary, the bilateral witness
  outside. **The obstruction is bilaterality, not raggedness.**

Mechanism-level consequence the corpus had only observed empirically: the classical
product formula is the ultimate separable charge (`log ∏ = Σ` of place-blind terms),
possible on `ℚ` exactly because classical places never read each other; Phase 13
§13.4's product-law breakage for CF combination is the same fact from the other side
— the Gosper tensor reads both streams, so any invariant that refuses to look at the
interface is structurally doomed. What survived there (carry frequency) is
accounting, as predicted by the boundary.

**Scope discipline:** "no product formula" is the *design conclusion* from a proven
factorization theorem plus a proven witness; it is not a universal impossibility
quantified over all conceivable invariants. Stated precisely: any invariant whose
local terms are place-computed factors through the prefixes separately and cannot
account coupled transport. The full classification ("place-locally accountable ⟺
grant satisfies the rectangle identity on reachables") remains open.

## 3. The Config consequence (theorem-forced type design)

```
no separable charge
⇒ accounting cannot be node-local
⇒ ledgers must live on couplings
⇒ Config requires edge registers
```

So the radix complex configuration type is forced, not chosen:

```
Config = (per-node state) ⊕ (per-edge interface registers)
```

with SU4b's capacity-one register (`pending : Option`) as the minimal instance —
deliberately the latency/Kahn discipline of `CoupledSystem.Coupling` — and
queue-valued interfaces as the declared generalization. The balance law
`issued = consumed + pending` is the per-edge invariant; the network law is its sum
over edges (the gluing is finite additive bookkeeping, to be formalized with the
network `Config`).

**Honest naming:** "balance **sheaf**" is structural vocabulary, not a claim — no
restriction maps or gluing axioms are formalized. Until they are, the formal object
is a family of edge ledgers with an additive total. (Ledger item 4 below.)

## 4. The trace-monoid gauge problem — and a scalar no-go (NEW, to be probed)

The keystone question posed for the network geometry:

> What is the smallest trace-monoid gauge that reduces to SU0 on linear words,
> respects independent swaps, and supports an ultrametric on configurations?

**Design finding: no scalar gauge can do it.** Sketch (to be machine-checked as a
probe before fdrs.md asserts it): take two completely independent places A, B. Any
swap-invariant scalar gauge `g` on trace-prefixes that genuinely reduces to SU0 on
each place's own line is unbounded along pure-A and pure-B extensions. Consider runs

```
x = (α,  β )    y = (α,  β′)    z = (α′, β′)
```

with `α, α′` differing at A's first symbol and `β, β′` differing at B's first
symbol. Trace meets: `x ⊓ y` = (α-events only) — gauge `→ ∞` with the depth of `α`;
`y ⊓ z` = (β′-events only) — gauge `→ ∞`; but `x ⊓ z` = the empty trace — gauge
bounded. So `δ(x,y), δ(y,z) → 0` while `δ(x,z) ≥ 1/g(ε) > 0`: **even the ordinary
triangle inequality fails**, not merely the strong one. Depth earned at one place
masks total blindness at another; a scalar cannot price both.

(Precise scope: this kills *meet-reciprocal scalar* metrics `δ = 1/g(x ⊓ z)` under
the stated premises — not every conceivable scalar function. The probe should pin
the premises exactly.)

**The resolution the failure forces:** index the gauge by observer. Each place's
projection of a run is a *linear* word (projections are invariant under independent
swaps — definitionally schedule-invariant), so each place carries an ordinary SU0
`PrefixGauge`, and the network distance is the **sup-gluing**

```
δ(x, z) = sup over places v of  δ_v(π_v x, π_v z)
```

A finite sup of ultrametrics is an ultrametric (one-line gluing argument), it
reduces to SU0 when there is one place, and it is swap-invariant because the
projections are. Its reading is honest network epistemology: *you are only as close
as your most-disagreeing observer.* This is exactly the `ObserverComplex`
(Definition 82) shape — the third instance of the §1 thesis: geometry, like value
and conservation, survives by becoming indexed and glued.

Classical background to cite, not claim: Mazurkiewicz traces, prefix order as
downset lattice, reconstruction of traces from per-location projections
(Zielonka-adjacent; the corpus needs only the easy direction).

**Minimality** ("smallest") is posed, not claimed: sup-gluing is *a* solution; what
is provable is the scalar no-go plus sufficiency of the glued family.

### The SU5 build plan (after this note is blessed and the probe lands)

| Step | Content | Status |
|---|---|---|
| SU5.0 | The scalar no-go (`scalar_trace_metric_no_go`) — STRONGER than sketched: ordinary triangle refuted; no positivity/swap-invariance premises | ✅ BUILT (`TraceGeometry.lean`, Thm 91) |
| SU5.1 | Trace equivalence toolkit, block commute, projections, swap-invariance (`proj_traceEquiv`) | ✅ BUILT (`TraceGeometry.lean`, Def 199) |
| SU5.2 | `netDist` sup-gluing: ultrametric, identity of indiscernibles, `netBall_eq_cylinder` (cylinder profiles), SU0 reduction (`netDist_unique`) | ✅ BUILT (`NetworkGauge.lean`, Def 200/Thm 92) |
| SU5.3 | Schedule-invariance of everything built on the projection tuple (`netObservable_traceEquiv`) | ✅ BUILT (`NetworkGauge.lean`) |
| SU5.4 | Network separation cost: per-place `DecidedAt` priced by per-place gauge (`network_separation_cost`) | ✅ BUILT (`NetworkGauge.lean`) |

Then liveness for coupled traps (Phase 8's deadlock story, now with conservation
vocabulary) and the accountability iff, in that order.

## 5. Integration plan (fdrs.md Phase 14)

Sequencing: **this note → SU5.0 probe → fdrs.md Phase 14 prose with numbered items →
index regeneration.** Candidate numbered items (Lean homes already exist except SU5):

| Candidate item | Lean home |
|---|---|
| Def: prefix gauge; Thm: gauge ⇒ ultrametric, ball = cylinder | `GaugeUltrametric.lean` (SU0) |
| Prop: product & CF gauges are instances (`cfDist` recovered) | `GaugeUltrametric.lean` |
| Def: coupled fiber (chain-context oracle); Thm: level-only ⇒ SU; Prop: ragged witness | `Composition.lean` (SU1) |
| Thm: coupled gauge ultrametric (geometry survives raggedness) | `Composition.lean` |
| Def: transfer structure, uncertainty ledger; Thm: admissibility trap soundness | `AdmissibilityTrap.lean` (SU2) |
| Thm: indistinguishability below the gauge; depth hierarchy strict | `Restriction.lean` (SU3) |
| Thm: partition law; Cor: zero leak | `Conservation.lean` (SU4a) |
| Thm: interface balance (Prop-128 shape, arbitrary coupling) | `InterfaceBalance.lean` (SU4b) |
| Thm: factorization; Thm: no-go; Thm: B-blind boundary | `ConservationRigidity.lean` (SU4c) |
| Thm: scalar trace-gauge no-go; Def/Thm: observer-glued network ultrametric | SU5 (future) |

## 6. Anti-confabulation ledger (Phase 14 additions; SPS ledger items 1–7 inherited)

1. **"Balance sheaf" / "gauge sheaf" are structural vocabulary.** No sheaf axioms
   (restriction maps, gluing conditions) are formalized; the formal objects are
   indexed families with additive/sup gluing. Do not let the word harden into a claim.
2. **"No product formula" has exact scope** (§2): proven factorization + proven
   bilateral witness; consequence-level for the general slogan; full iff open.
3. **The scalar trace-gauge no-go is machine-checked** (SU5.0 landed:
   `TraceGeometry.lean`, `scalar_trace_metric_no_go`, Theorem 91) — and the proven
   statement is *stronger* than the §4 sketch: no positivity or swap-invariance of
   the gauge is assumed, and even the ordinary triangle inequality is refuted. Cite
   the theorem, not the sketch.
4. **Trace theory is classical.** Mazurkiewicz traces, downset lattices, projection
   reconstruction — cite; the corpus contributes the FDRS-shaped statements and the
   verified artifact only.
5. **Kahn-style stream determinacy remains unproven here** (the conditional diamond
   is open); the determinacy triage (state / streams / charges) must keep its three
   tiers distinct in all prose.
6. **Liveness is still absent**: every certificate is sound; none is yet guaranteed
   to fire. No engine prose may imply progress without a liveness theorem.
7. **"Networked transport object" / "gauge-indexed transport geometry"** are names
   for an architecture, not theorems. The theorems are §2–§4's specific statements.
