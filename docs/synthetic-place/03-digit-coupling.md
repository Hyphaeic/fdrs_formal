# SU6 — digit coupling: the six axes, the window lattice, and the third obstruction

**Status:** design blessed in-session; first three targets **BUILT**
(`Grading.lean`, `CurrencyBalance.lean`, `WindowAccountability.lean` — 0 sorries,
axiom-clean). This document is the design record for the digit-coupling layer of the
synthetic place complex: *when and how two separate FDRS lines couple, across and
within digits.* Companion to `00-thesis.md`–`02-phase14-design.md`; Phase 14
numbering for SU6 awaits the next corpus pass.

---

## 1. The base general case (inductive from the lines, not abstracted on top)

A coupling is **not** an abstract interface posited above the lines. The primitive
remains what a number line actually does: a **tick with its carry chain**
(inductively defined on the line; carry *is* routing — Theorem 61,
`carryRouteDecision_eq_carry`). The base case of every coupling is the
**window-coupled step**:

> The source executes one primitive step. The step emits a **message** — the carry
> content of that transition (a weight; need not be `1`). The receiver's
> fiber/admissibility at its own prefix is gated by the pair *(message,
> window-reading of the source)*, where the **window** is a declared element of the
> source's observation lattice.

Everything else is induction over runs. The SU4b machine is the transport layer,
unchanged (its balance law never assumed unit grants).

## 2. The six axes

Every coupling rule is a point in this space; the test cases all land:

| Axis | Values | Anchors |
|---|---|---|
| **Topology** | which digits couple: graph/hypergraph; chains = paths | `CouplingGraph` (SU6a); sea = free topology incl. manifest-on-arrival nodes |
| **Window** | what the receiver sees: blind ⊂ clock ⊂ … ⊂ content ⊂ full prefix | SU1 `CoupledFiber` = full; blind/clock/content calibrated by SU4c + SU6c |
| **Message** | what crosses: unit, `k`-block, vector — a commutative monoid | `CurrencyConfig M` (SU6b); Phase 12 `overflowCarry`/`fitCount` compute weights |
| **Distribution** | route / split / mirror — the comultiplication | route+split = transport; mirror = trigger (§4); fan-out across edges DEFERRED |
| **Activation** | what initiates: overflow threshold, mirror trigger, manifestation-on-arrival | `manifestOnOverflow`, `tickDigit_none`; sea capacity (Def 162) |
| **Grading** | exact vs frustrated (the holonomy dichotomy, §5) | `Gradable`, `gradable_holonomy`, witnesses both sides (SU6a) |

Ordinary numbers: path topology, blind window, unit mass, route-to-next, overflow
activation, exact grading. The mediator, the sea, orthogonal mirrors, the Penrose
triangle — all coordinates.

## 3. The window lattice (and exp38)

What a receiver sees of a source is a **sub-algebra of the source's observation
lattice**. The user's taxonomy, placed: blind "1" = the overflow event only; the
coupled digit = the level-`p` fiber; digits to the right = the depth-`p` cylinder
algebra (`mod B_p`, Prop 6); digits to the left = the quotient coordinates
(`div B_{p+1}`, the dual filtration); the whole prefix = SU1.

Windows come in two species, and the design must declare which: **substrate rules**
(chart-free — factor through a divisibility condition, `q ∣ B`, Theorem 17 form;
invariant across re-factorizations; secretly arithmetic — the CRT shadow) and
**chart rules** (chart-bound — "the digit at level p"; transform under
re-factorization). Sage **exp38** (`fdrs_exp38_kernel_cylinder_radix9_atlas.sage`) is
the empirical probe of exactly this: the divisor-lens kernel (Theorem 21 / Prop 51's
object) rendered in nine cylinder charts of the same modulus `B = 60` — same
substrate, different towers; the Frobenius-vs-V1 deltas measure chart sensitivity.
Lean corroboration: Prop 6 (`cylinder_iff_congruence`), Theorem 17 (+ sharp
converse), Theorem 21, Prop 51, and the mediator's documented intermediate-depth CRT
counterexample.

**Calibrated accountability boundary (SU4c + SU6c):** blind — accountable (Thm 90
iii); **clock — accountable** (`issued_placeLocal_of_lengthWindow`: alternation is a
shared clock, so reading the partner's *time* is free); content — **not** (Thm 90
ii, the bilateral witness). Conjecture (open): accountability ⟺ the window is
deducible from the shared schedule. Note the honest caveat: the clock point depends
on the alternation discipline; under free scheduling it reopens.

## 4. The two currencies (mirrors do not break conservation)

Overflow distribution has two semantic species that must never be conflated:
**transport** (route/split — the carry is conserved mass; distributed weights sum;
the partition constraint is Theorem 88's shape) and **trigger** (mirror — every
coupled digit generates its own tick; the carry is *copied like information*).
Mirrors conserve too — in a different currency: SU6b proves the interface balance
law once, generically over any commutative monoid (`currencyReachable_balanced`),
with transport (`mass_balance`) and trigger (`trigger_balance`, grants ≡ one
event-token) as instantiations. **Every coupling edge declares its currency;
conservation holds in the declared currency.** Multi-target fan-out (split vs
broadcast across several edges — the comultiplication proper) needs the network
`Config` and is deferred to that arc.

## 5. Grading: the holonomy dichotomy (the third obstruction)

Size is not a node property. Its two readings — composition (one target-increment is
worth `ratio` source-units) and activity (the target is touched once per `ratio`
source-steps) — are reciprocal currencies of one **edge** datum, and ratios compose
multiplicatively along paths: size is a cocycle on the coupling graph. Then:

- **`gradable_holonomy`** (SU6a): a global magnitude exists only if every closed
  walk has ratio-product `1`. *Direction is not geometry; it is exactness.*
- **`chainGraph_gradable`**: the number line is graded — the potential is the place
  value; "most significant digit" is well-defined because chains are trees.
- **`frustratedTriangle_not_gradable`**: three digits, each overflowing into the
  next at ratio 2 — loop factor 8 (`frustrated_loop_factor`) — **no global
  bigger/smaller exists**, machine-checked, while the dynamics and per-edge balance
  remain perfectly well-defined. A Penrose staircase of digits.

With raggedness (Prop 148: kills the rank chart) and bilaterality (Thm 90: kills
separable conservation), frustration (kills global magnitude) completes the **three
independent obstructions to number-hood**. A coupling complex is "a number" exactly
when it clears all three; each failure leaves a survivor — geometry, balance,
per-edge ratios.

## 6. Exact charts and dilation (recorded decisions)

- **Exactness**: the outer fiber equals the inner mass "on the nose" — Theorem 88
  makes the chart lossless; lossy/quotient charts are the sea's regime and remain a
  declared variant, not the default.
- **Dilation**: a weight-`k` carry is `k` inner steps executed atomically; Lipschitz
  constants are gauge-relative, and the composite gauge restores 1-Lipschitz — *the
  gauge is the clock; coupling re-clocks.* **The gauge half is now proven**
  (`NestedChain.lean`): the spliced line's potential is composite inside the block
  (`B_p·C_j` — the synthetic fraction's denominator), rejoins the outer gauge exactly
  under exactness (lossless chart), and crossing the block multiplies resolution by
  exactly `b p` (`nested_dilation_gauge`). The dynamic half
  (`tick_outer ∘ φ = φ ∘ tick_inner^k`) remains open.

## 7. Build state and open items

| Target | Status |
|---|---|
| SU6a holonomy dichotomy + both witnesses (`Grading.lean`) | ✅ BUILT |
| SU6a′ holonomy converse — **full iff**: connected complex gradable ⟺ every loop product 1 (`gradable_of_trivial_holonomy`, walk reversal toolkit) | ✅ BUILT |
| SU6b currency-generic balance + two currencies (`CurrencyBalance.lean`) | ✅ BUILT |
| SU6c shared clock + length-window accountability (`WindowAccountability.lean`) | ✅ BUILT |
| SU6d nested chart, gauge half (`NestedChain.lean`): synthetic fractions (`refined_potential_inside`, composite gauge `B_p·C_j`), gauge-lossless splice (`refined_potential_top/above`), `nested_dilation_gauge` | ✅ BUILT |
| Dilation theorem, dynamic half (tick conjugation through the chart) | open (gauge half done) |
| Window boundary beyond three points (clock-deducible conjecture) | open |
| Comultiplication / multi-edge fan-out; network `Config` | open (next arc) |
| `NestedLaw` (prefix-dependent version of the nested chart) | open (chain core done) |
| Non-blocking couplability (relational `J`, empty-fiber reachability via SU2) | open |
| Mutual coupling well-formedness (per-step dependency acyclicity, reuse Phase 8) | open |

## 8. Anti-confabulation ledger (SU6 additions; prior ledgers inherited)

1. **Potentials-on-graphs is classical** (discrete gauge theory); the contribution is
   placement + verified witnesses. Same for Mazurkiewicz background (02 §ledger).
2. **"Three obstructions" is a classification of failure modes, not a completeness
   claim** — no assertion that no fourth obstruction exists.
3. **The clock-window accountability is discipline-relative** (alternation); do not
   cite it for free schedulers.
4. **Mirror conservation is event-currency conservation** — never present it as mass
   conservation; the currency must be named wherever the law is cited.
5. **exp38 is an empirical probe** (weighted, row-normalized, sampled); cite the Lean
   theorems (Prop 6/Thm 17/Thm 21/Prop 51) for the facts, the experiment for the
   chart-sensitivity phenomenon.
6. **The frustrated triangle does not model any classical number system** — that is
   its point; do not present frustration as a pathology of FDRS but as a region of
   the design space with its own surviving laws.
