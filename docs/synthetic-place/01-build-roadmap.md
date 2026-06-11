# SPS build roadmap — SU0–SU3

Companion to `00-thesis.md`. Modules live in `FdrsFormal/Modes/SyntheticPlace/`.
House rules: 0 sorries, axiom-clean (`propext`/`Classical.choice`/`Quot.sound` only),
`#eval` demos wherever computable, honest-scope banner per module.

## Design decisions (binding for the series)

- **D1 — generic digit type.** Words are `List D`, points are `ℕ → D`, for any
  `[DecidableEq D]`. This lets pair digits (`D = ℕ × ℕ`, SU1) flow into SU0 directly
  and avoids re-encoding tricks.
- **D2 — predicate admissibility, not dependent fibers.** No `Digit : Node → Type`;
  fibers are ranges/predicates plus validity invariants (the `LinearChain` pattern).
  Dependent fibers put every proof in the `HEq` swamp (cf. `cylinderSuffixEquiv`).
- **D3 — distance is a theorem, not a field.** A gauge structure carries data +
  minimal laws; the ultrametric is *derived* (SU0). Structure fields are data and
  proof obligations only (the `AdelicLaw.conservation` idiom).
- **D4 — two-tier gauge hypotheses.** Positivity + extension-monotonicity give the
  ultrametric and ball=cylinder *given the radius*; unboundedness along a point is a
  separate hypothesis needed only for "balls of every radius are cylinders"
  (cylinders shrink). Bounded gauges are legal and have honest, weaker conclusions.
- **D5 — reuse `PlaceEngine`** for any executable engine layer; do not fork it.
- **D6 — SU1 scheduling convention.** In a coupled step, A's digit is chosen first
  within the step; B's fiber at that step sees A's prefix *including* the current
  A-digit. (One convention, stated once; the mirror is symmetric.)

## SU0 — `GaugeUltrametric.lean` (the gauge→ultrametric keystone)

**Object.** `PrefixGauge D`: `Adm : List D → Prop` (closed under `adm_append`),
`gauge : List D → ℕ`, `pos` on admissible words, `mono_append` on admissible
extensions. Points: `AdmissiblePoint G x := ∀ n, G.Adm (pre x n)`.

**Theorems.**
- `gauge_mono_of_append` (prefix-monotone from one-step), `gaugeAt_pos`,
  `gaugeAt_monotone`.
- `gaugeDist` = first-disagreement reciprocal gauge; `self/nonneg/comm/eq_zero_iff/`
  **`triangle`** (strong) — the `cfDist` proofs, gauge-generic.
- `ball_eq_cylinder` under `GaugeUnbounded`.
- **Bridges:** `productGauge ω` (`Adm := True`, `gauge := prefixWeight ω`) — recovers
  Definition 79's formula, unbounded via `2^|s| ≤ β_ω(s)`; `cfGauge`
  (`Adm := all ≥ 1`, `gauge := (steps init ·).qCur.toNat`) with
  `gaugeDist cfGauge = cfDist` on admissible points — `cfDist` literally becomes an
  instance. (No `= δ_ω` claim: thesis ledger item 2.)

## SU1 — `Composition.lean` (nested / cross-timeline digit composition)

**Object.** `CoupledFiber`: `fiberA : List ℕ → ℕ`, `fiberB : List ℕ → List ℕ → ℕ`
(B's fiber sees its own prefix *and* A's prefix — the Phase 7 oracle `Ω(s, c)` with
chain-valued context), both ≥ 2. `coupledCount C k sA sB`: completion counts of the
coupled tree (Definition 61's `W`, coupled).

**Theorems.**
- `coupledCount_pos`.
- **SU survives** under level-only fibers: counts depend only on lengths
  (⇒ sibling-uniform), recovering the product regime (cf. Theorem 70).
- **The ragged regime, machine-checked:** an explicit coupled instance with two
  A-siblings of *different* completion counts (`decide` witness) — Phase 5.4 §5's
  warning realized concretely; with coupling the pair-fiber is jagged and the
  structure is not a `RadixLaw` at all (thesis ledger item 3).
- **The headline:** `coupledGauge C : PrefixGauge (ℕ × ℕ)` (path place-value of the
  coupled chain) satisfies SU0's hypotheses — *even in the ragged regime the coupled
  chain carries a genuine ultrametric with ball = cylinder.* Refinement geometry
  survives the death of the odometer.

## SU2 — `AdmissibilityTrap.lean` (the third trap)

**Object.** `TransferStructure Q D O`: finite states `Q`, total `step`, Boolean
`allowed`, observation `obs : Q → O`. Uncertainty ledger: `S : Finset Q` (the states
consistent with what has been observed). `stepSet T S` = admissible one-step image;
`candidates T S` = its observations.

**Theorems.**
- `trap_sound`: if `candidates T S = {o}` then **every** admissible tail from
  **every** state in `S` observes `o` after one step — the forced-emission
  certificate, quantified over all admissible continuations, decidable on the finite
  transfer-state set. Siblings: order trap (`emit_traps`), congruence trap
  (`padic_emit_traps`), admissibility trap (this).
- Executable `ready`/`emitDriver` with first-emission soundness; emissions only when
  forced (thesis ledger item 4).
- **Demo:** the golden-mean (Zeckendorf) structure — after a `1` the next observation
  is *forced* to `0`; from state `0` the engine must refine. `#eval`-checked; ties to
  `SubshiftParry`'s kernel (`goldenP 1 0 = 1`).

## SU3 — `Restriction.lean` (zoom-out restriction)

**Object.** `DecidedAt f n`: observable `f` constant on depth-`n` cylinders.

**Theorems.**
- `decided_separation` / `separation_cost`: a depth-`n` observable cannot separate
  points closer than `(gaugeAt G x n)⁻¹` — equivalently, distinguishing by a depth-`n`
  observable costs at least the depth-`n` gauge reciprocal in distance. This is
  Theorem 44 (`Lip = max β_ω`) in gauge-general, decode-free form: *the gauge prices
  observability.*
- `decidedAt_mono` and **strictness**: with a genuine branch at depth `n`, there is an
  observable decided at `n+1` but not at `n` (explicit indicator witness) — the
  depth hierarchy is strict (Prop 133's shape, gauge-general).
- The SU-regime modulus-by-depth (residues decided when `q ∣ β_ω(s)`) **already
  exists** (Theorem 38 / Corollary 27, `ThreeLineMediator/CoupledSystem.lean`) — cited,
  not rebuilt.

## SU4 — the conservation arc (BUILT)

Resolves the theorem-shaped part of thesis §3; statuses and headline theorems:

| ID | Module | Headline | Status |
|---|---|---|---|
| **SU4a** | `Conservation.lean` | `setMass_partition` (the continuity equation of refinement); `certified_mass_conservation` (zero leak: certified emission transfers mass exactly); Fibonacci demos, kernel `decide` | ✅ BUILT |
| **SU4b** | `InterfaceBalance.lean` | the coupled machine with declared ledger; `reachable_balanced` (`issued = consumed + pending`, Prop-128/Thm-57 shape, arbitrary coupling); `reachable_consumed_le_issued` (obstruction reading) | ✅ BUILT |
| **SU4c** | `ConservationRigidity.lean` | `placeLocal_factors` (place-local charges are separable — cannot measure the coupling); `issued_not_placeLocal` (NO-GO: bilateral coupling, rectangle `5+5 ≠ 6+6`, machine-checked); `issued_placeLocal_of_blind` (boundary positive: B-blind couplings accountable; `raggedFiber` inside, `jointFiber` outside) | ✅ BUILT |

Design notes binding for SU4: the ledger (`issued`/`consumed`/`pending`) is declared
state, never hidden memory; the interface register has capacity one (the
latency/Kahn discipline of `CoupledSystem.Coupling`); `decide` only, never
`native_decide`.

## SU5 — the network geometry arc (BUILT; see `02-phase14-design.md` §4)

| ID | Module | Headline | Status |
|---|---|---|---|
| **SU5.0/5.1** | `TraceGeometry.lean` | trace equivalence + block commute; `proj_traceEquiv` (projections schedule-invariant); **`scalar_trace_metric_no_go`** (no scalar trace gauge supports a refinement metric — ordinary triangle refuted) | ✅ BUILT |
| **SU5.2–5.4** | `NetworkGauge.lean` | `netDist` observer-glued sup: ultrametric, cylinder *profiles*, SU0 reduction at one place, schedule invariance, `network_separation_cost` (per-observer gauge speed) | ✅ BUILT |

**Phase 14 is in the corpus**: `docs/fdrs.md` Definitions 192–200, Theorems 83–92,
Propositions 147–149; index block appended to `docs/fdrs-index.md`.

## After SU5 (not in this arc)

Coupled-place confluence (conditional Kahn diamond — thesis §3 layer b), the full
accountability iff ("place-local ⟺ rectangle identity on reachables"), queue-valued
interfaces (capacity > 1), the run-tuple fairness bridge (infinite schedules → total
stream tuples), executable coupled engines over `PlaceEngine`, the SU2×SU1 composite
(traps on coupled structures), and network liveness (certificates guaranteed to
fire).
