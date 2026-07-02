# SU7 — the network arc: `Config` + `complexStep` (the radix-complex machine)

**Status:** design blessed; **SU7.0 probe BUILT** (`NetworkConfig.lean`, 0 sorries,
axiom-clean): the 2-node/1-edge network machine recovers the SU4b interface machine
exactly (`pairNet_reachable_iff` — reachable sets correspond under the bijective
configuration correspondence; balance transports per edge; the ragged demo run lands
on SU4b's ledger, kernel-checked). The `Config` design passes its own mandatory gate
(§5.6). **SU7.1 BUILT** (`NetworkComplexStep.lean`, 0 sorries, axiom-clean): the
three-clause `complexStep` — fan-out lawfulness as a firing guard (declared carry
mass partitioned by transport shares, Theorem-88 shape; trigger diagonal), joint-fiber
guards with per-edge `admit` windows, and well-formedness = dependency grading with
Phase 8's `time_ordered_deadlock_free` reused verbatim as the certificate (a
dependency cycle admits no potential — the causal-frustration no-go, candidate
only). Conservative over SU7.0 (`ofRule_reachable_iff`; the SU4b probe transports:
`pairComplex_reachable_iff`); mixed split witness live (lawful `1+3=4` fires with
trigger token, unlawful `1+2` blocked, kernel-checked). Recorded decisions D7 (one
ambient currency per module instance; per-edge currencies + morphisms = SU7.2) and
D8 (carry mass is a per-node declaration; `none` = SU4b's capacity-grant regime).
**SU7.2 BUILT** (`NetworkBalance.lean`, 0 sorries, axiom-clean): per-edge balance by
literal SU6b reuse (`edge_currencyReachable` — the firing guards ARE the ledger
discipline; `network_balanced_per_edge` via `currencyReachable_balanced` verbatim);
the cross-edge sum in the ambient currency (`network_balanced_total` — the only
regime where it is meaningful, ledger item 3); **fan-out exactness as a theorem**
(`fire_fanout_exact`: a declaring node's firing issues exactly its carry across its
transport out-edges), with the structural bonus `fire_no_self_loop` (clause-2 guards
make self-loops unfireable — not legislated, derived). The heterogeneous machine
(`HRule`/`HConfig`/`HReachable`) delivers per-edge-per-currency balance
(`hnetwork_balanced_per_edge`, each edge in its own monoid); **D9 recorded**: the
heterogeneous carry partition needs per-node currencies + declared push morphisms
`Mv →+ M_e` — open, not smuggled. **SU7.3 BUILT** (`NetworkCouplability.lean`, 0 sorries, axiom-clean):
`Enabled`/`NonBlocking` (couplability = every reachable Config has an enabled
step); the **decidable check** `couplableCheck` (reachable-set fixpoint over a
declared finite-state abstraction — the SU2 stepSet shape — closure + all-enabled,
`Decidable` instance) with one-directional **soundness**
(`nonBlocking_of_couplableCheck`; no completeness claimed); the **live witness**
(constant coupled pair, Bool abstraction, check by `decide`, pending invariant —
`live_nonBlocking`); the **blocked witness** (`admit := False`, the empty joint
fiber: one step reachable then nothing enabled — `blocked_stuck`,
`blocked_not_nonBlocking` — a grammar strangled by its own coupling,
machine-checked). **SU7.4 BUILT** (`NetworkTraps.lean`, 0 sorries, axiom-clean): per-node engines
(`NodeEngines`: a `TransferStructure` + initial ledger per node, **windows as the
declared observation maps** from in-flight grants to the node's alphabet); the
tracked machine (`Tracked`/`trackedFire`/`TrackedReachable` — firing refines the
firing node's uncertainty ledger by its window observation; `tracked_base`:
tracking is conservative over SU7.1); consistency (`consistency_step` +
`tracked_consistent_fire` — refinement never loses the truth when the window is a
faithful observation map); and **`network_trap_sound`** — Theorem 86 per node on
the network, `trap_sound`/`emitNow_sound` transported VERBATIM: the network adds
bookkeeping, never new trust. Trajectory-level consistency needs the §14.7 fairness
bridge (SU7.5 territory). **SU7.5 BUILT** (`NetworkDeterminacy.lean`, 0 sorries, axiom-clean —
`[propext, Quot.sound]` only): the conditional Kahn diamond, local form. THE
DISCIPLINE PAYS (`no_edge_between`): under capacity-one, two distinct
simultaneously-enabled nodes can share NO coupling edge — the diamond's
independence side-condition is DERIVED from enabledness, not assumed.
`fireC_comm` (two enabled firings at distinct nodes commute on the nose),
`enabled_after_fire` (each survives the other, all four guards incl. fan-out
sums), `diamond` (both interleavings reachable, same configuration). Global KPN
determinacy = diamond + fairness (classical, cited; §14.7's open bridge). Same-node
choice non-determinism is the scheduler's, not the machine's. SU7.6 remains
pre-formalization. This is the arc the whole SPS series has
been statics for: the coupled radix network as a verified abstract machine — the
standing radix-complex goal (`Config` + `complexStep` + value), now with its value
layer correctly replaced by graded observables (Phase 14 thesis). Three previously
separate open rows of `03-digit-coupling.md` §7 are folded here deliberately —
**fan-out comultiplication, non-blocking couplability, and within-step dependency
orientation are clauses of the same `complexStep` definition**; designing them
separately would re-litigate the same edge structure three times.

---

## 1. What is already settled (the statics, all BUILT)

The network machine's *type* is assembled from proven layers; none of this is a
design choice anymore:

```
Config =
  nodes : per-node digit state          -- words; hierarchical nodes via exact
                                        -- charts (SU6d), certified conservative
                                        -- (SU6d′: resolution, never arithmetic)
  edges : per-edge interface register   -- CurrencyConfig M_e (forced by Thm 90:
                                        -- the conserved quantity lives ON the
                                        -- coupling; capacity-one = D6 latency)
```

Per-edge declarations (the coupling rule, axes of `03` §2):

| Declaration | Law already proven |
|---|---|
| ratio | grading classification of the graph — gradable ⟺ loop products 1 (SU6a iff); frustration legal |
| currency `M_e` + grant set | balance `issued = consumed + pending` monoid-generic (SU6b); transport vs trigger |
| window | accountability ⟺ grant uniformity (SU6c′, alternating case); clock free, content not |
| distribution species | transport splits must sum (Thm 88 shape); triggers are diagonal |

Geometry needs **no** new work: SU5's observer-glued ultrametric is already
network-native (per-place projections + sup), and SU3/SU5.4 price observability per
observer.

## 2. `complexStep` — one definition, three clauses

A step is: *one node fires, against its in-edge state, emitting into its out-edges.*

**Clause 1 — fan-out (the comultiplication).** A firing node's overflow event of
weight `g` produces a family of grants across its out-edges,
`Δ : M → Π_{e ∈ out} M_e`, lawful per species: the transport-edges' grants **sum to
the carry mass** (the emission-side partition law — Theorem 88's shape, now a
*constraint* on Δ rather than a theorem about refinement); trigger-edges each
receive one event-token (the diagonal). Mixed fan-out is legal. **Currencies never
mix**: there is no implicit exchange between mass and events — any cross-currency
flow requires a declared morphism on the edge (ledger item 3).

**Clause 2 — guards, and couplability as liveness.** A node may fire iff its joint
fiber is nonempty — digit choices consistent with every in-edge's pending grant and
window — and its transport out-edges have capacity (pending = none; the capacity-one
latency discipline, D6 generalized: an edge with an unconsumed grant blocks its
source). **"These lines can couple" = the guard system is non-blocking**: every
reachable `Config` has an enabled step. For finite-state window abstractions this is
*decidable* via the SU2 uncertainty machinery (reachable-set fixpoint over the joint
transfer structure); blocked witnesses are grammars strangled by their own coupling
— the empty-joint-fiber phenomenon of `03` §7.

**Clause 3 — within-step dependency orientation (acyclicity as grading).** When a
step reads several edges and writes several others, the rule declares its
reads-before-writes order. Well-formedness = **the dependency cocycle is graded**: a
`timeOf` potential exists — which is exactly Phase 8's
`time_ordered_deadlock_free`, reused as the certificate. The unification (from the
table discussion): `gradable_holonomy` (SU6a — multiplicative ℚ cocycle, magnitude)
and `time_ordered_deadlock_free` (order cocycle, causality) are the *same*
potential-existence mathematics. **The asymmetry is the design law**: magnitude MAY
be frustrated (the Penrose digit triangle is a legal, interesting complex — SU6a);
causality MUST NOT be (a causal loop within a step has no execution order at all).
Candidate **fourth obstruction to number-hood**: causal frustration — recorded as a
candidate only (ledger item 2).

Why one definition: all three clauses quantify over the same out/in-edge sets of the
firing node. The fan-out's targets, the guard's joint fiber, and the dependency
orientation are projections of one record. Three separate designs would fix the edge
structure three times and disagree.

## 3. Scheduling, and what reopens

The alternating two-place machine (SU4b) is the single-edge instance of the
capacity-one discipline; every balance/accountability result transfers per edge.
What does NOT transfer: the **window boundary**. SU6c′ closed it for strict
alternation because alternation broadcasts the partner's clock
(`reachable_length`); under free network scheduling, what a node can deduce of its
partners is governed by the *dependency grading*, not by lengths. The free-scheduler
boundary conjecture, properly stated, becomes: *accountable ⟺ the window factors
through schedule-deducible data, where "schedule-deducible" = determined by the
dependency potential.* Open; this arc's SU7.5–7.6 build the vocabulary it needs.

## 4. Build plan (SU7.x)

| Step | Content | Leverage |
|---|---|---|
| SU7.0 | Probe: the 2-node/1-edge instance of the network machine is (isomorphic to) the SU4b machine — the network conservatively extends what is built | sanity gate |
| SU7.1 | `Config`, `complexStep` (three clauses), well-formedness = dependency grading | Phase 8 reuse |
| SU7.2 | Network balance: per-edge, per-currency `issued = consumed + pending`, summed over edges; fan-out exactness (transport splits sum) | SU6b generic law per edge |
| SU7.3 | Non-blocking couplability: decidable check + soundness; a blocked witness and a live witness | SU2 fixpoint |
| SU7.4 | Per-node trap soundness on the network (uncertainty sets per node, windows as the observation maps) | SU2 transported |
| SU7.5 | Stream determinacy under the latency discipline — the conditional Kahn diamond | classical KPN, cited |
| SU7.6 | Network liveness: certificates guaranteed to fire under non-blocking + graded dependencies | Phase 8 + SU7.3 |

Sequencing: SU7.0–7.2 are one push (the machine + its conservation); SU7.3–7.4 the
couplability layer; SU7.5–7.6 the determinacy/liveness layer, hardest last.

## 5. Anti-confabulation ledger (SU7; prior ledgers inherited)

1. **Kahn-network determinacy is classical** (Kahn 1974 lineage); SU7.5 contributes
   the FDRS-shaped statement and artifact, nothing more.
2. **"Causal frustration = fourth obstruction" is a CANDIDATE**, promoted only if a
   theorem separates it from the existing three. No completeness claim over the
   obstruction list, ever.
3. **No implicit currency exchange.** Transport mass and trigger events never
   convert without a declared edge morphism; any prose implying "total network
   charge" must name the currency per edge or stay silent.
4. **SU6/SU6′ results are not yet numbered in fdrs.md.** Before SU7 cites them as
   corpus items, Phase 14 needs its addendum (the holonomy iff, currencies, window
   boundary, nested chart + conservativity). Until then, cite Lean names.
5. **The window boundary is closed only for strict alternation** (SU6c′). Free
   scheduling reopens it (§3); do not cite the iff outside its machine.
6. **The probe gate is mandatory**: if SU7.0 fails to recover the SU4b machine, the
   `Config` design is wrong — fix the design, not the probe.
