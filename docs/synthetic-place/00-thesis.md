# Synthetic Place System (SPS) — thesis and scope

**Status:** design committed; build follows the roadmap in `01-build-roadmap.md` (SU0–SU3).
**Frame:** this series is the unification of the standing *radix-complex* goal (the
operational closure of `CoupledDigitNetwork`) with the synthetic-ultrametric program:
one named object — the **synthetic place complex** — carrying gauges, digit fibers,
emission certificates, and coupling. The adelic complex (`Modes/Adelic/`) is the
*ancestor and template*, not the target.

---

## 1. Thesis

> A **synthetic ultrametric** is a constructed refinement geometry whose "digits" are
> not merely positional symbols but admissible local states inside a substrate.
> Mixed-radix structure supplies the branching degrees of this geometry, while coupling
> laws restrict which digit configurations can coexist across levels, places, or
> timelines. **Sequence emission is the observable trace of movement through nested
> ultrametric domains** — and an emission is *certified*, not chosen: a symbol is
> emitted only when every admissible continuation of the current state agrees on it.
> The resulting representations are constrained not by ordinary magnitude but by the
> substrate's admissibility, refinement, and coupling laws: the ultrametric basis is a
> representation-constraint generator.

Two corrections are baked into this statement relative to its first draft:

1. **Emission is transductive, not generative.** Walking a tree by free choice has no
   theorems in it. The engine content is the *forced* digit — the certificate that all
   admissible tails agree — which is the third sibling of the corpus's two existing
   certificates (the Archimedean four-corner order trap, `BihomographicSound.lean`;
   the p-adic congruence trap, `PadicEmitTraps.lean`). SPS adds the **admissibility
   trap** (SU2).
2. **This is not a number system.** History-dependent fibers and cross-timeline
   coupling generically destroy sibling uniformity (Phase 5.4 §5): there is no global
   rank chart, no odometer, no `dec`/`enc`. Transport-through-decode — the corpus's
   primary proof engine — is unavailable here by design. Proofs in this series use
   invariant-preservation induction (the `LinearChain`/sea style, Theorem 64's
   template). Where decode *does* survive (the SU regime), the corpus already has the
   results (Theorem 38, Corollary 27); SPS does not rebuild them.

## 2. What SPS is not (the boundary, machine-checked elsewhere)

- **Not fake p-adics.** `Rigidity.lean` proves the FDRS gauge aligns with a p-adic
  place value iff the base is constantly `p`: there are no synthetic places *on ℚ's
  arithmetic*. SPS never couples to `ℚ`, `ℝ`, or `ℚ_p`; its gauges are first-class
  objects with their own laws.
- **Not the adelic product formula.** See §3.
- **Not a classification.** SPS builds gauges, traps, and couplings; it makes no
  Ostrowski-style claim that its places exhaust anything.

## 3. The conservation question — boundary PROVEN (SU4), cross-place law beyond accounting still open

The classical instance had a quantitative cross-place identity (`∏_v |x|_v = 1`).
For synthetic places three layers must not be conflated:

| Layer | Content | Status |
|---|---|---|
| (a) Safety | admissibility/coherence preserved by every step (`Coherent → Coherent ∘ step`) | provable per instance; corpus precedents: Thm 51 (injection preserves CSU), `linearChainStep_valid`, sea validity (Prop 127) |
| (b) Determinacy | scheduler confluence — result depends only on per-place step counts | proven for *disjoint* places (`run_eq_of_counts`); for *coupled* places it is conditional and genuinely new (expect a local-confluence-under-independence theorem) |
| (c) Conserved quantity | a nontrivial invariant tying coupled places together | **partially resolved — SU4 BUILT** (below); product-formula-analogue slot honestly empty |

Layer (a) is not a conservation law and must never be presented as one. The
carry-accounting candidate is now **theorem-shaped** (the SU4 arc, all 0-sorry,
axiom-clean):

- **SU4a — the partition law** (`Conservation.lean`): completion mass is partitioned
  by the observed symbol (`setMass_partition`, the continuity equation of
  refinement), and **certified emission transfers mass exactly** — zero leak
  (`certified_mass_conservation`); golden-instance demos are Fibonacci counts,
  kernel-`decide`-checked.
- **SU4b — the interface balance law** (`InterfaceBalance.lean`): the coupled machine
  with a declared ledger satisfies `issued = consumed + pending` on every reachable
  configuration (`reachable_balanced` — Prop 128 / Theorem 57 shape, exact and
  per-step local), for **arbitrary** `CoupledFiber` coupling.
- **SU4c — conservation rigidity** (`ConservationRigidity.lean`): any place-locally
  accounted charge **factors** as `Φ(init) + f(sA) + g(sB)` (`placeLocal_factors`) —
  it cannot measure the coupling. **No-go**: for a genuinely bilateral coupling
  (`jointFiber`), the carry charge admits *no* place-local transfer rule
  (machine-checked rectangle violation `5+5 ≠ 6+6`); **boundary**: B-blind couplings
  are place-locally accountable (`issued_placeLocal_of_blind` — SU1's `raggedFiber`
  sits inside). The obstruction is bilaterality, not raggedness; the conserved
  quantity of a genuine coupling lives ON the interface, not in the places.

**Still open, and to be stated as open**: the full iff ("place-locally accountable ⟺
grant satisfies the rectangle identity on reachables"); coupled-place confluence
(layer b); and any *cross-place multiplicative identity* beyond accounting — the
corpus's own evidence (the product law broke on leaving radix products while the
carry-frequency law survived, Phase 13 §13.4) suggests none should be expected, and
none is claimed.

## 4. Corpus leverage (what exists / what is new)

| Ingredient | Status |
|---|---|
| Substrate states | ✅ `Sea`, `CoupledDigitNetwork`, `LinearChain` |
| First-disagreement cylinder metrics | ✅ Phase 1 δ; δ_ω (Def 79); `cfDist` (Phase 13) |
| History-dependent fibers (one timeline) | ✅ `RadixLaw` (Def 57); subshift constraints (`subshiftWeight`) |
| Gauge → ultrametric, *general* | 🔨 **SU0** (unifies the product and CF instances) |
| Fibers driven by *another* chain's state | 🔨 **SU1** (Phase 7 oracle with chain-valued context) |
| Emission engine interface | ✅ `PlaceEngine` (reused verbatim) |
| Emission certificate on designed gauges | 🔨 **SU2** (the admissibility trap) |
| Zoom-out representation restrictions | ✅ in instances (Thm 43, Cor 27, Thm 66, Prop 133); 🔨 **SU3** gauge-general forms |
| Confluence, disjoint places | ✅ `run_eq_of_counts` |
| Confluence, coupled places | 🔬 open (after SU1) |
| Conserved quantity | 🔬 open (§3) |

## 5. Anti-confabulation ledger

1. **Do not claim a conservation law.** Layer (a) safety results are invariants, not
   conservation; the quantitative invariant is open (§3).
2. **Do not claim SU0 proves "= δ_ω".** δ_ω lives on the dependent
   `InfiniteVariableSpace`; SU0's product-gauge instance carries the same defining
   formula (Definition 79's `β_ω(lcp)⁻¹`) on raw digit streams. The type alignment is
   the same outstanding infrastructure as Theorem 43 step 4 — cite, don't blur.
3. **Do not call the coupled tree a `RadixLaw`.** With coupling, even a single node's
   pair-fiber is jagged (the valid `(a,b)` set is not a rectangle), so it is not a
   radix tree in the Mode-I sense — that is the *point*, not a defect (Phase 5.4 §5).
4. **Generative walks are not results.** Only certified (trap-gated) emissions count
   as engine theorems.
5. **No neural/learned anything in Lean claims.** Codebooks, task grammars etc. are
   motivation prose only.
6. **`decide`, not `native_decide`,** for finite witnesses — `native_decide` would
   break the axiom-clean discipline.
7. **Honest naming:** "synthetic place" = a designed gauge + fiber + certificate
   package; it does not imply any field, any valuation theory, or any completeness
   claim.
