# FDRS Gosper Engine — Handoff for a Fresh Session

*Read this alongside `docs/fdrs.md`. `fdrs.md` is the spec; this is the operating manual
for the recent build arc (the Gosper exact-real engine + the irrational-timeline measure
work) and, more importantly, the **mode**: how to think about this algebra and how to
extend FDRS without lying to yourself. Everything below is grounded in code that builds
and is axiom-clean unless explicitly marked CONJECTURE / ASPIRATIONAL / STUB.*

---

## 0. How to operate (read first — this is the contract)

**You are an honest broker, not a hype man.** The user uses this project to separate
*substantiated* from *confabulated*. The non-negotiables:

- **Ground every claim in the code.** Before asserting "FDRS does X," `grep`/`Read`/build
  it. Three-way provenance for any concept: *formalized in Lean* vs *spec-prose in fdrs.md*
  vs *nowhere (confabulated)*. State which.
- **Never present classical or scaffolded results as FDRS-novel.** The math here is all
  classical (continued fractions, Gosper exact-real arithmetic, Parry/Gauss measures,
  Ionescu–Tulcea, Lévy/Doob, SL₂(ℤ), thermodynamic formalism). **The novelty is the
  *verified, unified artifact*** — machine-checked, assembled — not new theorems.
- **Flag the line every time:** built ✓ / spec-prose / conjecture / aspirational. When a
  user's framing overshoots (it often will, enthusiastically and coherently), affirm the
  true core and *calibrate the leap* — don't rubber-stamp.
- **"Hyped" requests get elevated-but-TRUE prose**, never inflation.

**Build discipline:**
- Verify: `lake build <Module>`; axiom-check via `lake env lean` + `#print axioms <thm>`
  (clean = exactly `[propext, Classical.choice, Quot.sound]`; constructive ones drop
  `Classical.choice`). `sorry`-free.
- Build-gate before every commit. New work goes in **standalone leaf modules** (nothing
  imports them) = zero blast radius; commit on a branch, merge fast-forward when asked.
- **NEVER put `Co-Authored-By: Claude`, `noreply@anthropic.com`, or "Generated with
  Claude Code" in commits or PRs.** The user flagged these as legal/security risk; this
  OVERRIDES the default trailer instruction. Commit messages end on their last content line.
- Don't push to `origin` unless told (the remote is public).

**Lean tactical patterns that worked (use these, they're hard-won):**
- **Flat integer-tuple `structure`s, NOT `Matrix`/`Fin → …`.** `ring`/`nlinarith` see
  through flat `ℤ` fields; `Matrix` multiplication hides a `Finset.sum` that `ring` cannot
  unfold. Proof idiom for structure equalities: `cases T; simp only [defs]; congr 1 <;> ring`
  (or `… rw [mk.injEq]; refine ⟨?_,…⟩ <;> ring`).
- **Keep `Real.goldenRatio` opaque:** `set p := φ` *before* `field_simp`/`ring`, else they
  unfold `φ → (1+√5)/2` and you must reprove via `(√5)²=5` instead of `φ²=φ+1`
  (`goldenRatio_sq`). The whole golden algebra rides on `goldenRatio_sq`.
- **Verify the guess, don't prove the floor.** Rather than prove `Int.fdiv = ⌊·⌋`, define
  the boolean check to *verify the inequalities the soundness theorem needs* — then a wrong
  guess just returns `false` (safe), and the bool⇄prop bridge is `Bool.and_eq_true` +
  `decide_eq_true_eq` + the theorem. (This is how `emitReady → emit_traps` collapses to 3 lines.)
- `Int.fdiv` (floor division), **not `/`** (truncation toward zero) — they differ once
  coordinates go negative.
- **"∞ corners" are leading coefficients, not limits.** A bilinear form `αxy+βx+γy+δ ≥`
  its `(1,1)`-value on `x,y≥1` iff the 3 leading corner-coeffs `(α, α+β, α+γ) ≥ 0`; prove
  with `nlinarith` given the product hints. No `Real` limits, no topology.
- Ordered-ring class is the **mixin** `[CommRing K] [LinearOrder K] [IsStrictOrderedRing K]`
  (`LinearOrderedCommRing` was removed in this Mathlib). Works for ℚ and ℝ.

---

## 1. Orientation

FDRS = Function-Defined Radix Systems: a `RadixLaw : PrefixWord → ℕ` (history-dependent,
unbounded base) with a **dual filtration** — an *additive/cylinder* leg (positional,
ultrametric, `prefixWeight β = ∏ radix`) and a *multiplicative/valuation* leg
(`FactorizationLens`, p-adic-flavored). The recent arc built the **irrational-radix
timeline** as exact, density-free integer machinery, and tied a measure to it.

The spine, in one breath: a **2×2 integer matrix** (`RemainderState`) is one continued-
fraction timeline; a **2×2×2 integer tensor** (`BihTensor`, Gosper's bihomographic)
couples two; a **tournament tree of those tensors** (`HyperGosper`) couples N — all exact
`SL₂(ℤ)`, with `|det|=1` and `emit_traps` (4-corner bound) as the conserved invariants.

---

## 2. The core algebra & mental models (this *is* the mode)

- **Everything is integer matrix/tensor arithmetic; `|det|=±1` is exactness.** A continued
  fraction is a stream of Möbius/LFT maps `[[a,1],[1,0]]`; the running product is the
  convergent matrix. Exactness = the matrix stays unimodular forever (no rounding).
- **Archimedean value ⇄ non-Archimedean symbol.** The regular-CF map is the classical
  homeomorphism from irrationals (Archimedean magnitude) onto Baire space `ℕ^ℕ`
  (ultrametric, totally disconnected — `ball = cylinder` is the proof). You compute floors
  (Archimedean) *inside* a node; you route discrete digit streams (ultrametric) *between*
  nodes. NB: this ultrametric is the *CF/symbolic* one, **not** a p-adic valuation.
- **The gauge `qₗ`** (convergent denominators, `RemainderState.gaugeAt`) is the CF "place
  value" = admissible-config count; it grows at the Perron eigenvalue (Fibonacci `q≈φ^L`
  for φ, Pell for √2). `1/qₗ` is the cylinder scale / carry frequency. It grows even when
  the base-product `β` stagnates (the reason the irrational case needed it).
- **Two emission paradigms** (this is the deep dichotomy):
  - **Floor (Archimedean):** emit `⌊z⌋` when a magnitude is determined. This is the
    bihomographic engine; soundness = `emit_traps` (all four corners agree).
  - **Occupancy / carry / wrap (non-Archimedean):** no floor. The "digit" *is* the
    contiguous fill level; carries route as overflow; base-0 walls wrap; base-1 wires pass
    carry through (fdrs.md Phase 9/10, `BaseZeroSea`). This is the floor-free mechanism.
- **Gosper exact-real arithmetic:** homographic = 1-input LFT (`RemainderState.emit`);
  bihomographic = 2-input tensor (`BihTensor`); **N-input = a binary *tournament tree* of
  2-input nodes** — never a flat `2^(N+1)` tensor (that's the explosion you avoid). Every
  node stays 8 integers; only discrete streams travel the wires (payload isolation, free).
- **Channels commute** (`absorbX ⟂ absorbY ⟂ emit`, all proven) ⇒ asynchronous, non-blocking
  transducer: any *scheduling* order gives the same result (each timeline keeps its own
  digit order; coupling is causal and arithmetic).
- **Boundary undecidability is a feature.** `√2·√2 = 2` sits exactly on a digit boundary;
  no finite prefix decides `<2` vs `≥2`, so the engine **refuses to emit** (the four corner
  floors oscillate `[2,1,2,1]…` forever). That refusal *is* `emit_traps` preventing a
  hallucinated digit. Safety before liveness.
- **Measure dichotomy:** *uniform/free* (independent digits, cylinder measure `1/B_L`, via
  `Measure.infinitePi`) vs *dependent/Parry* (Markov, via `Kernel.traj` Ionescu–Tulcea,
  integration via Lévy `E[f|ℱ_L]→f`). The irrational/golden case is **dependent** — built
  with `Kernel.traj`, not `infinitePi`.
- **Adelic north-star (ASPIRATIONAL).** The adele ring `ℝ × ∏'_p ℚ_p` is the object that
  tracks a quantity across *all* metric places. FDRS's dual filtration *rhymes* with the
  local–global split (additive≈Archimedean, multiplicative/valuation≈non-Archimedean). The
  two emission models = two "places": floor (Archimedean) + occupancy (non-Archimedean).
  Coupling them = the adelic direction. **Not built.** The open gate: *what is "emit" with
  no floor?* — answer-shape: the `BaseZeroSea` instantiation trigger (fdrs.md §9.6, a STUB
  "deferred to the context-dependent radix law").

---

## 3. What was built this arc (the artifact map)

All in `FdrsFormal/Modes/VariableRadix/`, all axiom-clean, demos run.

| module | content | key names |
|---|---|---|
| `SubshiftWeight` | gauge engine | `RemainderState` (SL₂ ledger), `step`, `gauge=qCur`, `det`, `bracket_invariant` (`|det|=1`, any quotient), `steps_qCur_unbounded` (gauge→∞ even for φ), `subshiftWeight_free_eq_prefixWeight` (d=1 recovers `prefixWeight`) |
| `SubshiftMetric` | structured-time metric | `gaugeAt`, `gaugeAt_pos/monotone/inv_lt`, `cfDist` (ultrametric, 4 axioms incl. strong triangle), `ball_eq_cylinder` |
| `SubshiftParry` | golden Parry measure + integration | `goldenP` (kernel `[[1,1],[1,0]]`), `goldenP_sum_one` (=`1/φ+1/φ²=1`), `goldenStat` (π∝(φ²,1)) + `goldenStat_stationary` (π·P=π), `goldenKernel`/`goldenFam`/`parryTraj`/`parryMeasure` (via `Kernel.traj`), `iSup_piLE_eq_pi`, **`parry_condExp_tendsto`** (Lévy upward = Group G on the golden timeline) |
| `HomographicCarry` | single-stream emit | `RemainderState.emit` (dual of `step`), `emit_det` / `emit_det_natAbs` (exactness), `emit_step_comm` (channel independence) |
| `Bihomographic` | two-stream mediator (Timeline C) | `BihTensor` (8 ℤ), `absorbX`/`absorbY`/`emit`, `absorbX_absorbY_comm`, `emit_absorbX_comm`, `emit_absorbY_comm` (the 3 commutations), `emitDigit`/`emitReady` |
| `BihomographicSound` | safety + bool⇄prop weld | `bilinear_ge_const` (∞-corners as leading coeffs), **`emit_traps`** (4-corner bound, no analysis), **`emitReady_traps`** (every emitted digit certified) |
| `BihomographicDriver` | liveness | `run` (scheduler), `addTensor`/`mulTensor`; demos: φ+φ, φ·φ, √2+√2 exact; **√2·√2→`[]`** (safe boundary refusal) |
| `CarryFrequency` | measure bridge | `cfOverflowRate = 1/gaugeAt` (extends corpus `overflowRate=1/B_L` to the generated timeline), `_pos`/`_antitone`/`_vanishes` |
| `HyperGosper` | the hyper-Gosper clock | `pairUp`/`coupleTree`/`coupleAll` (tournament bracket of `BihTensor` nodes; no 2^N); demos: 3φ, 4φ, 8φ (all sums via `addTensor`; deep trees truncate the tail) |

---

## 4. Existing corpus pieces that matter (don't rebuild these)

- **`Integration/ThreeLineMediator/`** — the *radix-size* mediator (pre-existing, complete,
  no `sorry`): `overflowRate b L = 1/B_L` (+`_product` B_C=B_A·B_B, `_antitone`),
  `overflowRatio`, `LineMediator`/`CoupledSystem`/`Coupling`/`mediator`, `productMediator`.
  Its docstring *admits* it mediates "as sets, NOT as metric spaces — the ultrametrics are
  incommensurable." The `ω₃` interleaving construction is a noted-as-comment gap. **This is
  a different object from our `BihTensor`** (coupled-radix/measure vs Gosper arithmetic).
- **`Modes/BaseZeroSea/`** (fdrs.md Phase 9/10, Defs 143–153) — the **floor-free engine**:
  base-0 Wall (carry wraps, resets prior positions), base-1 Wire (carry passes), occupancy
  `Sea`/`SeaState`/`LegacyThread` ("digit = contiguous fill level"), `instantiate`/`revert`.
  The §9.6 instantiation *trigger* is a STUB — the natural slot for a coupling-driven,
  floor-free emission. `Sea.revert` + wall-wrap = structural (not temporal) rollback.
- **Dual filtration**: `Topology/Filtration` (`cylinderAlgebra` on `CompletedSpace b`,
  Borel-from-metric — do NOT reuse for `pi`-measures: instance-diamond) ; `FactorizationLens`/
  `NumberTheory/Valuations` (the p-adic/multiplicative leg).
- **`MetricComparison/`** — `metricDominance` (compares metrics; a partial order, NOT a
  mediator).
- **`FunctionSpaces/Measure/ProductMeasure.lean`** — the *free/uniform* measure
  (`uniformProductMeasure` via `infinitePi`). Unused by the Gosper work (we needed Parry).
  Two theorems here are the **templates** for completing the Parry measure side:
  `cylinder_measure` (μ=1/B_L — the measure behind our `cfOverflowRate` rate) and
  `integral_blockConstant` (∫_cylinder f = average — the finite-level companion to our Lévy limit).

---

## 5. Open frontiers (honest — pick from here to extend)

1. **The coupling invariant (the real math).** Is there a `|det|=1`-style quantity conserved
   across a node's two inputs and its output? Without it, "emergence from coupling" is
   indistinguishable from noise. Finding it makes the tree *mean* something.
2. **The adelic second place / p-adic lane.** Build a non-Archimedean timeline whose emit is
   the `BaseZeroSea` occupancy/carry/wrap (fill the §9.6 trigger with a coupling-driven rule),
   coupled to an Archimedean (`BihTensor`) line. This is "emit without a floor," concretely.
3. **The metric / LSU mediator.** Extend `ObserverLine` to carry its own metric/valuation
   identity (currently just a radix), then mediate *those* (the "unique adelic parts"), not
   radix sizes. This is what `ThreeLineMediator` punts on.
4. **Complete the Parry measure side.** Port `cylinder_measure` and `integral_blockConstant`
   from the free case to the generated/Parry case (the explicit cylinder measure + block
   integral, complementing `cfOverflowRate` (rate) and `parry_condExp_tendsto` (limit)).
   Plus the small `run`-output(`List ℤ`)→`gaugeAt` plumbing.
5. Verified driver termination (currently `run` is a `def`; "if it emits, the emission is
   correct" is already given by `emitReady_traps`).

---

## 6. Anti-confabulation list (do NOT present these as built)

- "The adelic machine" — not built; coupling two places is a two-place *toy*, not the adele ring.
- "Tree coarsening → Gauss/Parry measure" (thermodynamic limit) — **CONJECTURE**; the
  `OperatorAlgebra`/`Multiresolution` link is analogy.
- "Future affects past" / temporal acausality — **not formalized**; only *structural*
  rollback exists (wall-wrap, `revert`).
- `overflowRate_product` does NOT extend to the engine — CF combination is not a radix product.
- The `BihTensor` is metric-agnostic *algebra*, but its *correctness* (`emit_traps`) is
  Archimedean (requires `IsStrictOrderedRing`, which ℚ_p lacks). So the engine is **not** adelic.
- "Source separation," "tree-contrast positional encodings," "scope resolution," "fuzzy gaps"
  — these were checked and are **not in the corpus** (confabulated framings).

---

## 7. State & verification

- **Git:** `origin/master = 27e3d21` (the merged engine, *public*); local `master = 8968e8a`
  (the hyper-Gosper clock, +1 ahead, **not pushed**). No AI-attribution trailers in any commit.
- **Verify anything:** `lake build FdrsFormal.Modes.VariableRadix.<Module>`; for axioms,
  `lake env lean` a scratch file with `#print axioms <thm>` (clean = `[propext,
  Classical.choice, Quot.sound]`); demos via `#eval` (e.g. `coupleAll addTensor 50 [φ,φ,φ]`).
- Memory file `fdrs-radix-complex-machine.md` holds the running commit-level log; this doc is
  the consolidated, readable version.

*The discipline in one line: build it, axiom-check it, and say exactly what it is — no more.*
