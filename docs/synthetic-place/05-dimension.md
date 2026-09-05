# The dimension of a designed gauge (Hausdorff dimension as the tree↔gauge exchange rate)

**Status:** study COMPLETE (verdict GO) and **BUILD LANDED, all five rungs**
(2026-09-04): `FdrsFormal/Modes/SyntheticPlace/Dimension.lean`, 0 sorries,
axiom-clean (`propext`/`Classical.choice`/`Quot.sound`), wired into the
default build; spec numbered as **§14.15** (Definition 213, Theorems 116–118,
Proposition 153) with the §6.4.3 back-pointer; index rebuilt with exact
anchors. R1 Borel bridge ✓ (`pi_eq_borel_completedSpace`), R2 gauged synonym ✓
(full instance stack incl. `IsUltrametricDist`, basis, separability, Borel,
measure transport), R3 Moran frame ✓ (`GaugedSpace.dimH_univ_le` /
`GaugedSpace.le_dimH_univ`), R4 canonical = 1 ✓
(`dimH_completedSpace_eq_one`, every radix schedule, via the definitional
`canonicalIsometry`), R5 designed instances ✓ — `dimH_designedGauge` (= r, all
r > 0), `dimH_factorialGauge_eq_zero` (= 0), `dimH_polyGauge_eq_top` (= ∞).
The D4/D5 "stretch tier" fully landed; nothing was degraded. §5's open
frontier stands unchanged.

## 0. Frame — where this comes from

An external thread (fractal-CW / higher-categories) argued: there is no atomic
"r-morphism" for real `r` the way the `n`-disk is the atomic `n`-morphism for
natural `n`; a real-indexed cell theory must be built on diagrams and rewrite
witnesses, not representable atoms. Our reply: keep integer-indexed atoms
(cylinders at integer depth) and the usual attaching recursion, put the real
number on the **gauge** — then "the r" is not an arity but a *derived invariant
of the (tree, gauge) pair*, and atomicity questions become exactness questions
(Theorem 93's territory). This record turns the slogan into theorems:

> **The canonical gauge pins the dimension to 1 — that is what makes a number
> line a *line*. Freeing the gauge (Phase 6's inverse problem, Theorem 43's
> (C4) axis) frees the dimension: Hausdorff dimension is a programmable
> functional of the gauge schedule, realizable at every prescribed value.**

This is the corpus's first *analytic* invariant (its first contact with
`dimH`/Hausdorff measure), and it upgrades §6.4.3's growth-regime prose
(exponential / polynomial / factorial) from examples to computed dimensions.

## 1. The claims (all classical mathematics; see §3)

Let `R̂ = ∏ᵢ Fin(bᵢ)` (`CompletedSpace b`, `bᵢ ≥ 2`), `B_L = ∏_{i<L} bᵢ` the
place value. A **position gauge** is `g : ℕ → ℕ`, `g ≥ 1`, monotone,
unbounded; the gauged distance is `δ_g(x,y) = g(firstDiff x y)⁻¹` — the
position-only instance of Definition 192's prefix gauge, and the designed
ultrametric of §6.4 made concrete.

- **(D1) The Moran frame, cover half.** If `B_L · g(L)^{-d} → 0` then
  `dimH ≤ d`. (Cover by the `B_L` depth-`L` cylinders, each of diameter
  `≤ g(L)⁻¹`.)
- **(D2) The Moran frame, mass half.** If eventually `B_L⁻¹ ≤ (g(L)⁻¹)^d`,
  then `d ≤ dimH`. (Mass distribution / Frostman with the corpus's uniform
  product measure: `μ(cylinder_L) = B_L⁻¹` is Definition 21, already proven.)
- **(D3) Every number line is one-dimensional.** For the canonical gauge
  `g = B` (any radix schedule!): `dimH R̂ = 1`. Both halves are trivial
  instances of D1/D2 because `μ(cyl) = diam(cyl)` on the nose. Read with
  Theorem 43: condition (C4) — canonical diameters — is precisely the gauge
  locked to the tree; *being realizable as a number system pins r = 1*.
- **(D4) The gauge programs the dimension.** On the binary tree, the schedule
  `g(n) = 2^⌈n/r⌉` gives `dimH = r`, for every real `r > 0`. With D5's
  endpoints, every `r ∈ [0, ∞]` is realized by a designed gauge over a fixed
  tree — the "r" lives entirely on the gauge axis.
- **(D5) §6.4.3's regimes computed.** Factorial gauge (`g(n) = n!`,
  Example 6.4.3(3)) ⇒ `dimH = 0`; polynomial gauge (`g(n) = n+1`,
  Example 6.4.3(2)) ⇒ `dimH = ∞`; exponential schedules (6.4.3(1)) are D4.

Verification of the paper mathematics was done step-by-step against the
available Lean tools before any build (see §4 ladder); the only delicate
points, both resolved: (i) Mathlib's mass-distribution lemma
(`le_hausdorffMeasure`) carries no multiplicative constant — absorbed by the
`ε`-smallness parameter (only depths `≥ N` matter); (ii) non-strict gauges
(`⌈n/r⌉` has runs) break the `<`-iff of the canonical metric file — but
`dist < g(L)⁻¹ ⇒ agree through L` needs only monotonicity, and that is the
only direction the argument uses.

## 2. Reuse map (nothing rebuilt from scratch)

| Need | Existing artifact |
|---|---|
| space, cylinders, firstDiff, canonical metric | `Topology/Ultrametric/Definition.lean` (`MetricSpace (CompletedSpace b)`, `closedBall_eq_cylinder`, `agree_on_prefix_iff`) |
| uniform measure + `μ(cyl) = B_L⁻¹` | `FunctionSpaces/Measure/ProductMeasure.lean` (`uniformProductMeasure`, `cylinder_measure`, `cylinder_measurableSet`, probability instance) |
| cylinders are a topological basis; separability; second countability; `generateFrom(cyl) = borel` | `Topology/Filtration/Definition.lean` |
| `pi`-σ-algebra comparison technique | `Modes/VariableRadix/SubshiftParry.lean` (`iSup_piLE_eq_pi`) |
| Hausdorff machinery | Mathlib: `hausdorffMeasure_le_liminf_sum` (covers), `Measure.le_hausdorffMeasure` (mass distribution), `dimH_le_of_hausdorffMeasure_ne_top`, `le_dimH_of_hausdorffMeasure_ne_zero`, `dimH_univ` (isometry transport) |

New infrastructure that is corpus-valuable beyond this file: **the Borel
bridge** `MeasurableSpace.pi = borel (CompletedSpace b)` — the measure lives
on the product σ-algebra, the metric results on the Borel one; the corpus has
never welded them. (Half exists: `cylinder_generateFrom_eq_borel`; the other
half is the `pi ≤ generateFrom(cylinders)` comparison via coordinate
evaluations.)

The designed metric goes on a **type synonym** `GaugedSpace b G :=
CompletedSpace b` (instances keyed by the gauge; no clash with the canonical
instance; the measure transports definitionally since the measurable-space
instance is literally the same term). D3 is stated on `CompletedSpace b`
itself and transported through the definitional isometry
`GaugedSpace b (placeValue-gauge) ≃ᵢ CompletedSpace b`.

## 3. Prior art and honest novelty

- **The mathematics is classical.** D1–D5 are Moran (1946) / Falconer
  (*Fractal Geometry*, ch. 4) / Billingsley-style dimension on sequence
  spaces; "dimension of a self-similar/Moran set = ratio of branching to
  contraction" is textbook. **No new mathematics is claimed.**
- **Formalization prior art** (searched 2026-09-04: Lean/Mathlib docs +
  Zulip, Isabelle AFP, generic literature): Mathlib contains the *theory*
  (Hausdorff measure, `dimH`, Hölder/Lipschitz transport, `dimH` of real
  sets) but, in the checkout we build against, **no computed Hausdorff
  dimension of any Cantor-type/fractal set** (its `CantorSet` file carries no
  `dimH` statement; the only file mentioning `dimH` is the theory file
  itself). No AFP entry for Hausdorff dimension surfaced. So this is
  *plausibly* the first computed fractal `dimH` in the Lean ecosystem —
  stated as "plausibly": three searches, not a census.
- **What is FDRS-native here** is the statement, not the technique: dimension
  as a *design output* of the §6.4 inverse problem, the (C4)-axis reading of
  D3, and the wiring into the Phase-14 gauge keystone (Definition 192 /
  Theorem 83's position-only instance). Novelty = connection + curation +
  verified artifact, per the standing corpus verdict.

## 4. Build ladder (risk-ordered)

1. **R1 — Borel bridge** (`pi = borel`) + `BorelSpace` instances. Zero
  mathematical risk; pure σ-algebra bookkeeping.
2. **R2 — gauged synonym**: metric, ball = cylinder (monotone form), basis,
  separable, second countable, Borel, measure transport. Mirrors existing
  files; mechanical.
3. **R3 — D1 + D2** (the generic Moran frame). The declared grind: ENNReal
  `rpow`/`liminf` bookkeeping. The mathematics is fixed (§1); only names and
  casts are discovered on site.
4. **R4 — D3** (canonical = 1) via R3 + the definitional isometry.
5. **R5 — D4** (designed `r`) and **D5** endpoints (factorial ⇒ 0 via
  `c^n/n! → 0`; polynomial ⇒ ∞ via `(n+1)^d ≪ 2^n`). D4/D5 are the
  stretch tier: if a corner of the real-analysis grind exceeds budget, the
  landed subset is numbered in fdrs.md and the remainder recorded here —
  never numbered unlanded.

Landing spot: `FdrsFormal/Modes/SyntheticPlace/Dimension.lean` (leaf; wired
into `Modes/SyntheticPlace.lean`). Spec: new `### 14.15`, items numbered from
Definition 213 / Theorem 116 / Proposition 153; §6.4.3 gets a forward
pointer. Index rebuilt by `scripts/fdrs-rebuild`.

## 5. Open frontier (recorded, NOT claimed)

- **Does dimension survive the network migration?** Phase 14's law — scalars
  die, laws survive indexed-and-glued — poses: per-observer `dimH` is
  well-defined; the sup-glued `netDist` (Theorem 92) satisfies
  `dimH(glued) ≥ max(local)` for free (1-Lipschitz identities); what upper
  structure does coupling force? Conjecture-shaped: coupling shows up as a
  *dimension deficit* of the reachable configuration space.
- **The computability shadow (hypothesis, unverified analogy).** Unilateral
  coupling keeps tree-indexed structure (Bowen/Moran territory: computable
  ratios). *Bilateral* coupling — obstruction #2 — is structurally where
  multidimensional-SFT phenomena could enter; for ℤ^d-SFTs (d ≥ 2) the
  achievable entropies are exactly the right-recursively-enumerable reals
  (Hochman–Meyerovitch, *Annals* 171(3), 2010, 2011–2038; irreducible-SFT
  entropy is computable). If the analogy holds, "no atomic r" in the coupled
  regime has a hard computability echo. **Flagged loose:** FDRS networks are
  Kahn dataflow, not ℤ²-shifts; the correspondence is unestablished, and per
  the corpus's novelty priors the likely outcome of pursuing it is a
  decomposition into classical pieces. First task of any follow-up: the
  literature pass on dimension theory of constrained product systems.
- **The categorical restatement** (gauge cocycle as a functor killing π₁;
  Theorem 93 as an H¹-vanishing) and a **decidable gradability check**
  (spanning tree + fundamental cycles, Zaslavsky-style, currently absent from
  `Grading.lean`) remain curation candidates; neither is load-bearing for
  this record.
