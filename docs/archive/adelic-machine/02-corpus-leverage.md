# 02 — Corpus Leverage

*The exact FDRS Lean tools to build the adelic complex from, leg by leg, with
signatures and provenance. The decisive artifact is the **order-dependence map**
(§3): precisely which machinery transfers to `ℚ_p` and which does not. Signatures
here were read from source (`Bihomographic.lean`, `BihomographicSound.lean`,
`CylinderMeasurability.lean`) or confirmed verbatim by corpus survey; paths are
under `FdrsFormal/`.*

Provenance tags per the README. "✅" = read/confirmed axiom-clean.

---

## 1. The Archimedean engine (Gosper) — the template, mostly reusable

`Modes/VariableRadix/` — the Phase 13.6 exact-real transducer.

**The ledger (pure `ℤ`, no order).** ✅
```
structure RemainderState where hPrev hCur qPrev qCur : ℤ          -- SubshiftWeight.lean
  step : RemainderState → ℕ → RemainderState                       -- absorb a quotient
  emit : ℤ → RemainderState → RemainderState                       -- HomographicCarry.lean
  det  : RemainderState → ℤ      gauge := qCur
  bracket_invariant : (init.steps as).det.natAbs = 1               -- |det| = 1
  emit_step_comm  : emit q (step r a) = step (emit q r) a           -- channel independence
  steps_qCur_unbounded : q_k → ∞ even for φ
```

**The two-stream tensor (pure `ℤ`, no order).** ✅ `Bihomographic.lean`
```
structure BihTensor where a b c d e f g h : ℤ        -- z = (a·xy+b·x+c·y+d)/(e·xy+f·x+g·y+h)
  absorbX absorbY : ℤ → BihTensor → BihTensor          -- read A / read B
  emit            : ℤ → BihTensor → BihTensor          -- write C
  emitDigit T := T.a.fdiv T.e                          -- candidate = floor at (∞,∞)
  emitReady T : Bool                                   -- 12 integer inequalities (4 corners)
  absorbX_absorbY_comm, emit_absorbX_comm, emit_absorbY_comm   -- all `ring`, pure ℤ
```

**The scheduler & the N-way coupler (pure `ℤ`, no order).** ✅
```
run : BihTensor → List ℤ → List ℤ → Bool → ℕ → List ℤ           -- BihomographicDriver.lean
addTensor mulTensor : BihTensor                                  -- z = x+y , z = x·y
pairUp coupleTree coupleAll : … → List (List ℤ) → List ℤ         -- HyperGosper.lean (tournament tree)
```

**The soundness — the ONLY order-dependent part.** ✅ `BihomographicSound.lean`
```
theorem bilinear_ge_const {K} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K] … 
theorem emit_traps        {K} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K] (T)(k:ℤ)(8 ineqs){x y:K}(1≤x)(1≤y) : k·D ≤ N ∧ N < (k+1)·D
theorem emitReady_traps   {K} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K] (T)(emitReady T = true) … 
```

**Reusability verdict.** Everything except the three theorems above is pure `ℤ`
algebra and transfers to *any* place verbatim (it never mentions order or `ℝ`).
The three soundness theorems are Archimedean and **do not** transfer. The p-adic
engine reuses the ledger/tensor/scheduler unchanged and swaps the certificate
(§2). This is the single most important leverage fact in the corpus.

---

## 2. The non-Archimedean certificate — already proven (the keystone)

`NumberTheory/CylinderMeasurability.lean` (775 lines, ✅ axiom-clean). This file
proves "congruence pinned by finite prefix," which **is** the p-adic emission
certificate when the base is constant `p`.

```
def congruenceSet (b k q a) := {τ | decodeFinite b k τ % q = a % q}

theorem residue_depends_on_prefix (b k L q) (hL : L ≤ k+1) (hq : q ∣ placeValue b L) :
    ∀ τ σ, (agree on first L digits) → decodeFinite b k τ % q = decodeFinite b k σ % q
-- "the residue mod q is fixed by the first L digits, when q | B_L"

theorem congruenceSet_is_cylinder_union (b k L q a) (hL)(hq : q ∣ placeValue b L) :
    ∃ prefixes, congruenceSet … = ⋃ over those L-prefixes          -- SUFFICIENCY

theorem congruenceSet_not_cylinder_union_of_not_dvd (b k L q)(¬ q ∣ placeValue b L)(q ∣ B_{k+1}) :
    ∃ a, ¬ (congruenceSet is an L-cylinder union)                  -- NECESSITY (sharp)

theorem dirichletChar_cylinder_measurable …   theorem additiveChar_cylinder_measurable …
def radixDepth (b q) := min{L>0 : q ∣ placeValue b L}              -- the "depth a modulus appears"
```

**Why this is the p-adic `emit_traps`.** Take constant base `p`, so
`placeValue b L = pᴸ`. Then `q = pᵏ ∣ pᴸ ⟺ k ≤ L`, and `residue_depends_on_prefix`
reads: *the residue `mod pᵏ` is determined by the first `L ≥ k` digits.* I.e. the
next Hensel digit is **forced by a finite input prefix** — exactly what
`emit_traps` says with a floor, but here by congruence, **needing no order**
(`%` over `ℕ`, divisibility, `omega`). `radixDepth` is the p-adic *emission
latency*. The necessity theorem is the sharp converse: emit *only* when pinned.

> **Validated (scratch, Demo B):** output Hensel digit `aᵢ` of a homographic map
> over `ℤ₅` freezes exactly when the input is known `mod 5^{i+1}` — the linear
> pinning `residue_depends_on_prefix` predicts.

**The valuation leg.** `NumberTheory/Valuations` + `FactorizationLens` (✅):
```
padicValuation p n := padicValNat p n                       -- v_p on ℕ (wraps Mathlib)
valuationVector P hP n : P → ℕ                               -- (v_p(n))_{p∈P}
smoothPart P hP n, freePart P hP n                          -- n = u_P · s_P  (factorization lens)
factorization_unique : n = freePart · smoothPart            -- ✅
multiplicativeSigmaAlgebra P hP E                           -- valuation σ-algebra (the mult. filtration)
divisibilityProjector, exactValuationProjector             -- Π_{p^e}, Π_{p,=e}
```
These give the **integer** valuation data the machine needs (no real `|·|_p`), and
`freePart`/`smoothPart` is the "isolate the places in `P`" handle for `S`-adelic
work (`05`, M2; `04` product-formula check).

---

## 3. The order-dependence map (the decisive table)

For each engine component: does it need an order (hence fail over `ℚ_p`)? Read
from source.

| component | module | needs order? | transfers to `ℚ_p`? |
|---|---|---|---|
| `RemainderState`, `step`, `emit`, `det`, `gauge`, `bracket_invariant` | SubshiftWeight / HomographicCarry | **no** (pure ℤ) | ✅ yes |
| `BihTensor`, `absorbX/Y`, `emit`, channel commutations | Bihomographic | **no** (pure ℤ) | ✅ yes |
| `emitDigit = a.fdiv e` (floor) | Bihomographic | **yes** (floor is an order op) | ✗ replace w/ residue |
| `emitReady` (the Bool, 4-corner inequalities) | Bihomographic | **yes** (`<`, `≤`) | ✗ replace w/ congruence |
| `emit_traps`, `emitReady_traps`, `bilinear_ge_const` | BihomographicSound | **yes** `[IsStrictOrderedRing K]` | ✗ replace w/ §2 certificate |
| `run`, `coupleAll`, `coupleTree`, `pairUp` | Driver / HyperGosper | **no** (list/tree recursion) | ✅ yes (w/ new readiness) |
| `cfDist`, `gaugeAt`, `ball_eq_cylinder` | SubshiftMetric | **yes** (`ℝ`, Archimedean limit) | ✗ p-adic metric instead |
| `cfOverflowRate` (`ℚ`), `_pos/_antitone` | CarryFrequency | mild (`ℚ` order) | partial |
| `residue_depends_on_prefix` + cylinder-union thms | CylinderMeasurability | **no** (ℕ `%`, `∣`) | ✅ yes — *this is the p-adic cert* |
| `padicValuation`, `valuationVector`, `freePart` | Valuations / FactorizationLens | **no** | ✅ yes |

**The seam, stated once.** The engine is `ℤ`-algebra (transfers); the *digit
rule* and *readiness certificate* are place-specific (`⌊·⌋`+order-trap at `∞`;
residue+congruence at `p`). The build (`03`, `05`) factors the engine so the
certificate is a parameter, not a hard-coded floor.

---

## 4. `ℤ_p` for free: completed space, odometer, metric

```
def CompletedSpace (b : RadixSeq) := (i : ℕ) → Fin (b i)         -- Core/Infinite/DirectLimit.lean ✅
tickCompleted b : CompletedSpace b → CompletedSpace b            -- Topology/Dynamics/Odometer.lean ✅
  (continuous, injective, aperiodic, minimal — all proven)
cylinderAlgebra b L ; filtration_generates_borel                -- Topology/Filtration ✅
prefixWeight ω s = ∏ radix  (= pᴸ for constant p)                -- PrefixWeights/Definition.lean ✅
```

With constant base `p` (legal: `RadixSeq` requires `b i ≥ 2`), `CompletedSpace`
is `ℤ_p` as a profinite set, `tickCompleted` is `+1` in `ℤ_p`, the cylinder
metric is `|·|_p` (`01` §3–4). **The additive/odometer/metric structure of the
p-adic integers is already in the corpus**; only the multiplicative field
arithmetic of `ℚ_p` is absent (📐 Mathlib).

---

## 5. The coupling fabric — present, but mind what kind

Three corpus subsystems offer coupling, each at a different level of substance.

**(a) `Integration/ThreeLineMediator/` — incommensurable-timeline coupling.** ✅
```
structure ObserverLine where radix : RadixSeq
structure LineMediator (A B) where
  toA toB fromAB … ; placeValue_factor ; overflow_factor          -- R̂_C ≅ R̂_A × R̂_B
def productMediator (A B) : LineMediator A B                       -- product radix instance
overflowRate b L := 1 / placeValue b L  (ℚ)
overflowRate_product : overflowRate (productRadix b₁ b₂) L = overflowRate b₁ L * overflowRate b₂ L
CoupledSystem ; Coupling (latency) ; InstantiationMode {preInitialized, manifestOnOverflow}
tickDigit … : null slot ↦ (some 0, false)  -- "manifestation absorbs carry"
```
This is the corpus's notion of coupling *incommensurable* lines without a common
clock — the right *philosophy* for places. **But its product law is fixed-radix
and does not carry the generated/CF gauge** (handoff anti-confab; `fdrs.md`
§13.4: "`overflowRate_product` has **no analogue** here"). So `productMediator`
mediates *radix sizes*, not *places*; it is a structural ancestor, not the adelic
coupler. The handoff's open frontier #3 ("give `ObserverLine` its own
metric/valuation identity and mediate *those*") is precisely the gap to the
adelic axis.

**(b) `Composition/` — routing topology (38 files, ~3.9k lines).** 🟡 BUILT-THIN
```
inductive Event | TICK | OVERFLOW (timeline)(cylPrefix) | INJECT (…)(payload : ℕ)
routingFunction … : List (ℕ × List ℕ × ℕ)        -- NB: ignores source/prefix args
inductive TransferType | TOTAL | PARTIAL | COPY | SPAWN | TERMINATE
applyTransfer : TransferType → ℕ → ℕ → ℕ × ℕ      -- payload is ℕ
TimelineGraph ; Path ; isAcyclic ; StrictTimelineGraph ; deadlock-freedom ; timing bounds
```
This *exists in Lean* (contradicting the handoff's "spec-prose" framing of
Phase 8) but is **payload-agnostic**: it routes `ℕ`, proves acyclicity ⟹
deadlock-freedom and compile-time timing bounds. **Leverage:** it supplies the
coupling *topology* (who routes to whom, well-formedness) — but **not** the
coupling *arithmetic*. For the adelic complex it is the wiring harness, not the
conserved-quantity law.

**(c) `Modes/BaseZeroSea/` — floor-free carry dynamics.** ✅
```
Sea ; SeaState ; seaTick ; instantiate ; revert ; LegacyThread
LinearChain ; linearChainStep ; chainToCylinder
linearChain_projectsTo_odometer    -- the strengthened Theorem 64 (chain ↦ Phase-9 odometer)
unifiedSpatialTick ; carryRouteDecision ; classifyCarry           -- carry = OVERFLOW route (Thm 61)
CoupledDigitNetwork                 -- abstract module graph (no dynamic digit state)
```
The base-0 wall / base-1 wire / occupancy model is the corpus's **floor-free
emission** mechanism (handoff §1, frontier #2). `carryRouteDecision`/
`classifyCarry` already unify "arithmetic carry" with "OVERFLOW routing." This is
the natural substrate for the p-adic place's *carry-up* (Hensel digits carry
toward higher powers of `p`), and `CoupledDigitNetwork` is the abstract shell the
"radix complex as verified machine" goal (memory) wants to give an operational
semantics. The §9.6 `instantiate` trigger is a STUB (📜) — the slot for a
coupling-driven emission rule.

---

## 6. Measure & filtration infrastructure (for the Axis-II / statistical layer)

```
uniformProductMeasure b := Measure.infinitePi (digitMeasure b)    -- ProductMeasure.lean ✅
cylinder_measure : μ (cylinder b L s) = (placeValue b L)⁻¹        -- = p^{-L} for constant p
integral_blockConstant                                            -- ∫_cylinder f = block average
-- Parry side (golden-mean shift), SubshiftParry.lean ✅:
goldenP ; goldenKernel (IsMarkovKernel) ; goldenStat (stationary) ; parryMeasure (Ionescu–Tulcea)
parry_condExp_tendsto                                             -- Lévy upward "Group G"
cylinderAlgebra ; filtration_generates_borel ; metricDominance
```
For constant base `p`, `uniformProductMeasure` is **Haar measure on `ℤ_p`** and
`cylinder_measure` gives `μ(ball of radius p^{-L}) = p^{-L}` — the p-adic Haar
normalization. This is the measure-theoretic anchor if the complex later needs an
adelic measure (Tate-style), but it is **not** needed for the exact-arithmetic
core (M0–M2).

---

## 7. Mathlib leverage (import, don't rebuild)

The toolchain is `lean4 v4.27.0-rc1` + Mathlib master. Available (📐):

| Mathlib object | gives | use in build |
|---|---|---|
| `Padic p` (= `ℚ_p`), `PadicInt p` (= `ℤ_p`) | the p-adic field/ring | **soundness target** for the p-adic certificate (like `ℝ`/`K` for `emit_traps`) |
| `padicValRat`, `padicNorm` | `v_p`, `\|·\|_p` on `ℚ` | product-formula statement (`04`, M4) |
| `Valuation`, `Valued`, `AddValuation` | abstract (non-Arch.) valuations | the typeclass the p-adic `emit_traps`-analogue is stated over |
| `IsDedekindDomain.HeightOneSpectrum` | "all finite places" uniformly | L3 restricted-product encoding |
| `NumberField.AdeleRing`, `DedekindDomain.FiniteAdeleRing` | `𝔸_ℚ`, finite adeles | M3/M4 *only if* needed; heavy (topology/measure) |

**Decision (recorded for the builder):** import `PadicInt`/`Padic` and `Valued`
as **semantic targets** for soundness statements; keep the engine in `ℤ`. Defer
`AdeleRing` to M3+, and only if a theorem genuinely needs the restricted-product
object rather than a finite-`S` identity.

---

## 8. Built / thin / absent — the one-screen map

- **✅ Reusable as-is:** the whole Gosper engine *algebra* (ledger, tensor,
  scheduler, hyper-tree); `residue_depends_on_prefix` + cylinder-union theorems
  (the p-adic certificate); `padicValuation`/`valuationVector`/`freePart`;
  `CompletedSpace`+`tickCompleted`+`cylinderAlgebra` (= `ℤ_p` additively);
  `uniformProductMeasure`/`cylinder_measure` (= Haar on `ℤ_p`); BaseZeroSea
  floor-free carry.
- **✅ Reusable but Archimedean (do not transfer):** `emit_traps`,
  `emitReady_traps`, `bilinear_ge_const`, `cfDist`/`gaugeAt` (these stay at `∞`).
- **🟡 Thin / topology-only:** `Composition/` routing (wiring harness, payload-`ℕ`);
  `productMediator` (radix sizes, not places); `CoupledDigitNetwork` (no dynamics).
- **📐 Import from Mathlib:** `ℚ_p`/`ℤ_p` field arithmetic, abstract valuations,
  height-one spectrum, the adele ring.
- **🔨 To build (the actual machine):** the p-adic emission certificate *as an
  `emit_traps`-shaped theorem*; the place-parametric engine; the two-place complex;
  the Axis-II product-formula invariant; the restricted-product encoding.

Next: [`03-architecture.md`](03-architecture.md) — how these assemble into a
machine.
