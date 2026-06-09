# 03 — Architecture

*The machine, concretely enough to build. Places are nodes; a quantity is a family
of exact digit streams; emission is certificate-parametric (order-trap at `∞`,
congruence-trap at `p`); the product formula is the cross-place conserved quantity.
Tags per README. The genuinely new obligations are flagged 🔨 (build) / 🔬
(conjecture) and gathered in `04`/`06`.*

---

## 1. The object

A quantity `x ∈ ℚ` (eventually `ℚ̄`/algebraic, or an exact-real/`ℚ_p` limit of one)
is represented by an **adelic configuration**:

```
  AdelicConfig x = {
    support S  : Finset Place           -- the active places: {∞} ∪ {finitely many p}
    perPlace   : (v ∈ S) → PlaceState v -- one exact ledger + digit stream per place
    invariant  : ProductFormulaResidual -- the Axis-II coupling datum (§6)
  }
```

This is an instance of the abstract `CoupledDigitNetwork` (✅ shell,
`BaseZeroSea/Modules.lean`) whose **nodes are places** and whose missing
operational semantics (`Config + step + value`, the memory's "radix complex as a
verified machine" goal) is supplied here, place-aware. There is **no global
clock**: places advance independently (`00` §4), legitimized by the channel
commutations (`emit_*_comm`, ✅) — scheduling order is irrelevant to the result.

---

## 2. The per-place engine is certificate-parametric

Both place kinds run *the same integer ledger algebra* (✅, `02` §1/§3) and differ
only in the **digit rule** and **readiness certificate**. Factor the engine so the
certificate is a parameter:

```
  class PlaceEngine (v : Place) (K : Type) where      -- K = soundness target: ℝ at ∞, ℚ_p at p
    Ledger    : Type                                   -- ℤ-tuple (RemainderState / BihTensor / p-adic ledger)
    absorb    : InDigit v → Ledger → Ledger            -- read one input digit (pure ℤ)
    emit      : OutDigit v → Ledger → Ledger           -- write one output digit (pure ℤ)
    candidate : Ledger → OutDigit v                     -- the proposed next digit
    ready     : Ledger → Bool                           -- decidable, pure ℤ (no K, no order)
    -- the certificate (the only place-specific theorem):
    sound     : ready L = true → ∀ tail, value_K L tail ∈ digitCell v (candidate L)
```

- At `∞`: `Ledger = BihTensor`, `candidate = a.fdiv e`, `ready = emitReady`,
  `sound = emitReady_traps` (`K = ℝ`/ordered ring). **All ✅ today.**
- At `p`: `Ledger` = p-adic homographic ledger, `candidate` = residue digit,
  `ready` = congruence check, `sound` = the p-adic dual of `emit_traps`
  (`K = ℚ_p`). **The ledger algebra is ✅; `candidate`/`ready`/`sound` are 🔨,
  built on the ✅ keystone `residue_depends_on_prefix` (§3).**

The scheduler (`run`, `coupleAll`, ✅) and the hyper-tree are *engine-generic*:
they call `ready`/`candidate`/`emit`/`absorb` and never touch order. So they
work at any place once the engine instance is supplied. This factoring is the
first concrete build step (`05`, M0-refactor).

---

## 3. The p-adic place engine in detail (emit without a floor)

This is the heart of the "second place." It is *not* a port of the floor engine;
it is the congruence dual, and it differs in three honest ways.

**(a) Recurrence: shift, not inversion.** A Hensel read is `x = α + p·x'`
(`α ∈ {0,…,p−1}`, `x' ∈ ℤ_p`), so for `y = (a x + b)/(c x + d)`:
```
  absorb α :  [[a,b],[c,d]] ↦ [[a·p, a·α+b],[c·p, c·α+d]]    -- right-mult by [[p,α],[0,1]]
  emit   β :  [[a,b],[c,d]] ↦ [[a−β·c, b−β·d],[c·p, d·p]]    -- y' = (y−β)/p
```
Pure `ℤ`, no order. (Contrast the CF read `x = a + 1/x'`, `[[a,1],[1,0]]`,
inversion.)

**(b) Within-place invariant: a p-power det, not `|det|=1`.** Each `absorb`/`emit`
multiplies `det` by `p` (computed above: `det ↦ p·det`). So the p-adic ledger is
**not** `SL₂(ℤ)`; instead `v_p(det) = (#digits processed)` and `det = ±pᵏ·det₀`.
The exactness invariant of the `∞` place (`|det|=1`) is replaced by **valuation
tracking** `v_p(det) = k`. This is a small, concrete build item (🔨) — the p-adic
analogue of `bracket_invariant`, proved by the same `det_step`-style induction
(the corpus's `det_step`/`det_steps` are the template, ✅). *It is not the hard
open problem* — that is Axis II (`04`).

**(c) Readiness & soundness: congruence, not order.** The output digit
`β = a_0(y)` is *forced* iff, regardless of the unread input tail `x' ∈ ℤ_p`, the
value `y mod p` is the same. Operationally:

- the denominator must be a p-adic **unit** on the *entire* tail-disk — **not**
  merely "the current denominator is nonzero mod `p`." This needs its own named
  lemma (🔨), because `c x + d` ranges over `d + c·ℤ_p` as the tail varies:

  > `denom_unit_on_disk` (🔨): `c·x + d ∈ ℤ_p^×` for **all** `x ∈ ℤ_p`
  > `⟺ c ≡ 0 (mod p) ∧ d ≢ 0 (mod p)` (then `c x + d ≡ d`, a unit, for every tail).
  > If instead `c ≢ 0 (mod p)`, there is a tail residue `x ≡ −d/c` where the
  > denominator hits the maximal ideal (a **pole on the disk**): `ready` must
  > return `false` and the engine must **refine the disk** (absorb another input
  > digit, splitting `ℤ_p` into its `p` sub-disks and re-testing) rather than emit.

  This pole-refinement branch is the p-adic counterpart of the Archimedean engine
  *withholding* a digit at a boundary (the `√2·√2=2 → []` behavior); it must be an
  explicit case, not an assumption.
- given a unit denominator on the disk, the residue `(a x + b)/(c x + d) mod p`
  must be **constant** across the `p` residue-classes of the tail (the **`p`
  congruence-corners**, the non-Archimedean analogue of the two order-endpoints
  `{1,∞}`).

`ready` is then a finite list of **divisibility/congruence** conditions over `ℤ`
(decidable, `omega`/`decide`; no `<`, no floor) — gated on `denom_unit_on_disk`.
The soundness theorem to prove:

```
  -- the p-adic emit_traps (🔨, target shape):
  theorem padic_emit_traps {K} [Field K] [Valued K Γ] (L : Ledger) (β)
      (cong : <the corner congruence conditions on L's ℤ entries hold mod p>) :
      ∀ x : 𝒪_K, value K L x ≡ β  (mod 𝔪)        -- y ≡ β in the residue field
```

stated over a discretely-valued field `K` (the 📐 Mathlib `Valued`/`Padic` target),
exactly as `emit_traps` is stated over `[IsStrictOrderedRing K]`. **Its
combinatorial core is already proven**: "the residue is fixed by a finite prefix"
is `residue_depends_on_prefix` / `congruenceSet_is_cylinder_union` (✅, `02` §2),
and the sharp converse `congruenceSet_not_cylinder_union_of_not_dvd` (✅) is the
"do not emit early" guarantee. So `padic_emit_traps` is a *wiring* of an existing
axiom-clean theorem to the ledger, not a new hard proof.

> **Validated (scratch, Demo B):** for `y=(3x+2)/(5x+1)` over `ℤ₅` (unit
> denominator), digit `aᵢ(y)` is forced once the input is known `mod 5^{i+1}` —
> the finite-prefix pinning, no order used.

**(d) The two-input p-adic tensor (Axis I at `p`).** The bihomographic tensor
generalizes: `BihTensor` algebra is pure `ℤ` (✅, transfers), and the four
order-corners `{1,∞}²` become **`p²` congruence-corners** (`(x mod p, y mod p) ∈
(ℤ/p)²`). `ready` checks the candidate digit agrees across those `p²` corners with
unit denominators; soundness is the bilinear congruence analogue of
`bilinear_ge_const` (🔬/🔨 — a divisibility identity, not an order inequality).
This is the precise non-Archimedean restatement of the handoff's frontier #1.

---

## 4. The emission table (the design in one screen)

| | Archimedean `∞` | p-adic `p` |
|---|---|---|
| ledger | `RemainderState` / `BihTensor` (✅) | same `ℤ`-tuple shape; shift recurrence (🔨) |
| read | `x = a + 1/x'`, `[[a,1],[1,0]]`, inversion (✅) | `x = α + p·x'`, `[[p,α],[0,1]]`, shift (🔨) |
| within-place invariant | `\|det\|=1` (`bracket_invariant`, ✅) | `v_p(det)=#steps` (🔨, via `det_step` template) |
| digit `candidate` | `⌊N/D⌋` = `a.fdiv e` (order) | `N/D mod p` (residue; needs `v_p(D)=0`) |
| `ready` (decidable, pure ℤ) | 4-corner **inequalities** `emitReady` (✅) | `p`-corner **congruences** + unit denom (🔨) |
| `sound` | `emit_traps`, `[IsStrictOrderedRing K]` (✅) | `padic_emit_traps`, `[Valued K]`; core = `residue_depends_on_prefix` (✅→wire 🔨) |
| gauge | CF denominator `q_n` (`gaugeAt`, ✅) | `pⁿ` / valuation (`placeValue` const-`p`, ✅) |
| metric | `cfDist = 1/q_ℓ` (✅, `ℝ`) | `\|·\|_p = p^{−L}` cylinder metric (✅) |
| floor-free? | no (floor *is* the rule) | **yes** — congruence/carry-up (BaseZeroSea, ✅) |

The whole machine is "emit only when `ready`, certified by `sound`" — one
abstraction, two instances. *That unification is the artifact.*

---

## 5. State format and one step

```
  PlaceState v = {
    ledger   : Ledger v          -- ℤ-tuple
    emitted  : List (OutDigit v) -- the exact output stream so far  (CF quotients / Hensel digits)
    pending  : List (InDigit v)  -- buffered input digits not yet absorbed
    gauge    : ℕ                 -- q_n at ∞ ; p^n at p   (precision / place value)
  }

  step (cfg : AdelicConfig x) (v : Place) : AdelicConfig x :=
    let s := cfg.perPlace v
    if PlaceEngine.ready s.ledger then
      -- EMIT: append certified digit, advance ledger; update product-formula residual (§6)
      let β := PlaceEngine.candidate s.ledger
      cfg.update v { s with emitted := s.emitted ++ [β],
                            ledger  := PlaceEngine.emit β s.ledger,
                            gauge   := bump v s.gauge }
          |>.recordEmission v β              -- Axis-II bookkeeping
    else
      -- ABSORB: pull one input digit for this place
      match s.pending with
      | d :: ds => cfg.update v { s with pending := ds,
                                         ledger  := PlaceEngine.absorb d s.ledger }
      | []      => cfg                       -- this place starves; scheduler picks another
```

- **Scheduling is free — formalized as confluence, not hand-waved.** Pick any `v`
  each step (round-robin, demand-driven, fuel-bounded). The precise claim is a
  **local diamond / confluence lemma** (🔨): for distinct places `v ≠ w`,
  `step v ∘ step w = step w ∘ step v` (steps at different places commute, since
  they touch disjoint `perPlace` slots and a step never reads another place's
  state). Its *core* — that absorb/emit at one place commute — is the channel
  commutations `emit_absorbX_comm`/`absorbX_absorbY_comm` (✅), lifted to `step`.
  From the diamond, the downstream theorem (🔨) is: **any two fair schedules
  produce equal emitted streams** (per place, prefix-equal up to fuel). This — not
  a vague "order-independence" — is the "no coerced common clock": places are
  incommensurable timelines (`ThreeLineMediator` philosophy, ✅) advanced
  asynchronously, with confluence guaranteeing determinacy of the result.
- **Everything stays exact.** `ledger` is `ℤ`; `emitted` is a list of integers;
  `gauge` is `ℕ`. No float, no `ℚ_p` element materialized — only emitted *digits*.

---

## 6. The coupling fabric

**Axis I (combine, within a place).** Use the (place-appropriate) bihomographic
tensor: at `∞`, `addTensor`/`mulTensor` + `coupleAll` (✅); at `p`, the `p²`-corner
tensor (🔨, §3d). This composes streams *inside* one place. The hyper-tree
(`coupleTree`, ✅) is engine-generic, so it scales Axis I at any place once the
p-adic engine instance exists.

**Axis II (couple across places — the adelic axis).** Two layers:

1. **Topology (✅, reuse `Composition/`).** Which places route to which, and the
   well-formedness guarantees (acyclic ⟹ deadlock-free, finite latency,
   compile-time timing). `Composition/`'s `Event`/`TransferType`/`TimelineGraph`
   is the wiring harness — payload-agnostic, so it carries *digit streams* between
   place-nodes without caring about their arithmetic. This is exactly what we need
   it for: structure, not law.
2. **Law (🔬, the new math — `04`).** The conserved quantity tying `x`'s positions
   together: the **product formula** `∏_v |x|_v = 1`. `recordEmission` maintains a
   `ProductFormulaResidual` held in a **symbolic exponent representation** — never
   real logarithms (that would violate NF1, `log p ∉ ℚ`):
   ```
   structure ProductFormulaResidual where
     archNum  : ℤ                 -- the Archimedean magnitude, exact rational …
     archDen  : ℕ                 -- … as a num/den pair (from the identified value, not a float)
     vExp     : Prime →₀ ℤ        -- finitely-supported p-adic valuations  v_p(x)
   ```
   The product formula is then the **factorization identity**
   `archNum/archDen = ∏_p p^{−vExp p}` (up to sign), proved by unique factorization,
   **not** by comparing reals. Logarithms appear **only** in an optional *semantic
   interpretation* theorem (`Σ_p vExp(p)·log p = log(archDen/archNum)`), never as
   the machine's stored value. Whether this residual is *conserved step-to-step*
   (vs. only checkable once the value is identified) is the open problem — and it
   splits into an **exact** identity from the identified value and a **bounded**
   residual from a finite prefix (`04` §3.3–§4; `05` M4a/M4b).

The honest split: **Axis-II topology is reusable today; Axis-II law is the
research frontier.** The machine can be *built and run* (exact streams, correct
per-place emissions) before the Axis-II law theorem exists — it just wouldn't yet
*certify* cross-place consistency. That is the L1→L4 ladder (`00` §5).

---

## 7. No-floats invariants (machine-checkable hygiene)

Properties the build should state and keep (each a cheap Lean lemma, the discipline
made executable):

- **(NF1)** every `Ledger` value is a tuple of `ℤ`; no `Real`/`Padic` *value* ever
  appears in `absorb`/`emit`/`candidate`/`ready` (only in `sound`'s statement).
- **(NF2)** `emitted` streams are `List ℤ` (CF quotients) / `List (Fin p)` (Hensel
  digits); a place's *value* is only ever its stream, never a materialized
  element of `ℝ`/`ℚ_p`.
- **(NF3)** no step references a global tick: `step` takes an explicit `v : Place`;
  there is no shared counter all places increment.

(NF1–NF3) are the formal content of "no floats / no clock coercion." They mirror
how the corpus already keeps `ℝ` out of the `∞` engine (✅).

---

## 8. The picture

```
                      AdelicConfig x   (a CoupledDigitNetwork; nodes = places)
   ┌───────────────┬───────────────────────────┬───────────────────────────┐
   │   place ∞     │        place p₁           │        place p₂   …        │
   │  CF / Gosper  │   p-adic homographic      │   p-adic homographic       │
   │  BihTensor    │   (shift recurrence)      │                            │
   │  ⌊·⌋ + order  │   residue + congruence    │                            │
   │  emit_traps ✅│   padic_emit_traps 🔨     │                            │
   │  gauge q_n    │   gauge pⁿ                │                            │
   └──────┬────────┴──────────┬────────────────┴───────────┬───────────────┘
          │ emitted CF stream │ emitted Hensel stream       │  (exact ℤ digits)
          ▼                   ▼                             ▼
   ╔═══════════════════════════════════════════════════════════════════════╗
   ║  Axis-II coupling:  routing topology (Composition/, ✅, payload-agnostic) ║
   ║                     + product-formula invariant  ∏_v |x|_v = 1  (🔬, 04) ║
   ╚═══════════════════════════════════════════════════════════════════════╝
                         exact integers throughout — no float, no global clock
```

Next: [`04-coupling-invariant.md`](04-coupling-invariant.md) — the open math that
the `🔬` above stands for; then [`05-build-roadmap.md`](05-build-roadmap.md) for
the staged plan.
