# 01 — Mathematical Background

*The classical objects the adelic complex stands on. All of this is standard
number theory (Ostrowski, Hensel, Tate's thesis, Weil); none of it is novel and
none is claimed to be. The point of this file is to fix notation and, for each
classical object, name its **existing FDRS counterpart** so the build (`05`) knows
what to reuse vs. import vs. write.*

References (classical, for the builder): Gouvêa, *p-adic Numbers*; Cassels,
*Local Fields*; Ramakrishnan–Valenza, *Fourier Analysis on Number Fields*; Khinchin,
*Continued Fractions*. Mathlib: `Mathlib.NumberTheory.Padics.*`,
`Mathlib.RingTheory.Valuation.*`, `Mathlib.NumberTheory.NumberField.AdeleRing`.

---

## 1. Places and absolute values of `ℚ`

A **place** of `ℚ` is an equivalence class of nontrivial absolute values. By
**Ostrowski's theorem** these are exactly:

- the **Archimedean place** `∞`, given by the ordinary absolute value `|x|_∞`;
- one **non-Archimedean place** per prime `p`, given by the **p-adic absolute
  value** `|x|_p := p^{−v_p(x)}`, where `v_p(x)` is the p-adic valuation
  (the exponent of `p` in `x`, with `v_p(0) = +∞`).

Write `V = {∞} ∪ {primes}`. Non-Archimedean means the **strong triangle
inequality** `|x+y|_p ≤ max(|x|_p,|y|_p)` — the ultrametric.

> **FDRS counterpart.** `v_p` is `padicValuation` (✅, `NumberTheory/Valuations`,
> wrapping Mathlib `padicValNat`); the valuation *vector* over a finite prime set
> `P` is `valuationVector` (✅, `FactorizationLens`). The absolute values
> `|·|_p` themselves are **not** in FDRS as such (📐 Mathlib `padicValRat` /
> `Padic` norm) — but the machine never needs the real number `|x|_p`; it needs
> the **integer** `v_p(x)`, which it has.

---

## 2. The product formula — the conserved coupling law

For every `x ∈ ℚ*`,

```
        ∏_{v ∈ V} |x|_v  =  |x|_∞ · ∏_p p^{−v_p(x)}  =  1.
```

Only finitely many factors differ from `1` (the primes dividing the numerator or
denominator), so the product is finite and well-defined. The formula is the
**global rigidity** of `ℚ`: the Archimedean "size" of `x` is exactly cancelled by
its non-Archimedean valuations. It is the reason the places are not independent —
it is the literal arithmetic coupling between "separate adelic positions."

This is the **Axis-II conserved invariant** (`00` §2). Its status as the
*machine's* invariant is the open problem of `04`; its status as a *theorem of
number theory* is settled and classical.

> **Validated (scratch, Demo A):** `∏_v |x|_v = 1` holds exactly on every sample
> rational, computed with `fractions.Fraction` (no floats). E.g.
> `x = 12/35`: `|x|_∞ = 12/35, |x|_2 = 1/4, |x|_3 = 1/3, |x|_5 = 5, |x|_7 = 7`,
> product `= 1`.

> **FDRS counterpart.** None yet (🔨). But `freePart`/`smoothPart`
> (✅, `FactorizationLens`) give the canonical `x = u_P · s_P` split that isolates
> "the places in `P`" from "the places outside `P`," which is the natural handle
> for an `S`-adelic product-formula check (`05`, M2).

---

## 3. p-adic integers `ℤ_p`, Hensel digits, and the FDRS completed space

`ℤ_p` is the ring of p-adic integers: `x ∈ ℤ_p ⟺ v_p(x) ≥ 0`. Every `x ∈ ℤ_p`
has a unique **Hensel expansion**

```
        x  =  Σ_{i ≥ 0} a_i p^i ,        a_i ∈ {0, 1, …, p−1},
```

and the digit `a_i` is determined by the **congruence** `x ≡ Σ_{j≤i} a_j p^j
(mod p^{i+1})`. `ℤ_p = lim_n ℤ/pⁿℤ` (the inverse limit / profinite completion);
`ℚ_p = Frac(ℤ_p)` allows finitely many negative-power digits.

This is exactly the FDRS completed space with **constant base `p`**:

> **FDRS counterpart (a clean identity).** `CompletedSpace b := (i:ℕ) → Fin (b i)`
> (✅, `Core/Infinite/DirectLimit.lean`). With `b ≡ p` (a constant `RadixSeq`,
> legal since `p ≥ 2`), a point is a digit sequence `(a_0,a_1,…) ∈ {0,…,p−1}^ℕ`
> — **this is `ℤ_p` as a profinite set.** The FDRS odometer `tickCompleted`
> (✅, `Topology/Dynamics/Odometer.lean`) is `+1` in `ℤ_p`; the cylinder filtration
> `cylinderAlgebra` (✅, `Topology/Filtration`) is the tower `ℤ/pⁿℤ`. So the
> *additive/digit* structure of `ℤ_p` is **already present** as a special case;
> what is *not* present is the **ring/field arithmetic** of `ℚ_p` (📐 Mathlib
> `PadicInt p`, `Padic p`).

The Hensel-digit emission rule "`a_i` is fixed by `x mod p^{i+1}`" is the engine's
floor-free emission: see `02` §4 and `03` §3.

---

## 4. The two ultrametrics — a subtlety the builder must not blur

FDRS carries **two** different ultrametrics, and only one of them is p-adic. This
distinction (flagged in the handoff §2: *"NB: this ultrametric is the CF/symbolic
one, not a p-adic valuation"*) decides which engine each place uses.

**(a) The p-adic / fixed-base metric.** On `CompletedSpace` with constant base
`p`: `δ(x,y) = β(lcp)⁻¹ = p^{−L}` where `L` is the first index where the digit
sequences differ. For `x,y ∈ ℤ_p`, `v_p(x−y) = L`, so

```
        δ(x,y) = p^{−L} = |x − y|_p.
```

**This is genuinely the p-adic metric.** (FDRS: the cylinder ultrametric of
Phase 1/6 with `β = ∏ radix = pᴸ`.)

**(b) The continued-fraction / symbolic metric.** On admissible CF sequences
`x : ℕ → ℕ` (partial quotients `≥ 1`): `cfDist x y = 1/q_ℓ` where `q_ℓ` is the
convergent **denominator** at the longest common prefix (✅, `cfDist`,
`SubshiftMetric.lean`). The gauge `q_ℓ` grows at the Perron rate (Fibonacci for
`φ`), **not** as a base power. This is the symbolic coding of the *irrationals*
via the Gauss map — the homeomorphism `irrationals ≅ ℕ^ℕ` — **not** a p-adic
valuation.

**Consequence for the design.** The Archimedean place uses metric (b) (the CF
gauge `q_n`, the Gosper engine). Each p-adic place uses metric (a) (the base-`p`
gauge `pⁿ`, a *simpler*, genuinely p-adic odometer). They are different gauges,
so the per-place engines are different — which is *why* the product law of the
fixed-radix mediator does **not** carry the CF combination (handoff §13.4
anti-confab) and why the adelic coupling cannot be "just multiply place values."

---

## 5. Continued fractions at `∞` (the existing engine, for contrast)

A real `x > 0` has a regular continued fraction `x = [a_0; a_1, a_2, …]`,
`a_i = ⌊x_i⌋` (an **order** decision), `x_{i+1} = 1/(x_i − a_i)`. Convergents
`p_n/q_n` come from the `SL₂(ℤ)` recurrence `(p_n,q_n) = a_n(p_{n−1},q_{n−1}) +
(p_{n−2},q_{n−2})`, and `|p_n q_{n−1} − p_{n−1} q_n| = 1` (the bracket invariant).

> **FDRS counterpart (all ✅).** `RemainderState` (the `(p_{k−1},p_k;q_{k−1},q_k)`
> ledger), `step` (absorb a quotient), `emit` (the homographic dual),
> `bracket_invariant` (`|det|=1`), `gauge = q_k`, `steps_qCur_unbounded`
> (`q_k → ∞` even for `φ`). The two-input version is `BihTensor` with the
> four-corner `emit_traps`. This is the **template** the p-adic engine mirrors,
> with the floor swapped for a residue and the order trap swapped for a congruence.

---

## 6. The adele ring (the target object, stated honestly)

The (rational) adele ring is the **restricted product**

```
        𝔸_ℚ  =  ℝ ×' ∏_p ℚ_p
              =  { (x_v)_v : x_p ∈ ℤ_p for all but finitely many p }.
```

`ℚ` embeds diagonally (`x ↦ (x,x,x,…)`), and the product formula says this
diagonal copy lands in the norm-1 locus. **Tate's thesis** does harmonic analysis
here; **Strong Approximation** and **Artin reciprocity** are the deep coupling
theorems. The machine does **not** aim to formalize Tate's thesis — it aims to be
a *computational, exact, coupled representation* of elements and their places, with
the product formula as its conservation law.

> **Honest note.** `Mathlib.NumberTheory.NumberField.AdeleRing` and
> `DedekindDomain.FiniteAdeleRing` (📐) define `𝔸` and the finite adeles for number
> fields (`ℚ` included). These carry topology and (for harmonic analysis) measure.
> The adelic complex deliberately does **not** start from these heavy objects: per
> the no-floats discipline (`00` §4) it stays in exact integer ledgers and digit
> streams, using `ℚ_p`/`𝔸` only as *semantic targets* for soundness, exactly as the
> Gosper engine uses `ℝ` only inside `emit_traps`. Whether to import the Mathlib
> adele ring at all is an M3/M4 decision (`05`), not an M0 one.

---

## 7. Dictionary (classical ↔ FDRS)

| classical object | FDRS counterpart | tag |
|---|---|---|
| `v_p(n)` (p-adic valuation) | `padicValuation` / `valuationVector` | ✅ |
| `\|x\|_p = p^{−v_p}` | (integer `v_p` used instead; real abs not needed) | ✅ / 📐 |
| product formula `∏\|x\|_v=1` | — (built on `freePart`/`smoothPart` split) | 🔨 |
| `ℤ_p` (profinite set + odometer) | `CompletedSpace (const p)` + `tickCompleted` | ✅ |
| Hensel digit forced by `x mod p^{i+1}` | `residue_depends_on_prefix` | ✅ |
| `ℤ_p`/`ℚ_p` ring/field arithmetic | (not in FDRS) | 📐 Mathlib `PadicInt`/`Padic` |
| p-adic metric `\|x−y\|_p` | cylinder metric `β=pᴸ` (Phase 1/6) | ✅ |
| CF expansion at `∞`, `SL₂(ℤ)` ledger | `RemainderState`/`step`/`emit`/`BihTensor` | ✅ |
| CF gauge `q_n` (≠ p-adic) | `gauge`/`gaugeAt`/`cfDist` | ✅ |
| adele ring `𝔸_ℚ` (restricted product) | (semantic target; not built) | 📐 / 🔨 |

Next: [`02-corpus-leverage.md`](02-corpus-leverage.md) — the exact tools, with the
order-dependence map that decides what transfers to `ℚ_p`.
