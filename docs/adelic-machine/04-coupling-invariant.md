# 04 — The Coupling Invariant (the real math / open problem)

*This is where the design stops being assembly and becomes research. The handoff's
open frontier #1 — "is there a `|det|=1`-style quantity conserved across coupling?
Without it, emergence from coupling is indistinguishable from noise" — is the
question this file confronts. Everything here is 🔬 unless tagged otherwise. The
job of this file is to state the conjecture **precisely**, say what is already
settled vs. genuinely unknown, and give a test plan.*

---

## 1. Three invariants, three statuses

Do not conflate these. The design needs all three; only the third is open.

| invariant | scope | status |
|---|---|---|
| **within-place exactness** | one place, one stream | ✅ (`∞`) / 🔨-easy (`p`) |
| **intra-place combination** (Axis I) | one place, two streams → one | ✅ (`∞`) / 🔬 (`p`) |
| **inter-place coupling** (Axis II) | one quantity, all places | 🔬 — *this file* |

---

## 2. Within-place exactness (settled / easy)

- At `∞`: `|det| = 1`, the bracket invariant (`bracket_invariant`, ✅). The
  `SL₂(ℤ)` ledger never rounds.
- At `p`: **not** `|det|=1`. The Hensel shift recurrence multiplies `det` by `p`
  each step (`03` §3b), so the exactness invariant is `v_p(det) = #steps`,
  i.e. `det = ±pᵏ`. Proving it is the same induction as `det_step`/`det_steps`
  (✅ template) — 🔨-easy, **not** the open problem.

So "exactness" transfers; it just wears a different face (`|det|=1` ↦ a p-power
det / valuation count). Already a small honest correction to any "it's all
`SL₂(ℤ)`" story.

---

## 3. Inter-place coupling: the product formula as adelic `|det|=1`

The conserved quantity that ties a single `x` across its positions is the
**product formula**

```
        ∏_{v} |x|_v = 1        (x ∈ ℚ*).
```

### 3.1 Why this is the right candidate (and its honest relationship to `|det|=1`)

There is a real structural rhyme — and a real difference — between `|det|=1` and
the product formula:

- `|det| = 1` says a convergent matrix is in `SL₂(ℤ)`: the *local/per-place* ledger
  is volume-preserving (a unit determinant in `ℤ`).
- `∏_v |x|_v = 1` says the *global/idelic* norm of `x` is a unit: the **idele class
  norm is 1**. In adelic `GL_n`, this is literally `|det(g)|_𝔸 = ∏_v |det(g_v)|_v`,
  and the product formula is its statement for scalars.

So both are "a determinant is a unit," one in the local ring `ℤ`, one in the idele
group. That is a genuine rhyme — the product formula *is* the adelic analogue of
`|det|=1` — but they are **not the same invariant**, and the design must not sell
them as such. (Confabulation watch: `06`.)

### 3.2 The clean axis (multiplicative) vs. the boundary (additive)

This is the sharpest honest fact about the coupling, and it decides what to build:

- **Multiplicative coupling composes locally.** For every place `v`,
  `|x·y|_v = |x|_v · |y|_v`. So the product formula is conserved under `×` *place
  by place*, and the idele norm is a homomorphism. **This is a locally-checkable,
  conserved invariant** — the strong candidate for the machine's Axis-II law.
- **Additive coupling has no local law.** `|x+y|_v` is *not* a function of `|x|_v`
  and `|y|_v` (only the bound `≤ max` at finite places, nothing at `∞`); and
  `x+y` can acquire places neither `x` nor `y` had. So the product formula of a
  *sum* is **not** computable from the summands' per-place data. This is the edge
  of the approach — strong-approximation territory.

> **Validated (scratch, Demo D):** for `x=12/35, y=−50/21`, `|xy|_v = |x|_v|y|_v`
> at every place `v ∈ {∞,2,3,5,7}` and `∏|xy| = ∏|x|·∏|y| = 1`; whereas for `x+y`
> the per-place values satisfy only the ultrametric bound and `∏|x+y|=1` is not
> reconstructible from the summands.

**Design consequence.** Target the **multiplicative / idele** axis first
(combination by `×`, `mulTensor` at each place). The idele norm is the
conserved, locally-checkable invariant. Defer additive coupling, and when it is
attempted, state plainly that no local product-formula law exists for it.

### 3.3 The finite-precision asymmetry (the actual subtlety for a machine)

A machine works with *finite prefixes* of the streams, and here the places behave
differently:

- **Non-Archimedean factors stabilize finitely.** `v_p(x)` is read off the leading
  Hensel digit position — pinned by a *finite* prefix (`residue_depends_on_prefix`,
  ✅). So `|x|_p` is *exact at finite precision*.
- **The Archimedean factor only converges.** A finite CF prefix gives a convergent
  `p_n/q_n ≈ x`, not `x` exactly; `|x|_∞` is pinned only in the limit.

So the running product `∏_v |x|_v` over finite prefixes is **not** exactly `1` at
finite precision — it converges to `1`, with the error controlled by the
Archimedean place. The honest machine invariant is therefore not "`= 1` at every
step" but a **bound**:

> **Adelic gauge bound — EMPIRICALLY CONFIRMED (📊, classical).** For `x ∈ ℚ`
> represented by the complex to CF-depth `n` (gauge `q_n`) and exact finite
> valuations, the running product satisfies `|∏_v |x|_v − 1| ≤ C / q_n`. The scratch
> probe (`scratch/gauge_bound_probe.py`) confirms it on every tested `x` with effective
> constant **`C = 1`**, in fact `Θ(1/q_n²)` (the Fibonacci/`φ` case converges to the
> Hurwitz constant `0.2764`), strictly decreasing, no divergence.

The reason — and the honest calibration — is that the non-Archimedean legs are *exact*
(`∏_S |x|_p = 1/|x|`), so `Δ_n = |p_n/q_n − x| / |x|`: the **entire** deviation is the
classical continued-fraction convergent error scaled by `1/|x|`, and the p-adic places
never interact with the Archimedean limit. So the bound is a *conserved machine
invariant* (a rational inequality on `q_n` and the `v_p`'s, checkable without floats) —
but it **is** the classical convergent bound `|x − p_n/q_n| < 1/(q_n q_{n+1})` in adelic
costume, **not** new mathematics. `C` exists and is effective; M4b is therefore
*reachable*, classical, and not a research stall point (`06` §5 failure-mode-1 was
tested and did not occur).

---

## 4. The adelic emission-soundness conjecture (the Axis-II `emit_traps`)

`emit_traps` certifies a *single-place* emission ("the digit is forced for all
tails"). The adelic analogue would certify a *cross-place consistency* — but the
finite-precision asymmetry of §3.3 means there are **two distinct theorems here,
and conflating them is an error** (they need different hypotheses). Split them:

> **Conjecture M4a (exact, value-identified, 🔬).** If `x ∈ ℚ` is `S`-integral and
> its value is **identified** (the Archimedean stream terminates / `x` is pinned to
> an exact rational, so `|x|_∞` is *exact*, not a convergent) and the emitted
> p-adic valuations are proven equal to `v_p(x)`, then the `S`-product-formula
> identity holds **exactly**: `∏_{v∈S} |x|_v = 1`, a *decidable* `ℤ`/`ℚ` statement.

> **Conjecture M4b (prefix residual bound, 🔬, the harder one).** From a **finite
> prefix** of (possibly nonterminating) emitted streams — value *not* yet
> identified, `|x|_∞` only a CF convergent — only a **bounded residual** is
> available: `|∏_v |x|_v − 1| ≤ C/q_n` (the §3.3 gauge bound). This is the genuine
> machine invariant; `C`'s effectivity is open.

**Why the split matters.** M4a's exactness comes *only* from the value being known
(then it is unique factorization, `freePart`/`smoothPart` ✅, wired to the emitted
valuations via `residue_depends_on_prefix` ✅). The moment the value is merely
*approximated by a convergent* (a live, nonterminating stream), the Archimedean
factor is inexact and **only M4b's bound can hold** — so a claim of an *exact*
product over *finite prefixes of a live stream* is false (§3.3). M4a is plausibly
provable (it bottoms out in factorization); **M4b is the real prize and the likely
stall point.** Build M4a first (it is the honest "exact" result); attempt M4b
after the scratch gauge-bound check (§5, item 4) confirms an `O(1/q_n)` envelope.

The *full* (non-`S`-integral, additive, restricted-product) version is **not**
conjectured to be easy and is the genuine research frontier (§3.2 boundary + L3
ladder).

---

## 5. Test plan (before committing to Lean)

Each item is a cheap exact-arithmetic check that *falsifies* a design assumption if
it fails. The scratch script already does the first three; the rest are scoped.

1. **Product formula holds.** ✅ done (Demo A): `∏_v|x|_v=1` exact on samples.
2. **p-adic emission is finite-prefix-forced.** ✅ done (Demo B): digit `aᵢ` frozen
   by input `mod p^{i+1}`.
3. **Multiplicative coupling composes; additive does not.** ✅ done (Demo D).
4. **Gauge-bound conjecture (§3.3).** 🔬 *to scratch:* represent `x` to CF-depth
   `n`, compute the running `∏_v|x|_v` from the convergent + exact valuations,
   tabulate the deviation vs. `1/q_n`. If the deviation is not `O(1/q_n)`, the
   bound conjecture is wrong — revise before formalizing.
5. **`S`-integral adelic soundness as factorization (§4).** 🔬 *to scratch:* for
   `S`-integral `x`, check `∏_{v∈S}|x|_v=1` is exactly recovered from the *emitted*
   valuations (not the closed-form `x`). This rehearses the M4a proof obligation.
6. **Idele combination through the tensor.** 🔬 *to scratch:* run `mulTensor` at
   each place on two represented quantities; verify the emitted product's per-place
   data equals the placewise product (the Axis-I⊗Axis-II compatibility).

Items 4–6 are the recommended next scratch work *before* any M4 Lean effort — they
de-risk the conjecture exactly as Demos A–D de-risked the architecture.

---

## 6. Lean obligations, if the conjectures survive scratch

Stated as concrete theorem targets (for `05`, M4), each naming the ✅ corpus piece
it builds on:

- `padic_valuation_from_stream` (🔨): the valuation read from the emitted Hensel
  stream equals `v_p(x)`. *Core:* `residue_depends_on_prefix` (✅).
- `idele_norm_multiplicative` (🔨): `|x·y|_v = |x|_v|y|_v` per place. *Core:*
  Mathlib valuation multiplicativity (📐); elementary.
- **`S_product_formula_from_exact_value`** (🔬, = **M4a**): for `S`-integral `x`
  with *identified* value, `∏_{v∈S} |x|_v = 1` as an exact `ℚ` identity. *Core:*
  `factorization_unique` / `freePart`·`smoothPart` (✅), i.e. unique factorization;
  `padicValRat` (📐); plus `padic_valuation_from_stream`. Plausibly reachable.
- **`prefix_residual_bound` / `gauge_bound`** (🔬, = **M4b**, hardest): the §3.3
  bound `|∏_v|x|_v − 1| ≤ C/q_n` over *finite live prefixes*. *Core:*
  `steps_qCur_unbounded` (✅) for gauge growth; the constant `C`'s effectivity is
  open and is the make-or-break.

The honest ordering: `padic_valuation_from_stream` and `idele_norm_multiplicative`
are routine-to-moderate; **M4a** (`S_product_formula_from_exact_value`) is the real
but plausibly-reachable prize (it bottoms out in unique factorization, exact only
because the value is identified); **M4b** (`gauge_bound`) is the genuinely uncertain
one — the actual research contribution, or the place the approach stalls.

---

## 7. Honest assessment

- **Settled:** within-place exactness (both faces); the product formula *as a
  theorem of number theory*; multiplicative local composition.
- **Plausibly buildable (the prize):** **M4a** — the `S`-integral, multiplicative,
  *value-identified* product-formula theorem, because it reduces to unique
  factorization + the existing congruence certificate (exact only because the value
  is identified).
- **BUILT ✅ (was "the prize/stall", now machine-checked):** **M4b** — the finite-precision
  gauge bound `| |p_n/q_n|·P − 1 | ≤ P/q_n` (`GaugeBound.lean`: `gauge_bound`, +
  `gauge_product_tendsto` for `Π_n → 1`). The scratch probe settled the shape (`Θ(1/q_n²)`,
  `C = 1`, Hurwitz); the Lean proof assembles Mathlib's `abs_sub_convs_le` (whose own proof
  goes through `fib(n+2) ≤ denom` — the gauge growth, FDRS's `steps_qCur_unbounded` /
  `bracket_invariant` in Mathlib form) + the product-formula constant `P`. It **is** the
  classical CF convergent bound in adelic costume — mechanical assembly, not new math.
- **Genuinely open / may not work:** any *additive* coupling law (§3.2 boundary); the
  full restricted-product (L3) version.
- **The failure mode that did NOT occur:** the worry was that the gauge bound might have
  no effective constant — leaving the Archimedean and non-Archimedean data unreconciled,
  "two bookkeeping systems / indistinguishable from noise." The scratch probe (item 4)
  **tested this and refuted it**: the constant exists (`C = 1`), the deviation strictly
  decreases, the coupling is one conserved law at finite precision.

Next: [`05-build-roadmap.md`](05-build-roadmap.md) — the staged plan that front-loads
the ✅ pieces and gates on these 🔬 checks.
