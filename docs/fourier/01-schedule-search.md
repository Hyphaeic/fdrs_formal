# Design record 01 — the radix-schedule circuit search

*Status: opened 2026-10-07; updated 2026-10-08. Every count reported here is a
**theorem**. **Grammar** counts (dense ≤ 2, conjugate pair, positional and residue
splits): fdrs.md Corollary 37 proves every plan of that grammar is an exact circuit
of exactly its cost, and `SearchCertificates.lean` checks each length `N ≤ 512` in
the kernel (all `N ≤ 2048` were checked once, about 5 minutes, outside the default
build). **Extended** counts (adding Rader and Bluestein): fdrs.md Corollary 38 does
the same for the extended grammar, and `SearchCertificatesExt.lean` checks each
length `N ≤ 512` where the extended plan wins (355 lengths; all 1727 such
`N ≤ 2048` were checked once, in chunks, about 12 minutes). Optimality is not
claimed anywhere.*

## 1. The question

fdrs.md §1.7 leaves open, in the corpus's own terms: **which radix schedules admit
exact Fourier circuits below the cost of their own staged transform?** Theorem 123
gives every schedule `N · Σ_i (2b_i − 1)` gates (one folded `b_i`-term block per
output per stage); Theorems 124–125 bring the binary schedule to
`(3/2) N log₂ N − N + 1`; family 130 proves that, in the same gate model, the
constant can be pushed below any `c > 0` along a subsequence.

This record starts the search from the constructive side: over a grammar of
classical plans, find the cheapest exact circuit for every `N ≤ 2048`, and read
off which schedule-and-chart choices win.

## 2. Model and search space

Gate model: family 130's (Definition 216) — add, subtract, scale by a fixed complex
constant, one gate each; outputs are named registers (free permutation and fan-out).

A **plan** for length `N` is one of:

| plan | gates | corpus counterpart |
|---|---|---|
| `D_N` dense — each output a combination of all inputs, `±1` coefficients unscaled | `Σ_k Σ_{j≥1} (1 or 2)` | Proposition 158, sharpened |
| `P_N` conjugate pair, odd `N = 2h+1` — `s_j = x_j + x_{N−j}`, `d_j = x_j − x_{N−j}`, cosines on `s`, sines on `d` | `N² − 1` | Theorem 126 (proven) |
| `CT(n₁, n₂)` positional split, explicit twiddles, `W = 1` skipped | `n₁C(n₂) + n₂C(n₁) + #{(a,p) : N ∤ ap}` | Theorem 127 (proven) |
| `CTF(n₁, n₂)` positional split, twiddles folded into the outer combinations | `n₁C(n₂) + Σ_k Σ_{a≥1} (1 or 2)` | Theorem 123's move (never wins) |
| `PFA(n₁, n₂)`, `gcd = 1` — residue chart in, Good's chart out | `n₁C(n₂) + n₂C(n₁)` | Theorem 128 (proven) |
| `Rader_p` (extended), prime `p` — cyclic convolution of length `p − 1` via two DFTs of length `p − 1` | `2C(p−1) + 2p − 1` | Theorem 129 (proven) |
| `Bluestein_N[M]` (extended), any `N` — chirp, cyclic convolution at `2N − 1 ≤ M ≤ 4N` via two grammar DFTs of length `M` | `2C(M) + M + 2·#{j : 2N ∤ j²}` | Theorem 130 (proven) |

A dynamic program takes, for each `N`, the cheapest plan with the cheapest
sub-plans. Read in FDRS terms, a plan tree is an **ordered radix schedule together
with a chart at every split** (positional, with twiddles, or residue, without).

Tool: `tools/radix-circuit-search` (Rust, no dependencies).

```bash
cd tools/radix-circuit-search
cargo test --release                       # kernels + planner vs Theorems 123/125
cargo run --release -- --max 2048 --verify 2048 \
  --csv ../../data/fourier-search/best-plans.csv \
  --md  ../../data/fourier-search/summary.md
```

Every grammar plan and every extended plan for `N ≤ 2048` was built as a program;
its length matched the planner's count and its output matched the naive DFT (two
pseudo-random inputs, f64, error `≤ 10⁻⁹ N`). `--lean PATH` writes the Lean
certificates for the grammar plans, `--lean-ext PATH` those for the extended plans
that beat the grammar. Full tables: `data/fourier-search/`.

## 3. Findings

Findings 1–6 concern the grammar, finding 7 the extended grammar. All counts are
theorems; optimality *within* a grammar is a property of the dynamic program, not
proven.

1. **Powers of two: Theorem 125 is the optimum of the grammar.** For every
   `N = 2^m ≤ 2048` the best plan is radix-2 Cooley–Tukey with trivial twiddles
   skipped, at exactly `(3/2) N log₂ N − N + 1` gates. No radix-4 or mixed split
   helps, because a multiplication by `±i` is a charged scale gate.
2. **Folding twiddles never wins.** `CTF` — the move behind Theorem 123 — is chosen
   for no `N ≤ 2048`. Explicit twiddles with skipping are always at least as cheap.
   Across all lengths the best plan costs `0.33–0.63×` Theorem 123's count.
3. **The residue chart usually wins.** Good–Thomas is the top-level move for
   1660 of the 2047 lengths. On a coprime split it is the positional split minus its
   twiddles, so it always beats `CT` on the *same* split.
4. **…but not always: balanced positional beats unbalanced residue.** At 47 lengths
   a positional split is the best top-level move even though coprime splits exist —
   typically the square of a length that itself has coprime parts:
   `144 = 12·12` costs `1537` by `CT(PFA(3,4), PFA(3,4))` against `1561` for the best
   residue split `9·16`; likewise `72, 225, 400, 441, 576`. The chart choice depends
   on the *balance* of the schedule, not only on coprimality.
5. **Primes are the bottleneck of the grammar.** With only the conjugate-pair
   kernel, a prime `p` costs `p² − 1` (`N = 2039`: about `4·10⁶` gates); the worst
   normalized grammar cost for `N ≥ 64` is about `185 · N log₂ N`.
6. **Cheapest lengths per `N log₂ N`.** For `N ≥ 64` they are the powers of two,
   followed by `3·2^m` via `PFA(P3, radix-2)` (e.g. `96: 1.397`, `192: 1.408`).
7. **Rader and Bluestein remove the prime bottleneck.** The extended
   planner improves 1727 of the 2047 lengths. Primes gain most: `257: 66048 → 6147`
   (Rader over radix-2), `1021: 23×`, `1999: 35×`, `2039: 28×` (Bluestein at
   `M = 4096`). Rader recurses — `1031 → 1030 = 2·5·103`, `103 → 102 = 2·3·17`,
   `17 → 16` — so its cost follows the factorization of `p − 1`. The worst
   normalized extended cost for `N ≥ 64` falls from about `185` to `8.2`
   (`N = 167`, Bluestein at `M = 384`); the median is `3.6`.

## 4. Formal status

Done (2026-10-08):

- **The conjugate-pair kernel** — Theorem 126 (`PairKernel.lean`).
- **Composition theorems** — Theorem 127 (positional split) and Theorem 128
  (residue split) for arbitrary circuits, and Corollary 37: every grammar plan is an
  exact circuit of exactly its cost (`CircuitCompose.lean`). The grammar column of
  `data/fourier-search/` is therefore a table of theorems; `SearchCertificates.lean`
  instantiates it for every `N ≤ 512`.

- **Rader and Bluestein** — Proposition 161 (a cyclic convolution from two forward
  transforms, the inverse read at the mirrored index), Theorem 129 (Rader,
  `2|C| + 2n + 1` at prime `n + 1`), Theorem 130 (Bluestein, `2|C| + M + 2·#chirp`
  for `M ≥ 2N − 1`), and Corollary 38: every extended plan is an exact circuit of
  exactly its cost (`RaderBluestein.lean`). Rader's generator comes from
  cyclicity of `(ℤ/p)^×`; primality in plan validity is trial division, so the
  kernel checks it. The extended column of `data/fourier-search/` is therefore a
  table of theorems as well; `SearchCertificatesExt.lean` instantiates it.

Open:

- **Finding 4 as a statement.** A precise version of "balanced positional beats
  unbalanced residue" for `N = m²`.

## 5. Next search steps

- **Exhaustive minimality for tiny `N` — not attempted, and naive search will not
  do it.** Deciding whether `P3 = 8` is minimal means excluding every 7-gate
  circuit; with values as linear forms and even a small finite constant pool the
  branching is about `250` per gate, `≈ 10¹⁶` sequences. A workable route needs a
  different formulation — e.g. a SAT/SMT encoding over a finite field where the DFT
  exists, or rank-based lower bounds — before any search.
- **Family 130's question on FDRS schedules.** Test small tensor powers `F_q^{⊗b}`
  (the Vilenkin transform of the constant schedule) for sub-tensor-axis savings in
  the call-count sense of family 130.

## 6. Anti-confabulation ledger

- Proven: every grammar count (Corollary 37), instantiated in the kernel for
  `N ≤ 512` in the default build and for all `N ≤ 2048` once.
- Proven: every extended count (Corollary 38, via Theorems 129–130), instantiated
  in the kernel for the 355 improved lengths `N ≤ 512` in the default build and for
  all 1727 improved lengths `N ≤ 2048` once.
- Also checked numerically: every built program, grammar and extended, `N ≤ 2048`
  (f64), as a cross-check of the tool against the theorems.
- Not claimed: optimality outside the plan grammar (or inside it, beyond what the
  dynamic program computes); any lower bound; anything about family 130's
  sub-`N log N` regime.
- Proven elsewhere in the corpus and only *re-observed* here: Theorem 123
  (staged), Theorem 125 (binary, skipping), Corollary 33 (Good–Thomas, no twiddles).
