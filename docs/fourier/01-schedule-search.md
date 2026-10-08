# Design record 01 — the radix-schedule circuit search

*Status: opened 2026-10-07. Measured, not proven: every number below is the exact
gate count of a straight-line program that was built and checked numerically
against the naive DFT. None of it is a theorem until it is formalized. The proven
counts it is compared with are fdrs.md Phase 3 §1.7–1.9 (Theorems 123–125).*

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
| `CT(n₁, n₂)` positional split, explicit twiddles, `W = 1` skipped | `n₁C(n₂) + n₂C(n₁) + #{(a,p) : N ∤ ap}` | Theorem 120 / 125 |
| `CTF(n₁, n₂)` positional split, twiddles folded into the outer combinations | `n₁C(n₂) + Σ_k Σ_{a≥1} (1 or 2)` | Theorem 123's move |
| `PFA(n₁, n₂)`, `gcd = 1` — residue chart in, Good's chart out | `n₁C(n₂) + n₂C(n₁)` | Corollary 33 |

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

Every plan for `N ≤ 2048` was built as a program; its length matched the planner's
count and its output matched the naive DFT (two pseudo-random inputs, f64, error
`≤ 10⁻⁹ N`). Full tables: `data/fourier-search/`.

## 3. Findings (measured)

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
5. **Primes are the bottleneck.** With only the conjugate-pair kernel, a prime
   `p` costs `p² − 1` (`N = 2039`: about `4·10⁶` gates). This is the grammar's gap,
   not a lower bound: Rader's and Bluestein's reductions are not yet in it.
6. **Cheapest lengths per `N log₂ N`.** For `N ≥ 64` they are the powers of two,
   followed by `3·2^m` via `PFA(P3, radix-2)` (e.g. `96: 1.397`, `192: 1.408`).

## 4. Formal targets this suggests

In order of payoff and difficulty:

- **The conjugate-pair kernel** — every odd `N` has an exact circuit with
  `N² − 1` gates. General, self-contained, and it already halves Proposition 158.
- **Composition theorems** turning the planner's recurrences into proofs:
  `C(N) ≤ n₁C(n₂) + n₂C(n₁)` for coprime splits (from Theorems 121–122), and
  `C(N) ≤ n₁C(n₂) + n₂C(n₁) + #{(a,p) : N ∤ ap}` in general (from Theorem 119).
  Together with the kernels, every count in `data/fourier-search/` would become a
  proven upper bound.
- **Finding 4 as a statement.** A precise version of "balanced positional beats
  unbalanced residue" for `N = m²`.

## 5. Next search steps

- Add **Rader** (prime `p` → cyclic convolution of length `p − 1`) and **Bluestein**
  (any `N` → convolution at a power of two) to the grammar; finding 5 should move.
- **Exhaustive minimality for tiny `N`.** Search all circuits with scales from a
  finite constant pool to test whether `D2 = 2`, `P3 = 8`, `CT(2,2) = 9` are minimal.
- **Family 130's question on FDRS schedules.** Test small tensor powers `F_q^{⊗b}`
  (the Vilenkin transform of the constant schedule) for sub-tensor-axis savings in
  the call-count sense of family 130.

## 6. Anti-confabulation ledger

- Measured: all gate counts are exact lengths of programs that were built.
  Correctness is checked numerically in f64, not proven.
- Not claimed: optimality outside the plan grammar; any lower bound; anything about
  family 130's sub-`N log N` regime.
- Proven elsewhere in the corpus and only *re-observed* here: Theorem 123
  (staged), Theorem 125 (binary, skipping), Corollary 33 (Good–Thomas, no twiddles).
