# limb-schedule

This tool analyses limb schedules for multi-limb arithmetic modulo `B − c`. For each
schedule it reports the product coefficients, the defects, the Christoffel (ceiling)
schedule, the cost of a schoolbook multiply, and the landing criterion. It has no
dependencies.

It is the evaluation companion to these Lean modules:

| fdrs.md | Lean module | Content |
|---|---|---|
| §3.12 | `CarryQuotient.lean` | Limb vectors modulo carries are exactly `ℤ/(B − c)` |
| §3.13 | `MixedRingProduct.lean` | Product coefficients `κ(m,j) = B_m B_j / B_{m+j}`, product-closed rings |
| §3.14 | `ProductSpread.lean` | Landing criterion `gcd(ε·B_t, M) ∣ B_m B_j` |
| §3.23 | `ChristoffelSchedule.lean` | The ceiling schedule `⌈qk/N⌉` is the unique power-of-two schedule with all `κ ∈ {1,2}`; every product-closed schedule lies above it |
| §3.24 | `CostLaw.lean` | Exactly `N(N − gcd(q, N))/2` products are doubled on the ceiling schedule |
| §3.25 | `ValuationClosure.lean` | Product closure prime by prime; squarefree `κ` ⇔ every `v_p(B_k)` is a ceiling schedule |
| §3.26 | `ChristoffelRing.lean` | That ring exists iff some `p^N` divides the holonomy; first/last radix are the ceiling/floor `N`-th roots |

## Commands

```
cargo run --release -- table                                   # standard moduli
cargo run --release -- sweep  --q 255 --c 19 --word 32         # choose a limb count N
cargo run --release -- check  --widths 44,44,42 --c 5 --word 64
cargo run --release -- check  --q 521 --ceil 9 --c 1 --slack 2  # lazy-reduced inputs
cargo run --release -- verify --max-n 8                        # brute-force check of Thms 174–175 and the cost law
cargo run --release -- radices --r 2,3,2 --c 3                 # any radices: κ, residue landing, BLOCKED
cargo run --release -- rings --h 144 --n 3                     # the ring of holonomy h with squarefree κ, if any
cargo run --release -- rings --verify 1 --max-h 3000 --max-n 7 # brute-force check of §3.25–3.26
```

## Columns of the `table` and `sweep` output

- **scaled**: how many partial products have a coefficient other than 1, i.e. how many need a
  shift or doubling before accumulation.
- **cost law**: the count `N (N − gcd(q, N)) / 2`, equivalently `N²(b−1)/(2b)` with
  `b = N / gcd(q, N)`. It was first observed with this tool and is now proved in Lean
  (§3.24, `CostLaw.lean`, Theorem 177).
- **col bits**: the largest column of the schoolbook product, in bits. It assumes every input
  limb is full, `--slack` extra bits per limb if given, and includes the gain `c` on wrapped
  terms.
- **fits**: whether that column fits a double-width accumulator (128 bits for 64-bit limbs,
  64 bits for 32-bit limbs).

## Findings

```
modulus / layout              q   c   N  ceiling widths    scaled  cost law col bits   fits
Curve25519, 64-bit          255  19   5  51×5                0/25         0    108.3    yes
Curve25519, 32-bit          255  19  10  26×5 25×5         25/100        25     59.0    yes
Curve25519, 9 limbs         255  19   9  29×3 28×6          27/81        27     64.6     no
Poly1305, 64-bit            130   5   3  44×1 43×2            3/9         3     90.6    yes
P-521 = 2^521-1, 64-bit     521   1   9  58×8 57×1          36/81        36    119.9    yes
```

- **Radix 2^25.5 is forced.** The 26/25 ladder of Curve25519 is the ceiling schedule. It is
  the only 10-limb schedule needing at most a doubling (Lean: `radix_25_5_unique`).
- **Nine 32-bit limbs overflow.** For 2^255 − 19, nine limbs would need 64.6-bit columns,
  which does not fit a u64 accumulator. This is consistent with the 10-limb choice made in
  practice.
- **poly1305-donna-64 is not a ceiling schedule, and that costs it nothing.** Its limbs are
  44, 44, 42. Checked against the source (`poly1305-donna-64.h`, floodyberry/poly1305-donna,
  master, 2026-10-15), the masks are `0xfffffffffff` (44 bits) and `0x3ffffffffff` (42 bits),
  and the multiply uses `s1 = r1 * (5 << 2)` and `s2 = r2 * (5 << 2)`.
  - The coefficient table from `check --widths 44,44,42 --c 5` reproduces donna's multiply
    exactly: the 20s sit at `h1·r2` and `h2·r1` (into limb 0) and `h2·r2` (into limb 1).
  - The ceiling schedule 44, 43, 43 would cap the gain at `2·5 = 10`.
  - But `r` is fixed per key, so `s = r·20` is precomputed once. The larger gain has no run-time
    cost; it costs about one bit of column headroom (91.5 vs 90.6 of 128 bits).
  - The source and README give no rationale for 44, 44, 42.
  - Lesson: a defect costs run time only when *both* operands vary (field multiplication in
    ECC). There, deployed code uses the ceiling schedule, e.g. the 26/25 ladder of Curve25519.
- **Brute-force evidence.** `verify --max-n 8` enumerates 1,284,475 schedules, 30,617 of them
  product-closed. It finds 0 violations of Theorem 174, Theorem 175 or the cost law.

## Tests

`cargo test --release` runs five tests:

- the Curve25519 ladder is the ceiling schedule, with 25 scaled products;
- Theorems 174–175 and the cost law hold for N ≤ 6;
- the cost law holds on real moduli;
- poly1305-donna-64 has defect 2;
- the (2,3,2) ring witnesses of §3.14–3.15 hold: `4/6 ≡ 8 (mod 11)`, and the product is
  blocked mod 9.
