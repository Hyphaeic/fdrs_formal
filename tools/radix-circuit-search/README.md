# radix-circuit-search

Search for exact DFT circuits over FDRS radix schedules in family 130's gate model
(fdrs.md Definition 216). Design record and findings:
[`docs/fourier/01-schedule-search.md`](../../docs/fourier/01-schedule-search.md).

Two planners run side by side:

- **grammar** — 2-point butterfly, conjugate-pair kernel, positional and residue
  splits. Every count is a theorem (fdrs.md Corollary 37); `--lean` writes the
  per-length certificates (`SearchCertificates.lean`).
- **extended** — the grammar plus Rader (primes) and Bluestein (any length).
  Every count is a theorem (fdrs.md Corollary 38); `--lean-ext` writes the
  certificates for the lengths where it beats the grammar
  (`SearchCertificatesExt.lean`).

```bash
cargo test --release
cargo run --release -- --max 2048 --verify 2048 \
  --csv ../../data/fourier-search/best-plans.csv \
  --md  ../../data/fourier-search/summary.md
# Lean certificates (default build covers N ≤ 512)
cargo run --release -- --max 512 --verify 0 \
  --lean ../../FdrsFormal/NumberTheory/Characters/SearchCertificates.lean \
  --lean-ext ../../FdrsFormal/NumberTheory/Characters/SearchCertificatesExt.lean
```

Gate counts are exact program lengths. Correctness of every built program is checked
numerically (f64); both planners' counts are additionally proven in Lean.
