# radix-circuit-search

Search for exact DFT circuits over FDRS radix schedules in family 130's gate model
(fdrs.md Definition 216). Design record and findings:
[`docs/fourier/01-schedule-search.md`](../../docs/fourier/01-schedule-search.md).

```bash
cargo test --release
cargo run --release -- --max 2048 --verify 2048 \
  --csv ../../data/fourier-search/best-plans.csv \
  --md  ../../data/fourier-search/summary.md
```

Gate counts are exact program lengths; correctness is checked numerically (f64),
not proven.
