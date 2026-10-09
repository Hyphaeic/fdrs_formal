# carry-lattice

Explore carries on the FDRS radix lattice (fdrs.md §3.8). Two numbers on two
different schedules multiply without carries on the 2-D lattice (cell `(i, j)` has
weight `B_i · C_j`, Theorem 139). Each carry route moves value along row lines
(ratio `b_i`) or column lines (ratio `c_j`); value is conserved (Theorem 137) and the
ledger records what moved where (Theorem 138).

```bash
cargo test --release
cargo run --release -- --b 2,3,5 --c 3,4,7 --x 29 --y 50
```

Schedules repeat cyclically. Three routes are run: rows first, columns first, and a
greedy route. They end in different lattice states with different ledgers and the same
value: on the 2-D lattice, normal forms are not unique, and the route is information.
