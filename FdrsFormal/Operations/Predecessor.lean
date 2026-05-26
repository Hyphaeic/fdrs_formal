/-
Operations Predecessor - Decrement operator with borrow

Predecessor operator pred: R → R defined as pred(τ) = enc(dec(τ) - 1)

## Key Results
- Proposition 7: dec(pred(τ)) = dec(τ) - 1
- Proposition 8: Borrow algorithm equals pred

## References
- fdrs.md Phase 1 Fragment 2 Section 2.1
- Paper: Predecessor operation
-/

import FdrsFormal.Operations.Predecessor.Correctness
import FdrsFormal.Operations.Predecessor.Locality
