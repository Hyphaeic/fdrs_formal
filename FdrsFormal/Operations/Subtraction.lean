/-
Operations Subtraction - Mixed-radix subtraction operator

Subtraction operator ⊖: R × R → R (partial) defined as τ ⊖ σ = enc(dec(τ) - dec(σ))

## Key Results
- Definition 13: Subtraction (partial, when dec(τ) ≥ dec(σ))
- Proposition 9: Correctness and basic laws

## References
- fdrs.md Phase 1 Fragment 2 Section 2.2
- Paper: Arithmetic operations
-/

import FdrsFormal.Operations.Subtraction.Correctness
import FdrsFormal.Operations.Subtraction.Locality
