/-
Core - Foundation layer for mixed-radix systems

Provides all primitive definitions and fundamental theorems:
- Primitives: RadixSeq, Digit, placeValue
- Finite: R^(k) spaces and Proposition 1 (finite bijection)
- Infinite: R^(∞)_fin and Theorem 1 (order isomorphism with ℕ)
- UnitComplement: additive complement-to-unity on [0,1]
- UnitCarry: irrational unit-carry decomposition (fitCount, residue, overflow)

This is the foundation that all other modules build upon.

## References
- fdrs.md Phase 1 Fragment 1 Sections 1-3
- fdrs.md Phase 12 Sections 12.1-12.2
- Paper §2.1-2.2
-/

import FdrsFormal.Core.Primitives
import FdrsFormal.Core.Finite
import FdrsFormal.Core.Infinite
import FdrsFormal.Core.PrefixValue
import FdrsFormal.Core.UnitComplement
import FdrsFormal.Core.UnitCarry
