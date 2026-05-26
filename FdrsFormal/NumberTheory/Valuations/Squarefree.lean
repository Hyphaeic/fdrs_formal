/-
Copyright 2026 Hyphaeic SPC.

Licensed under the Hyphaeic Public License, Version 1.0 (the
"License"); you may not use this file except in compliance with
the License. You may obtain a copy of the License at

https://github.com/hyphaeic/hpl

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
implied. See the License for the specific language governing
permissions and limitations under the License.

# Squarefree Projector

Squarefree indicator and its factorization via prime-square exclusion.

## Mathematical Content (fdrs.md lines 2099-2142)

**Definition**: μ²(n) = 1 iff n is squarefree (no p² divides n).

**Theorem 19** (product form):
On {1,...,N}, the squarefree projector is:
  S_sf = ∏_{p : p² ≤ N} (I - Π_{p²})

**Proof**: μ²(n) = 1 iff p² ∤ n for all primes p ≤ √n.
Therefore μ²(n) = ∏_{p² ≤ N} (1 - 𝟙_{p² | n}).

## References

- fdrs.md, Phase 3 Fragment 3, Section 2 (lines 2099-2142)
-/

import FdrsFormal.NumberTheory.Valuations.Definition
import FdrsFormal.NumberTheory.ArithmeticFunctions.Definition
import Mathlib.Data.Nat.Squarefree

namespace FdrsFormal.NumberTheory.Valuations

open FdrsFormal.NumberTheory.ArithmeticFunctions

/-!
## Squarefree Indicator
-/

/--
**Theorem 19**: Squarefree characterization via prime squares.

**Statement** (fdrs.md lines 2124-2135):
n is squarefree iff p² ∤ n for all primes p.

**Proof**: Delegates to Mathlib's `Squarefree.squarefree_iff_prime_squarefree`.

The full operator form S_sf = ∏_{p² ≤ N} (I - Π_{p²}) requires
Finset product infrastructure over primes.
-/
theorem squarefree_iff_no_prime_sq (n : ℕ) :
    Squarefree n ↔ ∀ p : ℕ, p.Prime → ¬(p * p ∣ n) :=
  Nat.squarefree_iff_prime_squarefree

end FdrsFormal.NumberTheory.Valuations
