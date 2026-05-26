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

# Prefix Value (Residue Map)

This file defines the prefix residue map r_L that computes the numeric
value of a prefix.

## Mathematical Content (fdrs.md lines 282-300)

**Definition 11 (prefix residue map)**:
Define the residue map r_L : ∏_{i=0}^{L-1} D_i → {0, ..., B_L - 1} by
  r_L(s_0, ..., s_{L-1}) := ∑_{i=0}^{L-1} s_i * B_i

**Proposition 6 (prefix–congruence equivalence)**:
For τ ∈ R and s ∈ ∏_{i=0}^{L-1} D_i,
  π_L(τ) = s  ⟺  dec(τ) ≡ r_L(s) (mod B_L)

This is the engine behind locality and continuity proofs: anything defined
by arithmetic on ℕ automatically respects prefixes because arithmetic
respects congruences.

## Implementation Notes

- prefixValue L x extracts the first L digits of x and computes their mixed-radix value
- This is the key connection between prefix (syntactic) and modular arithmetic (semantic)
- Used for proving tick period theorems and locality of operations

## References

- fdrs.md, Phase 1 Fragment 2, Definition 11 (lines 282-287)
- fdrs.md, Phase 1 Fragment 2, Proposition 6 (lines 292-300)
-/

import FdrsFormal.Core.Infinite.DirectLimit
import FdrsFormal.Core.Finite.Bijection
import FdrsFormal.FunctionSpaces.Basic.PrefixSet

namespace FdrsFormal.Core

open FdrsFormal.Core.Primitives FdrsFormal.Core.Infinite FdrsFormal.Core.Finite
open FdrsFormal.FunctionSpaces.Basic

/-!
## Prefix Value Definition
-/

/--
The prefix value (residue map) r_L(π_L(x)).

**fdrs.md Definition 11**: For a prefix s = (s_0, ..., s_{L-1}),
  r_L(s) = ∑_{i=0}^{L-1} s_i * B_i

This computes the numeric value of the first L digits of x when interpreted
as a mixed-radix number.
-/
def prefixValue (b : RadixSeq) (L : ℕ) (x : CompletedSpace b) : ℕ :=
  ∑ i : Fin L, (x i : ℕ) * placeValue b i

/-- Notation for prefix value -/
scoped notation "r_" L => prefixValue _ L

/-!
## Basic Properties
-/

section BasicProperties

variable {b : RadixSeq}

/--
The prefix value is bounded by B_L.

**Proof**: This follows from the standard bound on digit sums.
-/
theorem prefixValue_lt (L : ℕ) (x : CompletedSpace b) :
    prefixValue b L x < placeValue b L := by
  cases L with
  | zero =>
    simp only [prefixValue, Finset.univ_eq_empty, Finset.sum_empty, placeValue.zero]
    exact Nat.one_pos
  | succ k =>
    simp only [prefixValue]
    exact placeValue.sum_digits_lt k (fun i => x i.val)

/--
If two sequences agree on their first L digits, they have the same prefix value.
-/
theorem prefixValue_eq_of_prefix_eq (L : ℕ) (x y : CompletedSpace b)
    (h : ∀ i : Fin L, x i.val = y i.val) :
    prefixValue b L x = prefixValue b L y := by
  simp only [prefixValue]
  apply Finset.sum_congr rfl
  intro i _
  have : x i.val = y i.val := h i
  simp only [this]

end BasicProperties

/-!
## Modular Arithmetic Properties
-/

section ModularArithmetic

variable {b : RadixSeq}

/--
Prefix value respects prefix extensions.

If s is an L-prefix and s' extends it to L+1, then:
  r_{L+1}(s') = r_L(s) + s'_L * B_L

**Proof**: By definition:
  r_{L+1} = ∑_{i=0}^L s_i * B_i
          = (∑_{i=0}^{L-1} s_i * B_i) + s_L * B_L
          = r_L + s_L * B_L
-/
theorem prefixValue_succ (L : ℕ) (x : CompletedSpace b) :
    prefixValue b (L + 1) x = prefixValue b L x + (x L : ℕ) * placeValue b L := by
  simp only [prefixValue, Fin.sum_univ_castSucc, Fin.last, Fin.val_castSucc]

/--
**Key theorem for tick locality**: Prefix value modulo B_L depends only on the first L digits.

This is half of Proposition 6 (the "only if" direction).
-/
theorem prefixValue_mod (L : ℕ) (x : CompletedSpace b) :
    prefixValue b L x % placeValue b L = prefixValue b L x := by
  apply Nat.mod_eq_of_lt
  exact prefixValue_lt L x

end ModularArithmetic

end FdrsFormal.Core
