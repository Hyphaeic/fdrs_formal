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

# Variable Digit Alphabets

This file defines the digit alphabet D_ω(s) at each prefix.

## Mathematical Content (fdrs.md lines 3962-3965)

For a prefix s ∈ Σ*, define the allowed next-digit set:
  D_ω(s) := {0, 1, ..., ω(s) - 1}

The digit at position |s| can be any value in D_ω(s).

## References

- fdrs.md, Phase 5-6, Section 1.1 (lines 3962-3965)
- DEPENDENCY_BASED_STRUCTURE.md, Modes/VariableRadix/Basic
-/

import FdrsFormal.Modes.VariableRadix.Basic.RadixLaw

namespace FdrsFormal.Modes.VariableRadix

open RadixLaw

/-!
## Digit Type at a Prefix
-/

/--
The digit alphabet at prefix s under radix law ω.

**fdrs.md**: D_ω(s) = {0, 1, ..., ω(s) - 1}

We use Fin (ω.radix s) to represent this finite set.
-/
def DigitAt (ω : RadixLaw) (s : PrefixWord) := Fin (ω.radix s)

namespace DigitAt

variable {ω : RadixLaw} {s : PrefixWord}

/-- The digit alphabet is nonempty (since radix ≥ 2) -/
instance : Nonempty (DigitAt ω s) :=
  ⟨⟨0, ω.radix_pos s⟩⟩

/-- The digit alphabet is a finite type -/
instance : Fintype (DigitAt ω s) := Fin.fintype _

/-- The digit alphabet has at least 2 elements -/
theorem card_ge_two : 2 ≤ Fintype.card (DigitAt ω s) := by
  simp only [DigitAt, Fintype.card_fin]
  exact ω.radix_ge_two s

/-- Zero is always a valid digit -/
def zero : DigitAt ω s := ⟨0, ω.radix_pos s⟩

/-- Convert a digit to its natural number value -/
def toNat (d : DigitAt ω s) : ℕ := d.val

/-- A digit's value is less than the radix -/
theorem toNat_lt (d : DigitAt ω s) : d.toNat < ω.radix s := d.isLt

end DigitAt

/-!
## Valid Digit Predicate
-/

/-- A natural number is a valid digit at prefix s if it's less than the radix -/
def isValidDigit (ω : RadixLaw) (s : PrefixWord) (d : ℕ) : Prop :=
  d < ω.radix s

theorem isValidDigit_zero (ω : RadixLaw) (s : PrefixWord) : isValidDigit ω s 0 :=
  ω.radix_pos s

theorem isValidDigit_of_lt {ω : RadixLaw} {s : PrefixWord} {d : ℕ}
    (h : d < ω.radix s) : isValidDigit ω s d := h

end FdrsFormal.Modes.VariableRadix
