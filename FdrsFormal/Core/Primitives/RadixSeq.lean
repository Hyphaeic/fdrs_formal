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

# Radix Sequences

Defines the RadixSeq structure: a sequence of radices (b_i)_{i≥0} with each b_i ≥ 2.

## References

- fdrs.md, Phase 1 Fragment 1, Section 1 (lines 4-15)
- Paper (external draft) §2.1
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace FdrsFormal.Core.Primitives

/-! ## Radix Sequence -/

/-- A radix sequence is a function `ℕ → ℕ` where each value is at least 2.
    This represents the sequence of bases (b₀, b₁, b₂, ...) in a mixed-radix system. -/
structure RadixSeq where
  /-- The radix at position `i` -/
  toFun : ℕ → ℕ
  /-- Each radix is at least 2 -/
  ge_two : ∀ i, 2 ≤ toFun i

namespace RadixSeq

instance : CoeFun RadixSeq (fun _ => ℕ → ℕ) := ⟨RadixSeq.toFun⟩

/-- The radix at position `i` is positive -/
theorem pos (b : RadixSeq) (i : ℕ) : 0 < b i :=
  Nat.lt_of_lt_of_le (by norm_num : 0 < 2) (b.ge_two i)

/-- The radix at position `i` is at least 1 -/
theorem one_le (b : RadixSeq) (i : ℕ) : 1 ≤ b i :=
  Nat.one_le_of_lt (b.pos i)

/-- The radix at position `i` is not zero -/
theorem ne_zero (b : RadixSeq) (i : ℕ) : b i ≠ 0 :=
  Nat.pos_iff_ne_zero.mp (b.pos i)

end RadixSeq

end FdrsFormal.Core.Primitives
