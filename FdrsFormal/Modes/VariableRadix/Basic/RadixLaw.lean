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

# Radix Law (Variable Branching Function)

This file defines the radix law ω: Σ* → ℕ≥2 that determines variable branching.

## Mathematical Content (fdrs.md lines 3956-3968)

**Definition 57 (branching function / radix law)**:
A radix law is a function ω: Σ* → {2,3,4,...}, where Σ* denotes the set of all
finite digit words (prefixes). For a prefix s ∈ Σ*, define the allowed next-digit set
  D_ω(s) := {0, 1, ..., ω(s) - 1}

Interpretation: at prefix s, the next digit ranges over D_ω(s). This is exactly
a rooted tree T_ω whose node s has ω(s) children.

## References

- fdrs.md, Phase 5-6, Section 1.1 (lines 3956-3968)
-/

import FdrsFormal.Core.Primitives

namespace FdrsFormal.Modes.VariableRadix

/-!
## Prefix Words (Σ*)

We represent finite digit words as lists of natural numbers.
Each position can have a different alphabet size determined by the radix law.
-/

/-- A prefix word is a finite sequence of digits (as natural numbers) -/
abbrev PrefixWord := List ℕ

/-- The empty prefix -/
def emptyPrefix : PrefixWord := []

/-!
## Radix Law Definition
-/

/--
A radix law determines the branching factor at each prefix.

**fdrs.md Definition 57**: ω: Σ* → ℕ≥2

The radix law ω(s) gives the number of children of node s in the radix tree.
We require ω(s) ≥ 2 for all prefixes s.
-/
structure RadixLaw where
  /-- The branching function: given a prefix, returns the radix at that position -/
  radix : PrefixWord → ℕ
  /-- The radix is always at least 2 -/
  radix_ge_two : ∀ s, 2 ≤ radix s

namespace RadixLaw

variable (ω : RadixLaw)

/-- The radix at a prefix is positive -/
theorem radix_pos (s : PrefixWord) : 0 < ω.radix s :=
  Nat.lt_of_lt_of_le (by norm_num : 0 < 2) (ω.radix_ge_two s)

/-- The radix at a prefix is at least 1 -/
theorem radix_ge_one (s : PrefixWord) : 1 ≤ ω.radix s :=
  Nat.one_le_of_lt (ω.radix_pos s)

/-!
## Constant Radix Law (Fixed Radix Sequence)

A constant radix law corresponds to the fixed radix sequence case from Core.
-/

/-- Convert a fixed RadixSeq to a RadixLaw (radix depends only on position, not path) -/
def ofRadixSeq (b : Core.Primitives.RadixSeq) : RadixLaw where
  radix := fun s => b s.length
  radix_ge_two := fun s => b.ge_two s.length

/-- A radix law is position-only if radix depends only on prefix length -/
def isPositionOnly (ω : RadixLaw) : Prop :=
  ∀ s t, s.length = t.length → ω.radix s = ω.radix t

theorem ofRadixSeq_isPositionOnly (b : Core.Primitives.RadixSeq) : (ofRadixSeq b).isPositionOnly := by
  intro s t hlen
  simp only [ofRadixSeq, hlen]

end RadixLaw

end FdrsFormal.Modes.VariableRadix
