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

# Prescribed Asymptotic Growth Rates

This file handles design of radix laws with specific asymptotic growth behavior.

## Mathematical Content (fdrs.md lines 5278-5296)

**Example 6.4.3 (Prescribed asymptotic growth rate)**:

Solutions for different growth functions f:
1. **Exponential**: f(L) = c^L achieved by constant radix ω(s) = c
2. **Polynomial**: f(L) = L^α requires variable ω(s) ~ |s|^{α-1}
3. **Factorial**: f(L) = L! achieved by ω(s) = |s| + 1

## References

- fdrs.md, Phase 6, Section 6.4 (lines 5278-5296)
-/

import FdrsFormal.Modes.VariableRadix.Design.InverseProblem
import FdrsFormal.Modes.VariableRadix.Basic.RadixLaw
import FdrsFormal.Modes.VariableRadix.PrefixWeights.Definition

namespace FdrsFormal.Modes.VariableRadix.Design

/-!
## Asymptotic Growth Patterns
-/

/-- Constant radix `c` gives exponential prefix weight `β_ω(s) = c^{|s|}`. -/
private theorem prefixWeight_const (c : ℕ) (hc : 2 ≤ c) (s : PrefixWord) :
    prefixWeight ⟨fun _ => c, fun _ => hc⟩ s = c ^ s.length := by
  induction s using List.reverseRecOn with
  | nil => simp
  | append_singleton t d ih =>
    rw [prefixWeight_append, ih]
    simp [List.length_append, pow_succ]

/--
**Exponential growth** — β_ω(s) = c^{|s|}.

**fdrs.md lines 5284-5287**: achieved by the constant radix `ω(s) = c`, giving the
standard p-adic-like structure. Here the prefix weight is computed exactly as the
power `c^{|s|}`.
-/
theorem exponentialGrowthRadix (c : ℕ) (hc : 2 ≤ c) :
    ∃ ω : RadixLaw, (∀ s, ω.radix s = c) ∧ (∀ s, prefixWeight ω s = c ^ s.length) :=
  ⟨⟨fun _ => c, fun _ => hc⟩, fun _ => rfl, prefixWeight_const c hc⟩

/--
**Polynomial growth regime** — variable radices.

**fdrs.md lines 5288-5290**: polynomial target `β_ω(s) ~ |s|^α` "requires variable
radices." We exhibit a genuinely variable radix law (its radix is not constant
across prefixes), the regime the spec identifies for sub-exponential design.

Note: an *exact* polynomial `β_ω ~ |s|^α` is unattainable under the `ω ≥ 2`
constraint, since then `β_ω(s) = ∏ ω ≥ 2^{|s|}` grows at least exponentially; the
realizable content is precisely that polynomial-regime design demands variable
radices (constant radices give pure exponential growth, above).
-/
theorem polynomialGrowthRadix (α : ℝ) (hα : 0 < α) :
    ∃ ω : RadixLaw, ∃ s t, ω.radix s ≠ ω.radix t :=
  ⟨⟨fun s => 2 + s.length % 2, fun _ => Nat.le_add_right 2 _⟩, [], [0], by decide⟩

/-- The radix `ω(s) = |s| + 2` gives factorial prefix weight `β_ω(s) = (|s|+1)!`. -/
private def linearRadix : RadixLaw := ⟨fun s => s.length + 2, fun _ => Nat.le_add_left 2 _⟩

private theorem prefixWeight_linearRadix (s : PrefixWord) :
    prefixWeight linearRadix s = Nat.factorial (s.length + 1) := by
  induction s using List.reverseRecOn with
  | nil => simp [linearRadix, Nat.factorial]
  | append_singleton t d ih =>
    rw [prefixWeight_append, ih]
    show Nat.factorial (t.length + 1) * (t.length + 2) = Nat.factorial ((t ++ [d]).length + 1)
    rw [List.length_append, List.length_singleton, Nat.factorial_succ (t.length + 1)]
    ring

/--
**Factorial growth** — β_ω(s) = (|s|+1)!.

**fdrs.md lines 5292-5294**: the spec's `ω(s) = |s| + 1` gives `β_ω` super-exponential
(`|s|!`). Since a radix law requires `ω ≥ 2` (the spec's `ω([]) = 1` is degenerate),
we use `ω(s) = |s| + 2`, for which `β_ω(s) = ∏_{i=0}^{|s|-1}(i+2) = (|s|+1)!` —
still factorial, super-exponential refinement.
-/
theorem factorialGrowthRadix :
    ∃ ω : RadixLaw, (∀ s, ω.radix s = s.length + 2) ∧
      (∀ s, prefixWeight ω s = Nat.factorial (s.length + 1)) :=
  ⟨linearRadix, fun _ => rfl, prefixWeight_linearRadix⟩

end FdrsFormal.Modes.VariableRadix.Design
