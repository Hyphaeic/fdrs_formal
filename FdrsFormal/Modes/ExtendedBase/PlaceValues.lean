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

# Generalized Place Values

Place values using effective base, with monotonicity and recovery properties.

## Mathematical Content (fdrs.md lines 6913-6929)

**Definition 139**: Generalized cumulative radix products B_m = ∏ max(b_i, 1)
**Proposition 120**: Monotonicity preserved (B_m ≥ 1, B_{m+1} ≥ B_m)
**Proposition 121**: Recovery of original (when all b_i ≥ 2)

## References

- fdrs.md, Phase 9, Section 9.2 (lines 6913-6929)
- DEPENDENCY_BASED_STRUCTURE.md, Tier 20
-/

import FdrsFormal.Modes.ExtendedBase.IndexSets

namespace FdrsFormal.Modes.ExtendedBase

/-! ## Definition 139: Generalized place values -/

/--
**fdrs.md**: Definition 139 (Generalized cumulative radix products) [§9.2.1 · Phase 9] (lines 6913-6919)

For m ≥ 0, define:
  B_m := ∏_{i=0}^{m-1} b̃_i = ∏_{i=0}^{m-1} max(b_i, 1)
with B_0 := 1.
-/
def generalizedPlaceValue (b : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => generalizedPlaceValue b n * effectiveBase b n

/-! ## Proposition 120: Monotonicity -/

/--
**fdrs.md**: Proposition 120 (Monotonicity preserved) [§9.2.2 · Phase 9] (lines 6921-6925)

For all m ≥ 0: B_m ≥ 1 and B_{m+1} ≥ B_m.

**Proof**: Since b̃_i ≥ 1 for all i, all products are ≥ 1.
Also B_{m+1} = B_m · b̃_m ≥ B_m · 1 = B_m.
-/
theorem placeValue_ge_one (b : ℕ → ℕ) (m : ℕ) : generalizedPlaceValue b m ≥ 1 := by
  induction m with
  | zero => simp [generalizedPlaceValue]
  | succ n ih =>
    unfold generalizedPlaceValue
    have h := effectiveBase_ge_one b n
    calc 1 = 1 * 1 := by ring
    _ ≤ generalizedPlaceValue b n * effectiveBase b n :=
      Nat.mul_le_mul ih h

theorem placeValue_monotone (b : ℕ → ℕ) (m : ℕ) :
    generalizedPlaceValue b m ≤ generalizedPlaceValue b (m + 1) := by
  show generalizedPlaceValue b m ≤ generalizedPlaceValue b m * effectiveBase b m
  have h := effectiveBase_ge_one b m
  calc generalizedPlaceValue b m
    _ = generalizedPlaceValue b m * 1 := by ring
    _ ≤ generalizedPlaceValue b m * effectiveBase b m :=
      Nat.mul_le_mul_left _ h

/-! ## Proposition 121: Recovery -/

/--
**fdrs.md**: Proposition 121 (Recovery of original) [§9.2.3 · Phase 9] (lines 6927-6929)

When all b_i ≥ 2, the generalized place value coincides with the original
B_m = ∏_{i<m} b_i.

**Axiomatized**: Requires connecting to Core.Primitives.placeValue.
-/
theorem placeValue_recovery (b : ℕ → ℕ) (hb : ∀ i, b i ≥ 2) (m : ℕ) :
    generalizedPlaceValue b m = (List.range m).foldl (fun acc j => acc * b j) 1 := by
  induction m with
  | zero => simp [generalizedPlaceValue]
  | succ n ih =>
    simp only [generalizedPlaceValue, List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
    rw [ih]
    -- effectiveBase b n = b n when b n ≥ 2
    have : effectiveBase b n = b n := by unfold effectiveBase; have := hb n; omega
    rw [this]

end FdrsFormal.Modes.ExtendedBase
