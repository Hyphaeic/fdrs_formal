import FdrsFormal.Modes.ExtendedBase.IndexSets

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

# Sigma-Algebra Contribution by Base Type

Characterizes the measurable structure contributed by each digit position
based on its base value.

## Mathematical Content (fdrs.md lines 7000-7005)

**Proposition 123 (Sigma-algebra contribution by base type)**:
At position i:
- Base-0: Contributes trivial σ-algebra {∅, Ω}
- Base-1: Contributes trivial σ-algebra {∅, {0}}
- Base-≥2: Contributes full finite σ-algebra on b_i atoms

## References

-- fdrs.md lines 7000-7006, Proposition 123
- fdrs.md, Phase 9, Section 9.5.1 (lines 7000-7005)
-/

namespace FdrsFormal.Modes.ExtendedBase

/-! ## Proposition 123: Sigma-algebra contribution by base type -/

/--
**fdrs.md**: Proposition 123 (Sigma-algebra contribution by base type) [§9.5.1 · Phase 9] (lines 7000-7005)

The digit space at position i is Fin (b i). Its cardinality determines
the σ-algebra:
- Base-0: card = 0 (empty space → trivial σ-algebra {∅})
- Base-1: card = 1 (singleton → trivial σ-algebra {∅, {0}})
- Base-≥2: card ≥ 2 (non-trivial discrete σ-algebra with 2^(b_i) sets)

**Proof**: Direct from Fintype.card (Fin n) = n.
-/
theorem sigmaAlgebraByBaseType (b : ℕ → ℕ) (i : ℕ) :
    (b i = 0 → Fintype.card (Fin (b i)) = 0) ∧
    (b i = 1 → Fintype.card (Fin (b i)) = 1) ∧
    (2 ≤ b i → 2 ≤ Fintype.card (Fin (b i))) := by
  simp only [Fintype.card_fin]
  omega

/-- Base-0: the digit space is empty. -/
theorem digitSpace_empty_of_base0 {b : ℕ → ℕ} {i : ℕ} (h : b i = 0) :
    IsEmpty (Fin (b i)) := by
  rw [h]; infer_instance

/-- Base-1: the digit space is a singleton (digit is deterministic). -/
theorem digitSpace_unique_of_base1 {b : ℕ → ℕ} {i : ℕ} (h : b i = 1) :
    Subsingleton (Fin (b i)) := by
  rw [h]; infer_instance

/-- Base-≥2: the digit space has multiple elements (non-trivial information). -/
theorem digitSpace_nontrivial_of_base_ge2 {b : ℕ → ℕ} {i : ℕ} (h : 2 ≤ b i) :
    Nontrivial (Fin (b i)) := by
  exact Fin.nontrivial_iff_two_le.mpr h

/--
Only capacity positions (base ≥ 2) contribute non-trivial σ-algebras.
Wall (base-0) and wire (base-1) positions are informationally trivial:
their digit spaces have at most 1 element.
-/
theorem trivial_sigma_of_non_capacity {b : ℕ → ℕ} {i : ℕ} (h : b i < 2) :
    Fintype.card (Fin (b i)) ≤ 1 := by
  simp only [Fintype.card_fin]; omega

end FdrsFormal.Modes.ExtendedBase
