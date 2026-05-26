import FdrsFormal.Core

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

# Instantiation API

Defines the instantiation operation that converts a base-0 position
to a given new base.

## Mathematical Content (fdrs.md lines 7029-7034)

**Definition 144 (Instantiation API)**:
The operation instantiate(position, new_base) converts a base-0 position
to base new_base ≥ 1:
- Updates the radix sequence
- Initializes the digit to 0
- Recomputes block sizes

## References

- fdrs.md lines 7029-7049, Definition 144
- fdrs.md, Phase 9, Section 9.6 (lines 7029-7049)
-/

namespace FdrsFormal.Modes.ExtendedBase

/-! ## Definition 144: Instantiation API -/

/--
**fdrs.md**: Definition 144 (Instantiation API) [§9.6.1 · Phase 9] (lines 7029-7034)

The operation instantiate(position, new_base) converts a base-0 position
to base new_base ≥ 1:
- Updates the radix sequence
- Initializes the digit to 0
- Recomputes block sizes

The core operation is a pointwise update of the radix function:
  instantiate(b, p, k)(i) = k if i = p, else b(i)
-/
def instantiate (b : ℕ → ℕ) (position : ℕ) (newBase : ℕ) : ℕ → ℕ :=
  fun i => if i = position then newBase else b i

/-- Instantiation updates the base at the target position. -/
theorem instantiate_at (b : ℕ → ℕ) (p : ℕ) (k : ℕ) :
    instantiate b p k p = k := by
  simp [instantiate]

/-- Instantiation preserves bases at all other positions. -/
theorem instantiate_ne (b : ℕ → ℕ) (p : ℕ) (k : ℕ) (i : ℕ) (h : i ≠ p) :
    instantiate b p k i = b i := by
  simp [instantiate, h]

/-- Double instantiation at the same position keeps the last value. -/
theorem instantiate_instantiate_same (b : ℕ → ℕ) (p : ℕ) (k₁ k₂ : ℕ) :
    instantiate (instantiate b p k₁) p k₂ = instantiate b p k₂ := by
  funext i
  simp only [instantiate]
  split <;> simp_all

/-- Instantiation at different positions commutes. -/
theorem instantiate_comm (b : ℕ → ℕ) (p₁ p₂ : ℕ) (k₁ k₂ : ℕ) (h : p₁ ≠ p₂) :
    instantiate (instantiate b p₁ k₁) p₂ k₂ =
    instantiate (instantiate b p₂ k₂) p₁ k₁ := by
  funext i
  simp only [instantiate]
  split <;> split <;> omega

end FdrsFormal.Modes.ExtendedBase
