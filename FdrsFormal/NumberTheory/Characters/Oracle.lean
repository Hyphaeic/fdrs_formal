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

# Mathlib Oracle Layer - Dirichlet Character Orthogonality

Theorems that bridge the project's Dirichlet character conventions with Mathlib.
Isolate Mathlib API coupling to this single file.

## Provenance

All theorems here follow from:
- `Mathlib.NumberTheory.DirichletCharacter.Orthogonality`
- `MulChar.star_apply'` (star = inverse character for ℂ-valued chars)

## Import Safety

This file imports ONLY Mathlib, NOT other FdrsFormal modules,
to avoid import cycles.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.MulChar.Lemmas

namespace FdrsFormal.NumberTheory.Characters

open scoped BigOperators

/-!
## Dirichlet Character Orthogonality

These theorems bridge the project's conventions (starRingEnd ℂ for conjugation,
sums over units) with Mathlib's Dirichlet character orthogonality lemmas.
-/

/-- For ℂ-valued multiplicative characters, (χ ↑b)⁻¹ = χ (↑(b⁻¹)).
    Characters respect inverses on units. -/
private theorem mulchar_inv_val {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (b : (ZMod q)ˣ) : (χ (↑b : ZMod q))⁻¹ = χ (↑(b⁻¹) : ZMod q) := by
  have hprod : χ (↑b : ZMod q) * χ (↑(b⁻¹) : ZMod q) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hne : χ (↑b : ZMod q) ≠ 0 := ((Units.isUnit b).map χ.toMonoidHom).ne_zero
  exact mul_left_cancel₀ hne
    ((mul_inv_cancel₀ hne).trans hprod.symm)

/--
**Oracle 2**: Dual orthogonality (sum over characters).

**Statement** (fdrs.md lines 1866-1872):
  ∑_{χ} χ(a) · conj(χ(b)) = φ(q) · δ_{a,b}  for a, b ∈ (ℤ/qℤ)ˣ

**Proof**: Convert star to inverse character via `MulChar.star_apply'`,
use `mulchar_inv_val` to convert inverse values to character of inverse,
combine via `map_mul`, and apply `DirichletCharacter.sum_characters_eq`.
-/
theorem dirichlet_dual_oracle
  (q : ℕ) [NeZero q]
  [HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod q)ˣ)]
  (a b : (ZMod q)ˣ) :
  (∑ χ : DirichletCharacter ℂ q, χ a * (starRingEnd ℂ) (χ b)) =
    (@ite ℂ (a = b) (Classical.propDecidable _) (Nat.totient q) 0) := by
  -- Step 1: star(χ b) = (χ b)⁻¹ via star_apply' + inv_apply_eq_inv'
  simp_rw [starRingEnd_apply, MulChar.star_apply', MulChar.inv_apply_eq_inv']
  -- Step 2: (χ ↑b)⁻¹ = χ (↑(b⁻¹))
  simp_rw [mulchar_inv_val]
  -- Step 3: Combine χ ↑a * χ ↑(b⁻¹) = χ (↑a * ↑(b⁻¹)) via map_mul
  simp_rw [← map_mul]
  -- Step 4: Apply sum_characters_eq
  rw [DirichletCharacter.sum_characters_eq]
  -- Step 5: Show conditions are equivalent: ↑a * ↑(b⁻¹) = 1 ↔ a = b
  congr 1
  exact propext ⟨
    fun h => by
      have h1 : ↑(a * b⁻¹) = (1 : ZMod q) := by rw [Units.val_mul]; exact h
      exact mul_inv_eq_one.mp (Units.val_injective (h1.trans (Units.val_one).symm)),
    fun h => by subst h; rw [Units.mul_inv]⟩

/--
**Oracle 1**: Main orthogonality over units.

**Statement** (fdrs.md lines 1860-1865):
  ∑_{a ∈ (ℤ/qℤ)ˣ} χ(a) · conj(ψ(a)) = φ(q) · δ_{χ,ψ}

**Proof**: Factor out ψ⁻¹ using star = inverse character,
reduce to sum of (χ * ψ⁻¹)(a) over units, and apply
character sum formula via reindexing.
-/
theorem dirichlet_main_oracle
  (q : ℕ) [NeZero q]
  [HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod q)ˣ)]
  (χ ψ : DirichletCharacter ℂ q) :
  (∑ a : (ZMod q)ˣ, χ a * (starRingEnd ℂ) (ψ a)) =
    (@ite ℂ (χ = ψ) (Classical.propDecidable _) (Nat.totient q) 0) := by
  -- Convert star(ψ a) to ψ⁻¹ a, then combine to (χ * ψ⁻¹) a
  simp_rw [starRingEnd_apply, MulChar.star_apply', ← MulChar.mul_apply]
  -- Split on whether χ * ψ⁻¹ is trivial
  by_cases hη : χ * ψ⁻¹ = 1
  · -- Trivial case: χ = ψ
    have hχψ : χ = ψ := by rwa [mul_inv_eq_one] at hη
    subst hχψ
    simp only [mul_inv_cancel, ite_true, MulChar.one_apply_coe, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one]
    exact_mod_cast ZMod.card_units_eq_totient q
  · -- Nontrivial case: χ ≠ ψ, sum = 0
    have hχψ : χ ≠ ψ := fun h => hη (by rw [h, mul_inv_cancel])
    simp only [hχψ, ite_false]
    obtain ⟨h₀, hh₀⟩ := MulChar.ne_one_iff.mp hη
    exact eq_zero_of_mul_eq_self_left hh₀ (by
      simp_rw [Finset.mul_sum, ← map_mul, ← Units.val_mul]
      exact (Group.mulLeft_bijective h₀).sum_comp
        (fun a : (ZMod q)ˣ => (χ * ψ⁻¹) (↑a : ZMod q)))

end FdrsFormal.NumberTheory.Characters
