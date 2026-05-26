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

# Chinese Remainder Theorem (CRT)

CRT for both additive residues and multiplicative characters.

## Mathematical Content (fdrs.md lines 1902-1942)

**Proposition 46** (additive residue projectors factor):
For coprime q₁, q₂ and a ≡ (a₁, a₂) under CRT:
  𝟙_{x ≡ a (mod q₁q₂)} = 𝟙_{x ≡ a₁ (mod q₁)} · 𝟙_{x ≡ a₂ (mod q₂)}

**Proposition 47** (Dirichlet characters factor):
Every χ ∈ X(q₁q₂) factors uniquely as χ(n) = χ₁(n) · χ₂(n)
with χᵢ ∈ X(qᵢ).

**Corollary 11** (projectors factor):
  Π_{q₁q₂,a} = Π_{q₁,a₁} · Π_{q₂,a₂}

## References

- fdrs.md, Phase 3 Fragment 2, Section 3 (lines 1902-1942)
- Mathlib: ZMod.chineseRemainder, IsCoprime
-/

import FdrsFormal.NumberTheory.Characters.DirichletCharacters
import Mathlib.Data.ZMod.Basic

namespace FdrsFormal.NumberTheory.Characters

/-!
## Residue Class Indicator
-/

/-- Residue class indicator: 1 if x = a in ZMod q, 0 otherwise.
    Building block for residue projectors Π_{q,a}. -/
noncomputable def residueIndicator {q : ℕ} [NeZero q] (a x : ZMod q) : ℂ :=
  if x = a then 1 else 0

/-!
## CRT for Additive Residues
-/

/--
**Proposition 46**: Residue indicators factor under CRT.

**Mathematical content** (fdrs.md lines 1911-1917):
For coprime q₁, q₂, let a ∈ ZMod (q₁*q₂) correspond to (a₁, a₂) under CRT. Then:
  𝟙_{x ≡ a (mod q₁q₂)} = 𝟙_{x ≡ a₁ (mod q₁)} · 𝟙_{x ≡ a₂ (mod q₂)}

**Proof**: The CRT isomorphism ZMod (q₁*q₂) ≃+* ZMod q₁ × ZMod q₂ is injective,
so x = a iff both components agree. The indicator product follows by case analysis.
-/
-- fdrs.md lines 1911-1917, Proposition 46
theorem residueProjector_CRT_factor (q₁ q₂ : ℕ) (hcop : Nat.Coprime q₁ q₂)
    [NeZero q₁] [NeZero q₂] (a x : ZMod (q₁ * q₂)) :
    residueIndicator a x =
    residueIndicator ((ZMod.chineseRemainder hcop a).1)
      ((ZMod.chineseRemainder hcop x).1) *
    residueIndicator ((ZMod.chineseRemainder hcop a).2)
      ((ZMod.chineseRemainder hcop x).2) := by
  haveI : NeZero (q₁ * q₂) := ⟨Nat.mul_ne_zero (NeZero.ne q₁) (NeZero.ne q₂)⟩
  unfold residueIndicator
  by_cases h : x = a
  · subst h; simp
  · -- x ≠ a, so by CRT injectivity at least one component differs
    simp only [if_neg h]
    have hne : (ZMod.chineseRemainder hcop x).1 ≠ (ZMod.chineseRemainder hcop a).1 ∨
               (ZMod.chineseRemainder hcop x).2 ≠ (ZMod.chineseRemainder hcop a).2 := by
      by_contra hall
      push_neg at hall
      exact h ((ZMod.chineseRemainder hcop).injective (Prod.ext hall.1 hall.2))
    rcases hne with h1 | h2
    · simp only [if_neg h1, zero_mul]
    · simp only [if_neg h2, mul_zero]

/-!
## Projector Operator Factorization
-/

/--
**Corollary 11**: Residue projector operators factor under CRT.

**Mathematical content** (fdrs.md lines 1935-1941):
For a ∈ (ℤ/(q₁q₂)ℤ)ˣ corresponding to (a₁, a₂):
  Π_{q₁q₂,a} = Π_{q₁,a₁} · Π_{q₂,a₂}

where Π_{q,a} is the pointwise multiplication operator by 𝟙_{x≡a (mod q)}.

**Proof**: Multiply both sides of Proposition 46 by f(x) and use associativity.
-/
-- fdrs.md lines 1935-1941, Corollary 11
theorem projectorsFactor (q₁ q₂ : ℕ) (hcop : Nat.Coprime q₁ q₂)
    [NeZero q₁] [NeZero q₂] (a : ZMod (q₁ * q₂))
    (f : ZMod (q₁ * q₂) → ℂ) (x : ZMod (q₁ * q₂)) :
    residueIndicator a x * f x =
    residueIndicator ((ZMod.chineseRemainder hcop a).1)
      ((ZMod.chineseRemainder hcop x).1) *
    (residueIndicator ((ZMod.chineseRemainder hcop a).2)
      ((ZMod.chineseRemainder hcop x).2) * f x) := by
  rw [← mul_assoc, ← residueProjector_CRT_factor]

/-!
## CRT for Multiplicative Characters
-/

/--
**Proposition 47**: Multiplicative functions on ℤ/(q₁q₂)ℤ factor under CRT.

-- fdrs.md lines 1926-1933, Proposition 47

**Proof**: Factor through CRT isomorphism φ : ℤ/(q₁q₂)ℤ ≃+* ℤ/q₁ℤ × ℤ/q₂ℤ.
Define χ₁(y) = χ(φ⁻¹(y,1)), χ₂(z) = χ(φ⁻¹(1,z)).
Then χ(x) = χ₁(φ(x).1) · χ₂(φ(x).2) since (p,1)·(1,q) = (p,q) in the product ring.
-/
theorem dirichletChar_CRT_factor (q₁ q₂ : ℕ) (hcoprime : Nat.Coprime q₁ q₂)
    [NeZero q₁] [NeZero q₂] :
    ∀ (χ : ZMod (q₁ * q₂) → ℂ)
      (hχ : ∀ a b, χ (a * b) = χ a * χ b),
      ∃ (χ₁ : ZMod q₁ → ℂ) (χ₂ : ZMod q₂ → ℂ),
        (∀ a b, χ₁ (a * b) = χ₁ a * χ₁ b) ∧
        (∀ a b, χ₂ (a * b) = χ₂ a * χ₂ b) ∧
        (∀ x, χ x = χ₁ ((ZMod.chineseRemainder hcoprime x).1) *
                     χ₂ ((ZMod.chineseRemainder hcoprime x).2)) := by
  intro χ hχ
  haveI : NeZero (q₁ * q₂) := ⟨Nat.mul_ne_zero (NeZero.ne q₁) (NeZero.ne q₂)⟩
  set φ := ZMod.chineseRemainder hcoprime
  -- Factor: χ₁(y) = χ(φ⁻¹(y,1)), χ₂(z) = χ(φ⁻¹(1,z))
  refine ⟨fun y => χ (φ.symm (y, 1)), fun z => χ (φ.symm (1, z)), ?_, ?_, ?_⟩
  · -- χ₁ multiplicative
    intro a b
    show χ (φ.symm (a * b, 1)) = χ (φ.symm (a, 1)) * χ (φ.symm (b, 1))
    rw [show (a * b, (1 : ZMod q₂)) = (a, 1) * (b, 1) from by ext <;> simp, map_mul]
    exact hχ _ _
  · -- χ₂ multiplicative
    intro a b
    show χ (φ.symm (1, a * b)) = χ (φ.symm (1, a)) * χ (φ.symm (1, b))
    rw [show ((1 : ZMod q₁), a * b) = (1, a) * (1, b) from by ext <;> simp, map_mul]
    exact hχ _ _
  · -- Factorization: χ(x) = χ₁(φ(x).1) · χ₂(φ(x).2)
    intro x
    show χ x = χ (φ.symm ((φ x).1, 1)) * χ (φ.symm (1, (φ x).2))
    rw [← hχ, ← map_mul]
    congr 1
    rw [show ((φ x).1, (1 : ZMod q₂)) * ((1 : ZMod q₁), (φ x).2) = φ x
        from by ext <;> simp]
    exact (φ.symm_apply_apply x).symm

end FdrsFormal.NumberTheory.Characters
