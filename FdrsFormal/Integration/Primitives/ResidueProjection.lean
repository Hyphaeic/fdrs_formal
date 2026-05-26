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

# Residue Projection Operator

This file defines the residue projection operator Proj_{q,a}.

## Mathematical Content (fdrs.md Phase 4)

**Residue Projection**: The operator `Proj_{q,a}` projects onto elements
congruent to a mod q. This is a fundamental ANT primitive.

**Key Properties**:
- Idempotent: `Proj_{q,a}² = Proj_{q,a}`
- Orthogonal: `Proj_{q,a} · Proj_{q,a'} = 0` for a ≠ a' (mod q)
- CRT composition: `Proj_{q₁,a₁} · Proj_{q₂,a₂} = Proj_{q₁q₂,a}` when gcd(q₁,q₂)=1

## References

- fdrs.md, Phase 4, Section 4.2 (ANT Primitives)
- fdrs.md, Phase 3, Section 3.1 (Residue Classes)
-/

import FdrsFormal.Core
import FdrsFormal.Topology
import FdrsFormal.NumberTheory

namespace FdrsFormal.Integration.Primitives

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Block size at depth L: B_L = ∏_{i=0}^{L-1} b_i -/
def blockSize (b : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => blockSize b n * b n

/-!
## Residue Projection Definition
-/

/--
Residue projection: filters to elements ≡ a (mod q).

**fdrs.md**: `Proj_{q,a}(f)(n) = f(n) if n ≡ a (mod q), else 0`
-/
def residueProj (q : ℕ) (a : ZMod q) (f : ℕ → V) : ℕ → V :=
  fun n => if (n : ZMod q) = a then f n else 0

/--
Residue projection on finite spaces.
-/
def residueProjFin (b : ℕ → ℕ) (k : ℕ) (q : ℕ) (a : ZMod q)
    (f : Fin (blockSize b k) → V) :
    Fin (blockSize b k) → V :=
  fun n => if ((n : ℕ) : ZMod q) = a then f n else 0

/-!
## Projection Properties
-/

/--
Residue projection is idempotent.

**fdrs.md**: `Proj_{q,a}² = Proj_{q,a}`
-/
theorem residueProj_idempotent (q : ℕ) (a : ZMod q) (f : ℕ → V) :
    residueProj q a (residueProj q a f) = residueProj q a f := by
  ext n
  simp only [residueProj]
  split_ifs with h
  · rfl
  · rfl

/--
Residue projections for different residues are orthogonal.

**fdrs.md**: `Proj_{q,a} · Proj_{q,a'} = 0` for a ≠ a'
-/
theorem residueProj_orthogonal (q : ℕ) (a a' : ZMod q) (hne : a ≠ a') (f : ℕ → V) :
    residueProj q a (residueProj q a' f) = 0 := by
  ext n
  simp only [residueProj, Pi.zero_apply]
  split_ifs with h1 h2
  · exfalso; exact hne (h1.symm.trans h2)
  · rfl
  · rfl

/--
CRT maps n to (n mod q₁, n mod q₂) component-wise.

**Mathematical Proof**: The CRT isomorphism is a RingHom, and RingHoms preserve nat casts.
-/
private theorem crt_nat_cast (q₁ q₂ : ℕ) (hcoprime : Nat.Coprime q₁ q₂) (n : ℕ) :
    let iso := ZMod.chineseRemainder hcoprime
    iso (n : ZMod (q₁ * q₂)) = ((n : ZMod q₁), (n : ZMod q₂)) := by
  simp only []
  have h : (ZMod.chineseRemainder hcoprime).toRingHom (n : ZMod (q₁ * q₂)) =
           (n : ZMod q₁ × ZMod q₂) := map_natCast _ n
  simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at h
  convert h using 1

/--
The key CRT equivalence: n ≡ a (mod q₁*q₂) iff (n ≡ a₁ (mod q₁) and n ≡ a₂ (mod q₂))
where a = CRT.symm(a₁, a₂).

**Mathematical Proof**: By injectivity of the CRT isomorphism.
-/
private theorem residue_crt_equiv (q₁ q₂ : ℕ) (hcoprime : Nat.Coprime q₁ q₂)
    (a₁ : ZMod q₁) (a₂ : ZMod q₂) (n : ℕ) :
    let a := (ZMod.chineseRemainder hcoprime).symm (a₁, a₂)
    ((n : ZMod (q₁ * q₂)) = a) ↔ ((n : ZMod q₁) = a₁ ∧ (n : ZMod q₂) = a₂) := by
  intro a
  let iso := ZMod.chineseRemainder hcoprime
  constructor
  · intro h
    have hcast := crt_nat_cast q₁ q₂ hcoprime n
    simp only at hcast
    have hiso_a : iso a = (a₁, a₂) := iso.apply_symm_apply (a₁, a₂)
    have heq : iso (n : ZMod (q₁ * q₂)) = iso a := congrArg iso h
    rw [hcast, hiso_a] at heq
    exact ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩
  · intro ⟨h1, h2⟩
    have hcast := crt_nat_cast q₁ q₂ hcoprime n
    simp only at hcast
    have heq : iso (n : ZMod (q₁ * q₂)) = (a₁, a₂) := by
      rw [hcast, h1, h2]
    have hiso_a : iso a = (a₁, a₂) := iso.apply_symm_apply (a₁, a₂)
    rw [← hiso_a] at heq
    exact iso.injective heq

/--
CRT composition: projections combine via Chinese Remainder Theorem.

**fdrs.md**: `Proj_{q₁,a₁} · Proj_{q₂,a₂} = Proj_{q₁q₂,a}` when gcd(q₁,q₂)=1

**Mathematical Proof**: By CRT, there exists unique a mod q₁q₂ with
a ≡ a₁ (mod q₁) and a ≡ a₂ (mod q₂). Then n ≡ a₁ (mod q₁) ∧ n ≡ a₂ (mod q₂)
iff n ≡ a (mod q₁q₂), so the projections coincide.
-/
theorem residueProj_crt (q₁ q₂ : ℕ) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hcoprime : Nat.Coprime q₁ q₂)
    (a₁ : ZMod q₁) (a₂ : ZMod q₂) (f : ℕ → V) :
    ∃ a : ZMod (q₁ * q₂),
      residueProj q₁ a₁ (residueProj q₂ a₂ f) = residueProj (q₁ * q₂) a f := by
  use (ZMod.chineseRemainder hcoprime).symm (a₁, a₂)
  ext n
  simp only [residueProj]
  -- The LHS is: if (n : ZMod q₁) = a₁ then (if (n : ZMod q₂) = a₂ then f n else 0) else 0
  -- The RHS is: if (n : ZMod (q₁ * q₂)) = a then f n else 0
  -- By CRT: (n : ZMod (q₁ * q₂)) = a ↔ ((n : ZMod q₁) = a₁ ∧ (n : ZMod q₂) = a₂)
  have hcrt := residue_crt_equiv q₁ q₂ hcoprime a₁ a₂ n
  simp only at hcrt
  -- Case split on both conditions
  by_cases h1 : (n : ZMod q₁) = a₁ <;> by_cases h2 : (n : ZMod q₂) = a₂
  · -- Both hold, so n ≡ a (mod q₁*q₂)
    simp only [h1, h2, ↓reduceIte, hcrt.mpr ⟨h1, h2⟩]
  · -- h1 holds but not h2, so n ≢ a (mod q₁*q₂)
    have hna : ¬((n : ZMod (q₁ * q₂)) = _) := fun h => h2 (hcrt.mp h).2
    simp only [h1, h2, ↓reduceIte, hna]
  · -- h2 holds but not h1, so n ≢ a (mod q₁*q₂)
    have hna : ¬((n : ZMod (q₁ * q₂)) = _) := fun h => h1 (hcrt.mp h).1
    simp only [h1, ↓reduceIte, hna]
  · -- Neither holds, so n ≢ a (mod q₁*q₂)
    have hna : ¬((n : ZMod (q₁ * q₂)) = _) := fun h => h1 (hcrt.mp h).1
    simp only [h1, ↓reduceIte, hna]

/-!
## Unit Restriction
-/

/--
Projection onto units mod q.

**fdrs.md**: `Proj^×_q = Σ_{a ∈ (ℤ/qℤ)×} Proj_{q,a}`
-/
def unitProj (q : ℕ) [NeZero q] (f : ℕ → V) : ℕ → V :=
  fun n => if Nat.Coprime n q then f n else 0

/--
Unit projection is idempotent.
-/
theorem unitProj_idempotent (q : ℕ) [NeZero q] (f : ℕ → V) :
    unitProj q (unitProj q f) = unitProj q f := by
  ext n
  simp only [unitProj]
  split_ifs <;> rfl

end FdrsFormal.Integration.Primitives
