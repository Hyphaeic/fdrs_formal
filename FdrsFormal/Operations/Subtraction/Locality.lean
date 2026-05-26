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

# Locality of Subtraction

This file proves locality properties of the subtraction operator:
operations preserve prefix agreement and satisfy finite dependence.

These lemmas support future continuity proofs.

## References

- fdrs.md, Phase 1 Fragment 2, Section 4
-/

import FdrsFormal.Operations.Subtraction.Correctness
import FdrsFormal.Operations.Predecessor.Locality

namespace FdrsFormal.Operations.Subtraction

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite FdrsFormal.Core.Infinite

variable {b : RadixSeq}

/-!
## Congruence Preservation

Subtraction preserves congruences: if inputs agree mod B_L, outputs agree mod B_L.
-/

/--
**Helper Lemma**: For natural numbers, if a ≡ b (mod n) and c ≡ d (mod n),
with a ≥ c and b ≥ d, then (a-c) ≡ (b-d) (mod n).
This is the core modular arithmetic fact for subtraction locality.

**Proof Strategy**: Convert to integers where subtraction is well-behaved,
use `Int.sub_emod`, then convert back to naturals.
-/
theorem Nat.sub_mod_eq_of_mod_eq (a b c d n : ℕ) (hac : c ≤ a) (hbd : d ≤ b)
    (hab : a % n = b % n) (hcd : c % n = d % n) :
    (a - c) % n = (b - d) % n := by
  -- Handle n = 0 case
  rcases n with _ | n'
  · simp only [Nat.mod_zero] at hab hcd ⊢
    simp [hab, hcd]
  -- Convert to integers where subtraction is better behaved
  -- Key: in integers, (a - c) % n = (a % n - c % n) % n
  -- Since a % n = b % n and c % n = d % n, we get (a - c) % n = (b - d) % n
  have hab_int : (a : ℤ) % (n' + 1 : ℕ) = (b : ℤ) % (n' + 1 : ℕ) := by
    norm_cast
  have hcd_int : (c : ℤ) % (n' + 1 : ℕ) = (d : ℤ) % (n' + 1 : ℕ) := by
    norm_cast
  -- Use Int.sub_emod: (a - c) % n = (a % n - c % n) % n
  have key : ((a : ℤ) - c) % (n' + 1 : ℕ) = ((b : ℤ) - d) % (n' + 1 : ℕ) := by
    conv_lhs => rw [Int.sub_emod, hab_int, hcd_int, ← Int.sub_emod]
  -- Convert back to naturals using Int.ofNat_sub
  have ha_int : ((a : ℤ) - c) = ((a - c : ℕ) : ℤ) := (Int.ofNat_sub hac).symm
  have hb_int : ((b : ℤ) - d) = ((b - d : ℕ) : ℤ) := (Int.ofNat_sub hbd).symm
  -- After substitution, key has type: ↑(a - c) % (n' + 1) = ↑(b - d) % (n' + 1)
  rw [ha_int, hb_int] at key
  -- key now says: ↑(a - c) % ↑(n' + 1) = ↑(b - d) % ↑(n' + 1)
  -- Need to show: (a - c) % (n' + 1) = (b - d) % (n' + 1)
  -- Use: for naturals m, n: ↑(m % n) = ↑m % ↑n (Int.natCast_mod)
  -- So ↑m % ↑n = ↑(m % n) is the symmetric version
  have h1 : ((a - c : ℕ) : ℤ) % ((n' + 1 : ℕ) : ℤ) = (((a - c) % (n' + 1) : ℕ) : ℤ) :=
    (Int.natCast_mod (a - c) (n' + 1)).symm
  have h2 : ((b - d : ℕ) : ℤ) % ((n' + 1 : ℕ) : ℤ) = (((b - d) % (n' + 1) : ℕ) : ℤ) :=
    (Int.natCast_mod (b - d) (n' + 1)).symm
  rw [h1, h2] at key
  exact Int.ofNat_inj.mp key

/--
**Key Locality Lemma**: If τ₁ ≡ τ₂ (mod B_L) and σ₁ ≡ σ₂ (mod B_L),
then (τ₁ ⊖ σ₁) ≡ (τ₂ ⊖ σ₂) (mod B_L).

This is the foundation for continuity of subtraction.
-/
theorem subtract_preserves_congr (L : ℕ) (τ₁ τ₂ σ₁ σ₂ : DirectLimitSpace b)
    (hτ₁σ₁ : decode b σ₁ ≤ decode b τ₁)
    (hτ₂σ₂ : decode b σ₂ ≤ decode b τ₂)
    (h_τ_congr : decode b τ₁ % placeValue b L = decode b τ₂ % placeValue b L)
    (h_σ_congr : decode b σ₁ % placeValue b L = decode b σ₂ % placeValue b L) :
    decode b (subtract b τ₁ σ₁ hτ₁σ₁) % placeValue b L =
    decode b (subtract b τ₂ σ₂ hτ₂σ₂) % placeValue b L := by
  repeat rw [subtract_decode_correct]
  exact Nat.sub_mod_eq_of_mod_eq _ _ _ _ _ hτ₁σ₁ hτ₂σ₂ h_τ_congr h_σ_congr

/--
**Prefix Agreement Preservation (Left)**: If the first L digits of τ and τ' agree,
then the first L digits of (τ ⊖ σ) and (τ' ⊖ σ) also agree.
-/
theorem subtract_preserves_prefix_left (L : ℕ) (τ τ' σ : DirectLimitSpace b)
    (hτσ : decode b σ ≤ decode b τ)
    (hτ'σ : decode b σ ≤ decode b τ')
    (h : decode b τ % placeValue b L = decode b τ' % placeValue b L) :
    decode b (subtract b τ σ hτσ) % placeValue b L =
    decode b (subtract b τ' σ hτ'σ) % placeValue b L :=
  subtract_preserves_congr L τ τ' σ σ hτσ hτ'σ h rfl

/--
**Prefix Agreement Preservation (Right)**: If the first L digits of σ and σ' agree,
then the first L digits of (τ ⊖ σ) and (τ ⊖ σ') also agree.
-/
theorem subtract_preserves_prefix_right (L : ℕ) (τ σ σ' : DirectLimitSpace b)
    (hτσ : decode b σ ≤ decode b τ)
    (hτσ' : decode b σ' ≤ decode b τ)
    (h : decode b σ % placeValue b L = decode b σ' % placeValue b L) :
    decode b (subtract b τ σ hτσ) % placeValue b L =
    decode b (subtract b τ σ' hτσ') % placeValue b L :=
  subtract_preserves_congr L τ τ σ σ' hτσ hτσ' rfl h

/-!
## Finite Dependence

The first L digits of (τ ⊖ σ) depend only on the first L digits of τ and σ.
-/

/--
**Finite Dependence Statement**: The first L digits of subtraction
depend only on the first L digits of both inputs.

This means subtraction is a "block-constant" operation at each resolution level.
-/
theorem subtract_finite_dependence (L : ℕ) (τ₁ τ₂ σ₁ σ₂ : DirectLimitSpace b)
    (hτ₁σ₁ : decode b σ₁ ≤ decode b τ₁)
    (hτ₂σ₂ : decode b σ₂ ≤ decode b τ₂)
    (h_τ : decode b τ₁ % placeValue b L = decode b τ₂ % placeValue b L)
    (h_σ : decode b σ₁ % placeValue b L = decode b σ₂ % placeValue b L) :
    decode b (subtract b τ₁ σ₁ hτ₁σ₁) % placeValue b L =
    decode b (subtract b τ₂ σ₂ hτ₂σ₂) % placeValue b L :=
  subtract_preserves_congr L τ₁ τ₂ σ₁ σ₂ hτ₁σ₁ hτ₂σ₂ h_τ h_σ

/--
**Continuity Bridge Lemma**: Version for the topology specialist.

This is exactly what's needed to show subtraction is continuous (1-Lipschitz)
in each argument in the ultrametric topology.
-/
theorem subtract_locality_for_continuity (L : ℕ) (τ₁ τ₂ σ₁ σ₂ : DirectLimitSpace b)
    (hτ₁σ₁ : decode b σ₁ ≤ decode b τ₁)
    (hτ₂σ₂ : decode b σ₂ ≤ decode b τ₂) :
    decode b τ₁ % placeValue b L = decode b τ₂ % placeValue b L →
    decode b σ₁ % placeValue b L = decode b σ₂ % placeValue b L →
    decode b (subtract b τ₁ σ₁ hτ₁σ₁) % placeValue b L =
    decode b (subtract b τ₂ σ₂ hτ₂σ₂) % placeValue b L :=
  fun h_τ h_σ => subtract_preserves_congr L τ₁ τ₂ σ₁ σ₂ hτ₁σ₁ hτ₂σ₂ h_τ h_σ

/-!
## Connection to Predecessor

Subtraction by 1 is predecessor.
-/

/--
Locality of "subtract by 1" reduces to locality of predecessor.
-/
theorem subtract_one_locality (L : ℕ) (τ σ : DirectLimitSpace b)
    (hτ : 1 ≤ decode b τ) (hσ : 1 ≤ decode b σ)
    (h : decode b τ % placeValue b L = decode b σ % placeValue b L) :
    decode b (subtract b τ (encode b 1) (by rw [decode_encode]; exact hτ)) % placeValue b L =
    decode b (subtract b σ (encode b 1) (by rw [decode_encode]; exact hσ)) % placeValue b L := by
  rw [subtract_one_eq_predecessor b τ hτ, subtract_one_eq_predecessor b σ hσ]
  -- Use the nonzero variant since hτ and hσ guarantee τ, σ ≠ 0
  have hτ_ne : decode b τ ≠ 0 := Nat.one_le_iff_ne_zero.mp hτ
  have hσ_ne : decode b σ ≠ 0 := Nat.one_le_iff_ne_zero.mp hσ
  exact Predecessor.predecessor_preserves_congr_of_ne_zero L τ σ hτ_ne hσ_ne h

end FdrsFormal.Operations.Subtraction
