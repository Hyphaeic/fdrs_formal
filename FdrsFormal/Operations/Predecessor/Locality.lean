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

# Locality of Predecessor

This file proves locality properties of the predecessor operator:
operations preserve prefix agreement and satisfy finite dependence.

These lemmas support future continuity proofs (Propositions 4.3, 4.4 in fdrs.md).

## References

- fdrs.md, Phase 1 Fragment 2, Section 4 (lines 468-476)
-/

import FdrsFormal.Operations.Predecessor.Correctness

namespace FdrsFormal.Operations.Predecessor

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite FdrsFormal.Core.Infinite

variable {b : RadixSeq}

/-!
## Congruence Preservation

The key to locality: predecessor preserves congruences modulo place values.
-/

/--
**Predecessor Preserves Congruence (Nonzero Variant)**:
Clean version for nonzero inputs - no edge cases!

If τ and σ are both nonzero and agree mod B_L, then their predecessors agree mod B_L.
This is the version that's actually useful for continuity proofs.
-/
theorem predecessor_preserves_congr_of_ne_zero (L : ℕ) (τ σ : DirectLimitSpace b)
    (hτ : decode b τ ≠ 0) (hσ : decode b σ ≠ 0)
    (h_congr : decode b τ % placeValue b L = decode b σ % placeValue b L) :
    decode b (predecessor b τ) % placeValue b L = decode b (predecessor b σ) % placeValue b L := by
  rw [predecessor_decode_correct b τ hτ, predecessor_decode_correct b σ hσ]
  have hτ_pos : decode b τ ≥ 1 := Nat.one_le_iff_ne_zero.mpr hτ
  have hσ_pos : decode b σ ≥ 1 := Nat.one_le_iff_ne_zero.mpr hσ
  -- Key lemma: If a ≡ b (mod n) and both a, b ≥ 1, then (a - 1) ≡ (b - 1) (mod n)
  set a := decode b τ with ha_def
  set c := decode b σ with hc_def
  set n := placeValue b L with hn_def
  -- n > 0 by placeValue.pos
  have hn_pos : n > 0 := placeValue.pos L
  -- Use the key modular arithmetic fact
  have h_mod_sub : ∀ x : ℕ, x ≥ 1 → (x - 1) % n = if x % n = 0 then n - 1 else x % n - 1 := by
    intro x hx
    split_ifs with h
    · -- x % n = 0: x is a multiple of n, x ≥ 1 means x ≥ n
      have h_xn : x ≥ n := Nat.le_of_dvd hx (Nat.dvd_of_mod_eq_zero h)
      have h_exists : ∃ k : ℕ, k ≥ 1 ∧ x = k * n := by
        use x / n
        constructor
        · exact Nat.one_le_div_iff hn_pos |>.mpr h_xn
        · rw [Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)]
      obtain ⟨k, hk_pos, hk_eq⟩ := h_exists
      -- k * n - 1 = (n - 1) + (k - 1) * n when k ≥ 1
      have h_rewrite : k * n - 1 = (n - 1) + (k - 1) * n := by
        have hk_ge : k ≥ 1 := hk_pos
        have hkn_ge : k * n ≥ n := Nat.le_mul_of_pos_left n hk_pos
        calc k * n - 1
          _ = (k - 1 + 1) * n - 1 := by rw [Nat.sub_add_cancel hk_ge]
          _ = (k - 1) * n + n - 1 := by ring_nf
          _ = (n - 1) + (k - 1) * n := by omega
      calc (x - 1) % n
        _ = (k * n - 1) % n := by rw [hk_eq]
        _ = ((n - 1) + (k - 1) * n) % n := by rw [h_rewrite]
        _ = (n - 1) % n := Nat.add_mul_mod_self_right (n - 1) (k - 1) n
        _ = n - 1 := Nat.mod_eq_of_lt (Nat.sub_lt hn_pos Nat.one_pos)
    · -- x % n ≠ 0: remainder is positive
      have h_rem_pos : x % n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
      have h_decomp : x = x % n + n * (x / n) := (Nat.mod_add_div x n).symm
      -- Rewrite: x % n + n * (x / n) - 1 = (x % n - 1) + (x / n) * n
      have h_rearrange : x % n + n * (x / n) - 1 = (x % n - 1) + (x / n) * n := by
        -- Use commutativity and associativity
        rw [mul_comm n (x / n)]
        -- Now: x % n + (x / n) * n - 1 = (x % n - 1) + (x / n) * n
        -- Since x % n ≥ 1, we have x % n - 1 + 1 = x % n
        have h_sub_add : x % n - 1 + 1 = x % n := Nat.sub_add_cancel h_rem_pos
        calc x % n + (x / n) * n - 1
          _ = (x % n - 1 + 1) + (x / n) * n - 1 := by rw [h_sub_add]
          _ = (x % n - 1) + 1 + (x / n) * n - 1 := by ring_nf
          _ = (x % n - 1) + (x / n) * n := by omega
      calc (x - 1) % n
        _ = (x % n + n * (x / n) - 1) % n := by rw [← h_decomp]
        _ = ((x % n - 1) + (x / n) * n) % n := by rw [h_rearrange]
        _ = (x % n - 1) % n := Nat.add_mul_mod_self_right (x % n - 1) (x / n) n
        _ = x % n - 1 := Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.sub_lt h_rem_pos Nat.one_pos)
                                                             (Nat.mod_lt x hn_pos).le)
  -- Apply to both a and c
  rw [h_mod_sub a hτ_pos, h_mod_sub c hσ_pos]
  -- Now just case split on whether the remainder is 0
  simp only [h_congr]

/--
**Key Locality Lemma**: If τ ≡ σ (mod B_L), then pred(τ) ≡ pred(σ) (mod B_L)

This is the foundation for continuity: operations that preserve congruences
preserve prefixes (cylinder sets).

**Note**: This additionally requires `h_zero_iff` to ensure the mixed case
(one zero, one nonzero multiple of B_L) is excluded. The reason: predecessor
at 0 returns 0, but pred(B_L) = B_L - 1 ≢ 0 (mod B_L).
Thus predecessor has a "wrap-around" discontinuity at multiples of B_L when starting from 0.
-/
theorem predecessor_preserves_congr (L : ℕ) (τ σ : DirectLimitSpace b)
    (h_congr : decode b τ % placeValue b L = decode b σ % placeValue b L)
    (h_zero_iff : decode b τ = 0 ↔ decode b σ = 0) :
    decode b (predecessor b τ) % placeValue b L = decode b (predecessor b σ) % placeValue b L := by
  -- Case analysis on whether τ and σ decode to zero
  by_cases hτ : decode b τ = 0
  · -- τ zero implies σ zero by h_zero_iff
    have hσ : decode b σ = 0 := h_zero_iff.mp hτ
    simp only [predecessor, hτ, hσ, Nat.pred_zero, decode_encode]
  · -- τ nonzero implies σ nonzero by h_zero_iff
    have hσ : decode b σ ≠ 0 := fun h => hτ (h_zero_iff.mpr h)
    exact predecessor_preserves_congr_of_ne_zero L τ σ hτ hσ h_congr

/--
**Prefix Agreement Preservation**: If the first L digits of τ and σ agree,
then the first L digits of pred(τ) and pred(σ) also agree.

This is stated via decode + congruence, which is equivalent to digit agreement
by the prefix-congruence theorem (Proposition 6 in fdrs.md).

Note: Requires both τ and σ to be nonzero.
-/
theorem predecessor_preserves_prefix (L : ℕ) (τ σ : DirectLimitSpace b)
    (hτ : decode b τ ≠ 0) (hσ : decode b σ ≠ 0)
    (h : decode b τ % placeValue b L = decode b σ % placeValue b L) :
    decode b (predecessor b τ) % placeValue b L = decode b (predecessor b σ) % placeValue b L :=
  predecessor_preserves_congr_of_ne_zero L τ σ hτ hσ h

/-!
## Finite Dependence

The first L digits of pred(τ) depend only on a finite prefix of τ.
-/

/--
**Finite Dependence Statement**: The first L digits of predecessor
depend only on the first L digits of the input.

This means predecessor is a "block-constant" operation at each resolution level.

Note: Requires both τ and σ to be nonzero.
-/
theorem predecessor_finite_dependence (L : ℕ) (τ σ : DirectLimitSpace b)
    (hτ : decode b τ ≠ 0) (hσ : decode b σ ≠ 0)
    (h : decode b τ % placeValue b L = decode b σ % placeValue b L) :
    decode b (predecessor b τ) % placeValue b L = decode b (predecessor b σ) % placeValue b L :=
  predecessor_preserves_prefix L τ σ hτ hσ h

/--
**Continuity Bridge Lemma**: Version for the topology specialist.

If τ and σ agree on first L digits (measured via congruence),
then pred(τ) and pred(σ) agree on first L digits.

This is exactly what's needed to show pred is continuous (1-Lipschitz)
in the ultrametric topology where cylinders correspond to congruence classes.

Note: Requires both τ and σ to be nonzero.
-/
theorem predecessor_locality_for_continuity (L : ℕ) (τ σ : DirectLimitSpace b)
    (hτ : decode b τ ≠ 0) (hσ : decode b σ ≠ 0) :
    decode b τ % placeValue b L = decode b σ % placeValue b L →
    decode b (predecessor b τ) % placeValue b L = decode b (predecessor b σ) % placeValue b L :=
  predecessor_preserves_congr_of_ne_zero L τ σ hτ hσ

end FdrsFormal.Operations.Predecessor
