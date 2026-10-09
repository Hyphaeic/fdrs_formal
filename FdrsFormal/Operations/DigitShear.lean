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

# Address shears and digit interchange (Phase 1 addendum, §3.6)

Interchanging two address fields of an array is the data movement at the heart of
OpenAI family 109: it is done there not by moving data but by three *shears*
`(H, D) ↦ (H + D, D)` over a residue ring. In FDRS a field of `u` bits is a single
digit of radix `2^u`, so a field interchange is a swap of two equal-radix digits of
`𝓡^{(k)}`.

- **Definition 222** (`shear`, `unshear`, `negDigit`, `swapDigits`): the shear
  `τ_i ← τ_i + τ_j`, its inverse, digit negation, and the swap of two digits of equal
  radix.
- **Proposition 167** (`unshear_shear`, `shear_unshear`, `swap_eq_shears`): shears are
  bijections of `𝓡^{(k)}`, and the swap is three shears followed by one negation:
  `(u, v) ↦ (u + v, v) ↦ (u + v, −u) ↦ (v, −u) ↦ (v, u)`.
- **Proposition 168** (`decodeFinite_update`, `decodeFinite_swapDigits`): the address
  displacement of a swap, `dec(swap τ) = dec τ + (τ_j − τ_i)(B_i − B_j)`.

**Honest scope.** Classical (the three-shear factorisation of a transposition). The
corpus contributes the statements on its digit charts. The cost claims of family 109
(sub-linear tape interchange) are not formalized.
-/

import FdrsFormal.Core.Finite

namespace FdrsFormal.Operations.DigitShear

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite

variable {b : RadixSeq} {k : ℕ}

/-! ## Definition 222 -/

/-- The shear `τ_i ← τ_i + τ_j (mod b_i)`; all other digits unchanged.

**fdrs.md**: Definition 222 (address shears and digit swap). -/
def shear (i j : Fin (k + 1)) (τ : FiniteRadixSpace b k) : FiniteRadixSpace b k :=
  Function.update τ i ⟨((τ i : ℕ) + τ j) % b i, Nat.mod_lt _ (b.pos i)⟩

/-- The inverse shear `τ_i ← τ_i − τ_j (mod b_i)`. -/
def unshear (i j : Fin (k + 1)) (τ : FiniteRadixSpace b k) : FiniteRadixSpace b k :=
  Function.update τ i ⟨((τ i : ℕ) + (b i - (τ j : ℕ) % b i)) % b i, Nat.mod_lt _ (b.pos i)⟩

/-- Digit negation `τ_j ← −τ_j (mod b_j)` — a digit permutation (Definition 37). -/
def negDigit (j : Fin (k + 1)) (τ : FiniteRadixSpace b k) : FiniteRadixSpace b k :=
  Function.update τ j ⟨(b j - τ j) % b j, Nat.mod_lt _ (b.pos j)⟩

/-- The swap of two digits of equal radix.

**fdrs.md**: Definition 222 (address shears and digit swap). -/
def swapDigits (i j : Fin (k + 1)) (h : b i = b j) (τ : FiniteRadixSpace b k) :
    FiniteRadixSpace b k :=
  Function.update (Function.update τ i ⟨τ j, by rw [h]; exact (τ j).isLt⟩) j
    ⟨τ i, by rw [← h]; exact (τ i).isLt⟩

/-! ## Proposition 167: shears are bijections; a swap is three shears -/

/-- A residue identity `a mod q = c` (for `c < q`) can be checked in `ℤ/q`. -/
theorem mod_eq_of_zmod {q a c : ℕ} (hc : c < q) (h : (a : ZMod q) = c) : a % q = c := by
  have := (ZMod.natCast_eq_natCast_iff' a c q).mp h
  rwa [Nat.mod_eq_of_lt hc] at this

theorem unshear_shear {i j : Fin (k + 1)} (hij : i ≠ j) (τ : FiniteRadixSpace b k) :
    unshear i j (shear i j τ) = τ := by
  funext l
  rcases eq_or_ne l i with rfl | hl
  · apply Fin.ext
    simp only [unshear, shear, Function.update_self, Function.update_of_ne hij.symm]
    have hu := (τ l).isLt
    generalize (τ l : ℕ) = u at *
    generalize (τ j : ℕ) = v
    have h1 : v % b l ≤ b l := (Nat.mod_lt _ (b.pos l)).le
    apply mod_eq_of_zmod hu
    push_cast [ZMod.natCast_mod, Nat.cast_sub h1, ZMod.natCast_self]
    ring
  · simp only [unshear, shear, Function.update_of_ne hl]

theorem shear_unshear {i j : Fin (k + 1)} (hij : i ≠ j) (τ : FiniteRadixSpace b k) :
    shear i j (unshear i j τ) = τ := by
  funext l
  rcases eq_or_ne l i with rfl | hl
  · apply Fin.ext
    simp only [unshear, shear, Function.update_self, Function.update_of_ne hij.symm]
    have hu := (τ l).isLt
    generalize (τ l : ℕ) = u at *
    generalize (τ j : ℕ) = v
    have h1 : v % b l ≤ b l := (Nat.mod_lt _ (b.pos l)).le
    apply mod_eq_of_zmod hu
    push_cast [ZMod.natCast_mod, Nat.cast_sub h1, ZMod.natCast_self]
    ring

  · simp only [unshear, shear, Function.update_of_ne hl]

/-- A shear is a bijection of `𝓡^{(k)}`. -/
theorem shear_bijective {i j : Fin (k + 1)} (hij : i ≠ j) :
    Function.Bijective (shear (b := b) i j) :=
  ⟨Function.LeftInverse.injective (unshear_shear hij),
    Function.RightInverse.surjective (shear_unshear hij)⟩

/-- **Proposition 167 (a swap is three shears).** For `i ≠ j` with `b_i = b_j`:
`swap_{ij} = neg_j ∘ sh_{i←j} ∘ sh⁻¹_{j←i} ∘ sh_{i←j}`, i.e.
`(u, v) ↦ (u + v, v) ↦ (u + v, −u) ↦ (v, −u) ↦ (v, u)`.

**fdrs.md**: Proposition 167 (a swap is three shears). -/
theorem swap_eq_shears {i j : Fin (k + 1)} (hij : i ≠ j) (h : b i = b j)
    (τ : FiniteRadixSpace b k) :
    swapDigits i j h τ = negDigit j (shear i j (unshear j i (shear i j τ))) := by
  funext l
  rcases eq_or_ne l i with rfl | hli
  · apply Fin.ext
    simp only [swapDigits, negDigit, shear, unshear, Function.update_of_ne hij,
      Function.update_self, Function.update_of_ne hij.symm]
    have hu := (τ l).isLt
    have hv := (τ j).isLt
    generalize (τ l : ℕ) = u at *
    generalize (τ j : ℕ) = v at *
    rw [← h] at hv ⊢
    have h1 : (u + v) % b l % b l ≤ b l := (Nat.mod_lt _ (b.pos l)).le
    symm; apply mod_eq_of_zmod hv
    push_cast [ZMod.natCast_mod, Nat.cast_sub h1, ZMod.natCast_self]
    ring
  · rcases eq_or_ne l j with rfl | hlj
    · apply Fin.ext
      simp only [swapDigits, negDigit, shear, unshear, Function.update_self,
        Function.update_of_ne hij, Function.update_of_ne hij.symm]
      have hu := (τ i).isLt
      have hv := (τ l).isLt
      generalize (τ i : ℕ) = u at *
      generalize (τ l : ℕ) = v at *
      rw [← h] at hv ⊢
      have h1 : (u + v) % b i % b i ≤ b i := (Nat.mod_lt _ (b.pos i)).le
      have h2 : (v + (b i - (u + v) % b i % b i)) % b i ≤ b i := (Nat.mod_lt _ (b.pos i)).le
      symm; apply mod_eq_of_zmod hu
      push_cast [ZMod.natCast_mod, Nat.cast_sub h1, Nat.cast_sub h2, ZMod.natCast_self]
      ring
    · simp only [swapDigits, negDigit, shear, unshear, Function.update_of_ne hli,
        Function.update_of_ne hlj]

/-! ## Proposition 168: the address displacement of a swap -/

/-- Changing one digit moves the address by `(v − τ_i) B_i`. -/
theorem decodeFinite_update (τ : FiniteRadixSpace b k) (i : Fin (k + 1)) (v : Fin (b i)) :
    (decodeFinite b k (Function.update τ i v) : ℤ) =
      decodeFinite b k τ + ((v : ℤ) - (τ i : ℕ)) * placeValue b i := by
  simp only [decodeFinite]
  push_cast
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hrest : ∑ l ∈ Finset.univ.erase i,
      ((Function.update τ i v l : ℕ) : ℤ) * (placeValue b l : ℤ) =
      ∑ l ∈ Finset.univ.erase i, ((τ l : ℕ) : ℤ) * (placeValue b l : ℤ) :=
    Finset.sum_congr rfl fun l hl => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  rw [hrest, Function.update_self]
  ring

/-- **Proposition 168 (the address displacement of a swap).** For `i ≠ j` with
`b_i = b_j`: `dec(swap τ) = dec τ + (τ_j − τ_i)(B_i − B_j)`.

**fdrs.md**: Proposition 168 (the address displacement of a swap). -/
theorem decodeFinite_swapDigits {i j : Fin (k + 1)} (hij : i ≠ j) (h : b i = b j)
    (τ : FiniteRadixSpace b k) :
    (decodeFinite b k (swapDigits i j h τ) : ℤ) =
      decodeFinite b k τ + ((τ j : ℕ) - (τ i : ℕ) : ℤ) * (placeValue b i - placeValue b j) := by
  rw [swapDigits, decodeFinite_update, decodeFinite_update,
    Function.update_of_ne hij.symm]
  ring

end FdrsFormal.Operations.DigitShear
