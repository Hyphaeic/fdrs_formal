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

# Multiplication on a mixed schedule: residues and carry lines (Phase 1 addendum, §3.7)

On a variable schedule the positional chart does not turn multiplication into a
convolution (Corollary 39). The residue chart does better: for pairwise-coprime
radices it makes multiplication **carry-free** — digitwise — and moves every carry
into the change of chart. Both changes of chart are triangular: residue `i` of the
positional digits reads digits `0, …, i` only, and Garner's inverse produces
positional digit `i` from residue `i` and the *carry line* into position `i` — the
value accumulated by the digits below.

- **Definition 224** (`vMul`, `garnerAcc`, `garnerDigit`, `garner`): digitwise product,
  Garner's accumulated carry line `V_i = Σ_{l<i} g_l B_l`, and Garner's digits
  `g_i = (r_i − V_i) · B_i^{-1} mod b_i`.
- **Proposition 169** (`crtChart_mul`): on every schedule the residue chart is
  multiplicative.
- **Proposition 170** (`crtChart_decode`): the chart from positional to residue
  digits is triangular: `dec x ≡ Σ_{l ≤ i} x_l B_l (mod b_i)`.
- **Theorem 136** (`crtChart_garner`, `garner_crtChart`): for pairwise-coprime
  radices, Garner's digits are the positional digits of the CRT solution — Garner
  inverts the residue chart, triangularly.
- **Corollary 46** (`mul_via_residues`): mixed-radix multiplication on a coprime
  schedule: `garner(ρ(dec x) · ρ(dec y)) = enc((dec x · dec y) mod N)`, and the full
  product when it is below `N`.

**Honest scope.** Classical (residue number systems; Garner 1959, mixed-radix
conversion). The corpus contributes the statements on its two charts of one
schedule and the triangular (carry-line) reading. No cost is claimed.
-/

import FdrsFormal.NumberTheory.Characters.ResidueConvolution

namespace FdrsFormal.NumberTheory.Characters.MixedRadixFFT

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite

variable {b : RadixSeq}

/-! ## Definition 224 and Proposition 169: the carry-free product -/

/-- Digitwise product, `(τ · σ)_i = τ_i σ_i mod b_i`.

**fdrs.md**: Definition 224 (residue product and Garner's carry lines). -/
def vMul {k : ℕ} (τ σ : FiniteRadixSpace b k) : FiniteRadixSpace b k :=
  fun i => ⟨((τ i : ℕ) * σ i) % b i, Nat.mod_lt _ (b.pos i)⟩

/-- **Proposition 169 (the residue chart is multiplicative).** On every schedule,
`ρ(n · m) = ρ(n) · ρ(m)` digitwise.

**fdrs.md**: Proposition 169 (the residue chart is multiplicative). -/
theorem crtChart_mul (k n m : ℕ) :
    crtChart b k (n * m) = vMul (crtChart b k n) (crtChart b k m) := by
  funext i
  exact Fin.ext (by simp [crtChart, vMul, Nat.mul_mod])

theorem crtChart_mod (k n : ℕ) :
    crtChart b k (n % placeValue b (k + 1)) = crtChart b k n := by
  funext i
  apply Fin.ext
  simp only [crtChart]
  exact Nat.mod_mod_of_dvd _ ⟨coBlock b k i, (mul_coBlock k i).symm⟩

/-! ## Proposition 170: positional to residue is triangular -/

theorem radix_dvd_placeValue {l i : ℕ} (h : l < i) : b l ∣ placeValue b i :=
  (Dvd.intro_left _ (placeValue.succ l).symm).trans (placeValue.dvd_of_le h)

/-- **Proposition 170 (the forward chart is triangular).** Residue `i` of a positional
digit vector reads only digits `0, …, i`: higher place values vanish mod `b_i`.

**fdrs.md**: Proposition 170 (both changes of chart are triangular). -/
theorem crtChart_decode {k : ℕ} (x : FiniteRadixSpace b k) (i : Fin (k + 1)) :
    ((decodeFinite b k x : ℕ) : ZMod (b i)) =
      ∑ l : Fin (k + 1), if (l : ℕ) ≤ i then (((x l : ℕ) * placeValue b l : ℕ) : ZMod (b i))
        else 0 := by
  simp only [decodeFinite]
  push_cast
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs with h
  · rfl
  · rw [(ZMod.natCast_eq_zero_iff _ _).mpr (radix_dvd_placeValue (by omega)), mul_zero]

/-! ## Definition 224: Garner's carry lines -/

/-- Garner's digit at position `i`, given the carry line `V` into it:
`((r_i − V) · B_i^{-1}) mod b_i`. -/
noncomputable def garnerStep {k : ℕ} (r : FiniteRadixSpace b k) (i V : ℕ) : ℕ :=
  if h : i < k + 1 then
    (((r ⟨i, h⟩ : ℕ) - (V : ZMod (b i))) * ((placeValue b i : ZMod (b i))⁻¹)).val
  else 0

/-- The carry line into position `i`: `V_i = Σ_{l<i} g_l B_l`, accumulated digit by
digit.

**fdrs.md**: Definition 224 (residue product and Garner's carry lines). -/
noncomputable def garnerAcc {k : ℕ} (r : FiniteRadixSpace b k) : ℕ → ℕ
  | 0 => 0
  | i + 1 => garnerAcc r i + garnerStep r i (garnerAcc r i) * placeValue b i

noncomputable def garnerDigit {k : ℕ} (r : FiniteRadixSpace b k) (i : ℕ) : ℕ :=
  garnerStep r i (garnerAcc r i)

theorem garnerDigit_lt {k : ℕ} (r : FiniteRadixSpace b k) (i : ℕ) :
    garnerDigit r i < b i := by
  unfold garnerDigit garnerStep
  split_ifs
  · haveI : NeZero (b i) := ⟨b.ne_zero i⟩
    exact ZMod.val_lt _
  · exact b.pos i

/-- Garner's positional digits.

**fdrs.md**: Definition 224 (residue product and Garner's carry lines). -/
noncomputable def garner {k : ℕ} (r : FiniteRadixSpace b k) : FiniteRadixSpace b k :=
  fun i => ⟨garnerDigit r i, garnerDigit_lt r i⟩

/-! ## Theorem 136: Garner inverts the residue chart -/

theorem placeValue_coprime {k : ℕ} (h : PairwiseCoprimeRadices b k) {i : ℕ} (hi : i < k + 1) :
    Nat.Coprime (placeValue b i) (b i) := by
  rw [placeValue_eq_prod_range]
  exact Nat.Coprime.prod_left fun l hl => by
    have hl' : l < i := Finset.mem_range.mp hl
    exact h (i := ⟨l, by omega⟩) (j := ⟨i, hi⟩) (by simp [Fin.ext_iff]; omega)

theorem garnerAcc_succ_eq {k : ℕ} (r : FiniteRadixSpace b k) (i : ℕ) :
    garnerAcc r (i + 1) = garnerAcc r i + garnerDigit r i * placeValue b i := rfl

/-- The carry line hits every residue below it. -/
theorem garnerAcc_mod {k : ℕ} (h : PairwiseCoprimeRadices b k) (r : FiniteRadixSpace b k) :
    ∀ i, i ≤ k + 1 → ∀ l : Fin (k + 1), (l : ℕ) < i →
      ((garnerAcc r i : ℕ) : ZMod (b l)) = ((r l : ℕ) : ZMod (b l))
  | 0, _, l, hl => absurd hl (Nat.not_lt_zero _)
  | i + 1, hi, l, hl => by
    rw [garnerAcc_succ_eq]
    push_cast
    rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hlt | heq
    · rw [garnerAcc_mod h r i (by omega) l hlt,
        (ZMod.natCast_eq_zero_iff _ _).mpr (radix_dvd_placeValue hlt), mul_zero, add_zero]
    · -- the new digit closes residue `i`
      have hli : (l : ℕ) = i := heq
      have hik : i < k + 1 := by omega
      haveI : NeZero (b i) := ⟨b.ne_zero i⟩
      have hunit : ((placeValue b i : ℕ) : ZMod (b i)) * ((placeValue b i : ℕ) : ZMod (b i))⁻¹ = 1 :=
        ZMod.mul_inv_of_unit _ (ZMod.unitOfCoprime _ (placeValue_coprime h hik)).isUnit
      have hl' : l = ⟨i, hik⟩ := Fin.ext hli
      subst hl'
      simp only [garnerDigit, garnerStep, dif_pos hik, ZMod.natCast_val, ZMod.cast_id', id]
      calc ((garnerAcc r i : ℕ) : ZMod (b i)) +
            ((r ⟨i, hik⟩ : ℕ) - (garnerAcc r i : ZMod (b i))) *
              ((placeValue b i : ZMod (b i)))⁻¹ * (placeValue b i : ZMod (b i))
          = ((garnerAcc r i : ℕ) : ZMod (b i)) +
            ((r ⟨i, hik⟩ : ℕ) - (garnerAcc r i : ZMod (b i))) *
              (((placeValue b i : ℕ) : ZMod (b i)) * ((placeValue b i : ℕ) : ZMod (b i))⁻¹) := by
            ring
        _ = _ := by rw [hunit]; ring

theorem decodeFinite_garner {k : ℕ} (r : FiniteRadixSpace b k) :
    decodeFinite b k (garner r) = garnerAcc r (k + 1) := by
  rw [decodeFinite]
  simp only [garner]
  rw [Fin.sum_univ_eq_sum_range (fun i => garnerDigit r i * placeValue b i)]
  generalize k + 1 = n
  induction n with
  | zero => rfl
  | succ n ih => rw [Finset.sum_range_succ, ih, garnerAcc_succ_eq]

/-- **Theorem 136 (Garner inverts the residue chart).** For pairwise-coprime radices,
the positional digits produced by Garner's carry lines have residues `r`.

**fdrs.md**: Theorem 136 (Garner's carry lines invert the residue chart). -/
theorem crtChart_garner {k : ℕ} (h : PairwiseCoprimeRadices b k) (r : FiniteRadixSpace b k) :
    crtChart b k (decodeFinite b k (garner r)) = r := by
  funext l
  apply Fin.ext
  simp only [crtChart]
  rw [decodeFinite_garner]
  have := garnerAcc_mod h r (k + 1) le_rfl l l.isLt
  rw [ZMod.natCast_eq_natCast_iff'] at this
  rw [this, Nat.mod_eq_of_lt (r l).isLt]

/-- **Theorem 136 (both directions).** Garner recovers the positional digits from
their residues: `garner(ρ(dec x)) = x`.

**fdrs.md**: Theorem 136 (Garner's carry lines invert the residue chart). -/
theorem garner_crtChart {k : ℕ} (h : PairwiseCoprimeRadices b k) (x : FiniteRadixSpace b k) :
    garner (crtChart b k (decodeFinite b k x)) = x := by
  have hinj := crtChartFin_injective (b := b) k h
  have hdec : decodeFinite b k (garner (crtChart b k (decodeFinite b k x))) =
      decodeFinite b k x := by
    have := @hinj ⟨_, decodeFinite_lt k (garner (crtChart b k (decodeFinite b k x)))⟩
      ⟨_, decodeFinite_lt k x⟩ (crtChart_garner h _)
    exact congrArg Fin.val this
  exact digits_unique _ _ hdec

/-! ## Corollary 46: multiplication through residues -/

/-- **Corollary 46 (mixed-radix multiplication through residues).** On a
pairwise-coprime schedule, multiply digitwise in the residue chart and return through
Garner's carry lines: the result is the positional encoding of `dec x · dec y mod N`.

**fdrs.md**: Corollary 46 (multiplication through residues). -/
theorem mul_via_residues {k : ℕ} (h : PairwiseCoprimeRadices b k) (x y : FiniteRadixSpace b k) :
    decodeFinite b k
        (garner (vMul (crtChart b k (decodeFinite b k x)) (crtChart b k (decodeFinite b k y)))) =
      (decodeFinite b k x * decodeFinite b k y) % placeValue b (k + 1) := by
  have hinj := crtChartFin_injective (b := b) k h
  set r := vMul (crtChart b k (decodeFinite b k x)) (crtChart b k (decodeFinite b k y))
  have h1 : crtChart b k (decodeFinite b k (garner r)) =
      crtChart b k ((decodeFinite b k x * decodeFinite b k y) % placeValue b (k + 1)) := by
    rw [crtChart_garner h, crtChart_mod, crtChart_mul]
  have := @hinj ⟨_, decodeFinite_lt k (garner r)⟩
    ⟨_, Nat.mod_lt _ (placeValue.pos (k + 1))⟩ h1
  exact congrArg Fin.val this

/-- **Corollary 46 (the full product).** When the product fits below `N = B_{k+1}`,
multiplication through residues returns it exactly.

**fdrs.md**: Corollary 46 (multiplication through residues). -/
theorem mul_via_residues_exact {k : ℕ} (h : PairwiseCoprimeRadices b k)
    (x y : FiniteRadixSpace b k)
    (hfit : decodeFinite b k x * decodeFinite b k y < placeValue b (k + 1)) :
    decodeFinite b k
        (garner (vMul (crtChart b k (decodeFinite b k x)) (crtChart b k (decodeFinite b k y)))) =
      decodeFinite b k x * decodeFinite b k y := by
  rw [mul_via_residues h, Nat.mod_eq_of_lt hfit]

end FdrsFormal.NumberTheory.Characters.MixedRadixFFT
