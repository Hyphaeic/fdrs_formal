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

# The Good–Thomas chart: a twist-free Fourier chart (Phase 3 addendum, §1.6)

Proposition 154 showed the positional chart always twists `ℤ/B` against its
digit groups once there are two digits. This file shows the twist belongs to the
*chart*, not the group, exactly when the radices are pairwise coprime.

- **Definition 215** (`crtChart`, `coBlock`, `ruritanian`): the residue chart
  `n ↦ (n mod b_i)_i` and Good's output chart `σ ↦ Σ_i σ_i · ∏_{l ≠ i} b_l`.
- **Theorem 121** (`zeta_pow_ruritanian_mul`): for **every** schedule,
  `ζ_N^{rur σ · n} = V(crt n, σ)` — the Vilenkin kernel exactly, no twiddles.
- **Theorem 122** (`crtChart_bijective_iff`): the residue chart is a bijection
  `ℤ/B_{k+1} ≃ 𝓡^{(k)}` **iff** the radices `b_0, …, b_k` are pairwise
  coprime; under that hypothesis Good's output chart is a bijection too
  (`ruritanianChart_bijective`).
- **Corollary 33** (`dft_goodThomas`): for pairwise-coprime radices the DFT on
  `ℤ/B_{k+1}` *is* the Vilenkin transform of `∏ ℤ/b_i`, re-indexed by the two
  charts.

**Honest scope.** Classical: Good (1958), Thomas (1963); the corpus contributes
the placement next to Proposition 154 — positional chart: twisted on every
multi-digit line; residue chart: untwisted, and a chart at all exactly in the
coprime case.
-/

import FdrsFormal.NumberTheory.Characters.MixedRadixStages
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.RingTheory.Coprime.Lemmas

namespace FdrsFormal.NumberTheory.Characters.MixedRadixFFT

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite

variable {b : RadixSeq}

/-! ## Definition 215: the two charts -/

theorem placeValue_eq_prod_range (m : ℕ) : placeValue b m = ∏ i ∈ Finset.range m, b i := by
  induction m with
  | zero => rfl
  | succ m ih => rw [placeValue.succ, ih, Finset.prod_range_succ]

theorem prod_univ_eq_placeValue (k : ℕ) : ∏ i : Fin (k + 1), b i = placeValue b (k + 1) := by
  rw [placeValue_eq_prod_range, ← Fin.prod_univ_eq_prod_range]

/-- The residue (CRT) chart `n ↦ (n mod b_i)_i`.

**fdrs.md**: Definition 215 (the residue and Good charts). -/
def crtChart (b : RadixSeq) (k n : ℕ) : FiniteRadixSpace b k :=
  fun i => ⟨n % b i, Nat.mod_lt _ (b.pos i)⟩

/-- The complementary block `∏_{l ≠ i} b_l`. -/
def coBlock (b : RadixSeq) (k : ℕ) (i : Fin (k + 1)) : ℕ :=
  ∏ l ∈ Finset.univ.erase i, b l

/-- Good's output chart `σ ↦ Σ_i σ_i · ∏_{l ≠ i} b_l`.

**fdrs.md**: Definition 215 (the residue and Good charts). -/
def ruritanian (b : RadixSeq) (k : ℕ) (σ : FiniteRadixSpace b k) : ℕ :=
  ∑ i : Fin (k + 1), (σ i : ℕ) * coBlock b k i

/-- The radices `b_0, …, b_k` are pairwise coprime. -/
def PairwiseCoprimeRadices (b : RadixSeq) (k : ℕ) : Prop :=
  Pairwise fun i j : Fin (k + 1) => Nat.Coprime (b i) (b j)

theorem coBlock_ne_zero (k : ℕ) (i : Fin (k + 1)) : coBlock b k i ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun l _ => b.ne_zero l

theorem mul_coBlock (k : ℕ) (i : Fin (k + 1)) :
    b i * coBlock b k i = placeValue b (k + 1) := by
  rw [coBlock, Finset.mul_prod_erase Finset.univ (fun l : Fin (k + 1) => b l) (Finset.mem_univ i),
    prod_univ_eq_placeValue]

theorem dvd_coBlock (k : ℕ) {i j : Fin (k + 1)} (h : i ≠ j) : b i ∣ coBlock b k j :=
  Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨h, Finset.mem_univ i⟩)

/-! ## Theorem 121: no twiddles -/

/-- **Theorem 121 (the residue chart is untwisted).** For every schedule, at Good's
output index the Fourier phase is exactly the Vilenkin kernel of the residues.

**fdrs.md**: Theorem 121 (the untwisted phase). -/
theorem zeta_pow_ruritanian_mul (k n : ℕ) (σ : FiniteRadixSpace b k) :
    zeta (placeValue b (k + 1)) ^ (ruritanian b k σ * n) = vilenkinKernel k (crtChart b k n) σ := by
  rw [ruritanian, Finset.sum_mul, ← Finset.prod_pow_eq_pow_sum, vilenkinKernel]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← mul_coBlock k i, show (σ i : ℕ) * coBlock b k i * n = coBlock b k i * ((σ i : ℕ) * n) by
    ring, zeta_mul_pow_mul _ _ _ (b.ne_zero i) (coBlock_ne_zero k i)]
  show zeta (b i) ^ ((σ i : ℕ) * n) = zeta (b i) ^ ((n % b i) * (σ i : ℕ))
  conv_lhs => rw [← Nat.mod_add_div n (b i)]
  rw [mul_add, pow_add, show (σ i : ℕ) * (b i * (n / b i)) = b i * ((σ i : ℕ) * (n / b i)) by ring,
    zeta_pow_self_mul _ _ (b.ne_zero i), mul_one, mul_comm]

/-! ## Theorem 122: the residue chart is a chart iff coprime -/

/-- The residue chart on `ℤ/B_{k+1}`. -/
def crtChartFin (b : RadixSeq) (k : ℕ) (n : Fin (placeValue b (k + 1))) : FiniteRadixSpace b k :=
  crtChart b k n

theorem crtChartFin_injective (k : ℕ)
    (h : PairwiseCoprimeRadices b k) :
    Function.Injective (crtChartFin b k) := by
  intro n n' hnn
  have hmod : ∀ i : Fin (k + 1), (n : ℕ) % b i = (n' : ℕ) % b i := fun i =>
    congrArg Fin.val (congrFun hnn i)
  have hdvd : (∏ i : Fin (k + 1), (b i : ℤ)) ∣ ((n' : ℕ) : ℤ) - (n : ℕ) :=
    Fintype.prod_dvd_of_coprime
      (fun i j hij => Nat.isCoprime_iff_coprime.mpr (h hij))
      fun i => (Nat.modEq_iff_dvd).mp (hmod i)
  have hN : (∏ i : Fin (k + 1), (b i : ℤ)) = (placeValue b (k + 1) : ℤ) := by
    rw [← prod_univ_eq_placeValue]; push_cast; rfl
  rw [hN, ← Nat.modEq_iff_dvd] at hdvd
  exact Fin.ext (hdvd.eq_of_lt_of_lt n.isLt n'.isLt)

/-- Without pairwise coprimality the residue chart collapses: with
`g = gcd(b_i, b_j) > 1`, the nonzero class `N / g` has all residues `0`. -/
theorem crtChartFin_not_injective (k : ℕ)
    (h : ¬ PairwiseCoprimeRadices b k) :
    ¬ Function.Injective (crtChartFin b k) := by
  classical
  simp only [PairwiseCoprimeRadices, Pairwise, not_forall] at h
  obtain ⟨i, j, hij, hnc⟩ := h
  set N := placeValue b (k + 1) with hNdef
  set g := Nat.gcd (b i) (b j) with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (b.pos i)
  have hg1 : 1 < g := by
    have : g ≠ 1 := hnc
    omega
  have hgi : g ∣ b i := Nat.gcd_dvd_left _ _
  have hgj : g ∣ b j := Nat.gcd_dvd_right _ _
  -- N = b_i · b_j · R
  set R := ∏ l ∈ (Finset.univ.erase i).erase j, b l
  have hNR : N = b i * (b j * R) := by
    rw [hNdef, ← prod_univ_eq_placeValue,
      ← Finset.mul_prod_erase Finset.univ (fun l : Fin (k + 1) => b l) (Finset.mem_univ i),
      ← Finset.mul_prod_erase (Finset.univ.erase i) (fun l : Fin (k + 1) => b l)
        (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
  have hNpos : 0 < N := placeValue.pos _
  have hgN : g ≤ N := Nat.le_of_dvd hNpos (hNR ▸ Dvd.dvd.mul_right hgi _)
  have hlt : N / g < N := Nat.div_lt_self hNpos hg1
  have hpos : 0 < N / g := Nat.div_pos hgN hgpos
  -- every radix divides N / g
  have hform1 : N / g = b i * ((b j / g) * R) := by
    rw [hNR, show b j * R = g * ((b j / g) * R) by rw [← mul_assoc, Nat.mul_div_cancel' hgj],
      show b i * (g * (b j / g * R)) = g * (b i * (b j / g * R)) by ring,
      Nat.mul_div_cancel_left _ hgpos]
  have hform2 : N / g = (b i / g) * (b j * R) := by
    rw [hNR, show b i * (b j * R) = g * ((b i / g) * (b j * R)) by
      rw [← mul_assoc g, Nat.mul_div_cancel' hgi], Nat.mul_div_cancel_left _ hgpos]
  have hall : ∀ l : Fin (k + 1), b l ∣ N / g := by
    intro l
    by_cases hli : l = i
    · subst hli; rw [hform1]; exact Dvd.intro _ rfl
    by_cases hlj : l = j
    · subst hlj; rw [hform2]; exact Dvd.dvd.mul_left (Dvd.intro _ rfl) _
    · rw [hform1]
      exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _
        (Finset.mem_erase.mpr ⟨hlj, Finset.mem_erase.mpr ⟨hli, Finset.mem_univ l⟩⟩)) _) _
  intro hinj
  have heq : crtChartFin b k ⟨N / g, hlt⟩ = crtChartFin b k ⟨0, hNpos⟩ := by
    funext l
    exact Fin.ext (by simp [crtChartFin, crtChart, Nat.mod_eq_zero_of_dvd (hall l)])
  have := congrArg Fin.val (hinj heq)
  simp at this
  omega

/-- **Theorem 122 (the residue chart is a chart iff coprime).**

**fdrs.md**: Theorem 122 (the coprime boundary). -/
theorem crtChart_bijective_iff (k : ℕ) :
    Function.Bijective (crtChartFin b k) ↔
      PairwiseCoprimeRadices b k := by
  constructor
  · intro hbij
    by_contra h
    exact crtChartFin_not_injective k h hbij.1
  · intro h
    refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨crtChartFin_injective k h, ?_⟩
    rw [Fintype.card_fin, card_finiteRadixSpace]

/-- Good's output index lands on `σ_i · ∏_{l ≠ i} b_l` modulo `b_i`. -/
theorem ruritanian_modEq (k : ℕ) (σ : FiniteRadixSpace b k) (i : Fin (k + 1)) :
    ruritanian b k σ ≡ (σ i : ℕ) * coBlock b k i [MOD b i] := by
  classical
  rw [ruritanian, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hd : b i ∣ ∑ j ∈ Finset.univ.erase i, (σ j : ℕ) * coBlock b k j :=
    Finset.dvd_sum fun j hj =>
      Dvd.dvd.mul_left (dvd_coBlock k (Finset.ne_of_mem_erase hj).symm) _
  obtain ⟨q, hq⟩ := hd
  rw [hq]
  exact Nat.add_mul_mod_self_left _ _ _

/-- Good's output chart on `ℤ/B_{k+1}`. -/
def ruritanianChart (b : RadixSeq) (k : ℕ) (σ : FiniteRadixSpace b k) :
    Fin (placeValue b (k + 1)) :=
  ⟨ruritanian b k σ % placeValue b (k + 1), Nat.mod_lt _ (placeValue.pos _)⟩

/-- **Theorem 122 (output half).** For pairwise-coprime radices Good's output chart
is a bijection `𝓡^{(k)} ≃ ℤ/B_{k+1}`.

**fdrs.md**: Theorem 122 (the coprime boundary). -/
theorem ruritanianChart_bijective (k : ℕ)
    (h : PairwiseCoprimeRadices b k) :
    Function.Bijective (ruritanianChart b k) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩
  · intro σ σ' hσ
    have hN : ruritanian b k σ ≡ ruritanian b k σ' [MOD placeValue b (k + 1)] :=
      congrArg Fin.val hσ
    funext i
    have hi : ruritanian b k σ ≡ ruritanian b k σ' [MOD b i] :=
      Nat.ModEq.of_dvd ⟨coBlock b k i, (mul_coBlock k i).symm⟩ hN
    have hcop : Nat.Coprime (b i) (coBlock b k i) :=
      Nat.Coprime.symm (Nat.coprime_prod_left_iff.mpr fun j hj =>
        h (Finset.ne_of_mem_erase hj))
    have hσi : (σ i : ℕ) * coBlock b k i ≡ (σ' i : ℕ) * coBlock b k i [MOD b i] :=
      ((ruritanian_modEq k σ i).symm.trans hi).trans (ruritanian_modEq k σ' i)
    have := Nat.ModEq.cancel_right_div_gcd (b.pos i) hσi
    rw [hcop.gcd_eq_one, Nat.div_one] at this
    exact Fin.ext (this.eq_of_lt_of_lt (σ i).isLt (σ' i).isLt)
  · rw [Fintype.card_fin, card_finiteRadixSpace]

/-! ## Corollary 33: the coprime DFT is the Vilenkin transform -/

/-- **Corollary 33 (Good–Thomas).** For pairwise-coprime radices, with inputs read
through the residue chart and outputs through Good's chart, the DFT on
`ℤ/B_{k+1}` is the Vilenkin transform of `∏ ℤ/b_i` — no twiddle factors.

**fdrs.md**: Corollary 33 (Good–Thomas). -/
theorem dft_goodThomas (k : ℕ) (h : PairwiseCoprimeRadices b k)
    (x : ℕ → ℂ) (σ : FiniteRadixSpace b k) :
    dft (placeValue b (k + 1)) x (ruritanian b k σ) =
      ∑ τ : FiniteRadixSpace b k,
        x (((Equiv.ofBijective _ ((crtChart_bijective_iff k).mpr h)).symm τ : ℕ)) *
          vilenkinKernel k τ σ := by
  set e := Equiv.ofBijective _ ((crtChart_bijective_iff (b := b) k).mpr h)
  rw [dft, Finset.sum_range (fun n => x n * zeta _ ^ (ruritanian b k σ * n))]
  refine Fintype.sum_equiv e _ _ fun n => ?_
  rw [Equiv.symm_apply_apply, zeta_pow_ruritanian_mul]
  rfl

end FdrsFormal.NumberTheory.Characters.MixedRadixFFT
