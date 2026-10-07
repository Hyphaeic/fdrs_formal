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

# The staged mixed-radix FFT and its read count (Phase 3 addendum, §1.5)

Proposition 155 says the Fourier kernel on `ℤ/B_{k+1}` is a product of stage
factors, the `i`-th seeing only `τ_i` and the frequency digits `σ_j, j ≥ i`.
This file turns that locality into an algorithm and counts what it reads.

- **Definition 214** (`stage`, `stages`): the stage operator `T_i` sums out
  digit `i` in place, `(T_i y)(ρ) = Σ_t y(ρ[i := t]) · S_i(t; ρ)`; the staged
  transform applies `T_k`, then `T_{k-1}`, …, then `T_0`. Intermediate arrays
  live on `𝓡^{(k)}` itself: positions `< i` still hold time digits, positions
  `≥ i` already hold frequency digits.
- **Theorem 120** (`stages_apply`, `fft_apply`, `fft_eq_dft`): the staged
  transform is the DFT — `(T_0 ⋯ T_k y)(σ) = Σ_τ y(τ) ζ_N^{rdec σ · dec τ}`.
- **Proposition 156** (`ReadsAtMost`, `stage_readsAtMost`,
  `dftChart_readsAtMost_iff`, `sum_radix_le_placeValue`): each stage reads at
  most `b_i` input entries per output entry, so the staged transform reads
  `N · Σ_i b_i` entries in total; the dense transform reads `N` entries per
  output and no fewer; and `Σ_i b_i ≤ N` on every schedule.

**Honest scope.** Classical (Cooley–Tukey 1965). The cost measure is *reads per
output* — the row sparsity of each stage, i.e. nonzeros of a sparse
factorization — not a circuit gate count; twiddle multiplications are folded
into the stage coefficients. In the gate model of OpenAI's family 130,
monomial maps are free and each stage is one tensor-axis call of a `b_i × b_i`
matrix; that family's sub-tensor-axis savings are invisible to this measure and
are not claimed here.
-/

import FdrsFormal.NumberTheory.Characters.MixedRadixFFT

namespace FdrsFormal.NumberTheory.Characters.MixedRadixFFT

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite

variable {b : RadixSeq}

/-! ## Definition 214: stage operators -/

/-- The stage operator `T_i`: sum out digit `i` in place against the stage factor.

**fdrs.md**: Definition 214 (stage operators; the staged transform). -/
noncomputable def stage (k : ℕ) (i : Fin (k + 1)) (y : FiniteRadixSpace b k → ℂ)
    (ρ : FiniteRadixSpace b k) : ℂ :=
  ∑ t : Fin (b i), y (Function.update ρ i t) * stageFactor k i t ρ

/-- The last `n` stages, `T_{k-n+1} ∘ ⋯ ∘ T_k` (identity once `n > k + 1`).

**fdrs.md**: Definition 214 (stage operators; the staged transform). -/
noncomputable def stages (k : ℕ) :
    ℕ → (FiniteRadixSpace b k → ℂ) → (FiniteRadixSpace b k → ℂ)
  | 0 => id
  | n + 1 => fun y =>
      if h : n ≤ k then stage k ⟨k - n, by omega⟩ (stages k n y) else stages k n y

/-- The kernel after `n` stages: time and frequency agree below the processed
block, and every processed digit has contributed its stage factor. -/
noncomputable def kernelAfter (k n : ℕ) (τ ρ : FiniteRadixSpace b k) : ℂ :=
  (if ∀ l : Fin (k + 1), (l : ℕ) + n < k + 1 → ρ l = τ l then 1 else 0) *
    ∏ l : Fin (k + 1), if k + 1 ≤ (l : ℕ) + n then stageFactor k l (τ l) ρ else 1

/-- One stage advances the kernel by one digit. -/
theorem stage_step (k n : ℕ) (hn : n ≤ k) (τ ρ : FiniteRadixSpace b k) :
    ∑ t : Fin (b (k - n)),
        kernelAfter k n τ (Function.update ρ ⟨k - n, by omega⟩ t) *
          stageFactor k ⟨k - n, by omega⟩ t ρ =
      kernelAfter k (n + 1) τ ρ := by
  set i : Fin (k + 1) := ⟨k - n, by omega⟩ with hi
  have hiv : (i : ℕ) = k - n := rfl
  -- the processed product does not see the digit being updated
  have hprod : ∀ t : Fin (b i),
      (∏ l : Fin (k + 1), if k + 1 ≤ (l : ℕ) + n then
          stageFactor k l (τ l) (Function.update ρ i t) else 1) =
        ∏ l : Fin (k + 1), if k + 1 ≤ (l : ℕ) + n then stageFactor k l (τ l) ρ else 1 := by
    intro t
    refine Finset.prod_congr rfl fun l _ => ?_
    split_ifs with hl
    · refine stageFactor_congr k l _ fun j hj => ?_
      have hji : j ≠ i := by
        intro h
        have : (j : ℕ) = k - n := by rw [h]
        have : (l : ℕ) ≤ j := hj
        omega
      rw [Function.update_of_ne hji]
    · rfl
  -- the indicator splits into the remaining agreement and `t = τ_i`
  have hind : ∀ t : Fin (b i),
      (∀ l : Fin (k + 1), (l : ℕ) + n < k + 1 → Function.update ρ i t l = τ l) ↔
        (∀ l : Fin (k + 1), (l : ℕ) + (n + 1) < k + 1 → ρ l = τ l) ∧ t = τ i := by
    intro t
    constructor
    · intro h
      refine ⟨fun l hl => ?_, ?_⟩
      · have hli : l ≠ i := by
          intro h'
          have : (l : ℕ) = k - n := by rw [h']
          omega
        have := h l (by omega)
        rwa [Function.update_of_ne hli] at this
      · have := h i (by omega)
        rwa [Function.update_self] at this
    · rintro ⟨h, rfl⟩ l hl
      rcases eq_or_ne l i with rfl | hli
      · rw [Function.update_self]
      · have hlv : (l : ℕ) ≠ k - n := fun h' => hli (Fin.ext h')
        rw [Function.update_of_ne hli]
        exact h l (by omega)
  -- the processed product gains exactly the factor of digit `i`
  have hsplit : ∀ l : Fin (k + 1),
      (if k + 1 ≤ (l : ℕ) + (n + 1) then stageFactor k l (τ l) ρ else 1) =
        (if k + 1 ≤ (l : ℕ) + n then stageFactor k l (τ l) ρ else 1) *
          (if l = i then stageFactor k l (τ l) ρ else 1) := by
    intro l
    rcases eq_or_ne l i with rfl | hli
    · rw [if_pos (by omega), if_neg (by omega), if_pos rfl, one_mul]
    · have hlv : (l : ℕ) ≠ k - n := fun h' => hli (Fin.ext h')
      rw [if_neg hli, mul_one]
      by_cases h3 : k + 1 ≤ (l : ℕ) + n
      · rw [if_pos h3, if_pos (by omega)]
      · rw [if_neg h3, if_neg (by omega)]
  -- assemble
  classical
  set A : Prop := ∀ l : Fin (k + 1), (l : ℕ) + (n + 1) < k + 1 → ρ l = τ l
  set P : ℂ := ∏ l : Fin (k + 1), if k + 1 ≤ (l : ℕ) + n then stageFactor k l (τ l) ρ else 1
  have hterm : ∀ t : Fin (b i),
      kernelAfter k n τ (Function.update ρ i t) * stageFactor k i t ρ =
        ((if A then 1 else 0) * P) * (if t = τ i then stageFactor k i t ρ else 0) := by
    intro t
    rw [kernelAfter, hprod t, if_congr (hind t) rfl rfl]
    by_cases hA : A <;> by_cases ht : t = τ i <;> simp [hA, ht]
  rw [Finset.sum_congr rfl fun t _ => hterm t, ← Finset.mul_sum, Finset.sum_ite_eq',
    if_pos (Finset.mem_univ _), kernelAfter, Finset.prod_congr rfl fun l _ => hsplit l,
    Finset.prod_mul_distrib, Finset.prod_ite_eq', if_pos (Finset.mem_univ _), mul_assoc]

/-- **Theorem 120 (the staged transform), invariant form.** After `n ≤ k + 1`
stages the array is `Σ_τ y(τ) · kernelAfter_n(τ, ρ)`.

**fdrs.md**: Theorem 120 (the staged transform is the DFT). -/
theorem stages_apply (k : ℕ) :
    ∀ n, n ≤ k + 1 → ∀ (y : FiniteRadixSpace b k → ℂ) (ρ : FiniteRadixSpace b k),
      stages k n y ρ = ∑ τ, y τ * kernelAfter k n τ ρ
  | 0, _, y, ρ => by
    classical
    rw [Finset.sum_eq_single ρ]
    · have hP : (∏ l : Fin (k + 1),
          if k + 1 ≤ (l : ℕ) + 0 then stageFactor k l (ρ l) ρ else 1) = 1 :=
        Finset.prod_eq_one fun l _ => if_neg (by have := l.isLt; omega)
      rw [kernelAfter, hP, if_pos (fun _ _ => rfl)]
      simp [stages]
    · intro τ _ hτ
      have : ¬ ∀ l : Fin (k + 1), (l : ℕ) + 0 < k + 1 → ρ l = τ l := by
        intro h
        exact hτ (funext fun l => (h l (by have := l.isLt; omega)).symm)
      rw [kernelAfter, if_neg this]
      simp
    · simp
  | n + 1, hn, y, ρ => by
    have hnk : n ≤ k := by omega
    have ih := stages_apply k n (by omega)
    simp only [stages, dif_pos hnk, stage]
    simp_rw [ih, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [← Finset.mul_sum, stage_step k n hnk]

/-- **Theorem 120 (the staged transform), kernel form.** All `k + 1` stages produce
the full Fourier kernel.

**fdrs.md**: Theorem 120 (the staged transform is the DFT). -/
theorem fft_apply (k : ℕ) (y : FiniteRadixSpace b k → ℂ) (σ : FiniteRadixSpace b k) :
    stages k (k + 1) y σ =
      ∑ τ, y τ * zeta (placeValue b (k + 1)) ^ (reverseDecode b k σ * decodeFinite b k τ) := by
  rw [stages_apply k (k + 1) le_rfl]
  refine Finset.sum_congr rfl fun τ _ => ?_
  congr 1
  rw [kernelAfter, if_pos (fun l hl => by omega), one_mul, kernel_eq_prod_stageFactor]
  exact Finset.prod_congr rfl fun l _ => if_pos (by omega)

/-- **Theorem 120 (the staged transform is the DFT).** Run on `x ∘ dec_k`, the
staged transform returns the DFT of `x` at every reversed-schedule frequency.

**fdrs.md**: Theorem 120 (the staged transform is the DFT). -/
theorem fft_eq_dft (k : ℕ) (x : ℕ → ℂ) (σ : FiniteRadixSpace b k) :
    stages k (k + 1) (fun τ => x (decodeFinite b k τ)) σ =
      dft (placeValue b (k + 1)) x (reverseDecode b k σ) := by
  rw [fft_apply, dft_factor]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [character_factor]

/-! ## Proposition 156: what each stage reads -/

/-- A transform of arrays on `X` *reads at most `r` entries per output*: each output
entry is determined by some `r` input entries. -/
def ReadsAtMost {X : Type*} (M : (X → ℂ) → (X → ℂ)) (r : ℕ) : Prop :=
  ∀ ρ, ∃ S : Finset X, S.card ≤ r ∧
    ∀ y y' : X → ℂ, (∀ x ∈ S, y x = y' x) → M y ρ = M y' ρ

/-- **Proposition 156 (read count), stage half.** Stage `i` reads at most `b_i`
entries per output: the entries `ρ[i := t]`, `t < b_i`.

**fdrs.md**: Proposition 156 (the read count). -/
theorem stage_readsAtMost (k : ℕ) (i : Fin (k + 1)) :
    ReadsAtMost (stage (b := b) k i) (b i) := by
  classical
  intro ρ
  refine ⟨Finset.univ.image fun t : Fin (b i) => Function.update ρ i t, ?_, ?_⟩
  · exact (Finset.card_image_le).trans (by simp)
  · intro y y' h
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [h _ (Finset.mem_image_of_mem _ (Finset.mem_univ t))]

/-- The dense transform on `𝓡^{(k)}`, read through the `dec`/`rdec` charts. -/
noncomputable def dftChart (k : ℕ) (y : FiniteRadixSpace b k → ℂ) (σ : FiniteRadixSpace b k) :
    ℂ :=
  ∑ τ, y τ * zeta (placeValue b (k + 1)) ^ (reverseDecode b k σ * decodeFinite b k τ)

theorem dftChart_eq_stages (k : ℕ) : dftChart (b := b) k = stages k (k + 1) := by
  funext y σ
  rw [fft_apply, dftChart]

theorem card_finiteRadixSpace (k : ℕ) :
    Fintype.card (FiniteRadixSpace b k) = placeValue b (k + 1) := by
  rw [Fintype.card_congr (finiteRadixEquiv b k), Fintype.card_fin]

theorem zeta_ne_zero (n : ℕ) : zeta n ≠ 0 := Complex.exp_ne_zero _

/-- **Proposition 156 (read count), dense half.** The dense transform reads at most
`r` entries per output **iff** `N ≤ r`: every kernel entry is a nonzero root of
unity, so no entry can be skipped.

**fdrs.md**: Proposition 156 (the read count). -/
theorem dftChart_readsAtMost_iff (k r : ℕ) :
    ReadsAtMost (dftChart (b := b) k) r ↔ placeValue b (k + 1) ≤ r := by
  classical
  constructor
  · intro h
    obtain ⟨S, hS, hdep⟩ := h default
    have hall : ∀ τ0, τ0 ∈ S := by
      intro τ0
      by_contra hτ0
      have := hdep (fun τ => if τ = τ0 then 1 else 0) 0 fun x hx => by
        have : x ≠ τ0 := fun h => hτ0 (h ▸ hx)
        simp [this]
      simp only [dftChart, Pi.zero_apply, zero_mul, Finset.sum_const_zero, ite_mul, one_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
      exact pow_ne_zero _ (zeta_ne_zero _) this
    rw [← card_finiteRadixSpace k]
    calc Fintype.card (FiniteRadixSpace b k) = S.card := by
          rw [Finset.eq_univ_of_forall hall, Finset.card_univ]
      _ ≤ r := hS
  · intro h ρ
    refine ⟨Finset.univ, ?_, fun y y' hy => ?_⟩
    · rw [Finset.card_univ, card_finiteRadixSpace]; exact h
    · exact Finset.sum_congr rfl fun τ _ => by rw [hy τ (Finset.mem_univ τ)]

/-- **Proposition 156 (read count), budget half.** On every schedule
`Σ_{i ≤ k} b_i ≤ B_{k+1}`, so the staged reads `N · Σ_i b_i` never exceed the
dense reads `N · N`.

**fdrs.md**: Proposition 156 (the read count). -/
theorem sum_radix_le_placeValue (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), b i ≤ placeValue b (k + 1) := by
  induction k with
  | zero => simp [placeValue]
  | succ k ih =>
    rw [Finset.sum_range_succ, placeValue.succ]
    have h1 : 2 ≤ placeValue b (k + 1) := by
      have := placeValue.mono (b := b) (show 1 ≤ k + 1 by omega)
      have h0 : placeValue b 1 = b 0 := by simp [placeValue]
      have := b.ge_two 0
      omega
    have h2 := b.ge_two (k + 1)
    nlinarith

end FdrsFormal.NumberTheory.Characters.MixedRadixFFT
