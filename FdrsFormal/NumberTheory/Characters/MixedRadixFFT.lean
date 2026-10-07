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

# The mixed-radix Fourier factorization (Phase 3 addendum, §1.4)

Phase 3 §1.1 pulls the additive characters of `ℤ/N` back to the finite radix
space through `dec_k`: `χ_m^{(k)}(τ) = χ_m(dec_k τ)`, `N = B_{k+1}`. This file
proves that, once the *frequency* is also written in digits — read in the
reversed schedule, `m = rdec_k σ = Σ_j σ_j · B_{[j+1, k+1)}` — the pulled-back
character factors digit-by-digit into a **triangular** kernel:

- **Theorem 119** (`zeta_pow_decode_mul_reverseDecode`): the phase
  `ζ_N^{dec τ · rdec σ}` is `∏_{i ≤ j} ζ_{B_{[i, j+1)}}^{τ_i σ_j}` — pairs of
  digits with `i > j` contribute nothing.
- **Corollary 32** (`character_factor`, `dft_factor`, `fourier_factor`): the
  diagonal `i = j` is the Vilenkin character `∏_i ζ_{b_i}^{τ_i σ_i}` of the
  carry-free group `∏ ℤ/b_i`; the strict upper triangle `i < j` is the
  twiddle kernel. The DFT on `ℤ/B_{k+1}` is the Vilenkin transform twisted by
  the twiddles.
- **Proposition 154** (`twiddleKernel_trivial_iff`): the twiddle kernel is
  identically `1` **iff** the line has a single digit. On every multi-digit
  number line the positional chart sees `ℤ/B` as a twisted, not a direct,
  product of its digit groups — the twiddles are where the carry lives.
- **Proposition 155** (`stageFactor`, `kernel_eq_prod_stageFactor`,
  `stageFactor_congr`): the kernel is a product of per-digit stage factors,
  the `i`-th depending only on `τ_i` and the frequency digits `σ_j, j ≥ i` —
  the locality that the Cooley–Tukey FFT exploits (sum out `τ_k`, then
  `τ_{k-1}`, …).

**Honest scope.** This is the classical mixed-radix Cooley–Tukey index
calculus (Cooley–Tukey 1965; Good 1958 for the coprime variant), restated on
the corpus's own `dec_k` chart; no new mathematics is claimed. Nothing here
counts operations — the circuit cost of the induced algorithm, and the
Good–Thomas CRT chart that removes twiddles for pairwise-coprime radices, are
recorded as follow-ups, not proven. Motivation: OpenAI's family 130
(sub-`n log n` exact Fourier circuits, via savings on tensor-axis
computations over digit coordinates) works on exactly this tensor/twiddle
decomposition.
-/

import FdrsFormal.Core.Finite.Bijection
import Mathlib.RingTheory.RootsOfUnity.Complex

namespace FdrsFormal.NumberTheory.Characters.MixedRadixFFT

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite
open Complex

variable {b : RadixSeq}

/-! ## Roots of unity -/

/-- The root of unity `ζ_n = exp(2πi/n)` (Phase 3 §1.1's `χ_1` on `ℤ/n`). -/
noncomputable def zeta (n : ℕ) : ℂ := exp (2 * Real.pi * I / n)

theorem zeta_pow_self (n : ℕ) (hn : n ≠ 0) : zeta n ^ n = 1 :=
  (isPrimitiveRoot_exp n hn).pow_eq_one

theorem zeta_ne_one {n : ℕ} (hn : 1 < n) : zeta n ≠ 1 :=
  (isPrimitiveRoot_exp n (by omega)).ne_one hn

/-- `ζ_n^{n·a} = 1`. -/
theorem zeta_pow_self_mul (n a : ℕ) (hn : n ≠ 0) : zeta n ^ (n * a) = 1 := by
  rw [pow_mul, zeta_pow_self n hn, one_pow]

/-- Coarsening: `ζ_{P·Q}^{Q·a} = ζ_P^a`. -/
theorem zeta_mul_pow_mul (P Q a : ℕ) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    zeta (P * Q) ^ (Q * a) = zeta P ^ a := by
  rw [pow_mul]
  congr 1
  simp only [zeta, ← exp_nat_mul]
  congr 1
  have hP' : (P : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hP
  have hQ' : (Q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hQ
  push_cast
  field_simp

/-! ## Block products of radices -/

/-- The block product `B_{[i,j)} = ∏_{i ≤ l < j} b_l`. -/
def blockProd (b : RadixSeq) (i j : ℕ) : ℕ := ∏ l ∈ Finset.Ico i j, b l

theorem blockProd_ne_zero (i j : ℕ) : blockProd b i j ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun l _ => b.ne_zero l

theorem blockProd_mul {i j l : ℕ} (hij : i ≤ j) (hjl : j ≤ l) :
    blockProd b i j * blockProd b j l = blockProd b i l :=
  Finset.prod_Ico_consecutive _ hij hjl

theorem blockProd_succ (i : ℕ) : blockProd b i (i + 1) = b i := by
  simp [blockProd]

/-- `B_j = B_i · B_{[i,j)}` for `i ≤ j`. -/
theorem placeValue_eq_mul_blockProd {i j : ℕ} (h : i ≤ j) :
    placeValue b j = placeValue b i * blockProd b i j := by
  induction j, h using Nat.le_induction with
  | base => simp [blockProd]
  | succ j hij ih =>
    have hstep : blockProd b i (j + 1) = blockProd b i j * b j :=
      Finset.prod_Ico_succ_top hij _
    rw [placeValue.succ, ih, hstep, mul_assoc]

/-! ## The reversed-schedule decode of a frequency -/

/-- Frequency decode: digit `σ_j` carries weight `B_{[j+1, k+1)} = B_{k+1}/B_{j+1}`
(the schedule read most-significant-first). -/
def reverseDecode (b : RadixSeq) (k : ℕ) (σ : FiniteRadixSpace b k) : ℕ :=
  ∑ j : Fin (k + 1), (σ j : ℕ) * blockProd b ((j : ℕ) + 1) (k + 1)

/-! ## Theorem 119: the triangular phase -/

/-- One digit pair `(i, j)` of the phase. For `i ≤ j` the weight `B_i · B_{[j+1,k+1)}`
coarsens `ζ_N` to `ζ_{B_{[i,j+1)}}`; for `i > j` it is a multiple of `N`. -/
theorem zeta_pow_pair (k : ℕ) (i j : Fin (k + 1)) (a : ℕ) :
    zeta (placeValue b (k + 1)) ^ (placeValue b i * blockProd b ((j : ℕ) + 1) (k + 1) * a) =
      if i ≤ j then zeta (blockProd b i ((j : ℕ) + 1)) ^ a else 1 := by
  have hi := i.isLt
  have hj := j.isLt
  split_ifs with h
  · have hij : (i : ℕ) ≤ j := h
    have hN : placeValue b (k + 1) =
        blockProd b i ((j : ℕ) + 1) * (placeValue b i * blockProd b ((j : ℕ) + 1) (k + 1)) := by
      rw [placeValue_eq_mul_blockProd (show (i : ℕ) ≤ k + 1 by omega),
        ← blockProd_mul (show (i : ℕ) ≤ j + 1 by omega) (show (j : ℕ) + 1 ≤ k + 1 by omega)]
      ring
    rw [hN]
    exact zeta_mul_pow_mul _ _ _ (blockProd_ne_zero _ _)
      (mul_ne_zero (placeValue.ne_zero _) (blockProd_ne_zero _ _))
  · have hji : (j : ℕ) + 1 ≤ i := by
      have : ¬ (i : ℕ) ≤ j := h
      omega
    have hN : placeValue b (k + 1) = placeValue b ((j : ℕ) + 1) * blockProd b ((j : ℕ) + 1) (k + 1) :=
      placeValue_eq_mul_blockProd (by omega)
    have hw : placeValue b i * blockProd b ((j : ℕ) + 1) (k + 1) * a =
        placeValue b (k + 1) * (blockProd b ((j : ℕ) + 1) i * a) := by
      rw [placeValue_eq_mul_blockProd hji, hN]
      ring
    rw [hw]
    exact zeta_pow_self_mul _ _ (placeValue.ne_zero _)

/-- **Theorem 119 (the triangular phase).** With `n = dec_k τ` and
`m = rdec_k σ`, the phase `ζ_N^{n·m}` (`N = B_{k+1}`) factors over digit pairs,
and only pairs with `i ≤ j` survive:
`ζ_N^{n·m} = ∏_{i ≤ j} ζ_{B_{[i, j+1)}}^{τ_i σ_j}`.

**fdrs.md**: Theorem 119 (the triangular phase). -/
theorem zeta_pow_decode_mul_reverseDecode (k : ℕ) (τ σ : FiniteRadixSpace b k) :
    zeta (placeValue b (k + 1)) ^ (decodeFinite b k τ * reverseDecode b k σ) =
      ∏ i : Fin (k + 1), ∏ j : Fin (k + 1),
        if i ≤ j then zeta (blockProd b i ((j : ℕ) + 1)) ^ ((τ i : ℕ) * σ j) else 1 := by
  rw [decodeFinite, reverseDecode, Finset.sum_mul_sum, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← zeta_pow_pair k i j]
  congr 1
  ring

/-! ## Corollary 32: Vilenkin character × twiddle kernel -/

/-- The Vilenkin kernel: the character of the carry-free product group `∏ ℤ/b_i`,
pairing digits only on the diagonal. -/
noncomputable def vilenkinKernel (k : ℕ) (τ σ : FiniteRadixSpace b k) : ℂ :=
  ∏ i : Fin (k + 1), zeta (b i) ^ ((τ i : ℕ) * σ i)

/-- The twiddle kernel: the strictly upper-triangular digit pairs `i < j`. -/
noncomputable def twiddleKernel (k : ℕ) (τ σ : FiniteRadixSpace b k) : ℂ :=
  ∏ i : Fin (k + 1), ∏ j : Fin (k + 1),
    if i < j then zeta (blockProd b i ((j : ℕ) + 1)) ^ ((τ i : ℕ) * σ j) else 1

/-- **Corollary 32 (character form).** The pulled-back character `χ_m(dec_k τ)` at
frequency `m = rdec_k σ` is the Vilenkin character times the twiddle kernel.

**fdrs.md**: Corollary 32 (Vilenkin × twiddle). -/
theorem character_factor (k : ℕ) (τ σ : FiniteRadixSpace b k) :
    zeta (placeValue b (k + 1)) ^ (reverseDecode b k σ * decodeFinite b k τ) =
      vilenkinKernel k τ σ * twiddleKernel k τ σ := by
  rw [mul_comm (reverseDecode b k σ), zeta_pow_decode_mul_reverseDecode, vilenkinKernel,
    twiddleKernel,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hsplit : ∀ j : Fin (k + 1),
      (if i ≤ j then zeta (blockProd b i ((j : ℕ) + 1)) ^ ((τ i : ℕ) * σ j) else 1) =
        (if i = j then zeta (blockProd b i ((j : ℕ) + 1)) ^ ((τ i : ℕ) * σ j) else 1) *
        (if i < j then zeta (blockProd b i ((j : ℕ) + 1)) ^ ((τ i : ℕ) * σ j) else 1) := by
    intro j
    rcases lt_trichotomy i j with h | h | h
    · simp [h.le, h.ne, h]
    · subst h; simp
    · simp [not_le.mpr h, h.ne', not_lt.mpr h.le]
  rw [Finset.prod_congr rfl fun j _ => hsplit j, Finset.prod_mul_distrib, Finset.prod_ite_eq,
    if_pos (Finset.mem_univ _), blockProd_succ]

/-- The unnormalized DFT on `ℤ/N` in the corpus sign convention
(`χ_m(x) = exp(2πi m x / N)`, Phase 3 §1.1). -/
noncomputable def dft (N : ℕ) (x : ℕ → ℂ) (m : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, x n * zeta N ^ (m * n)

/-- **Corollary 32 (transform form).** On `ℤ/B_{k+1}`, read through `dec_k`, the DFT
at frequency `rdec_k σ` is the Vilenkin transform twisted by the twiddle kernel.

**fdrs.md**: Corollary 32 (Vilenkin × twiddle). -/
theorem dft_factor (k : ℕ) (x : ℕ → ℂ) (σ : FiniteRadixSpace b k) :
    dft (placeValue b (k + 1)) x (reverseDecode b k σ) =
      ∑ τ : FiniteRadixSpace b k,
        x (decodeFinite b k τ) * (vilenkinKernel k τ σ * twiddleKernel k τ σ) := by
  rw [dft, Finset.sum_range (fun n => x n * zeta _ ^ (reverseDecode b k σ * n))]
  refine (Fintype.sum_equiv (finiteRadixEquiv b k) _ _ fun τ => ?_).symm
  rw [← character_factor]
  rfl

/-- **Corollary 32 (spec normalization).** Phase 3 §1.1's normalized transform
`f̂(m) = (1/N) Σ_x f(x) · conj χ_m(x)`, at `m = rdec_k σ`.

**fdrs.md**: Corollary 32 (Vilenkin × twiddle). -/
theorem fourier_factor (k : ℕ) (f : ℕ → ℂ) (σ : FiniteRadixSpace b k) :
    (1 / (placeValue b (k + 1) : ℂ)) *
        ∑ n ∈ Finset.range (placeValue b (k + 1)),
          f n * (starRingEnd ℂ) (zeta (placeValue b (k + 1)) ^ (reverseDecode b k σ * n)) =
      (1 / (placeValue b (k + 1) : ℂ)) *
        ∑ τ : FiniteRadixSpace b k, f (decodeFinite b k τ) *
          ((starRingEnd ℂ) (vilenkinKernel k τ σ) * (starRingEnd ℂ) (twiddleKernel k τ σ)) := by
  congr 1
  rw [Finset.sum_range (fun n => f n *
    (starRingEnd ℂ) (zeta _ ^ (reverseDecode b k σ * n)))]
  refine (Fintype.sum_equiv (finiteRadixEquiv b k) _ _ fun τ => ?_).symm
  rw [← map_mul, ← character_factor]
  rfl

/-! ## Proposition 154: twiddles are unavoidable on multi-digit lines -/

/-- **Proposition 154 (the twiddle boundary).** The twiddle kernel is identically `1`
iff the line has a single digit (`k = 0`). With two or more digits, the digit pair
`τ_0 = 1`, `σ_1 = 1` already carries the nontrivial twiddle `ζ_{b_0 b_1}`.

**fdrs.md**: Proposition 154 (the twiddle boundary). -/
theorem twiddleKernel_trivial_iff (k : ℕ) :
    (∀ τ σ : FiniteRadixSpace b k, twiddleKernel k τ σ = 1) ↔ k = 0 := by
  constructor
  · intro h
    by_contra hk
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    let i0 : Fin (k + 1) := ⟨0, by omega⟩
    let i1 : Fin (k + 1) := ⟨1, by omega⟩
    -- τ = indicator of digit 0, σ = indicator of digit 1
    let τ : FiniteRadixSpace b k := fun i =>
      if i = i0 then ⟨1, by have := b.ge_two i; omega⟩ else ⟨0, b.pos i⟩
    let σ : FiniteRadixSpace b k := fun j =>
      if j = i1 then ⟨1, by have := b.ge_two j; omega⟩ else ⟨0, b.pos j⟩
    have hτ : ∀ i, ((τ i : ℕ)) = if i = i0 then 1 else 0 := by
      intro i; by_cases hi : i = i0 <;> simp [τ, hi]
    have hσ : ∀ j, ((σ j : ℕ)) = if j = i1 then 1 else 0 := by
      intro j; by_cases hj : j = i1 <;> simp [σ, hj]
    have htw : twiddleKernel k τ σ = zeta (blockProd b 0 2) := by
      rw [twiddleKernel]
      have hrow : ∀ i : Fin (k + 1), (∏ j : Fin (k + 1),
          if i < j then zeta (blockProd b i ((j : ℕ) + 1)) ^ ((τ i : ℕ) * σ j) else 1) =
            if i = i0 then zeta (blockProd b 0 2) else 1 := by
        intro i
        by_cases hi : i = i0
        · subst hi
          rw [if_pos rfl, Finset.prod_eq_single i1]
          · simp [hτ, hσ, i0, i1]
          · intro j _ hj
            simp [hσ, hj]
          · simp
        · rw [if_neg hi]
          refine Finset.prod_eq_one fun j _ => ?_
          simp [hτ, hi]
      rw [Finset.prod_congr rfl fun i _ => hrow i, Finset.prod_ite_eq', if_pos (Finset.mem_univ _)]
    have hne : zeta (blockProd b 0 2) ≠ 1 := by
      apply zeta_ne_one
      have h01 : blockProd b 0 1 = b 0 := blockProd_succ 0
      have h12 : blockProd b 1 2 = b 1 := blockProd_succ 1
      have h2 : blockProd b 0 2 = b 0 * b 1 := by
        rw [← blockProd_mul (show 0 ≤ 1 by omega) (show 1 ≤ 2 by omega), h01, h12]
      rw [h2]
      have := b.ge_two 0
      have := b.ge_two 1
      nlinarith
    have hτσ := h τ σ
    rw [htw] at hτσ
    exact hne hτσ
  · rintro rfl τ σ
    simp only [twiddleKernel]
    refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => ?_
    have : ¬ i < j := by
      rw [Fin.lt_def]
      have := i.isLt
      have := j.isLt
      omega
    simp [this]

/-! ## Proposition 155: stage locality (the FFT's structure) -/

/-- The stage-`i` factor: everything in the kernel that involves the time digit `τ_i`. -/
noncomputable def stageFactor (k : ℕ) (i : Fin (k + 1)) (t : ℕ) (σ : FiniteRadixSpace b k) : ℂ :=
  ∏ j : Fin (k + 1), if i ≤ j then zeta (blockProd b i ((j : ℕ) + 1)) ^ (t * σ j) else 1

/-- **Proposition 155 (stage locality), product half.** The full kernel is the product
of the stage factors, one per time digit.

**fdrs.md**: Proposition 155 (stage locality). -/
theorem kernel_eq_prod_stageFactor (k : ℕ) (τ σ : FiniteRadixSpace b k) :
    zeta (placeValue b (k + 1)) ^ (reverseDecode b k σ * decodeFinite b k τ) =
      ∏ i : Fin (k + 1), stageFactor k i (τ i) σ := by
  rw [mul_comm (reverseDecode b k σ), zeta_pow_decode_mul_reverseDecode]
  rfl

/-- **Proposition 155 (stage locality), locality half.** The stage-`i` factor sees only
the frequency digits `σ_j` with `j ≥ i`: summing out `τ_k` first needs only `σ_k`,
then `τ_{k-1}` needs `σ_{k-1}, σ_k`, and so on — the Cooley–Tukey recursion.

**fdrs.md**: Proposition 155 (stage locality). -/
theorem stageFactor_congr (k : ℕ) (i : Fin (k + 1)) (t : ℕ) {σ σ' : FiniteRadixSpace b k}
    (h : ∀ j, i ≤ j → (σ j : ℕ) = σ' j) :
    stageFactor k i t σ = stageFactor k i t σ' := by
  refine Finset.prod_congr rfl fun j _ => ?_
  split_ifs with hij
  · rw [h j hij]
  · rfl

end FdrsFormal.NumberTheory.Characters.MixedRadixFFT
