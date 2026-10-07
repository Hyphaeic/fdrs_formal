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

# Gate counts for exact Fourier circuits (Phase 3 addendum, §1.7)

In family 130's gate model (Definition 216, `FourierCircuit.lean`) this file
builds explicit circuits and counts their gates exactly.

- **Proposition 157** (`reverseDecode_bijective`, `rdecEquiv`): the reversed-schedule
  frequency chart `rdec_k` is a bijection `𝓡^{(k)} ≃ ℤ/B_{k+1}` — it is `dec_k`
  of the reversed schedule — so the staged transform covers every frequency.
- **Theorem 123** (`exists_staged_circuit`): for every radix schedule, the DFT of
  length `N = B_{k+1}` has an exact circuit with **exactly**
  `N · Σ_{i ≤ k} (2 b_i - 1)` gates — one linear-combination block of `b_i`
  terms per output per stage, wired by the dec/rdec charts.
- **Proposition 158** (`exists_dense_circuit`): every length `n ≥ 1` has an
  exact circuit with `n (2n - 1)` gates (the dense matrix–vector product).
- **Corollary 34** (`exists_radixTwo_circuit`, `mainStatement_of_three_lt`): on the
  binary schedule the count is `3 · N · log₂ N`, so family 130's statement holds
  for every `c > 3` by this construction alone.

**Honest scope.** Classical (Cooley–Tukey 1965). The construction folds twiddles
into its scalars and spends `2 b_i - 1` gates per output per stage; the
classical radix-2 butterfly (one twiddle, one add, one subtract per *pair*)
reaches `1.5 · N log₂ N` (`FFTButterfly.lean`, §1.8), and split-radix lower. Family 130's theorem — every
`c > 0` along a subsequence — is recorded as `MainStatement` and is **not**
proven here; what is proven is the `c > 3` instance and exact counts for every
mixed-radix schedule.
-/

import FdrsFormal.NumberTheory.Characters.FourierCircuit
import FdrsFormal.NumberTheory.Characters.MixedRadixStages

namespace FdrsFormal.NumberTheory.Characters.FourierCircuit

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite
open FdrsFormal.NumberTheory.Characters.MixedRadixFFT

variable {b : RadixSeq}

/-! ## Proposition 157: the frequency chart is a bijection -/

/-- The schedule read backwards from position `k`. -/
def revSeq (b : RadixSeq) (k : ℕ) : RadixSeq := ⟨fun l => b (k - l), fun _ => b.ge_two _⟩

theorem placeValue_revSeq (k : ℕ) :
    ∀ m, m ≤ k + 1 → placeValue (revSeq b k) m = blockProd b (k + 1 - m) (k + 1)
  | 0, _ => by simp [placeValue, blockProd]
  | m + 1, hm => by
    rw [placeValue.succ, placeValue_revSeq k m (by omega)]
    show blockProd b (k + 1 - m) (k + 1) * b (k - m) = blockProd b (k + 1 - (m + 1)) (k + 1)
    rw [show k + 1 - (m + 1) = k - m by omega,
      ← blockProd_mul (show k - m ≤ k - m + 1 by omega) (show k - m + 1 ≤ k + 1 by omega),
      blockProd_succ, show k - m + 1 = k + 1 - m by omega, mul_comm]

/-- Frequency digits, read in the reversed schedule. -/
def revDigits (k : ℕ) (σ : FiniteRadixSpace b k) : FiniteRadixSpace (revSeq b k) k :=
  fun l => ⟨σ (Fin.rev l), by
    have h : ((σ (Fin.rev l)) : ℕ) < b (Fin.rev l : ℕ) := (σ (Fin.rev l)).isLt
    have e : (Fin.rev l : ℕ) = k - l := by rw [Fin.val_rev]; omega
    exact lt_of_lt_of_eq h (congrArg b.toFun e)⟩

theorem reverseDecode_eq_decode (k : ℕ) (σ : FiniteRadixSpace b k) :
    reverseDecode b k σ = decodeFinite (revSeq b k) k (revDigits k σ) := by
  rw [reverseDecode, decodeFinite]
  refine (Fintype.sum_equiv Fin.revPerm _ _ fun l => ?_).symm
  have hl := l.isLt
  simp only [revDigits, Fin.revPerm_apply]
  rw [placeValue_revSeq k l (by omega)]
  congr 1
  rw [Fin.val_rev]
  congr 1
  omega

theorem reverseDecode_lt (k : ℕ) (σ : FiniteRadixSpace b k) :
    reverseDecode b k σ < placeValue b (k + 1) := by
  have h := decodeFinite_lt k (revDigits k σ)
  rw [placeValue_revSeq k (k + 1) le_rfl, Nat.sub_self] at h
  rw [placeValue_eq_mul_blockProd (show 0 ≤ k + 1 by omega), placeValue.zero, one_mul,
    reverseDecode_eq_decode]
  exact h

/-- The frequency chart `σ ↦ rdec_k σ` into `ℤ/B_{k+1}`. -/
def rdecChart (b : RadixSeq) (k : ℕ) (σ : FiniteRadixSpace b k) : Fin (placeValue b (k + 1)) :=
  ⟨reverseDecode b k σ, reverseDecode_lt k σ⟩

/-- **Proposition 157 (the frequency chart).** `rdec_k` is a bijection onto `ℤ/B_{k+1}`.

**fdrs.md**: Proposition 157 (the frequency chart is a bijection). -/
theorem reverseDecode_bijective (k : ℕ) : Function.Bijective (rdecChart b k) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨fun σ σ' h => ?_, ?_⟩
  · have h' : decodeFinite (revSeq b k) k (revDigits k σ) =
        decodeFinite (revSeq b k) k (revDigits k σ') := by
      rw [← reverseDecode_eq_decode, ← reverseDecode_eq_decode]
      exact congrArg Fin.val h
    have hd := decodeFinite_injective (b := revSeq b k) k h'
    funext j
    have := congrArg Fin.val (congrFun hd (Fin.rev j))
    simp only [revDigits] at this
    rw [Fin.rev_rev] at this
    exact Fin.ext this
  · rw [Fintype.card_fin, card_finiteRadixSpace]

noncomputable def rdecEquiv (b : RadixSeq) (k : ℕ) :
    FiniteRadixSpace b k ≃ Fin (placeValue b (k + 1)) :=
  Equiv.ofBijective _ (reverseDecode_bijective k)

/-! ## Theorem 123: the staged circuit -/

section Staged

variable (b) (k : ℕ)

/-- The digit processed by stage `s`. -/
def digitAt (s : ℕ) : Fin (k + 1) := ⟨k - s, by omega⟩

/-- First free register of stage `s`. -/
def stagePos : ℕ → ℕ
  | 0 => placeValue b (k + 1) + 1
  | s + 1 => stagePos s + placeValue b (k + 1) * (2 * b (k - s) - 1)

/-- Where the array after `s` stages lives. -/
def stageAddr : ℕ → FiniteRadixSpace b k → ℕ
  | 0, τ => decodeFinite b k τ
  | s + 1, ρ => stagePos b k s + decodeFinite b k ρ * (2 * b (k - s) - 1) + (2 * b (k - s) - 2)

/-- The terms of output `ρ` in stage `s`. -/
noncomputable def stageTerms (s : ℕ) (ρ : FiniteRadixSpace b k) : List (ℂ × ℕ) :=
  List.ofFn fun t : Fin (b (k - s)) =>
    (stageFactor k (digitAt k s) t ρ, stageAddr b k s (Function.update ρ (digitAt k s) t))

/-- Stage `s`, block `r` (the output `ρ = enc_k r`). -/
noncomputable def stageBlock (s r : ℕ) : List (ℂ × ℕ) :=
  if h : r < placeValue b (k + 1) then stageTerms b k s (encodeFinite b k ⟨r, h⟩) else []

/-- The first `s` stages as a gate list. -/
noncomputable def stagedGates : ℕ → List LGate
  | 0 => []
  | s + 1 => stagedGates s ++
      blockGates (stagePos b k s) (2 * b (k - s) - 1) (stageBlock b k s) (placeValue b (k + 1))

end Staged

/-- The input as a sequence on `ℕ` (zero beyond the length). -/
def extend {n : ℕ} (x : Fin n → ℂ) (i : ℕ) : ℂ := if h : i < n then x ⟨i, h⟩ else 0

theorem stagedGates_spec (k : ℕ) (x : Fin (placeValue b (k + 1)) → ℂ) :
    ∀ s, s ≤ k + 1 →
      (exec (stagedGates b k s) (initState _ x)).pos = stagePos b k s ∧
      ∀ ρ, stageAddr b k s ρ < stagePos b k s ∧
        (exec (stagedGates b k s) (initState _ x)).val (stageAddr b k s ρ) =
          stages k s (fun τ => extend x (decodeFinite b k τ)) ρ
  | 0, _ => by
    refine ⟨rfl, fun τ => ⟨?_, ?_⟩⟩
    · have := decodeFinite_lt k τ; simp only [stageAddr, stagePos]; omega
    · simp [stagedGates, exec, initState, stageAddr, stages, extend]
  | s + 1, hs => by
    obtain ⟨hpos, hinv⟩ := stagedGates_spec k x s (by omega)
    have hb := b.ge_two (k - s)
    have hblk := blockGates_spec (stagePos b k s) (b (k - s)) (by omega) (stageBlock b k s)
      (exec (stagedGates b k s) (initState _ x)) hpos (placeValue b (k + 1))
      fun r hr => by
        refine ⟨by simp only [stageBlock, dif_pos hr, stageTerms, List.length_ofFn], fun p hp => ?_⟩
        simp only [stageBlock, dif_pos hr, stageTerms, List.mem_ofFn] at hp
        obtain ⟨t, rfl⟩ := hp
        exact (hinv _).1
    obtain ⟨hpos', hval⟩ := hblk
    have hexec : exec (stagedGates b k (s + 1)) (initState _ x) =
        exec (blockGates (stagePos b k s) (2 * b (k - s) - 1) (stageBlock b k s)
          (placeValue b (k + 1))) (exec (stagedGates b k s) (initState _ x)) := by
      simp only [stagedGates, exec_append]
    rw [hexec]
    refine ⟨by rw [hpos']; rfl, fun ρ => ⟨?_, ?_⟩⟩
    · have hd := decodeFinite_lt k ρ
      have key : (decodeFinite b k ρ + 1) * (2 * b (k - s) - 1) ≤
          placeValue b (k + 1) * (2 * b (k - s) - 1) := Nat.mul_le_mul_right _ hd
      rw [add_mul, one_mul] at key
      simp only [stageAddr, stagePos]
      omega
    · have hd := decodeFinite_lt k ρ
      have h1 := hval (decodeFinite b k ρ) hd
      simp only [stageAddr]
      rw [h1, stageBlock, dif_pos hd, encodeFinite_decodeFinite, stageTerms, List.map_ofFn,
        List.sum_ofFn]
      simp only [stages, dif_pos (show s ≤ k by omega), stage]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [Function.comp_apply]
      rw [(hinv _).2, mul_comm]
      rfl

theorem stagedGates_length (k : ℕ) :
    ∀ s, (stagedGates b k s).length =
      ∑ j ∈ Finset.range s, placeValue b (k + 1) * (2 * b (k - j) - 1)
  | 0 => rfl
  | s + 1 => by
    rw [stagedGates, List.length_append, stagedGates_length k s, Finset.sum_range_succ,
      blockGates_length _ _ _ _
        (fun r hr => by simp only [stageBlock, dif_pos hr, stageTerms, List.length_ofFn])
        (by have := b.ge_two (k - s); omega)]

/-- **Theorem 123 (the staged circuit).** For every radix schedule, the DFT of length
`N = B_{k+1}` is computed exactly by a circuit with `N · Σ_{i ≤ k} (2 b_i - 1)` gates.

**fdrs.md**: Theorem 123 (the staged circuit). -/
theorem exists_staged_circuit (b : RadixSeq) (k : ℕ) :
    ∃ C : Circuit (placeValue b (k + 1)),
      C.Computes (fourierMatrix (placeValue b (k + 1))) ∧
      C.size = placeValue b (k + 1) * ∑ i ∈ Finset.range (k + 1), (2 * b i - 1) := by
  set N := placeValue b (k + 1)
  have hlen : (stagedGates b k (k + 1)).length = N * ∑ i ∈ Finset.range (k + 1), (2 * b i - 1) := by
    rw [stagedGates_length, Finset.mul_sum,
      ← Finset.sum_range_reflect (fun i => N * (2 * b i - 1)) (k + 1)]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [show k + 1 - 1 - j = k - j by omega]
  have hout : ∀ m : Fin N,
      stageAddr b k (k + 1) ((rdecEquiv b k).symm m) < N + 1 + (stagedGates b k (k + 1)).length := by
    intro m
    have h := (stagedGates_spec (b := b) k (fun _ => 0) (k + 1) le_rfl)
    have hp := h.1
    rw [exec_pos] at hp
    have hst : stagePos b k (k + 1) = N + 1 + (stagedGates b k (k + 1)).length := by
      rw [← hp]; rfl
    exact (h.2 _).1.trans_eq hst
  refine ⟨Circuit.ofGates N (stagedGates b k (k + 1))
    (fun m => stageAddr b k (k + 1) ((rdecEquiv b k).symm m)) hout, ?_, ?_⟩
  · intro x
    funext m
    rw [Circuit.ofGates_eval, ((stagedGates_spec k x (k + 1) le_rfl).2 _).2, fft_eq_dft]
    have hm : reverseDecode b k ((rdecEquiv b k).symm m) = m := by
      have := (rdecEquiv b k).apply_symm_apply m
      exact congrArg Fin.val this
    rw [hm, dft, Finset.sum_range (fun n => extend x n * zeta N ^ ((m : ℕ) * n))]
    simp only [Matrix.mulVec, dotProduct, fourierMatrix, extend]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dif_pos j.isLt, mul_comm]
  · rw [Circuit.ofGates_size, hlen]

/-! ## Proposition 158: the dense circuit -/

/-- **Proposition 158 (the dense circuit).** Every length `n ≥ 1` has an exact
Fourier circuit with `n (2n - 1)` gates.

**fdrs.md**: Proposition 158 (the dense circuit). -/
theorem exists_dense_circuit (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : Circuit n, C.Computes (fourierMatrix n) ∧ C.size = n * (2 * n - 1) := by
  let f : ℕ → List (ℂ × ℕ) := fun r => List.ofFn fun j : Fin n => (zeta n ^ (r * (j : ℕ)), (j : ℕ))
  have hf : ∀ r < n, (f r).length = n ∧ ∀ p ∈ f r, p.2 < n + 1 := fun r _ => by
    refine ⟨by simp [f], fun p hp => ?_⟩
    simp only [f, List.mem_ofFn] at hp
    obtain ⟨j, rfl⟩ := hp
    simp
  have hlen : (blockGates (n + 1) (2 * n - 1) f n).length = n * (2 * n - 1) :=
    blockGates_length _ _ _ _ (fun r hr => (hf r hr).1) hn
  have hout : ∀ m : Fin n, n + 1 + (m : ℕ) * (2 * n - 1) + (2 * n - 2) <
      n + 1 + (blockGates (n + 1) (2 * n - 1) f n).length := by
    intro m
    rw [hlen]
    have key : ((m : ℕ) + 1) * (2 * n - 1) ≤ n * (2 * n - 1) := Nat.mul_le_mul_right _ m.isLt
    rw [add_mul, one_mul] at key
    omega
  refine ⟨Circuit.ofGates n (blockGates (n + 1) (2 * n - 1) f n)
    (fun m => n + 1 + (m : ℕ) * (2 * n - 1) + (2 * n - 2)) hout, fun x => ?_, ?_⟩
  · funext m
    rw [Circuit.ofGates_eval]
    have hspec := blockGates_spec (n + 1) n hn f (initState n x) rfl n hf
    rw [hspec.2 m m.isLt]
    simp only [f, List.map_ofFn, List.sum_ofFn, Function.comp_apply, initState, Fin.is_lt,
      dif_pos, Matrix.mulVec, dotProduct, fourierMatrix]
  · rw [Circuit.ofGates_size, hlen]

/-! ## Corollary 34: the binary schedule -/

/-- The binary schedule `b_i = 2`. -/
def radixTwo : RadixSeq := ⟨fun _ => 2, fun _ => le_rfl⟩

theorem placeValue_radixTwo (m : ℕ) : placeValue radixTwo m = 2 ^ m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [placeValue.succ, ih, pow_succ]; rfl

/-- **Corollary 34 (binary count).** Length `N = 2^{k+1}` has an exact circuit with
`3 · N · (k + 1) = 3 N log₂ N` gates.

**fdrs.md**: Corollary 34 (the binary count). -/
theorem exists_radixTwo_circuit (k : ℕ) :
    ∃ C : Circuit (2 ^ (k + 1)), C.Computes (fourierMatrix (2 ^ (k + 1))) ∧
      C.size = 3 * 2 ^ (k + 1) * (k + 1) := by
  have h := exists_staged_circuit radixTwo k
  rw [placeValue_radixTwo] at h
  obtain ⟨C, hC, hsize⟩ := h
  refine ⟨C, hC, ?_⟩
  rw [hsize]
  simp only [radixTwo, Finset.sum_const, Finset.card_range, smul_eq_mul]
  ring

/-- **Corollary 34 (family 130's statement for `c > 3`).** The staged binary circuits
alone give `size < c · n · log₂ n` for every `c > 3` at arbitrarily large lengths.

**fdrs.md**: Corollary 34 (the binary count). -/
theorem mainStatement_of_three_lt (c : ℝ) (hc : 3 < c) (N₀ : ℕ) :
    ∃ n : ℕ, N₀ ≤ n ∧ ∃ C : Circuit n, C.Computes (fourierMatrix n) ∧
      (C.size : ℝ) < c * (n : ℝ) * Real.logb 2 (n : ℝ) := by
  obtain ⟨C, hC, hsize⟩ := exists_radixTwo_circuit N₀
  refine ⟨2 ^ (N₀ + 1), ?_, C, hC, ?_⟩
  · have := Nat.lt_two_pow_self (n := N₀ + 1); omega
  · rw [hsize]
    push_cast
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
    push_cast
    have hpos : (0 : ℝ) < 2 ^ (N₀ + 1) * ((N₀ : ℝ) + 1) := by positivity
    have key := mul_lt_mul_of_pos_right hc hpos
    linarith [key, show (3 : ℝ) * 2 ^ (N₀ + 1) * ((N₀ : ℝ) + 1) =
        3 * (2 ^ (N₀ + 1) * ((N₀ : ℝ) + 1)) by ring,
      show c * 2 ^ (N₀ + 1) * ((N₀ : ℝ) + 1) = c * (2 ^ (N₀ + 1) * ((N₀ : ℝ) + 1)) by ring]

end FdrsFormal.NumberTheory.Characters.FourierCircuit
