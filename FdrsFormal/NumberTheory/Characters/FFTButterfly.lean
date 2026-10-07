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

# The radix-2 butterfly circuit (Phase 3 addendum, §1.8)

On a binary digit the stage operator of Definition 214 collapses to a
butterfly. This file proves that and builds the classical radix-2 circuit in
family 130's gate model (Definition 216), with an exact gate count.

- **Proposition 159** (`stageFactor_split`, `stage_radixTwo`): the stage factor
  splits off its own digit, `S_i(t; ρ) = ζ_{b_i}^{t ρ_i} · W_i(ρ)^{(t)}`, where the
  twiddle part does not see `ρ_i`; on a binary digit, with `ζ_2 = -1`,
  `(T_i y)(ρ) = y(ρ⁰) + (-1)^{ρ_i} W_i(ρ⁰) y(ρ¹)` — the two outputs of a pair
  share one product.
- **Theorem 124** (`exists_butterfly_circuit`): length `N = 2^{k+1}` has an exact
  Fourier circuit with **exactly** `3 · 2^k · (k + 1) = (3/2) N log₂ N` gates —
  per stage, `N/2` butterflies of three gates (one scale, one add, one subtract).
- **Corollary 35** (`mainStatement_of_three_halves_lt`): family 130's statement
  holds for every `c > 3/2` by this construction.

**Honest scope.** Classical (Cooley–Tukey 1965). The construction scales by every
twiddle, trivial or not; skipping the `W = 1` products is `FFTTwiddleSkip.lean`
(§1.9). Split-radix schemes and family 130's every-`c > 0` theorem are not
claimed here.
-/

import FdrsFormal.NumberTheory.Characters.FFTCircuit

namespace FdrsFormal.NumberTheory.Characters.FourierCircuit

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite
open FdrsFormal.NumberTheory.Characters.MixedRadixFFT

/-! ## Butterfly gates -/

/-- One butterfly: `t = W · v(a₁)`, then `v(a₀) + t` and `v(a₀) - t`. -/
def bfGates (W : ℂ) (a0 a1 pos : ℕ) : List LGate := [.scale W a1, .add a0 pos, .sub a0 pos]

theorem bfGates_spec (W : ℂ) (a0 a1 : ℕ) (s : State) (h0 : a0 < s.pos) (h1 : a1 < s.pos) :
    (exec (bfGates W a0 a1 s.pos) s).pos = s.pos + 3 ∧
    (exec (bfGates W a0 a1 s.pos) s).val (s.pos + 1) = s.val a0 + W * s.val a1 ∧
    (exec (bfGates W a0 a1 s.pos) s).val (s.pos + 2) = s.val a0 - W * s.val a1 := by
  have e0 : a0 ≠ s.pos := by omega
  have e1 : a1 ≠ s.pos := by omega
  have e0' : a0 ≠ s.pos + 1 := by omega
  have e2 : s.pos + 2 ≠ s.pos + 1 := by omega
  have e3 : s.pos + 2 ≠ s.pos := by omega
  have e4 : s.pos + 1 ≠ s.pos := by omega
  simp only [bfGates, exec_cons, exec_nil, LGate.eval]
  refine ⟨trivial, ?_, ?_⟩
  · simp [Function.update_apply, e0]
  · simp [e0, e0']

/-- A row of `Q` butterflies, butterfly `q` occupying registers `pos0 + 3q + {0,1,2}`. -/
def bfRow (pos0 : ℕ) (it : ℕ → ℂ × ℕ × ℕ) : ℕ → List LGate
  | 0 => []
  | Q + 1 => bfRow pos0 it Q ++ bfGates (it Q).1 (it Q).2.1 (it Q).2.2 (pos0 + 3 * Q)

theorem bfRow_length (pos0 : ℕ) (it : ℕ → ℂ × ℕ × ℕ) :
    ∀ Q, (bfRow pos0 it Q).length = 3 * Q
  | 0 => rfl
  | Q + 1 => by rw [bfRow, List.length_append, bfRow_length pos0 it Q]; simp [bfGates]; ring

/-- **A row of butterflies.** With every address below `pos0`, butterfly `q` leaves its
sum at `pos0 + 3q + 1` and its difference at `pos0 + 3q + 2`. -/
theorem bfRow_spec (pos0 : ℕ) (it : ℕ → ℂ × ℕ × ℕ) (s : State) (hs : s.pos = pos0) :
    ∀ Q, (∀ q < Q, (it q).2.1 < pos0 ∧ (it q).2.2 < pos0) →
      (exec (bfRow pos0 it Q) s).pos = pos0 + 3 * Q ∧
      ∀ q < Q,
        (exec (bfRow pos0 it Q) s).val (pos0 + 3 * q + 1) =
            s.val (it q).2.1 + (it q).1 * s.val (it q).2.2 ∧
        (exec (bfRow pos0 it Q) s).val (pos0 + 3 * q + 2) =
            s.val (it q).2.1 - (it q).1 * s.val (it q).2.2
  | 0, _ => ⟨by simp [bfRow, exec, hs], fun q hq => absurd hq (Nat.not_lt_zero _)⟩
  | Q + 1, hit => by
    obtain ⟨hpos, hval⟩ := bfRow_spec pos0 it s hs Q fun q hq => hit q (by omega)
    obtain ⟨h0, h1⟩ := hit Q (by omega)
    set S := exec (bfRow pos0 it Q) s
    have hS : S.pos = pos0 + 3 * Q := hpos
    have hb := bfGates_spec (it Q).1 (it Q).2.1 (it Q).2.2 S (by omega) (by omega)
    rw [hS] at hb
    have hexec : exec (bfRow pos0 it (Q + 1)) s =
        exec (bfGates (it Q).1 (it Q).2.1 (it Q).2.2 (pos0 + 3 * Q)) S := by
      simp only [bfRow, exec_append]; rfl
    have hfr0 : S.val (it Q).2.1 = s.val (it Q).2.1 := by
      simp only [S]; exact exec_frame _ _ (by omega)
    have hfr1 : S.val (it Q).2.2 = s.val (it Q).2.2 := by
      simp only [S]; exact exec_frame _ _ (by omega)
    rw [hexec]
    refine ⟨by rw [hb.1]; ring, fun q hq => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq | rfl
    · have hlt1 : pos0 + 3 * q + 1 < S.pos := by rw [hS]; omega
      have hlt2 : pos0 + 3 * q + 2 < S.pos := by rw [hS]; omega
      rw [exec_frame _ _ hlt1, exec_frame _ _ hlt2]
      exact hval q hq
    · rw [hb.2.1, hb.2.2, hfr0, hfr1]
      exact ⟨rfl, rfl⟩

/-! ## Proposition 159: the binary stage is a butterfly -/

variable {b : RadixSeq}

/-- The twiddle of stage `i`: the part of the stage-`1` factor that does not see `ρ_i`. -/
noncomputable def twiddle (k : ℕ) (i : Fin (k + 1)) (ρ : FiniteRadixSpace b k) : ℂ :=
  ∏ j : Fin (k + 1), if i < j then zeta (blockProd b i ((j : ℕ) + 1)) ^ (ρ j : ℕ) else 1

/-- **Proposition 159 (the stage factor splits off its digit).**

**fdrs.md**: Proposition 159 (the binary butterfly). -/
theorem stageFactor_split (k : ℕ) (i : Fin (k + 1)) (t : ℕ) (ρ : FiniteRadixSpace b k) :
    stageFactor k i t ρ = zeta (b i) ^ (t * (ρ i : ℕ)) *
      ∏ j : Fin (k + 1), if i < j then zeta (blockProd b i ((j : ℕ) + 1)) ^ (t * (ρ j : ℕ))
        else 1 := by
  rw [stageFactor]
  have hsplit : ∀ j : Fin (k + 1),
      (if i ≤ j then zeta (blockProd b i ((j : ℕ) + 1)) ^ (t * (ρ j : ℕ)) else 1) =
        (if i = j then zeta (blockProd b i ((j : ℕ) + 1)) ^ (t * (ρ j : ℕ)) else 1) *
        (if i < j then zeta (blockProd b i ((j : ℕ) + 1)) ^ (t * (ρ j : ℕ)) else 1) := by
    intro j
    rcases lt_trichotomy i j with h | h | h
    · simp [h.le, h.ne, h]
    · subst h; simp
    · simp [not_le.mpr h, h.ne', not_lt.mpr h.le]
  rw [Finset.prod_congr rfl fun j _ => hsplit j, Finset.prod_mul_distrib, Finset.prod_ite_eq,
    if_pos (Finset.mem_univ _), blockProd_succ]

/-- The twiddle does not see the stage's own digit. -/
theorem twiddle_update (k : ℕ) (i : Fin (k + 1)) (ρ : FiniteRadixSpace b k) (t : Fin (b i)) :
    twiddle k i (Function.update ρ i t) = twiddle k i ρ := by
  refine Finset.prod_congr rfl fun j _ => ?_
  split_ifs with h
  · rw [Function.update_of_ne (ne_of_lt h).symm]
  · rfl

theorem zeta_two : zeta 2 = -1 := by
  rw [zeta, show (2 : ℂ) * (Real.pi : ℂ) * Complex.I / ((2 : ℕ) : ℂ) = Real.pi * Complex.I by
    push_cast; ring]
  exact Complex.exp_pi_mul_I

/-- **Proposition 159 (the binary butterfly).** On the binary schedule,
`(T_i y)(ρ) = y(ρ⁰) + (-1)^{ρ_i} · W_i(ρ⁰) · y(ρ¹)` with `ρ^t = ρ[i := t]`.

**fdrs.md**: Proposition 159 (the binary butterfly). -/
theorem stage_radixTwo (k : ℕ) (i : Fin (k + 1)) (y : FiniteRadixSpace radixTwo k → ℂ)
    (ρ : FiniteRadixSpace radixTwo k) :
    stage k i y ρ =
      y (Function.update ρ i (0 : Fin 2)) +
        (-1) ^ (ρ i : ℕ) * twiddle k i (Function.update ρ i (0 : Fin 2)) *
          y (Function.update ρ i (1 : Fin 2)) := by
  show (∑ t : Fin 2, y (Function.update ρ i t) * stageFactor k i (t : ℕ) ρ) = _
  rw [Fin.sum_univ_two, stageFactor_split, stageFactor_split, twiddle_update]
  have h2 : zeta (radixTwo i) = -1 := zeta_two
  simp only [Fin.val_zero, Fin.val_one, zero_mul, pow_zero, one_mul, Finset.prod_const_one,
    ite_self, mul_one, h2, twiddle]
  ring

/-! ## Theorem 124: the butterfly circuit -/

section Butterfly

variable (k : ℕ)

/-- Pair representatives at digit `i`: points whose digit `i` is `0`. -/
def Low (i : Fin (k + 1)) : Type := {ρ : FiniteRadixSpace radixTwo k // (ρ i : ℕ) = 0}

noncomputable instance (i : Fin (k + 1)) : Fintype (Low k i) := by
  unfold Low; infer_instance

/-- The pair representative of `ρ`. -/
def lowOf (i : Fin (k + 1)) (ρ : FiniteRadixSpace radixTwo k) : Low k i :=
  ⟨Function.update ρ i (0 : Fin 2), by simp⟩

/-- Points are pairs (representative, digit). -/
def lowEquiv (i : Fin (k + 1)) : Low k i × Fin 2 ≃ FiniteRadixSpace radixTwo k where
  toFun p := Function.update p.1.1 i p.2
  invFun ρ := (lowOf k i ρ, ρ i)
  left_inv p := by
    obtain ⟨⟨ρ, hρ⟩, t⟩ := p
    have hρ0 : Function.update ρ i (0 : Fin 2) = ρ := by
      rw [Function.update_eq_self_iff]; exact Fin.ext hρ.symm
    simp only [lowOf, Function.update_idem, Function.update_self]
    exact Prod.ext (Subtype.ext hρ0) rfl
  right_inv ρ := by
    simp only [lowOf, Function.update_idem, Function.update_eq_self]

theorem card_low (i : Fin (k + 1)) : Fintype.card (Low k i) = 2 ^ k := by
  have h := Fintype.card_congr (lowEquiv k i)
  rw [Fintype.card_prod, Fintype.card_fin, card_finiteRadixSpace, placeValue_radixTwo,
    pow_succ] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h

/-- Numbering of the pairs at digit `i`. -/
noncomputable def lowNum (i : Fin (k + 1)) : Low k i ≃ Fin (Fintype.card (Low k i)) :=
  Fintype.equivFin _

/-- First free register of butterfly stage `s`. -/
noncomputable def bfPos : ℕ → ℕ
  | 0 => placeValue radixTwo (k + 1) + 1
  | s + 1 => bfPos s + 3 * Fintype.card (Low k (digitAt k s))

/-- Where the array after `s` butterfly stages lives. -/
noncomputable def bfAddr : ℕ → FiniteRadixSpace radixTwo k → ℕ
  | 0, τ => decodeFinite radixTwo k τ
  | s + 1, ρ => bfPos k s + 3 * (lowNum k (digitAt k s) (lowOf k (digitAt k s) ρ) : ℕ) + 1 +
      (ρ (digitAt k s) : ℕ)

/-- Butterfly `q` of stage `s`: twiddle and the two input registers. -/
noncomputable def bfItem (s q : ℕ) : ℂ × ℕ × ℕ :=
  if h : q < Fintype.card (Low k (digitAt k s)) then
    let ρ := ((lowNum k (digitAt k s)).symm ⟨q, h⟩).1
    (twiddle k (digitAt k s) ρ, bfAddr k s ρ,
      bfAddr k s (Function.update ρ (digitAt k s) (1 : Fin 2)))
  else (0, 0, 0)

/-- The first `s` butterfly stages. -/
noncomputable def bfStages : ℕ → List LGate
  | 0 => []
  | s + 1 => bfStages s ++ bfRow (bfPos k s) (bfItem k s) (Fintype.card (Low k (digitAt k s)))

end Butterfly

theorem bfStages_spec (k : ℕ) (x : Fin (placeValue radixTwo (k + 1)) → ℂ) :
    ∀ s, s ≤ k + 1 →
      (exec (bfStages k s) (initState _ x)).pos = bfPos k s ∧
      ∀ ρ, bfAddr k s ρ < bfPos k s ∧
        (exec (bfStages k s) (initState _ x)).val (bfAddr k s ρ) =
          stages k s (fun τ => extend x (decodeFinite radixTwo k τ)) ρ
  | 0, _ => by
    refine ⟨rfl, fun τ => ⟨?_, ?_⟩⟩
    · have := decodeFinite_lt k τ; simp only [bfAddr, bfPos]; omega
    · simp [bfStages, exec, initState, bfAddr, stages, extend]
  | s + 1, hs => by
    obtain ⟨hpos, hinv⟩ := bfStages_spec k x s (by omega)
    have hrow := bfRow_spec (bfPos k s) (bfItem k s) (exec (bfStages k s) (initState _ x)) hpos
      (Fintype.card (Low k (digitAt k s))) fun q hq => by
        simp only [bfItem, dif_pos hq]
        exact ⟨(hinv _).1, (hinv _).1⟩
    obtain ⟨hpos', hval⟩ := hrow
    have hexec : exec (bfStages k (s + 1)) (initState _ x) =
        exec (bfRow (bfPos k s) (bfItem k s) (Fintype.card (Low k (digitAt k s))))
          (exec (bfStages k s) (initState _ x)) := by
      simp only [bfStages, exec_append]
    rw [hexec]
    refine ⟨by rw [hpos']; rfl, fun ρ => ⟨?_, ?_⟩⟩
    · have hq := (lowNum k (digitAt k s) (lowOf k (digitAt k s) ρ)).isLt
      have hd : (ρ (digitAt k s) : ℕ) < 2 := (ρ (digitAt k s)).isLt
      simp only [bfAddr, bfPos]
      omega
    · set q := lowNum k (digitAt k s) (lowOf k (digitAt k s) ρ) with hqdef
      have hq := q.isLt
      have hsymm : (lowNum k (digitAt k s)).symm ⟨q, hq⟩ = lowOf k (digitAt k s) ρ := by
        rw [Fin.eta, hqdef, Equiv.symm_apply_apply]
      obtain ⟨h1, h2⟩ := hval q hq
      simp only [bfItem, dif_pos hq, hsymm, lowOf, Function.update_idem] at h1 h2
      have hstage : stages k (s + 1) (fun τ => extend x (decodeFinite radixTwo k τ)) ρ =
          stage k (digitAt k s) (stages k s (fun τ => extend x (decodeFinite radixTwo k τ))) ρ := by
        simp only [stages, dif_pos (show s ≤ k by omega)]; rfl
      rw [hstage, stage_radixTwo, ← (hinv _).2, ← (hinv _).2]
      have hlt : (ρ (digitAt k s) : ℕ) < 2 := (ρ (digitAt k s)).isLt
      have haddr : bfAddr k (s + 1) ρ = bfPos k s + 3 * (q : ℕ) + 1 + (ρ (digitAt k s) : ℕ) := rfl
      have hd : (ρ (digitAt k s) : ℕ) = 0 ∨ (ρ (digitAt k s) : ℕ) = 1 := by omega
      rcases hd with h0 | h1'
      · rw [haddr, h0, add_zero, h1, pow_zero, one_mul]
      · rw [haddr, h1', show bfPos k s + 3 * (q : ℕ) + 1 + 1 = bfPos k s + 3 * (q : ℕ) + 2 by ring,
          h2, pow_one]
        ring

theorem bfStages_length (k : ℕ) :
    ∀ s, (bfStages k s).length = 3 * 2 ^ k * s
  | 0 => rfl
  | s + 1 => by
    rw [bfStages, List.length_append, bfStages_length k s, bfRow_length, card_low]
    ring

/-- **Theorem 124 (the butterfly circuit).** Length `N = 2^{k+1}` has an exact Fourier
circuit with `3 · 2^k · (k + 1) = (3/2) N log₂ N` gates.

**fdrs.md**: Theorem 124 (the butterfly circuit). -/
theorem exists_butterfly_circuit (k : ℕ) :
    ∃ C : Circuit (2 ^ (k + 1)), C.Computes (fourierMatrix (2 ^ (k + 1))) ∧
      C.size = 3 * 2 ^ k * (k + 1) := by
  suffices h : ∃ C : Circuit (placeValue radixTwo (k + 1)),
      C.Computes (fourierMatrix (placeValue radixTwo (k + 1))) ∧
      C.size = 3 * 2 ^ k * (k + 1) by
    rwa [placeValue_radixTwo] at h
  set N := placeValue radixTwo (k + 1)
  have hout : ∀ m : Fin N,
      bfAddr k (k + 1) ((rdecEquiv radixTwo k).symm m) < N + 1 + (bfStages k (k + 1)).length := by
    intro m
    have h := bfStages_spec k (fun _ => 0) (k + 1) le_rfl
    have hp := h.1
    rw [exec_pos] at hp
    have hst : bfPos k (k + 1) = N + 1 + (bfStages k (k + 1)).length := by
      rw [← hp]; rfl
    exact (h.2 _).1.trans_eq hst
  refine ⟨Circuit.ofGates N (bfStages k (k + 1))
    (fun m => bfAddr k (k + 1) ((rdecEquiv radixTwo k).symm m)) hout, fun x => ?_, ?_⟩
  · funext m
    rw [Circuit.ofGates_eval, ((bfStages_spec k x (k + 1) le_rfl).2 _).2, fft_eq_dft]
    have hm : reverseDecode radixTwo k ((rdecEquiv radixTwo k).symm m) = m :=
      congrArg Fin.val ((rdecEquiv radixTwo k).apply_symm_apply m)
    rw [hm, dft, Finset.sum_range (fun n => extend x n * zeta N ^ ((m : ℕ) * n))]
    simp only [Matrix.mulVec, dotProduct, fourierMatrix, extend]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dif_pos j.isLt, mul_comm]
  · rw [Circuit.ofGates_size, bfStages_length]

/-- **Corollary 35.** Family 130's statement holds for every `c > 3/2` by the
butterfly circuits alone.

**fdrs.md**: Corollary 35 (the butterfly constant). -/
theorem mainStatement_of_three_halves_lt (c : ℝ) (hc : 3 / 2 < c) (N₀ : ℕ) :
    ∃ n : ℕ, N₀ ≤ n ∧ ∃ C : Circuit n, C.Computes (fourierMatrix n) ∧
      (C.size : ℝ) < c * (n : ℝ) * Real.logb 2 (n : ℝ) := by
  obtain ⟨C, hC, hsize⟩ := exists_butterfly_circuit N₀
  refine ⟨2 ^ (N₀ + 1), ?_, C, hC, ?_⟩
  · have := Nat.lt_two_pow_self (n := N₀ + 1); omega
  · rw [hsize]
    push_cast
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
    push_cast
    have hpos : (0 : ℝ) < 2 ^ N₀ * ((N₀ : ℝ) + 1) := by positivity
    have key := mul_lt_mul_of_pos_right (show (3 : ℝ) < 2 * c by linarith) hpos
    linarith [key, show (3 : ℝ) * 2 ^ N₀ * ((N₀ : ℝ) + 1) = 3 * (2 ^ N₀ * ((N₀ : ℝ) + 1)) by ring,
      show c * 2 ^ (N₀ + 1) * ((N₀ : ℝ) + 1) = 2 * c * (2 ^ N₀ * ((N₀ : ℝ) + 1)) by ring]

end FdrsFormal.NumberTheory.Characters.FourierCircuit
