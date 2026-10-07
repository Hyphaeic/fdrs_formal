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

# Skipping trivial twiddles: how far the constant drops (Phase 3 addendum, §1.9)

The butterfly circuit of §1.8 multiplies by every twiddle. This file finds every
trivial one, skips it, and counts the result exactly.

- **Proposition 160** (`twiddle_eq_one_iff`): on the binary schedule the stage-`i`
  twiddle is trivial, `W_i(ρ) = 1`, **iff** every digit above `i` vanishes. Writing
  `W_i(ρ) = ζ_M^E` with `M = 2^{k+1-i}` and `E = Σ_{j>i} 2^{k-j} ρ_j < M/2`, the
  power is `1` exactly when `E = 0`. So digit `i` has exactly `2^i` trivial pairs,
  and no twiddle equals `-1`.
- **Theorem 125** (`exists_skip_circuit`): length `N = 2^{k+1}` has an exact Fourier
  circuit with exactly `(3/2) N log₂ N − N + 1` gates — stated over `ℕ` as
  `size + 2^{k+1} = 3 · 2^k · (k + 1) + 1`. Trivial pairs cost two gates (add,
  subtract), the rest three.
- **Corollary 36** (`skip_gap`): the saving over §1.8 is exactly `N − 1` gates. The
  normalized count `size / (N log₂ N) = 3/2 − (N − 1)/(N log₂ N)` rises *toward*
  `3/2` — skipping trivial twiddles moves the lower-order term, not the constant.

**Honest scope.** Classical (radix-2 Cooley–Tukey with the trivial twiddles
removed: `N log₂ N` additions and `(N/2) log₂ N − N + 1` multiplications). In this
gate model a multiplication by `±i` is a charged scale gate, so the radix-4 and
split-radix savings of the real-arithmetic literature do not transfer as they
stand; family 130 shows the constant itself can be pushed to any `c > 0` along a
subsequence. Neither is claimed here.
-/

import FdrsFormal.NumberTheory.Characters.FFTButterfly

namespace FdrsFormal.NumberTheory.Characters.FourierCircuit

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite
open FdrsFormal.NumberTheory.Characters.MixedRadixFFT

/-! ## Variable-width butterflies -/

open scoped Classical in
/-- Gates of one butterfly: two when the twiddle is trivial, three otherwise. -/
noncomputable def bfWidth (W : ℂ) : ℕ := if W = 1 then 2 else 3

open scoped Classical in
/-- A butterfly that skips a trivial twiddle. -/
noncomputable def bf2 (W : ℂ) (a0 a1 pos : ℕ) : List LGate :=
  if W = 1 then [.add a0 a1, .sub a0 a1] else bfGates W a0 a1 pos

theorem two_le_bfWidth (W : ℂ) : 2 ≤ bfWidth W := by
  unfold bfWidth; split_ifs <;> omega

theorem bf2_length (W : ℂ) (a0 a1 pos : ℕ) : (bf2 W a0 a1 pos).length = bfWidth W := by
  unfold bf2 bfWidth; split_ifs <;> rfl

theorem bf2_spec (W : ℂ) (a0 a1 : ℕ) (s : State) (h0 : a0 < s.pos) (h1 : a1 < s.pos) :
    (exec (bf2 W a0 a1 s.pos) s).pos = s.pos + bfWidth W ∧
    (exec (bf2 W a0 a1 s.pos) s).val (s.pos + bfWidth W - 2) = s.val a0 + W * s.val a1 ∧
    (exec (bf2 W a0 a1 s.pos) s).val (s.pos + bfWidth W - 1) = s.val a0 - W * s.val a1 := by
  unfold bf2 bfWidth
  split_ifs with hW
  · subst hW
    have e0 : a0 ≠ s.pos := by omega
    have e1 : a1 ≠ s.pos := by omega
    have e2 : s.pos + 1 ≠ s.pos := by omega
    simp only [exec_cons, exec_nil, LGate.eval]
    refine ⟨trivial, ?_, ?_⟩
    · rw [show s.pos + 2 - 2 = s.pos by omega]
      simp [Function.update_apply]
    · rw [show s.pos + 2 - 1 = s.pos + 1 by omega]
      simp [e0, e1]
  · obtain ⟨hp, hs, hd⟩ := bfGates_spec W a0 a1 s h0 h1
    refine ⟨hp, ?_, ?_⟩
    · rw [show s.pos + 3 - 2 = s.pos + 1 by omega]; exact hs
    · rw [show s.pos + 3 - 1 = s.pos + 2 by omega]; exact hd

/-- Start of butterfly `q` in a variable-width row. -/
noncomputable def vStart (pos0 : ℕ) (it : ℕ → ℂ × ℕ × ℕ) (q : ℕ) : ℕ :=
  pos0 + ∑ q' ∈ Finset.range q, bfWidth (it q').1

/-- A row of `Q` butterflies, each skipping a trivial twiddle. -/
noncomputable def vRow (pos0 : ℕ) (it : ℕ → ℂ × ℕ × ℕ) : ℕ → List LGate
  | 0 => []
  | Q + 1 => vRow pos0 it Q ++ bf2 (it Q).1 (it Q).2.1 (it Q).2.2 (vStart pos0 it Q)

theorem vStart_succ (pos0 : ℕ) (it : ℕ → ℂ × ℕ × ℕ) (q : ℕ) :
    vStart pos0 it (q + 1) = vStart pos0 it q + bfWidth (it q).1 := by
  simp [vStart, Finset.sum_range_succ, add_assoc]

theorem vStart_mono (pos0 : ℕ) (it : ℕ → ℂ × ℕ × ℕ) {q Q : ℕ} (h : q ≤ Q) :
    vStart pos0 it q ≤ vStart pos0 it Q := by
  unfold vStart
  exact Nat.add_le_add_left (Finset.sum_le_sum_of_subset (Finset.range_mono h)) _

theorem vRow_length (pos0 : ℕ) (it : ℕ → ℂ × ℕ × ℕ) :
    ∀ Q, (vRow pos0 it Q).length = ∑ q ∈ Finset.range Q, bfWidth (it q).1
  | 0 => rfl
  | Q + 1 => by rw [vRow, List.length_append, vRow_length pos0 it Q, bf2_length,
      Finset.sum_range_succ]

/-- **A row of skipping butterflies.** Butterfly `q`'s sum and difference land in its
last two registers. -/
theorem vRow_spec (pos0 : ℕ) (it : ℕ → ℂ × ℕ × ℕ) (s : State) (hs : s.pos = pos0) :
    ∀ Q, (∀ q < Q, (it q).2.1 < pos0 ∧ (it q).2.2 < pos0) →
      (exec (vRow pos0 it Q) s).pos = vStart pos0 it Q ∧
      ∀ q < Q,
        (exec (vRow pos0 it Q) s).val (vStart pos0 it q + bfWidth (it q).1 - 2) =
            s.val (it q).2.1 + (it q).1 * s.val (it q).2.2 ∧
        (exec (vRow pos0 it Q) s).val (vStart pos0 it q + bfWidth (it q).1 - 1) =
            s.val (it q).2.1 - (it q).1 * s.val (it q).2.2
  | 0, _ => ⟨by simp [vRow, exec, hs, vStart], fun q hq => absurd hq (Nat.not_lt_zero _)⟩
  | Q + 1, hit => by
    obtain ⟨hpos, hval⟩ := vRow_spec pos0 it s hs Q fun q hq => hit q (by omega)
    obtain ⟨h0, h1⟩ := hit Q (by omega)
    set S := exec (vRow pos0 it Q) s
    have hS : S.pos = vStart pos0 it Q := hpos
    have hge : pos0 ≤ vStart pos0 it Q := Nat.le_add_right _ _
    have hb := bf2_spec (it Q).1 (it Q).2.1 (it Q).2.2 S (by omega) (by omega)
    rw [hS] at hb
    have hexec : exec (vRow pos0 it (Q + 1)) s =
        exec (bf2 (it Q).1 (it Q).2.1 (it Q).2.2 (vStart pos0 it Q)) S := by
      simp only [vRow, exec_append]; rfl
    have hfr0 : S.val (it Q).2.1 = s.val (it Q).2.1 := by
      simp only [S]; exact exec_frame _ _ (by omega)
    have hfr1 : S.val (it Q).2.2 = s.val (it Q).2.2 := by
      simp only [S]; exact exec_frame _ _ (by omega)
    rw [hexec]
    refine ⟨by rw [hb.1, vStart_succ], fun q hq => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq | rfl
    · have hw := two_le_bfWidth (it q).1
      have hend : vStart pos0 it q + bfWidth (it q).1 ≤ S.pos := by
        rw [hS, ← vStart_succ]; exact vStart_mono pos0 it hq
      have ha : vStart pos0 it q + bfWidth (it q).1 - 2 < S.pos := by omega
      have hb' : vStart pos0 it q + bfWidth (it q).1 - 1 < S.pos := by omega
      rw [exec_frame _ S ha, exec_frame _ S hb']
      exact hval q hq
    · rw [hb.2.1, hb.2.2, hfr0, hfr1]
      exact ⟨rfl, rfl⟩

/-! ## Proposition 160: which twiddles are trivial -/

theorem blockProd_radixTwo (a c : ℕ) : blockProd radixTwo a c = 2 ^ (c - a) := by
  simp [blockProd, radixTwo, Finset.prod_const, Nat.card_Ico]

/-- `Σ_{i < j ≤ k} 2^{k-j} + 1 = 2^{k-i}`. -/
theorem geom_tail (i : ℕ) : ∀ k, i ≤ k →
    ∑ j ∈ Finset.range (k + 1), (if i < j then 2 ^ (k - j) else 0) + 1 = 2 ^ (k - i) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    rw [Finset.sum_eq_zero fun j hj => if_neg (by simp at hj; omega)]
    simp
  | succ k hik ih =>
    rw [Finset.sum_range_succ, if_pos (show i < k + 1 by omega), Nat.sub_self, pow_zero]
    have h2 : ∑ j ∈ Finset.range (k + 1), (if i < j then 2 ^ (k + 1 - j) else 0) =
        2 * ∑ j ∈ Finset.range (k + 1), (if i < j then 2 ^ (k - j) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      simp at hj
      split_ifs
      · rw [show k + 1 - j = (k - j) + 1 by omega, pow_succ]; ring
      · rfl
    rw [h2, show k + 1 - i = (k - i) + 1 by omega, pow_succ]
    omega

/-- **Proposition 160 (trivial twiddles).** On the binary schedule, `W_i(ρ) = 1` iff
every digit above `i` is `0`.

**fdrs.md**: Proposition 160 (trivial twiddles). -/
theorem twiddle_eq_one_iff (k : ℕ) (i : Fin (k + 1)) (ρ : FiniteRadixSpace radixTwo k) :
    twiddle k i ρ = 1 ↔ ∀ j : Fin (k + 1), i < j → (ρ j : ℕ) = 0 := by
  have hik := i.isLt
  set M := 2 ^ (k + 1 - (i : ℕ)) with hM
  set E := ∑ j : Fin (k + 1), (if i < j then 2 ^ (k - (j : ℕ)) * (ρ j : ℕ) else 0) with hE
  -- each factor is a power of ζ_M
  have hfac : ∀ j : Fin (k + 1),
      (if i < j then zeta (blockProd radixTwo i ((j : ℕ) + 1)) ^ (ρ j : ℕ) else 1) =
        zeta M ^ (if i < j then 2 ^ (k - (j : ℕ)) * (ρ j : ℕ) else 0) := by
    intro j
    split_ifs with h
    · have hij : (i : ℕ) < j := h
      have hj := j.isLt
      rw [blockProd_radixTwo,
        show M = 2 ^ ((j : ℕ) + 1 - i) * 2 ^ (k - (j : ℕ)) by
          rw [hM, ← pow_add]; congr 1; omega]
      exact (zeta_mul_pow_mul _ _ _ (by positivity) (by positivity)).symm
    · simp
  have hW : twiddle k i ρ = zeta M ^ E := by
    rw [twiddle, Finset.prod_congr rfl fun j _ => hfac j, Finset.prod_pow_eq_pow_sum]
  -- E < M
  have hEle : E ≤ ∑ j : Fin (k + 1), (if i < j then 2 ^ (k - (j : ℕ)) else 0) := by
    refine Finset.sum_le_sum fun j _ => ?_
    split_ifs
    · have : (ρ j : ℕ) < 2 := (ρ j).isLt
      calc 2 ^ (k - (j : ℕ)) * (ρ j : ℕ) ≤ 2 ^ (k - (j : ℕ)) * 1 :=
            Nat.mul_le_mul_left _ (by omega)
        _ = _ := mul_one _
    · exact le_rfl
  have hgeo := geom_tail i k (by omega)
  rw [← Fin.sum_univ_eq_sum_range (fun j => if (i : ℕ) < j then 2 ^ (k - j) else 0) (k + 1)]
    at hgeo
  have hEM : E < M := by
    have hlt : E < 2 ^ (k - (i : ℕ)) := by
      have : (∑ j : Fin (k + 1), if i < j then 2 ^ (k - (j : ℕ)) else 0) =
          ∑ j : Fin (k + 1), if (i : ℕ) < (j : ℕ) then 2 ^ (k - (j : ℕ)) else 0 := rfl
      omega
    calc E < 2 ^ (k - (i : ℕ)) := hlt
      _ ≤ M := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hMne : M ≠ 0 := by positivity
  have hprim : IsPrimitiveRoot (zeta M) M := Complex.isPrimitiveRoot_exp M hMne
  rw [hW, hprim.pow_eq_one_iff_dvd]
  constructor
  · intro hdvd j hj
    have hE0 : E = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hEM
    have := (Finset.sum_eq_zero_iff.mp hE0) j (Finset.mem_univ j)
    rw [if_pos hj] at this
    exact (Nat.mul_eq_zero.mp this).resolve_left (by positivity)
  · intro h
    have hE0 : E = 0 := Finset.sum_eq_zero fun j _ => by
      split_ifs with hj
      · rw [h j hj, mul_zero]
      · rfl
    rw [hE0]
    exact dvd_zero _

/-! ## Counting the trivial pairs -/

section Counting

variable (k : ℕ)

/-- Points with every digit from `i` up equal to `0` are the functions on the
digits below `i`. -/
def highZeroEquiv (i : Fin (k + 1)) :
    {ρ : FiniteRadixSpace radixTwo k // ∀ j : Fin (k + 1), i ≤ j → (ρ j : ℕ) = 0} ≃ ({j : Fin (k + 1) // (j : ℕ) < i} → Fin 2) where
  toFun ρ j := ρ.1 j.1
  invFun g := ⟨fun j => if h : (j : ℕ) < i then g ⟨j, h⟩ else (0 : Fin 2), fun j hj => by
    have : ¬ (j : ℕ) < i := by have : (i : ℕ) ≤ j := hj; omega
    simp [this]⟩
  left_inv ρ := by
    obtain ⟨ρ, hρ⟩ := ρ
    refine Subtype.ext (funext fun j => ?_)
    by_cases h : (j : ℕ) < i
    · simp [h]
    · simp only [h, dif_neg, not_false_eq_true]
      exact Fin.ext (hρ j (by show (i : ℕ) ≤ j; omega)).symm
  right_inv g := by
    funext ⟨j, h⟩
    simp [h]

/-- Digits below `i`, as a type of size `i`. -/
def belowEquiv (i : Fin (k + 1)) : {j : Fin (k + 1) // (j : ℕ) < i} ≃ Fin i where
  toFun j := ⟨j.1, j.2⟩
  invFun j := ⟨⟨j, by have := i.isLt; omega⟩, j.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_highZero (i : Fin (k + 1)) :
    Fintype.card {ρ : FiniteRadixSpace radixTwo k // ∀ j : Fin (k + 1), i ≤ j → (ρ j : ℕ) = 0} =
      2 ^ (i : ℕ) := by
  rw [Fintype.card_congr (highZeroEquiv k i), Fintype.card_fun, Fintype.card_fin,
    Fintype.card_congr (belowEquiv k i), Fintype.card_fin]

/-- Pair representative number `q` at digit `i`. -/
noncomputable def repAt (i : Fin (k + 1)) (q : ℕ) : FiniteRadixSpace radixTwo k :=
  if h : q < Fintype.card (Low k i) then ((lowNum k i).symm ⟨q, h⟩).1 else default

/-- **The width of a stage.** Over the `2^k` pairs at digit `i`, the skipping
butterflies spend `3 · 2^k − 2^i` gates.

**fdrs.md**: Proposition 160 (trivial twiddles). -/
theorem sum_bfWidth (i : Fin (k + 1)) :
    ∑ q ∈ Finset.range (Fintype.card (Low k i)), bfWidth (twiddle k i (repAt k i q)) + 2 ^ (i : ℕ) =
      3 * 2 ^ k := by
  classical
  -- re-index the pairs by `Low`, then by the filtered point set
  have h1 : ∑ q ∈ Finset.range (Fintype.card (Low k i)), bfWidth (twiddle k i (repAt k i q)) =
      ∑ ℓ : Low k i, bfWidth (twiddle k i ℓ.1) := by
    rw [Finset.sum_range (fun q => bfWidth (twiddle k i (repAt k i q)))]
    refine Fintype.sum_equiv (lowNum k i).symm _ _ fun q => ?_
    simp only [repAt, dif_pos q.isLt, Fin.eta]
  let p : FiniteRadixSpace radixTwo k → Prop := fun ρ => (ρ i : ℕ) = 0
  have h2 : ∑ ℓ : Low k i, bfWidth (twiddle k i ℓ.1) =
      ∑ ρ ∈ Finset.univ.filter p, bfWidth (twiddle k i ρ) :=
    (Finset.sum_subtype (p := p) (Finset.univ.filter p) (fun ρ => by simp [p])
      (fun ρ => bfWidth (twiddle k i ρ))).symm
  have hsplit : ∀ ρ : FiniteRadixSpace radixTwo k, bfWidth (twiddle k i ρ) + (if twiddle k i ρ = 1 then 1 else 0) = 3 := by
    intro ρ; unfold bfWidth; split_ifs <;> rfl
  have h3 : ∑ ρ ∈ Finset.univ.filter p, bfWidth (twiddle k i ρ) +
      ((Finset.univ.filter p).filter fun ρ => twiddle k i ρ = 1).card =
        3 * (Finset.univ.filter p).card := by
    rw [Finset.card_filter, ← Finset.sum_add_distrib, Finset.sum_congr rfl fun ρ _ => hsplit ρ,
      Finset.sum_const, smul_eq_mul, mul_comm]
  have hcardp : (Finset.univ.filter p).card = 2 ^ k := by
    rw [← card_low k i]; exact (Fintype.card_subtype p).symm
  have hcardt : ((Finset.univ.filter p).filter fun ρ => twiddle k i ρ = 1).card = 2 ^ (i : ℕ) := by
    rw [← card_highZero k i, Fintype.card_subtype, Finset.filter_filter]
    congr 1
    refine Finset.filter_congr fun ρ _ => ?_
    rw [twiddle_eq_one_iff]
    constructor
    · rintro ⟨h0, h⟩ j hj
      rcases eq_or_lt_of_le hj with rfl | hlt
      · exact h0
      · exact h j hlt
    · intro h
      exact ⟨h i le_rfl, fun j hj => h j hj.le⟩
  rw [h1, h2, ← hcardt, h3, hcardp]

end Counting

/-! ## Theorem 125: the skipping circuit -/

section Skip

variable (k : ℕ)

/-- Width of butterfly `q` in stage `s`. -/
noncomputable def skWidth (s q : ℕ) : ℕ := bfWidth (twiddle k (digitAt k s) (repAt k (digitAt k s) q))

/-- First free register of skipping stage `s`. -/
noncomputable def skPos : ℕ → ℕ
  | 0 => placeValue radixTwo (k + 1) + 1
  | s + 1 => skPos s + ∑ q ∈ Finset.range (Fintype.card (Low k (digitAt k s))), skWidth k s q

/-- Where the array after `s` skipping stages lives. -/
noncomputable def skAddr : ℕ → FiniteRadixSpace radixTwo k → ℕ
  | 0, τ => decodeFinite radixTwo k τ
  | s + 1, ρ =>
      skPos k s + ∑ q' ∈ Finset.range (lowNum k (digitAt k s) (lowOf k (digitAt k s) ρ) : ℕ),
          skWidth k s q' +
        skWidth k s (lowNum k (digitAt k s) (lowOf k (digitAt k s) ρ) : ℕ) - 2 +
        (ρ (digitAt k s) : ℕ)

/-- Butterfly `q` of skipping stage `s`. -/
noncomputable def skItem (s q : ℕ) : ℂ × ℕ × ℕ :=
  (twiddle k (digitAt k s) (repAt k (digitAt k s) q), skAddr k s (repAt k (digitAt k s) q),
    skAddr k s (Function.update (repAt k (digitAt k s) q) (digitAt k s) (1 : Fin 2)))

/-- The first `s` skipping stages. -/
noncomputable def skStages : ℕ → List LGate
  | 0 => []
  | s + 1 => skStages s ++ vRow (skPos k s) (skItem k s) (Fintype.card (Low k (digitAt k s)))

end Skip

theorem skStages_spec (k : ℕ) (x : Fin (placeValue radixTwo (k + 1)) → ℂ) :
    ∀ s, s ≤ k + 1 →
      (exec (skStages k s) (initState _ x)).pos = skPos k s ∧
      ∀ ρ, skAddr k s ρ < skPos k s ∧
        (exec (skStages k s) (initState _ x)).val (skAddr k s ρ) =
          stages k s (fun τ => extend x (decodeFinite radixTwo k τ)) ρ
  | 0, _ => by
    refine ⟨rfl, fun τ => ⟨?_, ?_⟩⟩
    · have := decodeFinite_lt k τ; simp only [skAddr, skPos]; omega
    · simp [skStages, exec, initState, skAddr, stages, extend]
  | s + 1, hs => by
    obtain ⟨hpos, hinv⟩ := skStages_spec k x s (by omega)
    have hrow := vRow_spec (skPos k s) (skItem k s) (exec (skStages k s) (initState _ x)) hpos
      (Fintype.card (Low k (digitAt k s))) fun q _ => ⟨(hinv _).1, (hinv _).1⟩
    obtain ⟨hpos', hval⟩ := hrow
    have hexec : exec (skStages k (s + 1)) (initState _ x) =
        exec (vRow (skPos k s) (skItem k s) (Fintype.card (Low k (digitAt k s))))
          (exec (skStages k s) (initState _ x)) := by
      simp only [skStages, exec_append]
    rw [hexec]
    refine ⟨by rw [hpos']; rfl, fun ρ => ⟨?_, ?_⟩⟩
    · set q := (lowNum k (digitAt k s) (lowOf k (digitAt k s) ρ) : ℕ) with hqdef
      have hq : q < Fintype.card (Low k (digitAt k s)) := (lowNum k _ _).isLt
      have hlt : (ρ (digitAt k s) : ℕ) < 2 := (ρ (digitAt k s)).isLt
      have hw := two_le_bfWidth (skItem k s q).1
      have hmono := vStart_mono (skPos k s) (skItem k s) (show q + 1 ≤ _ from hq)
      rw [vStart_succ] at hmono
      have haddr : skAddr k (s + 1) ρ =
          vStart (skPos k s) (skItem k s) q + bfWidth (skItem k s q).1 - 2 +
            (ρ (digitAt k s) : ℕ) := rfl
      have hend : skPos k (s + 1) = vStart (skPos k s) (skItem k s)
          (Fintype.card (Low k (digitAt k s))) := rfl
      rw [haddr, hend]
      omega
    · set q := (lowNum k (digitAt k s) (lowOf k (digitAt k s) ρ) : ℕ) with hqdef
      have hq : q < Fintype.card (Low k (digitAt k s)) := (lowNum k _ _).isLt
      have hrep : repAt k (digitAt k s) q = Function.update ρ (digitAt k s) (0 : Fin 2) := by
        rw [repAt, dif_pos hq]
        simp only [hqdef, Fin.eta, Equiv.symm_apply_apply, lowOf]
      obtain ⟨h1, h2⟩ := hval q hq
      simp only [skItem, hrep, Function.update_idem] at h1 h2
      have hstage : stages k (s + 1) (fun τ => extend x (decodeFinite radixTwo k τ)) ρ =
          stage k (digitAt k s) (stages k s (fun τ => extend x (decodeFinite radixTwo k τ))) ρ := by
        simp only [stages, dif_pos (show s ≤ k by omega)]; rfl
      rw [hstage, stage_radixTwo, ← (hinv _).2, ← (hinv _).2]
      have hlt : (ρ (digitAt k s) : ℕ) < 2 := (ρ (digitAt k s)).isLt
      have hw := two_le_bfWidth (skItem k s q).1
      have haddr : skAddr k (s + 1) ρ =
          vStart (skPos k s) (skItem k s) q + bfWidth (skItem k s q).1 - 2 +
            (ρ (digitAt k s) : ℕ) := rfl
      simp only [skItem, hrep] at haddr hw
      have hd : (ρ (digitAt k s) : ℕ) = 0 ∨ (ρ (digitAt k s) : ℕ) = 1 := by omega
      rcases hd with h0 | h1'
      · rw [haddr, h0, add_zero, h1, pow_zero, one_mul]
      · rw [haddr, h1', show vStart (skPos k s) (skItem k s) q +
            bfWidth (twiddle k (digitAt k s) (Function.update ρ (digitAt k s) (0 : Fin 2))) - 2 + 1 =
            vStart (skPos k s) (skItem k s) q +
            bfWidth (twiddle k (digitAt k s) (Function.update ρ (digitAt k s) (0 : Fin 2))) - 1 by
              omega, h2, pow_one]
        ring

theorem skStages_length (k : ℕ) :
    ∀ s, s ≤ k + 1 → (skStages k s).length + ∑ j ∈ Finset.range s, 2 ^ (k - j) = 3 * 2 ^ k * s
  | 0, _ => rfl
  | s + 1, hs => by
    have ih := skStages_length k s (by omega)
    have hw := sum_bfWidth k (digitAt k s)
    rw [skStages, List.length_append, vRow_length, Finset.sum_range_succ]
    have : ∑ q ∈ Finset.range (Fintype.card (Low k (digitAt k s))), bfWidth (skItem k s q).1 +
        2 ^ (k - s) = 3 * 2 ^ k := hw
    nlinarith [ih, this]

theorem sum_pow_two_range (n : ℕ) : ∑ j ∈ Finset.range n, 2 ^ j + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, pow_succ]; omega

/-- **Theorem 125 (the skipping circuit).** Length `N = 2^{k+1}` has an exact Fourier
circuit with exactly `(3/2) N log₂ N − N + 1` gates.

**fdrs.md**: Theorem 125 (the skipping circuit). -/
theorem exists_skip_circuit (k : ℕ) :
    ∃ C : Circuit (2 ^ (k + 1)), C.Computes (fourierMatrix (2 ^ (k + 1))) ∧
      C.size + 2 ^ (k + 1) = 3 * 2 ^ k * (k + 1) + 1 := by
  suffices h : ∃ C : Circuit (placeValue radixTwo (k + 1)),
      C.Computes (fourierMatrix (placeValue radixTwo (k + 1))) ∧
      C.size + 2 ^ (k + 1) = 3 * 2 ^ k * (k + 1) + 1 by
    rwa [placeValue_radixTwo] at h
  set N := placeValue radixTwo (k + 1)
  have hout : ∀ m : Fin N,
      skAddr k (k + 1) ((rdecEquiv radixTwo k).symm m) < N + 1 + (skStages k (k + 1)).length := by
    intro m
    have h := skStages_spec k (fun _ => 0) (k + 1) le_rfl
    have hp := h.1
    rw [exec_pos] at hp
    have hst : skPos k (k + 1) = N + 1 + (skStages k (k + 1)).length := by
      rw [← hp]; rfl
    exact (h.2 _).1.trans_eq hst
  refine ⟨Circuit.ofGates N (skStages k (k + 1))
    (fun m => skAddr k (k + 1) ((rdecEquiv radixTwo k).symm m)) hout, fun x => ?_, ?_⟩
  · funext m
    rw [Circuit.ofGates_eval, ((skStages_spec k x (k + 1) le_rfl).2 _).2, fft_eq_dft]
    have hm : reverseDecode radixTwo k ((rdecEquiv radixTwo k).symm m) = m :=
      congrArg Fin.val ((rdecEquiv radixTwo k).apply_symm_apply m)
    rw [hm, dft, Finset.sum_range (fun n => extend x n * zeta N ^ ((m : ℕ) * n))]
    simp only [Matrix.mulVec, dotProduct, fourierMatrix, extend]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dif_pos j.isLt, mul_comm]
  · rw [Circuit.ofGates_size]
    have hl := skStages_length k (k + 1) le_rfl
    have hg := sum_pow_two_range (k + 1)
    rw [← Finset.sum_range_reflect (fun j => 2 ^ j) (k + 1)] at hg
    have : ∑ j ∈ Finset.range (k + 1), 2 ^ (k + 1 - 1 - j) =
        ∑ j ∈ Finset.range (k + 1), 2 ^ (k - j) := rfl
    omega

/-- **Corollary 36 (the gap).** Against the §1.8 butterfly circuit
(`3 · 2^k · (k + 1)` gates) the skipping circuit saves exactly `N − 1 = 2^{k+1} − 1`
gates; normalized, `size / (N log₂ N) = 3/2 − (N − 1)/(N log₂ N)`.

**fdrs.md**: Corollary 36 (the gap). -/
theorem skip_gap (k : ℕ) :
    ∃ C : Circuit (2 ^ (k + 1)), C.Computes (fourierMatrix (2 ^ (k + 1))) ∧
      (C.size : ℝ) / ((2 : ℝ) ^ (k + 1) * Real.logb 2 ((2 : ℝ) ^ (k + 1))) =
        3 / 2 - ((2 : ℝ) ^ (k + 1) - 1) / ((2 : ℝ) ^ (k + 1) * (k + 1)) := by
  obtain ⟨C, hC, hsize⟩ := exists_skip_circuit k
  refine ⟨C, hC, ?_⟩
  have hs : (C.size : ℝ) = 3 * 2 ^ k * (k + 1) + 1 - 2 ^ (k + 1) := by
    have : ((C.size + 2 ^ (k + 1) : ℕ) : ℝ) = ((3 * 2 ^ k * (k + 1) + 1 : ℕ) : ℝ) := by rw [hsize]
    push_cast at this
    linarith
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one, hs]
  push_cast
  have hpos : (0 : ℝ) < 2 ^ (k + 1) * ((k : ℝ) + 1) := by positivity
  field_simp
  ring

end FdrsFormal.NumberTheory.Characters.FourierCircuit
