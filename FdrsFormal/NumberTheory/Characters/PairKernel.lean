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

# The conjugate-pair kernel (Phase 3 addendum, §1.10)

The radix-schedule search (`docs/fourier/01-schedule-search.md`) prices every
odd prime with one kernel: pair each input with its mirror. This file proves it.

- **Theorem 126** (`exists_pair_circuit`): every odd length `n = 2h + 1` has an
  exact Fourier circuit (Definition 216) with exactly `n² − 1` gates.

The construction, with `ζ = ζ_n` and `j = 1, …, h`:
`s_j = x_j + x_{n−j}`, `d_j = x_j − x_{n−j}` (`2h` gates);
`X_0 = x_0 + Σ s_j` (`h` gates); and for each `m = 1, …, h`,
`A_m = x_0 + Σ α_{mj} s_j` (`2h`), `B_m = Σ β_{mj} d_j` (`2h − 1`),
`X_m = A_m + B_m`, `X_{n−m} = A_m − B_m` (`2`), where
`α_{mj} = (ζ^{mj} + ζ^{m(n−j)})/2` and `β_{mj} = (ζ^{mj} − ζ^{m(n−j)})/2`.
Total `2h + h + h(4h + 1) = 4h² + 4h = n² − 1` — about half the dense
`n(2n − 1)` of Proposition 158.

**Honest scope.** Classical (the conjugate-pair / real-symmetry split of the DFT
kernel). Not claimed minimal; for primes, Rader's reduction is cheaper at large `n`.
-/

import FdrsFormal.NumberTheory.Characters.FFTCircuit

namespace FdrsFormal.NumberTheory.Characters.FourierCircuit

open FdrsFormal.NumberTheory.Characters.MixedRadixFFT

/-! ## Builder lemmas: independent gates, add chains, accumulations -/

/-- A gate reads only registers below `b`. -/
def LGate.ReadsBelow (b : ℕ) : LGate → Prop
  | .add i j => i < b ∧ j < b
  | .sub i j => i < b ∧ j < b
  | .scale _ i => i < b

theorem LGate.eval_congr {g : LGate} {b : ℕ} (hg : g.ReadsBelow b) {v w : ℕ → ℂ}
    (h : ∀ a < b, v a = w a) : g.eval v = g.eval w := by
  cases g with
  | add i j => obtain ⟨hi, hj⟩ := hg; simp [LGate.eval, h i hi, h j hj]
  | sub i j => obtain ⟨hi, hj⟩ := hg; simp [LGate.eval, h i hi, h j hj]
  | scale c i => simp [LGate.eval, h i hg]

/-- Gates that read only registers present before the run each leave their own
value, computed on the starting registers. -/
theorem exec_indep : ∀ (l : List LGate) (s : State), (∀ g ∈ l, g.ReadsBelow s.pos) →
    ∀ j (hj : j < l.length), (exec l s).val (s.pos + j) = (l[j]).eval s.val
  | [], _, _, j, hj => absurd hj (by simp)
  | g :: gs, s, hr, j, hj => by
    set s1 : State := ⟨s.pos + 1, Function.update s.val s.pos (g.eval s.val)⟩
    have hs1 : ∀ a < s.pos, s1.val a = s.val a := fun a ha =>
      Function.update_of_ne (by omega) _ _
    rw [exec_cons]
    rcases j with _ | j
    · rw [exec_frame _ _ (show s.pos + 0 < s1.pos by simp [s1])]
      simp [s1]
    · have hr' : ∀ g' ∈ gs, g'.ReadsBelow s1.pos := fun g' hg' => by
        have := hr g' (by simp [hg'])
        cases g' <;> simp only [LGate.ReadsBelow] at this ⊢ <;> simp [s1] <;> omega
      have := exec_indep gs s1 hr' j (by simpa using hj)
      rw [show s.pos + (j + 1) = s1.pos + j by simp [s1]; omega, this]
      simp only [List.getElem_cons_succ]
      exact LGate.eval_congr (hr _ (by simp)) hs1

/-- `v(acc) + Σ v(a)` by additions only. -/
def sumChain : ℕ → List ℕ → ℕ → List LGate
  | _, [], _ => []
  | acc, a :: rest, pos => .add acc a :: sumChain pos rest (pos + 1)

theorem sumChain_length : ∀ (acc : ℕ) (as : List ℕ) (pos : ℕ),
    (sumChain acc as pos).length = as.length
  | _, [], _ => rfl
  | acc, a :: rest, pos => by simp [sumChain, sumChain_length pos rest (pos + 1)]

theorem sumChain_spec : ∀ (as : List ℕ) (acc : ℕ) (s : State), as ≠ [] → acc < s.pos →
    (∀ a ∈ as, a < s.pos) →
    (exec (sumChain acc as s.pos) s).val ((exec (sumChain acc as s.pos) s).pos - 1) =
      s.val acc + (as.map s.val).sum
  | [], _, _, h, _, _ => absurd rfl h
  | [a], acc, s, _, hacc, ha => by
    have ha0 : a < s.pos := ha a (by simp)
    simp [sumChain, exec_cons, exec_nil, LGate.eval]
  | a :: b :: rest, acc, s, _, hacc, ha => by
    have ha0 : a < s.pos := ha a (by simp)
    set s1 : State := ⟨s.pos + 1, Function.update s.val s.pos (s.val acc + s.val a)⟩
    have hs1 : ∀ c < s.pos, s1.val c = s.val c := fun c hc =>
      Function.update_of_ne (by omega) _ _
    have ih := sumChain_spec (b :: rest) s.pos s1 (by simp) (by simp [s1])
      (fun c hc => by have := ha c (by simp_all); simp [s1]; omega)
    have hmap : ((b :: rest).map s1.val) = ((b :: rest).map s.val) :=
      List.map_congr_left fun c hc => hs1 c (ha c (by simp_all))
    show (exec (sumChain s.pos (b :: rest) (s.pos + 1)) s1).val
        ((exec (sumChain s.pos (b :: rest) (s.pos + 1)) s1).pos - 1) = _
    rw [show s.pos + 1 = s1.pos from rfl, ih, hmap]
    simp [s1, add_assoc]

/-- `v(acc) + Σ c · v(a)`: per term, scale then add. -/
def lcAcc : ℕ → List (ℂ × ℕ) → ℕ → List LGate
  | _, [], _ => []
  | acc, (c, a) :: rest, pos => .scale c a :: .add acc pos :: lcAcc (pos + 1) rest (pos + 2)

theorem lcAcc_length : ∀ (acc : ℕ) (ts : List (ℂ × ℕ)) (pos : ℕ),
    (lcAcc acc ts pos).length = 2 * ts.length
  | _, [], _ => rfl
  | acc, (c, a) :: rest, pos => by simp [lcAcc, lcAcc_length (pos + 1) rest (pos + 2)]; ring

theorem lcAcc_spec : ∀ (ts : List (ℂ × ℕ)) (acc : ℕ) (s : State), ts ≠ [] → acc < s.pos →
    (∀ p ∈ ts, p.2 < s.pos) →
    (exec (lcAcc acc ts s.pos) s).val ((exec (lcAcc acc ts s.pos) s).pos - 1) =
      s.val acc + (ts.map fun p => p.1 * s.val p.2).sum
  | [], _, _, h, _, _ => absurd rfl h
  | (c, a) :: rest, acc, s, _, hacc, ha => by
    have ha0 : a < s.pos := ha (c, a) (by simp)
    set s1 : State := ⟨s.pos + 1, Function.update s.val s.pos (c * s.val a)⟩
    set s2 : State := ⟨s1.pos + 1, Function.update s1.val s1.pos (s1.val acc + s1.val s.pos)⟩
    have hs2 : ∀ q < s.pos, s2.val q = s.val q := fun q hq => by
      simp only [s2, s1]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    have hlast : s2.val (s2.pos - 1) = s.val acc + c * s.val a := by
      simp only [s2, s1]
      rw [show s.pos + 1 + 1 - 1 = s.pos + 1 by omega, Function.update_self,
        Function.update_of_ne (by omega), Function.update_self]
    have hpos2 : s2.pos = s.pos + 2 := rfl
    have hmap : (rest.map fun p => p.1 * s2.val p.2) = (rest.map fun p => p.1 * s.val p.2) :=
      List.map_congr_left fun p hp => by rw [hs2 p.2 (ha p (by simp [hp]))]
    show (exec (lcAcc (s.pos + 1) rest (s.pos + 2)) s2).val
        ((exec (lcAcc (s.pos + 1) rest (s.pos + 2)) s2).pos - 1) = _
    by_cases hne : rest = []
    · subst hne
      simp only [lcAcc, exec_nil]
      rw [hlast]; simp
    · have ih := lcAcc_spec rest (s.pos + 1) s2 hne (by simp [s2, s1])
        (fun p hp => by have := ha p (by simp [hp]); simp [s2, s1]; omega)
      rw [← hpos2, ih, hmap]
      have : s2.val (s.pos + 1) = s.val acc + c * s.val a := by
        rw [show s.pos + 1 = s2.pos - 1 by have := hpos2; omega]; exact hlast
      rw [this]
      simp [add_assoc]

theorem list_sum_map_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∀ h, ((List.range h).map f).sum = ∑ j ∈ Finset.range h, f j
  | 0 => by simp
  | h + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, list_sum_map_range f h,
      Finset.sum_range_succ]
    simp

/-- An add and a subtract of the same two registers. -/
theorem exec_addsub (S : State) (a b : ℕ) (ha : a < S.pos) (hb : b < S.pos) :
    (exec [.add a b, .sub a b] S).pos = S.pos + 2 ∧
    (exec [.add a b, .sub a b] S).val S.pos = S.val a + S.val b ∧
    (exec [.add a b, .sub a b] S).val (S.pos + 1) = S.val a - S.val b := by
  have ea : a ≠ S.pos := by omega
  have eb : b ≠ S.pos := by omega
  simp only [exec_cons, exec_nil, LGate.eval]
  refine ⟨trivial, ?_, ?_⟩
  · simp [Function.update_apply]
  · simp [ea, eb]

/-! ## The kernel's arithmetic -/

theorem zeta_pow_mod (n a : ℕ) (hn : n ≠ 0) : zeta n ^ a = zeta n ^ (a % n) := by
  conv_lhs => rw [← Nat.mod_add_div a n, pow_add, pow_mul, zeta_pow_self n hn, one_pow, mul_one]

/-- `Σ_{j < 2h+1} f j = f 0 + Σ_{j < h} (f (j + 1) + f (2h − j))`. -/
theorem sum_range_pairs {M : Type*} [AddCommMonoid M] (f : ℕ → M) (h : ℕ) :
    ∑ j ∈ Finset.range (2 * h + 1), f j =
      f 0 + ∑ j ∈ Finset.range h, (f (j + 1) + f (2 * h - j)) := by
  rw [Finset.sum_range_succ', add_comm, Finset.sum_add_distrib, two_mul, Finset.sum_range_add]
  congr 2
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp at hj
  congr 1
  omega

section Pair

variable (h : ℕ)

/-- `α_{m j} = (ζ^{m j} + ζ^{m (n − j)})/2`, with `j = j' + 1`, `n − j = 2h − j'`. -/
noncomputable def pairAlpha (m j : ℕ) : ℂ :=
  (zeta (2 * h + 1) ^ (m * (j + 1)) + zeta (2 * h + 1) ^ (m * (2 * h - j))) / 2

/-- `β_{m j} = (ζ^{m j} − ζ^{m (n − j)})/2`. -/
noncomputable def pairBeta (m j : ℕ) : ℂ :=
  (zeta (2 * h + 1) ^ (m * (j + 1)) - zeta (2 * h + 1) ^ (m * (2 * h - j))) / 2

/-- Base of the `m`-blocks: after the `2h` pair gates and the `h`-gate chain for `X₀`. -/
def pairBase : ℕ := 2 * h + 1 + 1 + 3 * h

/-- One `m`-block (`m = m' + 1`) at `start`: `A_m`, `B_m`, then `A ± B`. -/
noncomputable def pairBlock (m' start : ℕ) : List LGate :=
  lcAcc 0 ((List.range h).map fun j => (pairAlpha h (m' + 1) j, 2 * h + 1 + 1 + j)) start ++
  lcGates ((List.range h).map fun j => (pairBeta h (m' + 1) j, 2 * h + 1 + 1 + h + j))
    (start + 2 * h) ++
  [.add (start + 2 * h - 1) (start + 4 * h - 2), .sub (start + 2 * h - 1) (start + 4 * h - 2)]

/-- The first `M` blocks. -/
noncomputable def pairRow : ℕ → List LGate
  | 0 => []
  | M + 1 => pairRow M ++ pairBlock h M (pairBase h + M * (4 * h + 1))

/-- All gates of the kernel. -/
noncomputable def pairGates : List LGate :=
  (List.range h).map (fun j => LGate.add (j + 1) (2 * h - j)) ++
  (List.range h).map (fun j => LGate.sub (j + 1) (2 * h - j)) ++
  sumChain 0 ((List.range h).map fun j => 2 * h + 1 + 1 + j) (2 * h + 1 + 1 + 2 * h) ++
  pairRow h h

end Pair

theorem pairBlock_length (h m' start : ℕ) (hh : 1 ≤ h) :
    (pairBlock h m' start).length = 4 * h + 1 := by
  rw [pairBlock, List.length_append, List.length_append, lcAcc_length, lcGates_length _ _
    (by simp; omega)]
  simp; omega

theorem pairRow_length (h : ℕ) (hh : 1 ≤ h) : ∀ M, (pairRow h M).length = M * (4 * h + 1)
  | 0 => by simp [pairRow]
  | M + 1 => by rw [pairRow, List.length_append, pairRow_length h hh M, pairBlock_length h _ _ hh]; ring

theorem pairGates_length (h : ℕ) (hh : 1 ≤ h) :
    (pairGates h).length = (2 * h + 1) ^ 2 - 1 := by
  simp only [pairGates, List.length_append, List.length_map, List.length_range, sumChain_length,
    pairRow_length h hh]
  have : (2 * h + 1) ^ 2 = 4 * h * h + 4 * h + 1 := by ring
  rw [this]
  ring_nf
  omega

/-- One block's outputs, read off any register file whose pair registers are written. -/
theorem pairBlock_spec (h m' : ℕ) (hh : 1 ≤ h) (s : State) (hs : pairBase h ≤ s.pos) :
    let E := exec (pairBlock h m' s.pos) s
    let A := s.val 0 + ∑ j ∈ Finset.range h, pairAlpha h (m' + 1) j * s.val (2 * h + 1 + 1 + j)
    let B := ∑ j ∈ Finset.range h, pairBeta h (m' + 1) j * s.val (2 * h + 1 + 1 + h + j)
    E.pos = s.pos + (4 * h + 1) ∧
    E.val (s.pos + 4 * h - 1) = A + B ∧ E.val (s.pos + 4 * h) = A - B := by
  intro E A B
  have hb : pairBase h = 2 * h + 1 + 1 + 3 * h := rfl
  -- stage 1: A
  set tA := (List.range h).map fun j => (pairAlpha h (m' + 1) j, 2 * h + 1 + 1 + j)
  set tB := (List.range h).map fun j => (pairBeta h (m' + 1) j, 2 * h + 1 + 1 + h + j)
  have hneA : tA ≠ [] := by simp [tA]; omega
  have hneB : tB ≠ [] := by simp [tB]; omega
  have hrA : ∀ p ∈ tA, p.2 < s.pos := fun p hp => by
    simp only [tA, List.mem_map, List.mem_range] at hp
    obtain ⟨j, hj, rfl⟩ := hp; simp; omega
  have hrB : ∀ p ∈ tB, p.2 < s.pos := fun p hp => by
    simp only [tB, List.mem_map, List.mem_range] at hp
    obtain ⟨j, hj, rfl⟩ := hp; simp; omega
  set S1 := exec (lcAcc 0 tA s.pos) s
  have hS1pos : S1.pos = s.pos + 2 * h := by
    simp only [S1, exec_pos, lcAcc_length, tA, List.length_map, List.length_range]
  have hA := lcAcc_spec tA 0 s hneA (by omega) hrA
  rw [← show S1 = exec (lcAcc 0 tA s.pos) s from rfl, hS1pos] at hA
  have hAval : S1.val (s.pos + 2 * h - 1) = A := by
    rw [hA]
    simp only [A, tA, List.map_map, Function.comp_def]
    rw [list_sum_map_range]
  -- stage 2: B
  have hB0 := lcGates_spec tB S1 hneB fun p hp => by have := hrB p hp; omega
  rw [hS1pos] at hB0
  set S2 := exec (lcGates tB (s.pos + 2 * h)) S1
  have hlenB := lcGates_length tB (s.pos + 2 * h) hneB
  have hS2pos : S2.pos = s.pos + 4 * h - 1 := by
    show (exec (lcGates tB (s.pos + 2 * h)) S1).pos = _
    rw [exec_pos, hlenB, hS1pos]; simp [tB]; omega
  rw [hS2pos] at hB0
  have hB2 : S2.val (s.pos + 4 * h - 2) = B := by
    rw [show s.pos + 4 * h - 2 = s.pos + 4 * h - 1 - 1 by omega, hB0]
    simp only [B, tB, List.map_map, Function.comp_def]
    rw [list_sum_map_range]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp at hj
    rw [exec_frame _ _ (by omega)]
  have hA2 : S2.val (s.pos + 2 * h - 1) = A := by
    rw [exec_frame _ _ (by omega), hAval]
  -- stage 3: the two outputs
  have hE : E = exec [.add (s.pos + 2 * h - 1) (s.pos + 4 * h - 2),
      .sub (s.pos + 2 * h - 1) (s.pos + 4 * h - 2)] S2 := by
    simp only [E, pairBlock, exec_append]; rfl
  obtain ⟨k1, k2, k3⟩ := exec_addsub S2 (s.pos + 2 * h - 1) (s.pos + 4 * h - 2)
    (by rw [hS2pos]; omega) (by rw [hS2pos]; omega)
  rw [hS2pos] at k1 k2 k3
  rw [hE]
  have k3' : (exec [.add (s.pos + 2 * h - 1) (s.pos + 4 * h - 2),
      .sub (s.pos + 2 * h - 1) (s.pos + 4 * h - 2)] S2).val (s.pos + 4 * h) =
      S2.val (s.pos + 2 * h - 1) - S2.val (s.pos + 4 * h - 2) := by
    rw [← k3]; congr 1; omega
  refine ⟨by rw [k1]; omega, by rw [k2, hA2, hB2], by rw [k3', hA2, hB2]⟩

theorem pairRow_spec (h : ℕ) (hh : 1 ≤ h) (s : State) (hs : s.pos = pairBase h) :
    ∀ M, (exec (pairRow h M) s).pos = pairBase h + M * (4 * h + 1) ∧
      ∀ m' < M,
        (exec (pairRow h M) s).val (pairBase h + m' * (4 * h + 1) + 4 * h - 1) =
          (s.val 0 + ∑ j ∈ Finset.range h, pairAlpha h (m' + 1) j * s.val (2 * h + 1 + 1 + j)) +
            ∑ j ∈ Finset.range h, pairBeta h (m' + 1) j * s.val (2 * h + 1 + 1 + h + j) ∧
        (exec (pairRow h M) s).val (pairBase h + m' * (4 * h + 1) + 4 * h) =
          (s.val 0 + ∑ j ∈ Finset.range h, pairAlpha h (m' + 1) j * s.val (2 * h + 1 + 1 + j)) -
            ∑ j ∈ Finset.range h, pairBeta h (m' + 1) j * s.val (2 * h + 1 + 1 + h + j)
  | 0 => ⟨by simp [pairRow, exec, hs], fun m' hm' => absurd hm' (Nat.not_lt_zero _)⟩
  | M + 1 => by
    obtain ⟨hpos, hval⟩ := pairRow_spec h hh s hs M
    set S := exec (pairRow h M) s
    have hb : pairBase h = 2 * h + 1 + 1 + 3 * h := rfl
    have hspec := pairBlock_spec h M hh S (by rw [hpos]; omega)
    rw [hpos] at hspec
    obtain ⟨hp, h1, h2⟩ := hspec
    -- the block reads the pair registers, unchanged since `s`
    have hfr : ∀ a < pairBase h, S.val a = s.val a := fun a ha => by
      simp only [S]; exact exec_frame _ _ (by omega)
    have hexec : exec (pairRow h (M + 1)) s =
        exec (pairBlock h M (pairBase h + M * (4 * h + 1))) S := by
      simp only [pairRow, exec_append]; rfl
    rw [hexec]
    refine ⟨by rw [hp]; ring, fun m' hm' => ?_⟩
    have rewr : ∀ j < h, S.val (2 * h + 1 + 1 + j) = s.val (2 * h + 1 + 1 + j) ∧
        S.val (2 * h + 1 + 1 + h + j) = s.val (2 * h + 1 + 1 + h + j) := fun j hj =>
      ⟨hfr _ (by omega), hfr _ (by omega)⟩
    have hsumA : ∑ j ∈ Finset.range h, pairAlpha h (M + 1) j * S.val (2 * h + 1 + 1 + j) =
        ∑ j ∈ Finset.range h, pairAlpha h (M + 1) j * s.val (2 * h + 1 + 1 + j) :=
      Finset.sum_congr rfl fun j hj => by rw [(rewr j (by simpa using hj)).1]
    have hsumB : ∑ j ∈ Finset.range h, pairBeta h (M + 1) j * S.val (2 * h + 1 + 1 + h + j) =
        ∑ j ∈ Finset.range h, pairBeta h (M + 1) j * s.val (2 * h + 1 + 1 + h + j) :=
      Finset.sum_congr rfl fun j hj => by rw [(rewr j (by simpa using hj)).2]
    have h0 : S.val 0 = s.val 0 := hfr 0 (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.mp hm' with hm' | rfl
    · have hlt1 : pairBase h + m' * (4 * h + 1) + 4 * h - 1 < S.pos := by
        have key : (m' + 1) * (4 * h + 1) ≤ M * (4 * h + 1) := Nat.mul_le_mul_right _ hm'
        rw [hpos]; rw [add_mul, one_mul] at key; omega
      have hlt2 : pairBase h + m' * (4 * h + 1) + 4 * h < S.pos := by
        have key : (m' + 1) * (4 * h + 1) ≤ M * (4 * h + 1) := Nat.mul_le_mul_right _ hm'
        rw [hpos]; rw [add_mul, one_mul] at key; omega
      rw [exec_frame _ _ hlt1, exec_frame _ _ hlt2]
      exact hval m' hm'
    · rw [h1, h2, h0, hsumA, hsumB]
      exact ⟨rfl, rfl⟩

/-! ## Theorem 126: assembling the kernel -/

theorem zeta_pow_eq_of_dvd (n a b c : ℕ) (hn : n ≠ 0) (ha : n ∣ a + c) (hb : n ∣ b + c) :
    zeta n ^ a = zeta n ^ b := by
  rw [zeta_pow_mod n a hn, zeta_pow_mod n b hn]
  congr 1
  have h1 : a + c ≡ b + c [MOD n] :=
    (Nat.modEq_zero_iff_dvd.mpr ha).trans (Nat.modEq_zero_iff_dvd.mpr hb).symm
  exact Nat.ModEq.add_right_cancel' c h1

/-- The registers the `m`-blocks read, after the pair gates and the `X₀` chain. -/
theorem pair_regs (h : ℕ) (hh : 1 ≤ h) (x : Fin (2 * h + 1) → ℂ) :
    let T := exec ((List.range h).map (fun j => LGate.add (j + 1) (2 * h - j)) ++
      (List.range h).map (fun j => LGate.sub (j + 1) (2 * h - j)) ++
      sumChain 0 ((List.range h).map fun j => 2 * h + 1 + 1 + j) (2 * h + 1 + 1 + 2 * h))
      (initState _ x)
    T.pos = pairBase h ∧
    T.val 0 = extend x 0 ∧
    (∀ j < h, T.val (2 * h + 1 + 1 + j) = extend x (j + 1) + extend x (2 * h - j)) ∧
    (∀ j < h, T.val (2 * h + 1 + 1 + h + j) = extend x (j + 1) - extend x (2 * h - j)) ∧
    T.val (pairBase h - 1) =
      extend x 0 + ∑ j ∈ Finset.range h, (extend x (j + 1) + extend x (2 * h - j)) := by
  intro T
  set S0 := initState (2 * h + 1) x
  set G1 := (List.range h).map (fun j => LGate.add (j + 1) (2 * h - j))
  set G2 := (List.range h).map (fun j => LGate.sub (j + 1) (2 * h - j))
  set G3 := sumChain 0 ((List.range h).map fun j => 2 * h + 1 + 1 + j) (2 * h + 1 + 1 + 2 * h)
  have hS0 : ∀ i < 2 * h + 1, S0.val i = extend x i := fun i _ => rfl
  have hS0pos : S0.pos = 2 * h + 1 + 1 := rfl
  set T1 := exec G1 S0
  set T2 := exec G2 T1
  have hT1pos : T1.pos = 2 * h + 1 + 1 + h := by simp [T1, exec_pos, G1, hS0pos]
  have hT2pos : T2.pos = 2 * h + 1 + 1 + 2 * h := by simp [T2, exec_pos, G2, hT1pos]; ring
  have hT : T = exec G3 T2 := by simp only [T, exec_append]; rfl
  -- pair sums
  have hT1 : ∀ j < h, T1.val (2 * h + 1 + 1 + j) = extend x (j + 1) + extend x (2 * h - j) := by
    intro j hj
    have := exec_indep G1 S0 (fun g hg => by
      simp only [G1, List.mem_map, List.mem_range] at hg
      obtain ⟨i, hi, rfl⟩ := hg; simp only [LGate.ReadsBelow, hS0pos]; omega) j (by simpa [G1])
    rw [hS0pos] at this
    rw [this]
    simp [G1, LGate.eval, hS0 _ (show j + 1 < 2 * h + 1 by omega)]
    rfl
  have hT1lo : ∀ i < 2 * h + 1 + 1, T1.val i = S0.val i := fun i hi =>
    exec_frame _ _ (by rw [hS0pos]; exact hi)
  -- pair differences
  have hT2 : ∀ j < h, T2.val (2 * h + 1 + 1 + h + j) = extend x (j + 1) - extend x (2 * h - j) := by
    intro j hj
    have := exec_indep G2 T1 (fun g hg => by
      simp only [G2, List.mem_map, List.mem_range] at hg
      obtain ⟨i, hi, rfl⟩ := hg; simp only [LGate.ReadsBelow, hT1pos]; omega) j (by simpa [G2])
    rw [hT1pos] at this
    rw [this]
    simp only [G2, List.getElem_map, List.getElem_range, LGate.eval]
    rw [hT1lo _ (by omega), hT1lo _ (by omega)]
    rfl
  have hT2lo : ∀ i < 2 * h + 1 + 1 + h, T2.val i = T1.val i := fun i hi =>
    exec_frame _ _ (by rw [hT1pos]; exact hi)
  have hT2s : ∀ j < h, T2.val (2 * h + 1 + 1 + j) = extend x (j + 1) + extend x (2 * h - j) :=
    fun j hj => by rw [hT2lo _ (by omega), hT1 j hj]
  have hT2zero : T2.val 0 = extend x 0 := by
    rw [hT2lo _ (by omega), hT1lo _ (by omega)]; rfl
  -- the chain for X₀
  have hlenG3 : G3.length = h := by simp [G3, sumChain_length]
  have hTpos : T.pos = pairBase h := by
    rw [hT, exec_pos, hT2pos, hlenG3]; simp [pairBase]; ring
  have hTlo : ∀ i < 2 * h + 1 + 1 + 2 * h, T.val i = T2.val i := fun i hi => by
    rw [hT]; exact exec_frame _ _ (by rw [hT2pos]; exact hi)
  refine ⟨hTpos, ?_, fun j hj => ?_, fun j hj => ?_, ?_⟩
  · rw [hTlo _ (by omega), hT2zero]
  · rw [hTlo _ (by omega), hT2s j hj]
  · rw [hTlo _ (by omega), hT2 j hj]
  · have hc := sumChain_spec ((List.range h).map fun j => 2 * h + 1 + 1 + j) 0 T2
      (by simp; omega) (by rw [hT2pos]; omega)
      (fun a ha => by simp only [List.mem_map, List.mem_range] at ha
                      obtain ⟨j, hj, rfl⟩ := ha; rw [hT2pos]; omega)
    rw [hT2pos] at hc
    rw [show pairBase h - 1 = T.pos - 1 by rw [hTpos], hT]
    rw [show (exec G3 T2).pos = (exec (sumChain 0 ((List.range h).map fun j => 2 * h + 1 + 1 + j)
      (2 * h + 1 + 1 + 2 * h)) T2).pos from rfl, hc, hT2zero, List.map_map]
    rw [list_sum_map_range]
    exact congrArg _ (Finset.sum_congr rfl fun j hj => by
      simp only [Function.comp_apply]; exact hT2s j (by simpa using hj))

/-- **Theorem 126 (the conjugate-pair kernel).** Every odd length `n = 2h + 1` has an
exact Fourier circuit with exactly `n² − 1` gates.

**fdrs.md**: Theorem 126 (the conjugate-pair kernel). -/
theorem exists_pair_circuit (h : ℕ) :
    ∃ C : Circuit (2 * h + 1), C.Computes (fourierMatrix (2 * h + 1)) ∧
      C.size = (2 * h + 1) ^ 2 - 1 := by
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · refine ⟨Circuit.ofGates 1 [] (fun _ => 0) (fun _ => by simp), fun x => ?_, by simp [Circuit.ofGates]⟩
    funext k
    rw [Circuit.ofGates_eval]
    have hk : k = 0 := Fin.ext (by have := k.isLt; omega)
    subst hk
    simp [exec, initState, Matrix.mulVec, dotProduct, fourierMatrix]
  set n := 2 * h + 1 with hn
  -- output registers
  let out : Fin n → ℕ := fun k =>
    if (k : ℕ) = 0 then pairBase h - 1
    else if (k : ℕ) ≤ h then pairBase h + ((k : ℕ) - 1) * (4 * h + 1) + 4 * h - 1
    else pairBase h + (n - (k : ℕ) - 1) * (4 * h + 1) + 4 * h
  have hlen := pairGates_length h hh
  have hrowlen := pairRow_length h hh h
  have hbase : pairBase h = 2 * h + 1 + 1 + 3 * h := rfl
  have hgl : (pairGates h).length = 3 * h + h * (4 * h + 1) := by
    simp only [pairGates, List.length_append, List.length_map, List.length_range,
      sumChain_length, hrowlen]; ring
  have hout : ∀ k, out k < n + 1 + (pairGates h).length := by
    intro k
    have hk := k.isLt
    rw [hgl]
    simp only [out]
    split_ifs with h0 h1
    · rw [hbase]; omega
    · have key : ((k : ℕ) - 1 + 1) * (4 * h + 1) ≤ h * (4 * h + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      rw [add_mul, one_mul] at key; rw [hbase]; omega
    · have key : (n - (k : ℕ) - 1 + 1) * (4 * h + 1) ≤ h * (4 * h + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      rw [add_mul, one_mul] at key; rw [hbase]; omega
  refine ⟨Circuit.ofGates n (pairGates h) out hout, fun x => ?_, ?_⟩
  · funext k
    rw [Circuit.ofGates_eval]
    obtain ⟨hTpos, h0, hs, hd, hX0⟩ := pair_regs h hh x
    set T := exec ((List.range h).map (fun j => LGate.add (j + 1) (2 * h - j)) ++
      (List.range h).map (fun j => LGate.sub (j + 1) (2 * h - j)) ++
      sumChain 0 ((List.range h).map fun j => 2 * h + 1 + 1 + j) (2 * h + 1 + 1 + 2 * h))
      (initState _ x) with hTdef
    have hexec : exec (pairGates h) (initState _ x) = exec (pairRow h h) T := by
      simp only [pairGates, exec_append, hTdef]
    obtain ⟨_, hrow⟩ := pairRow_spec h hh T hTpos h
    -- the target, split into mirror pairs
    have hsplit : (fourierMatrix n).mulVec x k =
        extend x 0 + ∑ j ∈ Finset.range h,
          (zeta n ^ ((k : ℕ) * (j + 1)) * extend x (j + 1) +
            zeta n ^ ((k : ℕ) * (2 * h - j)) * extend x (2 * h - j)) := by
      simp only [Matrix.mulVec, dotProduct, fourierMatrix]
      have e1 : ∑ j : Fin n, zeta n ^ ((k : ℕ) * (j : ℕ)) * x j =
          ∑ j ∈ Finset.range (2 * h + 1), zeta n ^ ((k : ℕ) * j) * extend x j := by
        rw [Finset.sum_range (fun j => zeta n ^ ((k : ℕ) * j) * extend x j)]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [extend, dif_pos j.isLt]
      rw [e1, sum_range_pairs]
      simp only [mul_zero, pow_zero, one_mul]
    rw [hsplit, hexec]
    have hsA : ∀ m, ∑ j ∈ Finset.range h, pairAlpha h m j * T.val (2 * h + 1 + 1 + j) =
        ∑ j ∈ Finset.range h, pairAlpha h m j * (extend x (j + 1) + extend x (2 * h - j)) :=
      fun m => Finset.sum_congr rfl fun j hj => by rw [hs j (by simpa using hj)]
    have hsB : ∀ m, ∑ j ∈ Finset.range h, pairBeta h m j * T.val (2 * h + 1 + 1 + h + j) =
        ∑ j ∈ Finset.range h, pairBeta h m j * (extend x (j + 1) - extend x (2 * h - j)) :=
      fun m => Finset.sum_congr rfl fun j hj => by rw [hd j (by simpa using hj)]
    simp only [out]
    split_ifs with hk0 hkh
    · -- frequency 0
      rw [exec_frame _ _ (by rw [hTpos]; rw [hbase]; omega), hX0, hk0]
      simp
    · -- frequency m = k ∈ [1, h]
      have hm : (k : ℕ) - 1 < h := by omega
      obtain ⟨hA, _⟩ := hrow ((k : ℕ) - 1) hm
      rw [hA, h0, hsA, hsB, add_assoc, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show (k : ℕ) - 1 + 1 = k by omega]
      simp only [pairAlpha, pairBeta]
      ring
    · -- frequency n − m, m = n − k ∈ [1, h]
      have hk := k.isLt
      have hm : n - (k : ℕ) - 1 < h := by omega
      obtain ⟨_, hB⟩ := hrow (n - (k : ℕ) - 1) hm
      rw [hB, h0, hsA, hsB, add_sub_assoc, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjh : j < h := by simpa using hj
      set m := n - (k : ℕ) with hmdef
      rw [show n - (k : ℕ) - 1 + 1 = m by omega]
      have hn0 : n ≠ 0 := by omega
      have e1 : zeta n ^ ((k : ℕ) * (j + 1)) = zeta n ^ (m * (2 * h - j)) :=
        zeta_pow_eq_of_dvd n _ _ (m * (j + 1)) hn0
          ⟨j + 1, by rw [← add_mul, show (k : ℕ) + m = n by omega]⟩
          ⟨m, by rw [← mul_add, show 2 * h - j + (j + 1) = n by omega, mul_comm]⟩
      have e2 : zeta n ^ ((k : ℕ) * (2 * h - j)) = zeta n ^ (m * (j + 1)) :=
        zeta_pow_eq_of_dvd n _ _ (m * (2 * h - j)) hn0
          ⟨2 * h - j, by rw [← add_mul, show (k : ℕ) + m = n by omega]⟩
          ⟨m, by rw [← mul_add, show j + 1 + (2 * h - j) = n by omega, mul_comm]⟩
      rw [e1, e2]
      simp only [pairAlpha, pairBeta]
      ring
  · rw [Circuit.ofGates_size, hlen]

end FdrsFormal.NumberTheory.Characters.FourierCircuit
