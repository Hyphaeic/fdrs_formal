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

# Exact convolution and multiplication circuits (Phase 3 addendum, §1.16)

Definition 216's gate model is linear: it cannot multiply two inputs. This file adds
a product gate and proves the classical convolution circuit in the resulting
bilinear model, with an exact gate count, built from any exact Fourier circuit of
the corpus (Corollaries 37–38). With Theorem 131 it gives exact integer
multiplication on a constant digit schedule.

- **Definition 223** (`BGate`, `bexec`, `BCircuit`, `acyclicConv`): bilinear gates
  (the linear gates of Definition 216 plus a scaled product `c · v_i · v_j`), their
  execution, bilinear circuits on two input vectors, and acyclic convolution.
- **Theorem 135** (`exists_conv_circuit`): from an exact Fourier circuit `C` of length
  `M ≥ 2n − 1`, an exact circuit for the acyclic convolution of two length-`n`
  vectors with `3|C| + M` gates, of which exactly `M` are products.
- **Corollary 44** (`XPlan.exists_conv_circuit`): every valid extended plan of length
  `M ≥ 2n − 1` gives such a circuit with `3·cost + M` gates.
- **Corollary 45** (`mul_eq_conv_circuit`): on a constant schedule, `dec x · dec y` is
  `Σ_m (x̄ ⋆ ȳ)_m B_m` with the convolution read off the circuit of Theorem 135.

**Honest scope.** Classical (convolution through the DFT; Cooley–Tukey 1965 and the
convolution theorem). The product gate carries a constant factor, so the `1/M`
normalisation is free; this is stated, not hidden. Exact complex arithmetic at unit
cost; nothing about bit complexity or family 109's `o(n log n)` bound is claimed.
-/

import FdrsFormal.NumberTheory.Characters.RaderBluestein
import FdrsFormal.Operations.Multiplication

namespace FdrsFormal.NumberTheory.Characters.FourierCircuit

open FdrsFormal.NumberTheory.Characters.MixedRadixFFT

/-! ## Definition 223: bilinear gates and circuits -/

/-- A bilinear gate: a linear gate of Definition 216, or a scaled product
`c · v_i · v_j`.

**fdrs.md**: Definition 223 (the bilinear gate model). -/
inductive BGate where
  | lin (g : LGate)
  | mul (c : ℂ) (i j : ℕ)

def BGate.eval (v : ℕ → ℂ) : BGate → ℂ
  | .lin g => g.eval v
  | .mul c i j => c * v i * v j

def BGate.isMul : BGate → Bool
  | .lin _ => false
  | .mul _ _ _ => true

/-- Run a bilinear gate list: each gate writes the next free register. -/
def bexec : List BGate → State → State
  | [], s => s
  | g :: gs, s => bexec gs ⟨s.pos + 1, Function.update s.val s.pos (g.eval s.val)⟩

theorem bexec_append (l₁ l₂ : List BGate) (s : State) :
    bexec (l₁ ++ l₂) s = bexec l₂ (bexec l₁ s) := by
  induction l₁ generalizing s with
  | nil => rfl
  | cons g gs ih => exact ih _

/-- Linear gates run as in Definition 216. -/
theorem bexec_lin (l : List LGate) (s : State) : bexec (l.map .lin) s = exec l s := by
  induction l generalizing s with
  | nil => rfl
  | cons g gs ih => exact ih _

theorem bexec_pos (l : List BGate) (s : State) : (bexec l s).pos = s.pos + l.length := by
  induction l generalizing s with
  | nil => simp [bexec]
  | cons g gs ih => simp only [bexec, ih, List.length_cons]; omega

theorem bexec_frame (l : List BGate) (s : State) {j : ℕ} (hj : j < s.pos) :
    (bexec l s).val j = s.val j := by
  induction l generalizing s with
  | nil => rfl
  | cons g gs ih =>
    simp only [bexec]
    rw [ih _ (by simp; omega)]
    exact Function.update_of_ne (by omega) _ _

/-- Product gates reading only earlier registers each leave their own value. -/
theorem bexec_mul_indep : ∀ (l : List (ℂ × ℕ × ℕ)) (s : State),
    (∀ p ∈ l, p.2.1 < s.pos ∧ p.2.2 < s.pos) →
    ∀ j (hj : j < l.length),
      (bexec (l.map fun p => BGate.mul p.1 p.2.1 p.2.2) s).val (s.pos + j) =
        l[j].1 * s.val l[j].2.1 * s.val l[j].2.2
  | [], _, _, j, hj => absurd hj (by simp)
  | p :: ps, s, hr, j, hj => by
    set s1 : State := ⟨s.pos + 1, Function.update s.val s.pos
      ((BGate.mul p.1 p.2.1 p.2.2).eval s.val)⟩
    have hs1 : ∀ a < s.pos, s1.val a = s.val a := fun a ha =>
      Function.update_of_ne (by omega) _ _
    simp only [List.map_cons, bexec]
    rcases j with _ | j
    · rw [bexec_frame _ _ (show s.pos + 0 < s1.pos by simp [s1])]
      simp [s1, BGate.eval]
    · have hr' : ∀ p' ∈ ps, p'.2.1 < s1.pos ∧ p'.2.2 < s1.pos := fun p' hp' => by
        have := hr p' (by simp [hp']); simp [s1]; omega
      have := bexec_mul_indep ps s1 hr' j (by simpa using hj)
      rw [show s.pos + (j + 1) = s1.pos + j by simp [s1]; omega, this]
      have hjlt : j < ps.length := by simpa using hj
      have h1 := hr ps[j] (List.mem_cons_of_mem _ (List.getElem_mem hjlt))
      simp only [List.getElem_cons_succ]
      rw [hs1 _ h1.1, hs1 _ h1.2]

/-- The initial register file on inputs `x, y`: `x` at `0, …, n−1`, `y` at
`n, …, 2n−1`, the constant `0` at `2n`, next free register `2n + 1`. -/
def binit (n : ℕ) (x y : Fin n → ℂ) : State :=
  ⟨2 * n + 1, fun i => if i < n then extend x i else if i < 2 * n then extend y (i - n) else 0⟩

/-- A bilinear circuit on two length-`n` inputs with `m` outputs.

**fdrs.md**: Definition 223 (the bilinear gate model). -/
structure BCircuit (n m : ℕ) where
  gates : List BGate
  out : Fin m → ℕ

def BCircuit.eval {n m : ℕ} (B : BCircuit n m) (x y : Fin n → ℂ) (r : Fin m) : ℂ :=
  (bexec B.gates (binit n x y)).val (B.out r)

def BCircuit.size {n m : ℕ} (B : BCircuit n m) : ℕ := B.gates.length

def BCircuit.mulCount {n m : ℕ} (B : BCircuit n m) : ℕ := B.gates.countP BGate.isMul

/-- Acyclic convolution of two length-`n` vectors, `(x ⋆ y)_r = Σ_{i ≤ r} x_i y_{r−i}`.

**fdrs.md**: Definition 223 (the bilinear gate model). -/
noncomputable def acyclicConv (n : ℕ) (x y : Fin n → ℂ) (r : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (r + 1), extend x i * extend y (r - i)

/-! ## Theorem 135: the convolution circuit -/

theorem extend_eq_zero {n : ℕ} (x : Fin n → ℂ) {i : ℕ} (hi : n ≤ i) : extend x i = 0 := by
  simp [extend, show ¬ i < n by omega]

/-- Padding removes the wrap (complex form of Corollary 40). -/
theorem cyclic_eq_acyclic {n M : ℕ} (hM : 2 * n - 1 ≤ M) (x y : Fin n → ℂ) {r : ℕ}
    (hr : r < M) :
    ∑ q ∈ Finset.range M, extend x q * extend y ((r + M - q) % M) = acyclicConv n x y r := by
  rw [acyclicConv]
  rw [← Finset.sum_subset (Finset.range_mono (show r + 1 ≤ M by omega))]
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ r := by simp at hi; omega
    rw [show r + M - i = (r - i) + M by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · intro i hi hir
    have hiM : i < M := by simpa using hi
    have hri : r < i := by simp at hir; omega
    by_cases hin : i < n
    · rw [Nat.mod_eq_of_lt (by omega), extend_eq_zero y (by omega), mul_zero]
    · rw [extend_eq_zero x (by omega), zero_mul]

section Conv

variable (n : ℕ) {M : ℕ} (C : Circuit M)

def cvInA (q : ℕ) : ℕ := if q < n then q else 2 * n
def cvInB (q : ℕ) : ℕ := if q < n then n + q else 2 * n
def cvBBase : ℕ := 2 * n + 1 + C.size
def cvPBase : ℕ := 2 * n + 1 + 2 * C.size
def cvDBase : ℕ := 2 * n + 1 + 2 * C.size + M

def cvA (k : ℕ) : ℕ :=
  if h : k < M then reloc M (cvInA n) (2 * n) (2 * n + 1) (C.outputs ⟨k, h⟩) else 0
def cvB (k : ℕ) : ℕ :=
  if h : k < M then reloc M (cvInB n) (2 * n) (cvBBase n C) (C.outputs ⟨k, h⟩) else 0
def cvD (k : ℕ) : ℕ :=
  if h : k < M then
    reloc M (fun j => cvPBase n C + j) (2 * n) (cvDBase n C) (C.outputs ⟨k, h⟩)
  else 0

/-- The convolution circuit: transforms of the padded inputs, `M` scaled products,
a third transform. -/
noncomputable def convGates : List BGate :=
  (C.program.toGates (cvInA n) (2 * n) (2 * n + 1)).map .lin ++
  (C.program.toGates (cvInB n) (2 * n) (cvBBase n C)).map .lin ++
  ((List.range M).map fun k => ((1 / (M : ℂ)), cvA n C k, cvB n C k)).map
    (fun p => BGate.mul p.1 p.2.1 p.2.2) ++
  (C.program.toGates (fun j => cvPBase n C + j) (2 * n) (cvDBase n C)).map .lin

end Conv

/-- **Theorem 135 (the exact convolution circuit).** From an exact Fourier circuit `C`
of length `M ≥ 2n − 1`, the acyclic convolution of two length-`n` vectors has an
exact bilinear circuit with `3|C| + M` gates, exactly `M` of them products.

**fdrs.md**: Theorem 135 (the exact convolution circuit). -/
theorem exists_conv_circuit {n M : ℕ} (hn : 1 ≤ n) (hM : 2 * n - 1 ≤ M) (C : Circuit M)
    (hC : C.Computes (fourierMatrix M)) :
    ∃ B : BCircuit n (2 * n - 1),
      (∀ x y r, B.eval x y r = acyclicConv n x y r) ∧
      B.size = 3 * C.size + M ∧ B.mulCount = M := by
  have hM0 : M ≠ 0 := by omega
  have hinA : ∀ q < M, cvInA n q < 2 * n + 1 := fun q _ => by unfold cvInA; split_ifs <;> omega
  have hinB : ∀ q < M, cvInB n q < 2 * n + 1 := fun q _ => by unfold cvInB; split_ifs <;> omega
  have hA : ∀ k < M, cvA n C k < cvBBase n C := fun k hk => by
    simp only [cvA, dif_pos hk]
    have := reloc_lt (k := C.size) (inAddr := cvInA n) (z0 := 2 * n) (base := 2 * n + 1)
      (fun i hi => hinA i hi) (by omega) (C.outputs ⟨k, hk⟩)
    simpa [cvBBase] using this
  have hB : ∀ k < M, cvB n C k < cvPBase n C := fun k hk => by
    simp only [cvB, dif_pos hk, cvPBase]
    have := reloc_lt (k := C.size) (inAddr := cvInB n) (z0 := 2 * n) (base := cvBBase n C)
      (fun i hi => (hinB i hi).trans_le (by simp [cvBBase])) (by simp [cvBBase]; omega)
      (C.outputs ⟨k, hk⟩)
    have h2 : cvBBase n C + C.size = 2 * n + 1 + 2 * C.size := by simp only [cvBBase]; ring
    omega
  have hD : ∀ k < M, cvD n C k < cvDBase n C + C.size := fun k hk => by
    simp only [cvD, dif_pos hk]
    exact reloc_lt (k := C.size) (inAddr := fun j => cvPBase n C + j) (z0 := 2 * n)
      (base := cvDBase n C) (fun i hi => by simp only [cvPBase, cvDBase]; omega)
      (by simp only [cvDBase]; omega) _
  refine ⟨⟨convGates n C, fun r => cvD n C ((M - r) % M)⟩, fun x y r => ?_, ?_, ?_⟩
  · simp only [BCircuit.eval]
    set S0 := binit n x y
    have hS0pos : S0.pos = 2 * n + 1 := rfl
    have hS0A : ∀ q, S0.val (cvInA n q) = extend x q := fun q => by
      by_cases hq : q < n
      · simp [S0, binit, cvInA, hq]
      · simp [S0, binit, cvInA, hq, show ¬ 2 * n < n by omega,
          extend_eq_zero x (not_lt.mp hq)]
    have hS0B : ∀ q, S0.val (cvInB n q) = extend y q := fun q => by
      by_cases hq : q < n
      · simp [S0, binit, cvInB, hq, show ¬ n + q < n by omega, show n + q < 2 * n by omega]
      · simp [S0, binit, cvInB, hq, show ¬ 2 * n < n by omega,
          extend_eq_zero y (not_lt.mp hq)]
    have hz : S0.val (2 * n) = 0 := by simp [S0, binit, show ¬ 2 * n < n by omega]
    -- first copy
    obtain ⟨hpos1, hval1⟩ := Program.toGates_spec (cvInA n) (2 * n) (2 * n + 1) S0 hS0pos
      hinA (by omega) hz C.program
    set S1 := exec (C.program.toGates (cvInA n) (2 * n) (2 * n + 1)) S0
    have hS1 : ∀ j < S0.pos, S1.val j = S0.val j := fun j hj => exec_frame _ S0 hj
    have hA1 : ∀ k < M, S1.val (cvA n C k) =
        ∑ q ∈ Finset.range M, zeta M ^ (k * q) * extend x q := fun k hk => by
      simp only [cvA, dif_pos hk]
      rw [hval1, show C.program.eval (fun j => S0.val (cvInA n j)) (C.outputs ⟨k, hk⟩) =
        C.eval (fun j => S0.val (cvInA n j)) ⟨k, hk⟩ from rfl, Circuit.eval_fourier hC,
        sum_fin_eq_range M (fun q => zeta M ^ (k * q) * S0.val (cvInA n q))]
      simp_rw [hS0A]
    -- second copy
    obtain ⟨hpos2, hval2⟩ := Program.toGates_spec (cvInB n) (2 * n) (cvBBase n C) S1
      (by rw [hpos1]; rfl) (fun q hq => (hinB q hq).trans_le (by simp [cvBBase]))
      (by simp [cvBBase]; omega) (by rw [hS1 _ (by omega), hz]) C.program
    set S2 := exec (C.program.toGates (cvInB n) (2 * n) (cvBBase n C)) S1
    have hS2 : ∀ j < S1.pos, S2.val j = S1.val j := fun j hj => exec_frame _ S1 hj
    have hB2 : ∀ k < M, S2.val (cvB n C k) =
        ∑ q ∈ Finset.range M, zeta M ^ (k * q) * extend y q := fun k hk => by
      simp only [cvB, dif_pos hk]
      rw [hval2, show C.program.eval (fun j => S1.val (cvInB n j)) (C.outputs ⟨k, hk⟩) =
        C.eval (fun j => S1.val (cvInB n j)) ⟨k, hk⟩ from rfl, Circuit.eval_fourier hC,
        sum_fin_eq_range M (fun q => zeta M ^ (k * q) * S1.val (cvInB n q))]
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [hS1 _ (by rw [hS0pos]; exact hinB q (by simpa using hq)), hS0B]
    have hA2 : ∀ k < M, S2.val (cvA n C k) = S1.val (cvA n C k) := fun k hk =>
      hS2 _ (by rw [hpos1]; exact hA k hk)
    have hS2pos : S2.pos = cvPBase n C := by rw [hpos2]; simp only [cvBBase, cvPBase]; ring
    -- products
    set PL : List (ℂ × ℕ × ℕ) := (List.range M).map fun k => ((1 / (M : ℂ)), cvA n C k, cvB n C k)
    set S3 := bexec (PL.map fun p => BGate.mul p.1 p.2.1 p.2.2) S2
    have hS3pos : S3.pos = cvDBase n C := by
      simp [S3, bexec_pos, hS2pos, PL, cvPBase, cvDBase]
    have hind := bexec_mul_indep PL S2 (fun p hp => by
      simp only [PL, List.mem_map, List.mem_range] at hp
      obtain ⟨k, hk, rfl⟩ := hp
      refine ⟨?_, ?_⟩
      · rw [hS2pos]; have := hA k hk; simp only [cvBBase, cvPBase] at this ⊢; omega
      · rw [hS2pos]; exact hB k hk)
    have hP3 : ∀ k < M, S3.val (cvPBase n C + k) =
        1 / (M : ℂ) * S2.val (cvA n C k) * S2.val (cvB n C k) := fun k hk => by
      have := hind k (by simpa [PL] using hk)
      rw [hS2pos] at this
      rw [this]
      simp [PL]
    -- third copy
    obtain ⟨_, hval4⟩ := Program.toGates_spec (fun j => cvPBase n C + j) (2 * n) (cvDBase n C)
      S3 hS3pos (fun i hi => by simp only [cvPBase, cvDBase]; omega)
      (by simp only [cvDBase]; omega)
      (by rw [bexec_frame _ _ (by rw [hS2pos]; simp [cvPBase]; omega),
            hS2 _ (by rw [hpos1]; omega), hS1 _ (by omega), hz])
      C.program
    have hexec : bexec (convGates n C) S0 =
        exec (C.program.toGates (fun j => cvPBase n C + j) (2 * n) (cvDBase n C)) S3 := by
      simp only [convGates, bexec_append, bexec_lin]
      rfl
    rw [hexec]
    have hr : (r : ℕ) < M := by have := r.isLt; omega
    have hm : (M - r) % M < M := Nat.mod_lt _ (by omega)
    simp only [cvD, dif_pos hm]
    rw [hval4, show C.program.eval (fun j => S3.val (cvPBase n C + j))
        (C.outputs ⟨(M - r) % M, hm⟩) =
      C.eval (fun j => S3.val (cvPBase n C + j)) ⟨(M - r) % M, hm⟩ from rfl,
      Circuit.eval_fourier hC,
      sum_fin_eq_range M (fun j => zeta M ^ ((M - r) % M * j) * S3.val (cvPBase n C + j))]
    have hconv := cyclic_conv M hM0 (extend x) (extend y) r hr
    rw [← cyclic_eq_acyclic hM x y hr, ← hconv]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < M := by simpa using hj
    rw [hP3 j hj', hA2 j hj', hA1 j hj', hB2 j hj']
    ring
  · simp [BCircuit.size, convGates, Program.toGates_length]; ring
  · simp only [BCircuit.mulCount, convGates, List.countP_append, List.countP_map]
    simp [Function.comp_def, BGate.isMul]

/-! ## Corollaries 44–45 -/

/-- **Corollary 44 (convolution circuits from search plans).** Every valid extended
plan of length `M ≥ 2n − 1` gives an exact convolution circuit with
`3 · cost + M` gates, `M` of them products.

**fdrs.md**: Corollary 44 (convolution circuits from search plans). -/
theorem XPlan.exists_conv_circuit (P : XPlan) (hv : P.valid = true) {n : ℕ} (hn : 1 ≤ n)
    (hM : 2 * n - 1 ≤ P.len) :
    ∃ B : BCircuit n (2 * n - 1),
      (∀ x y r, B.eval x y r = acyclicConv n x y r) ∧
      B.size = 3 * P.cost + P.len ∧ B.mulCount = P.len := by
  obtain ⟨C, hC, hs⟩ := P.exists_circuit hv
  obtain ⟨B, hB, hsz, hmc⟩ :=
    FdrsFormal.NumberTheory.Characters.FourierCircuit.exists_conv_circuit hn hM C hC
  exact ⟨B, hB, by rw [hsz, hs], hmc⟩

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite FdrsFormal.Operations.Multiplication in
/-- **Corollary 45 (exact multiplication).** On a constant digit schedule, for
`x, y ∈ 𝓡^{(k)}` and any circuit `B` computing acyclic convolution of length `k + 1`
(Theorem 135), `dec x · dec y = Σ_{m ≤ 2k} B(x̄, ȳ)_m · B_m`.

**fdrs.md**: Corollary 45 (exact multiplication). -/
theorem mul_eq_conv_circuit {b : RadixSeq} {k : ℕ} (hb : ∀ i, b i = b 0)
    (B : BCircuit (k + 1) (2 * (k + 1) - 1))
    (hB : ∀ x y r, B.eval x y r = acyclicConv (k + 1) x y r)
    (x y : FiniteRadixSpace b k) :
    ((decodeFinite b k x * decodeFinite b k y : ℕ) : ℂ) =
      ∑ m : Fin (2 * (k + 1) - 1),
        B.eval (fun i => ((x i : ℕ) : ℂ)) (fun i => ((y i : ℕ) : ℂ)) m * placeValue b m := by
  set x' : Fin (k + 1) → ℂ := fun i => ((x i : ℕ) : ℂ)
  set y' : Fin (k + 1) → ℂ := fun i => ((y i : ℕ) : ℂ)
  have hext : ∀ (z : FiniteRadixSpace b k) (i : ℕ),
      ((digitsOf z i : ℕ) : ℂ) = extend (fun j : Fin (k + 1) => ((z j : ℕ) : ℂ)) i :=
    fun z i => by
    unfold digitsOf extend
    split_ifs <;> simp
  calc ((decodeFinite b k x * decodeFinite b k y : ℕ) : ℂ)
      = ∑ m ∈ Finset.range (2 * k + 1),
          ((digitConv (digitsOf x) (digitsOf y) m : ℕ) : ℂ) * placeValue b m := by
        rw [← digitVal_conv hb x y, digitVal]; push_cast; rfl
    _ = ∑ m ∈ Finset.range (2 * (k + 1) - 1), acyclicConv (k + 1) x' y' m * placeValue b m := by
        rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
        refine Finset.sum_congr rfl fun m _ => ?_
        congr 1
        simp only [digitConv, acyclicConv]
        push_cast
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hext x, hext y]
    _ = _ := by
        rw [← Fin.sum_univ_eq_sum_range (fun m => acyclicConv (k + 1) x' y' m * placeValue b m)]
        refine Fintype.sum_congr _ _ fun m => ?_
        rw [hB]

/-- An instance: two 64-term vectors convolve exactly in `3 · 1217 + 128 = 3779` gates
(128 products), from the 128-point binary plan (Theorem 125). The schoolbook circuit
uses `64² + 63² = 8065` gates. -/
example : ∃ B : BCircuit 64 127,
    (∀ x y r, B.eval x y r = acyclicConv 64 x y r) ∧ B.size = 3779 ∧ B.mulCount = 128 := by
  obtain ⟨B, h1, h2, h3⟩ := XPlan.exists_conv_circuit
    (.ct .two (.ct .two (.ct .two (.ct .two (.ct .two (.ct .two .two))))))
    (by decide +kernel) (n := 64) (by norm_num) (by decide +kernel)
  exact ⟨B, h1, by rw [h2]; decide +kernel, by rw [h3]; decide +kernel⟩

end FdrsFormal.NumberTheory.Characters.FourierCircuit
