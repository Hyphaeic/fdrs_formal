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

# The exact Fourier gate model (Phase 3 addendum, §1.7)

**Definition 216** — the scalar linear-circuit model of OpenAI's mathematics
collection, family 130 ("Finite tensor savings and exact Fourier circuits"),
re-stated here with the same semantics as its comparator statement
`lean/ComparatorChallenges/ExactFourier.lean` (openai/math, Apache License 2.0):

- a gate adds, subtracts, or multiplies by a predetermined complex scalar one or
  two *available* values, and costs one;
- a program is a topologically ordered scalar DAG — the `k`-th gate may read the
  `n` inputs, the constant `0` (slot `n`), and the `k` earlier gates; values are
  never consumed;
- a circuit names its outputs among the available values, so permutations and
  fan-out are free; it *computes* a matrix `A` if `eval x = A x` for every `x`.

`MainStatement` records family 130's theorem as a proposition; it is **not**
proven in this corpus.

To build circuits compositionally, this file adds a straight-line builder over
`ℕ`-addressed registers (`LGate`, `exec`) — reading an unwritten register gives
`0` — and `Circuit.ofGates`, which compiles a gate list into a `Circuit` gate
for gate (`ofGates_eval`, `ofGates_size`). The workhorse is the linear-combination
block: `m` terms cost `2m - 1` gates (`lcGates_spec`), and a row of equal blocks
(`blockGates_spec`) is one layer of a sparse factorization.
-/

import FdrsFormal.NumberTheory.Characters.MixedRadixFFT
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace FdrsFormal.NumberTheory.Characters.FourierCircuit

open FdrsFormal.NumberTheory.Characters.MixedRadixFFT

/-! ## Definition 216: the gate model (family 130) -/

/-- One charged scalar gate, referencing only available values. -/
inductive Gate (w : ℕ) where
  | add (i j : Fin w)
  | sub (i j : Fin w)
  | scale (c : ℂ) (i : Fin w)

/-- Gate semantics. -/
def Gate.eval {w : ℕ} (v : Fin w → ℂ) : Gate w → ℂ
  | .add i j => v i + v j
  | .sub i j => v i - v j
  | .scale c i => c * v i

/-- A topologically ordered scalar DAG on `n` inputs with `k` gates. -/
inductive Program (n : ℕ) : ℕ → Type where
  | nil : Program n 0
  | step {k : ℕ} (p : Program n k) (g : Gate (n + 1 + k)) : Program n (k + 1)

/-- All available values: the inputs, the constant `0`, then each gate. -/
def Program.eval {n : ℕ} : {k : ℕ} → Program n k → (Fin n → ℂ) → (Fin (n + 1 + k) → ℂ)
  | 0, .nil, x => Fin.snoc x 0
  | _ + 1, .step p g, x =>
      let v := p.eval x
      Fin.snoc v (g.eval v)

/-- A circuit: a program plus the names of its `n` outputs.

**fdrs.md**: Definition 216 (the exact Fourier gate model). -/
structure Circuit (n : ℕ) where
  size : ℕ
  program : Program n size
  outputs : Fin n → Fin (n + 1 + size)

def Circuit.eval {n : ℕ} (C : Circuit n) (x : Fin n → ℂ) : Fin n → ℂ :=
  fun i => C.program.eval x (C.outputs i)

/-- The unnormalized Fourier matrix `(ζ_n^{jk})`. -/
noncomputable def fourierMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun j k => zeta n ^ (j.val * k.val)

def Circuit.Computes {n : ℕ} (C : Circuit n) (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ x, C.eval x = A.mulVec x

/-- Family 130's theorem, as a proposition (not proven here): for every `c > 0`,
arbitrarily long lengths admit exact Fourier circuits with fewer than
`c · n · log₂ n` gates. -/
def MainStatement : Prop :=
  ∀ c : ℝ, 0 < c → ∀ N₀ : ℕ, 2 ≤ N₀ → ∃ n : ℕ, N₀ ≤ n ∧
    ∃ C : Circuit n, C.Computes (fourierMatrix n) ∧
      (C.size : ℝ) < c * (n : ℝ) * Real.logb 2 (n : ℝ)

/-! ## The straight-line builder -/

/-- A gate on `ℕ`-addressed registers. -/
inductive LGate where
  | add (i j : ℕ)
  | sub (i j : ℕ)
  | scale (c : ℂ) (i : ℕ)

def LGate.eval (v : ℕ → ℂ) : LGate → ℂ
  | .add i j => v i + v j
  | .sub i j => v i - v j
  | .scale c i => c * v i

/-- Register file: the next free address and the register contents. -/
structure State where
  pos : ℕ
  val : ℕ → ℂ

/-- Run a gate list: each gate writes the next free register. -/
def exec : List LGate → State → State
  | [], s => s
  | g :: gs, s => exec gs ⟨s.pos + 1, Function.update s.val s.pos (g.eval s.val)⟩

theorem exec_nil (s : State) : exec [] s = s := rfl

theorem exec_cons (g : LGate) (gs : List LGate) (s : State) :
    exec (g :: gs) s = exec gs ⟨s.pos + 1, Function.update s.val s.pos (g.eval s.val)⟩ := rfl

theorem exec_append (l₁ l₂ : List LGate) (s : State) :
    exec (l₁ ++ l₂) s = exec l₂ (exec l₁ s) := by
  induction l₁ generalizing s with
  | nil => rfl
  | cons g gs ih => exact ih _

theorem exec_pos (l : List LGate) (s : State) : (exec l s).pos = s.pos + l.length := by
  induction l generalizing s with
  | nil => simp [exec]
  | cons g gs ih => rw [exec_cons, ih]; simp; omega

/-- Registers below the start are never written. -/
theorem exec_frame (l : List LGate) (s : State) {j : ℕ} (hj : j < s.pos) :
    (exec l s).val j = s.val j := by
  induction l generalizing s with
  | nil => rfl
  | cons g gs ih =>
    rw [exec_cons, ih _ (by simp; omega)]
    exact Function.update_of_ne (by omega) _ _

/-- Registers at or above the end are never written. -/
theorem exec_above (l : List LGate) (s : State) {j : ℕ} (hj : s.pos + l.length ≤ j) :
    (exec l s).val j = s.val j := by
  induction l generalizing s with
  | nil => rfl
  | cons g gs ih =>
    rw [exec_cons, ih _ (by simp at hj ⊢; omega)]
    exact Function.update_of_ne (by simp at hj; omega) _ _

/-- The initial register file on input `x`: inputs at `0, …, n-1`, zeros above,
next free register `n + 1` (slot `n` is the constant `0`). -/
def initState (n : ℕ) (x : Fin n → ℂ) : State :=
  ⟨n + 1, fun i => if h : i < n then x ⟨i, h⟩ else 0⟩

/-! ## Compiling a gate list to a circuit -/

/-- Read an address as a `Fin` slot; unwritten addresses read the constant slot `n`. -/
def slot (n k i : ℕ) : Fin (n + 1 + k) :=
  if h : i < n + 1 + k then ⟨i, h⟩ else ⟨n, by omega⟩

def LGate.compile (n k : ℕ) : LGate → Gate (n + 1 + k)
  | .add i j => .add (slot n k i) (slot n k j)
  | .sub i j => .sub (slot n k i) (slot n k j)
  | .scale c i => .scale c (slot n k i)

/-- Compile a gate list given in reverse (last gate first). -/
def compileRev (n : ℕ) : (rl : List LGate) → Program n rl.length
  | [] => .nil
  | g :: rl => .step (compileRev n rl) (g.compile n rl.length)

theorem snoc_apply {m : ℕ} (v : Fin m → ℂ) (a : ℂ) (i : Fin (m + 1)) :
    (Fin.snoc (α := fun _ => ℂ) v a i : ℂ) = if h : (i : ℕ) < m then v ⟨i, h⟩ else a := by
  simp only [Fin.snoc]
  split_ifs <;> rfl

theorem compileRev_eval (n : ℕ) (x : Fin n → ℂ) :
    ∀ (rl : List LGate) (i : Fin (n + 1 + rl.length)),
      (compileRev n rl).eval x i = (exec rl.reverse (initState n x)).val i
  | [], i => by
    simp only [compileRev, Program.eval, List.reverse_nil, exec_nil, initState]
    exact snoc_apply x 0 i
  | g :: rl, i => by
    have ih := compileRev_eval n x rl
    set S := exec rl.reverse (initState n x) with hS
    have hSpos : S.pos = n + 1 + rl.length := by
      rw [hS, exec_pos]; simp [initState]
    have hzero_n : S.val n = 0 := by
      rw [hS, exec_frame _ _ (by simp [initState])]; simp [initState]
    have hzero_above : ∀ j, n + 1 + rl.length ≤ j → S.val j = 0 := by
      intro j hj
      rw [hS, exec_above _ _ (by simp [initState]; omega)]
      simp [initState]; omega
    -- the compiled gate reads what the builder gate reads
    have hread : ∀ a : ℕ, (compileRev n rl).eval x (slot n rl.length a) = S.val a := by
      intro a
      unfold slot
      split_ifs with ha
      · exact ih ⟨a, ha⟩
      · rw [ih ⟨n, by omega⟩, hzero_n, hzero_above a (by omega)]
    have hgate : (g.compile n rl.length).eval ((compileRev n rl).eval x) = g.eval S.val := by
      cases g <;> simp [LGate.compile, Gate.eval, LGate.eval, hread]
    have hexec : exec (g :: rl).reverse (initState n x) =
        ⟨S.pos + 1, Function.update S.val S.pos (g.eval S.val)⟩ := by
      rw [List.reverse_cons, exec_append, ← hS]; rfl
    rw [hexec]
    refine (snoc_apply ((compileRev n rl).eval x)
      ((g.compile n rl.length).eval ((compileRev n rl).eval x)) i).trans ?_
    split_ifs with h
    · rw [ih ⟨i, h⟩]
      exact (Function.update_of_ne (by rw [hSpos]; omega) _ _).symm
    · have hi : (i : ℕ) = S.pos := by
        have := i.isLt; simp only [List.length_cons] at this; omega
      rw [hgate]
      show _ = Function.update S.val S.pos (g.eval S.val) (i : ℕ)
      rw [hi, Function.update_self]

/-- Compile a gate list and a choice of output registers into a circuit. -/
def Circuit.ofGates (n : ℕ) (l : List LGate) (out : Fin n → ℕ)
    (hout : ∀ m, out m < n + 1 + l.length) : Circuit n where
  size := l.reverse.length
  program := compileRev n l.reverse
  outputs m := ⟨out m, by simpa using hout m⟩

theorem Circuit.ofGates_size (n : ℕ) (l : List LGate) (out : Fin n → ℕ)
    (hout : ∀ m, out m < n + 1 + l.length) : (Circuit.ofGates n l out hout).size = l.length := by
  simp [Circuit.ofGates]

theorem Circuit.ofGates_eval (n : ℕ) (l : List LGate) (out : Fin n → ℕ)
    (hout : ∀ m, out m < n + 1 + l.length) (x : Fin n → ℂ) (m : Fin n) :
    (Circuit.ofGates n l out hout).eval x m = (exec l (initState n x)).val (out m) := by
  simp only [Circuit.eval, Circuit.ofGates]
  rw [compileRev_eval]
  simp

/-! ## Linear-combination blocks -/

/-- Accumulate further terms: at `pos`, scale; at `pos + 1`, add to the running
sum held at `pos - 1`. -/
def lcTail : ℕ → List (ℂ × ℕ) → List LGate
  | _, [] => []
  | pos, (c, a) :: rest => .scale c a :: .add (pos - 1) pos :: lcTail (pos + 2) rest

/-- `Σ_j c_j · v(a_j)` in `2m - 1` gates, result in the last register written. -/
def lcGates : List (ℂ × ℕ) → ℕ → List LGate
  | [], _ => []
  | (c, a) :: rest, pos => .scale c a :: lcTail (pos + 1) rest

theorem lcTail_length (pos : ℕ) (rest : List (ℂ × ℕ)) :
    (lcTail pos rest).length = 2 * rest.length := by
  induction rest generalizing pos with
  | nil => rfl
  | cons p rest ih => obtain ⟨c, a⟩ := p; simp [lcTail, ih]; ring

theorem lcGates_length (terms : List (ℂ × ℕ)) (pos : ℕ) (h : terms ≠ []) :
    (lcGates terms pos).length = 2 * terms.length - 1 := by
  obtain ⟨⟨c, a⟩, rest, rfl⟩ := List.exists_cons_of_ne_nil h
  simp [lcGates, lcTail_length]; omega

theorem lcTail_spec : ∀ (rest : List (ℂ × ℕ)) (s : State), 1 ≤ s.pos →
    (∀ p ∈ rest, p.2 < s.pos) →
    (exec (lcTail s.pos rest) s).val ((exec (lcTail s.pos rest) s).pos - 1) =
      s.val (s.pos - 1) + (rest.map fun p => p.1 * s.val p.2).sum
  | [], s, _, _ => by simp [lcTail, exec]
  | (c, a) :: rest, s, h1, ha => by
    have ha0 : a < s.pos := ha (c, a) (by simp)
    set s1 : State := ⟨s.pos + 1, Function.update s.val s.pos (c * s.val a)⟩
    set s2 : State := ⟨s1.pos + 1, Function.update s1.val s1.pos (s1.val (s.pos - 1) + s1.val s.pos)⟩
    have hs1a : ∀ j, j < s.pos → s1.val j = s.val j := fun j hj =>
      Function.update_of_ne (by omega) _ _
    have hs2a : ∀ j, j < s.pos → s2.val j = s.val j := fun j hj => by
      simp only [s2]
      rw [Function.update_of_ne (by simp [s1]; omega), hs1a j hj]
    have hrest : ∀ p ∈ rest, p.2 < s2.pos := fun p hp => by
      have := ha p (by simp [hp]); simp [s2, s1]; omega
    have ih := lcTail_spec rest s2 (by simp [s2, s1]) hrest
    have hpos : s2.pos = s.pos + 2 := by simp [s2, s1]
    have hlast : s2.val (s2.pos - 1) = s.val (s.pos - 1) + c * s.val a := by
      simp only [s2, s1]
      rw [show s.pos + 1 + 1 - 1 = s.pos + 1 by omega, Function.update_self,
        Function.update_of_ne (by omega), Function.update_self]
    have hsum : (rest.map fun p => p.1 * s2.val p.2) = (rest.map fun p => p.1 * s.val p.2) :=
      List.map_congr_left fun p hp => by rw [hs2a p.2 (ha p (by simp [hp]))]
    show (exec (lcTail (s.pos + 2) rest) s2).val ((exec (lcTail (s.pos + 2) rest) s2).pos - 1) = _
    rw [← hpos, ih, hlast, hsum]
    simp [add_assoc]

/-- **The linear-combination block.** Started at the next free register, with all
addresses already written, the block leaves `Σ_j c_j · v(a_j)` in its last register. -/
theorem lcGates_spec (terms : List (ℂ × ℕ)) (s : State) (hne : terms ≠ [])
    (ha : ∀ p ∈ terms, p.2 < s.pos) :
    (exec (lcGates terms s.pos) s).val ((exec (lcGates terms s.pos) s).pos - 1) =
      (terms.map fun p => p.1 * s.val p.2).sum := by
  obtain ⟨⟨c, a⟩, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have ha0 : a < s.pos := ha (c, a) (by simp)
  set s1 : State := ⟨s.pos + 1, Function.update s.val s.pos (c * s.val a)⟩
  have hs1a : ∀ j, j < s.pos → s1.val j = s.val j := fun j hj =>
    Function.update_of_ne (by omega) _ _
  have hrest : ∀ p ∈ rest, p.2 < s1.pos := fun p hp => by
    have := ha p (by simp [hp]); simp [s1]; omega
  have ih := lcTail_spec rest s1 (by simp [s1]) hrest
  have hsum : (rest.map fun p => p.1 * s1.val p.2) = (rest.map fun p => p.1 * s.val p.2) :=
    List.map_congr_left fun p hp => by rw [hs1a p.2 (ha p (by simp [hp]))]
  show (exec (lcTail (s.pos + 1) rest) s1).val ((exec (lcTail (s.pos + 1) rest) s1).pos - 1) = _
  rw [show s.pos + 1 = s1.pos from rfl, ih, hsum]
  simp [s1]

/-- A row of `R` linear-combination blocks, block `r` starting at `pos0 + r·w`. -/
def blockGates (pos0 w : ℕ) (f : ℕ → List (ℂ × ℕ)) : ℕ → List LGate
  | 0 => []
  | r + 1 => blockGates pos0 w f r ++ lcGates (f r) (pos0 + r * w)

/-- **A row of blocks.** If every block has `m ≥ 1` terms (`w = 2m - 1` gates) reading
registers below `pos0`, then block `r`'s sum lands at `pos0 + r·w + (w - 1)`. -/
theorem blockGates_spec (pos0 m : ℕ) (hm : 1 ≤ m) (f : ℕ → List (ℂ × ℕ)) (s : State)
    (hs : s.pos = pos0) :
    ∀ R, (∀ r < R, (f r).length = m ∧ ∀ p ∈ f r, p.2 < pos0) →
      (exec (blockGates pos0 (2 * m - 1) f R) s).pos = pos0 + R * (2 * m - 1) ∧
      ∀ r < R, (exec (blockGates pos0 (2 * m - 1) f R) s).val
          (pos0 + r * (2 * m - 1) + (2 * m - 2)) =
        ((f r).map fun p => p.1 * s.val p.2).sum
  | 0, _ => ⟨by simp [blockGates, exec, hs], fun r hr => absurd hr (Nat.not_lt_zero _)⟩
  | R + 1, hf => by
    obtain ⟨hpos, hval⟩ := blockGates_spec pos0 m hm f s hs R fun r hr => hf r (by omega)
    set S := exec (blockGates pos0 (2 * m - 1) f R) s
    obtain ⟨hlen, hread⟩ := hf R (by omega)
    have hne : f R ≠ [] := by intro h; rw [h] at hlen; simp at hlen; omega
    have hSpos : S.pos = pos0 + R * (2 * m - 1) := hpos
    have hgl := lcGates_length (f R) S.pos hne
    simp only [blockGates, exec_append]
    rw [← hSpos]
    refine ⟨?_, fun r hr => ?_⟩
    · rw [exec_pos, hgl, hSpos, hlen]; ring_nf
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl
      · have hfr : pos0 + r * (2 * m - 1) + (2 * m - 2) < S.pos := by
          have key : (r + 1) * (2 * m - 1) ≤ R * (2 * m - 1) := Nat.mul_le_mul_right _ hr
          rw [add_mul, one_mul] at key
          rw [hSpos]; omega
        rw [exec_frame _ _ hfr, hval r hr]
      · have hspec : (exec (lcGates (f r) S.pos) S).val
            ((exec (lcGates (f r) S.pos) S).pos - 1) =
            ((f r).map fun p => p.1 * S.val p.2).sum :=
          lcGates_spec (f r) S hne fun p hp => by
            have := hread p hp; rw [hSpos]; omega
        have haddr : (exec (lcGates (f r) S.pos) S).pos - 1 =
            pos0 + r * (2 * m - 1) + (2 * m - 2) := by
          rw [exec_pos, hgl, hlen, hSpos]; omega
        rw [← haddr]
        refine hspec.trans (congrArg List.sum (List.map_congr_left fun p hp => ?_))
        rw [exec_frame _ _ (by rw [hs]; exact hread p hp)]

theorem blockGates_length (pos0 m : ℕ) (f : ℕ → List (ℂ × ℕ)) :
    ∀ R, (∀ r < R, (f r).length = m) → 1 ≤ m →
      (blockGates pos0 (2 * m - 1) f R).length = R * (2 * m - 1)
  | 0, _, _ => by simp [blockGates]
  | R + 1, hf, hm => by
    have hne : f R ≠ [] := by intro h; have := hf R (by omega); rw [h] at this; simp at this; omega
    rw [blockGates, List.length_append, blockGates_length pos0 m f R (fun r hr => hf r (by omega)) hm,
      lcGates_length _ _ hne, hf R (by omega)]
    ring

end FdrsFormal.NumberTheory.Characters.FourierCircuit
