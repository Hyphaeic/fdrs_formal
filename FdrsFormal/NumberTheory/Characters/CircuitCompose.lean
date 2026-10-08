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

# Composing Fourier circuits (Phase 3 addendum, §1.11)

The radix-schedule search builds every circuit from small kernels by two splits.
This file proves both splits as theorems about arbitrary circuits, so that every
count the search reports becomes a proven upper bound.

- **Definition 217** (`reloc`, `Program.toGates`, `copyRow`): running a circuit
  inside a larger one — its inputs read from any registers, its constant from a
  z0 register, its gates relocated to a fresh block.
- **Theorem 127** (`exists_ct_circuit`): from circuits for lengths `n₁, n₂`, the
  positional split gives a circuit for `n₁n₂` with
  `n₁|C₂| + n₂|C₁| + #{(a, p) : n₁n₂ ∤ ap}` gates (trivial twiddles skipped).
- **Theorem 128** (`exists_pfa_circuit`): for coprime `n₁, n₂`, the residue split
  gives `n₁|C₂| + n₂|C₁|` gates — no twiddles.
- **Corollary 37** (`Plan`, `Plan.exists_circuit`): every plan of the search grammar
  (2-point butterfly, conjugate-pair kernel, positional and residue splits)
  yields an exact circuit with exactly its computed cost.

**Honest scope.** Classical (Cooley–Tukey 1965; Good 1958, Thomas 1963). The
corpus contributes the gate-exact statements in family 130's model and the bridge
from the search tool's plans to proofs.
-/

import FdrsFormal.NumberTheory.Characters.PairKernel

namespace FdrsFormal.NumberTheory.Characters.FourierCircuit

open FdrsFormal.NumberTheory.Characters.MixedRadixFFT

/-! ## Definition 217: relocating a circuit -/

/-- Where register `i` of an embedded circuit on `n` inputs lands: input `i` at
`inAddr i`, the constant at `z0`, gate `j` at `base + j`. -/
def reloc (n : ℕ) (inAddr : ℕ → ℕ) (z0 base i : ℕ) : ℕ :=
  if i < n then inAddr i else if i = n then z0 else base + (i - (n + 1))

/-- A gate of an embedded circuit, relocated. -/
def Gate.reloc (n : ℕ) {w : ℕ} (inAddr : ℕ → ℕ) (z0 base : ℕ) : Gate w → LGate
  | .add i j => .add (FourierCircuit.reloc n inAddr z0 base i) (FourierCircuit.reloc n inAddr z0 base j)
  | .sub i j => .sub (FourierCircuit.reloc n inAddr z0 base i) (FourierCircuit.reloc n inAddr z0 base j)
  | .scale c i => .scale c (FourierCircuit.reloc n inAddr z0 base i)

/-- The relocated gate list of a program.

**fdrs.md**: Definition 217 (embedding a circuit). -/
def Program.toGates {n : ℕ} (inAddr : ℕ → ℕ) (z0 base : ℕ) : {k : ℕ} → Program n k → List LGate
  | 0, .nil => []
  | _ + 1, .step p g => p.toGates inAddr z0 base ++ [Gate.reloc n inAddr z0 base g]

theorem Program.toGates_length {n : ℕ} (inAddr : ℕ → ℕ) (z0 base : ℕ) :
    ∀ {k : ℕ} (p : Program n k), (p.toGates inAddr z0 base).length = k
  | 0, .nil => rfl
  | _ + 1, .step p g => by simp [Program.toGates, Program.toGates_length inAddr z0 base p]

theorem reloc_lt {n k : ℕ} {inAddr : ℕ → ℕ} {z0 base : ℕ} (hin : ∀ i < n, inAddr i < base)
    (hz : z0 < base) (i : Fin (n + 1 + k)) : reloc n inAddr z0 base i < base + k := by
  have hi := i.isLt
  unfold reloc
  split_ifs with h1 h2
  · exact (hin _ h1).trans_le (Nat.le_add_right _ _)
  · exact hz.trans_le (Nat.le_add_right _ _)
  · omega

/-- **Running an embedded program.** Started at `base` with its inputs and its z0
register already written, the relocated program reproduces every register of the
original. -/
theorem Program.toGates_spec {n : ℕ} (inAddr : ℕ → ℕ) (z0 base : ℕ) (s : State)
    (hs : s.pos = base) (hin : ∀ i < n, inAddr i < base) (hz : z0 < base)
    (hz0 : s.val z0 = 0) :
    ∀ {k : ℕ} (p : Program n k),
      (exec (p.toGates inAddr z0 base) s).pos = base + k ∧
      ∀ i : Fin (n + 1 + k),
        (exec (p.toGates inAddr z0 base) s).val (reloc n inAddr z0 base i) =
          p.eval (fun j => s.val (inAddr j)) i
  | 0, .nil => by
    refine ⟨by simp [Program.toGates, exec, hs], fun i => ?_⟩
    simp only [Program.toGates, exec_nil, Program.eval]
    rw [snoc_apply]
    unfold reloc
    split_ifs with h1 h2
    · rfl
    · exact hz0
    · exfalso; have := i.isLt; omega
  | k + 1, .step p g => by
    obtain ⟨hpos, hval⟩ := Program.toGates_spec inAddr z0 base s hs hin hz hz0 p
    set S := exec (p.toGates inAddr z0 base) s
    have hexec : exec ((Program.step p g).toGates inAddr z0 base) s =
        ⟨S.pos + 1, Function.update S.val S.pos ((Gate.reloc n inAddr z0 base g).eval S.val)⟩ := by
      simp only [Program.toGates, exec_append, exec_cons, exec_nil]; rfl
    have hread : ∀ a : Fin (n + 1 + k), S.val (reloc n inAddr z0 base a) =
        p.eval (fun j => s.val (inAddr j)) a := hval
    have hgate : (Gate.reloc n inAddr z0 base g).eval S.val =
        g.eval (p.eval (fun j => s.val (inAddr j))) := by
      cases g <;> simp [Gate.reloc, LGate.eval, Gate.eval, hread]
    rw [hexec]
    refine ⟨by simp [hpos]; ring, fun i => ?_⟩
    simp only [Program.eval]
    rw [snoc_apply]
    split_ifs with hi
    · have hlt : reloc n inAddr z0 base i < base + k := reloc_lt (k := k) hin hz ⟨i, hi⟩
      rw [Function.update_of_ne (by rw [hpos]; omega)]
      exact hread ⟨i, hi⟩
    · have hi2 : (i : ℕ) < n + 1 + k + 1 := i.isLt
      have hi3 : ¬ (i : ℕ) < n + 1 + k := hi
      have hi' : (i : ℕ) = n + 1 + k := by omega
      have hr : reloc n inAddr z0 base i = S.pos := by
        unfold reloc; rw [if_neg (by omega), if_neg (by omega), hpos]; omega
      rw [hr, Function.update_self, hgate]

/-- `R` relocated copies of a circuit, copy `r` reading its inputs from `inOf r`. -/
def copyRow {n : ℕ} (C : Circuit n) (inOf : ℕ → ℕ → ℕ) (z0 base0 : ℕ) : ℕ → List LGate
  | 0 => []
  | R + 1 => copyRow C inOf z0 base0 R ++ C.program.toGates (inOf R) z0 (base0 + R * C.size)

theorem copyRow_length {n : ℕ} (C : Circuit n) (inOf : ℕ → ℕ → ℕ) (z0 base0 : ℕ) :
    ∀ R, (copyRow C inOf z0 base0 R).length = R * C.size
  | 0 => by simp [copyRow]
  | R + 1 => by
    rw [copyRow, List.length_append, copyRow_length C inOf z0 base0 R, Program.toGates_length]
    ring

/-- **A row of copies.** Each copy, run on registers below `base0`, leaves the outputs
of the circuit on its inputs. -/
theorem copyRow_spec {n : ℕ} (C : Circuit n) (inOf : ℕ → ℕ → ℕ) (z0 base0 : ℕ) (s : State)
    (hs : s.pos = base0) (hz : z0 < base0) (hz0 : s.val z0 = 0) :
    ∀ R, (∀ r < R, ∀ i < n, inOf r i < base0) →
      (exec (copyRow C inOf z0 base0 R) s).pos = base0 + R * C.size ∧
      ∀ r < R, ∀ m : Fin n,
        (exec (copyRow C inOf z0 base0 R) s).val
            (reloc n (inOf r) z0 (base0 + r * C.size) (C.outputs m)) =
          C.eval (fun j => s.val (inOf r j)) m
  | 0, _ => ⟨by simp [copyRow, exec, hs], fun r hr => absurd hr (Nat.not_lt_zero _)⟩
  | R + 1, hin => by
    obtain ⟨hpos, hval⟩ := copyRow_spec C inOf z0 base0 s hs hz hz0 R
      fun r hr => hin r (by omega)
    set S := exec (copyRow C inOf z0 base0 R) s
    have hge : base0 ≤ S.pos := by rw [hpos]; exact Nat.le_add_right _ _
    have hfr : ∀ a < base0, S.val a = s.val a := fun a ha => exec_frame _ _ (by omega)
    have hcopy := Program.toGates_spec (inOf R) z0 (base0 + R * C.size) S hpos
      (fun i hi => (hin R (by omega) i hi).trans_le (by omega)) (by omega)
      (by rw [hfr _ hz, hz0]) C.program
    have hexec : exec (copyRow C inOf z0 base0 (R + 1)) s =
        exec (C.program.toGates (inOf R) z0 (base0 + R * C.size)) S := by
      simp only [copyRow, exec_append]; rfl
    rw [hexec]
    refine ⟨by rw [hcopy.1]; ring, fun r hr m => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl
    · have hlt := reloc_lt (k := C.size) (base := base0 + r * C.size)
        (fun i hi => (hin r (by omega) i hi).trans_le (Nat.le_add_right _ _))
        (hz.trans_le (Nat.le_add_right _ _)) (C.outputs m)
      have hle : base0 + r * C.size + C.size ≤ S.pos := by
        rw [hpos]
        have : (r + 1) * C.size ≤ R * C.size := Nat.mul_le_mul_right _ hr
        rw [add_mul, one_mul] at this; omega
      rw [exec_frame _ _ (by omega)]
      exact hval r hr m
    · rw [hcopy.2 (C.outputs m)]
      simp only [Circuit.eval]
      congr 1
      funext j
      rw [hfr _ (hin r (by omega) j j.isLt)]

/-- A copy of a circuit computing the Fourier matrix leaves the DFT of its inputs. -/
theorem Circuit.eval_fourier {n : ℕ} {C : Circuit n} (hC : C.Computes (fourierMatrix n))
    (v : Fin n → ℂ) (m : Fin n) :
    C.eval v m = ∑ j : Fin n, zeta n ^ ((m : ℕ) * (j : ℕ)) * v j := by
  rw [hC v]; rfl

/-! ## Arithmetic for the splits -/

/-- `Σ_{j < n₁n₂} f j = Σ_{c < n₂} Σ_{a < n₁} f (n₁ c + a)`. -/
theorem sum_range_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n1 : ℕ) :
    ∀ n2, ∑ j ∈ Finset.range (n1 * n2), f j =
      ∑ c ∈ Finset.range n2, ∑ a ∈ Finset.range n1, f (n1 * c + a)
  | 0 => by simp
  | n2 + 1 => by
    rw [Nat.mul_succ, Finset.sum_range_add, sum_range_mul f n1 n2, Finset.sum_range_succ]

/-- The DFT of a register file, as a sum over `ℕ`. -/
theorem mulVec_fourier_eq (N : ℕ) (x : Fin N → ℂ) (k : Fin N) :
    (fourierMatrix N).mulVec x k =
      ∑ j ∈ Finset.range N, zeta N ^ ((k : ℕ) * j) * extend x j := by
  simp only [Matrix.mulVec, dotProduct, fourierMatrix]
  rw [Finset.sum_range (fun j => zeta N ^ ((k : ℕ) * j) * extend x j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [extend, dif_pos j.isLt]

theorem sum_fin_eq_range {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ∑ j : Fin n, f j = ∑ j ∈ Finset.range n, f j := (Finset.sum_range f).symm

/-- The positional phase: `ζ_N^{(p + n₂q)(n₁c + a)} = ζ_{n₂}^{cp} ζ_N^{ap} ζ_{n₁}^{qa}`. -/
theorem zeta_ct_phase (n1 n2 a c p q : ℕ) (h1 : n1 ≠ 0) (h2 : n2 ≠ 0) :
    zeta (n1 * n2) ^ ((p + n2 * q) * (n1 * c + a)) =
      zeta n2 ^ (c * p) * zeta (n1 * n2) ^ (a * p) * zeta n1 ^ (q * a) := by
  have e : (p + n2 * q) * (n1 * c + a) =
      n1 * (c * p) + a * p + (n1 * n2) * (c * q) + n2 * (q * a) := by ring
  rw [e, pow_add, pow_add, pow_add, zeta_pow_self_mul _ _ (mul_ne_zero h1 h2), mul_one,
    show zeta (n1 * n2) ^ (n1 * (c * p)) = zeta n2 ^ (c * p) by
      rw [mul_comm n1 n2]; exact zeta_mul_pow_mul n2 n1 _ h2 h1,
    zeta_mul_pow_mul n1 n2 _ h1 h2]

/-! ## Theorem 127: the positional split -/

/-- Nontrivial twiddle positions: `(a, p)` with `a < n₁`, `p < n₂`, `n₁n₂ ∤ ap`. -/
def twList (n1 n2 : ℕ) : List (ℕ × ℕ) :=
  ((List.range n1).flatMap fun a => (List.range n2).map fun p => (a, p)).filter
    fun ap => decide (ap.1 * ap.2 % (n1 * n2) ≠ 0)

/-- Number of nontrivial twiddles of the split `n₁ · n₂`. -/
def twiddleCount (n1 n2 : ℕ) : ℕ := (twList n1 n2).length

theorem mem_twList {n1 n2 a p : ℕ} :
    (a, p) ∈ twList n1 n2 ↔ a < n1 ∧ p < n2 ∧ a * p % (n1 * n2) ≠ 0 := by
  simp [twList, and_assoc]

section CT

variable (n1 : ℕ) {n2 : ℕ} (C2 : Circuit n2)

/-- Output `p` of inner copy `a`. -/
def ctY (a p : ℕ) : ℕ :=
  if h : p < n2 then
    reloc n2 (fun c => n1 * c + a) (n1 * n2) (n1 * n2 + 1 + a * C2.size) (C2.outputs ⟨p, h⟩)
  else 0

def ctTwBase : ℕ := n1 * n2 + 1 + n1 * C2.size

/-- The twiddled value `ζ_N^{ap} Y_a[p]`: the inner output itself when trivial. -/
noncomputable def ctZ (a p : ℕ) : ℕ :=
  if a * p % (n1 * n2) = 0 then ctY n1 C2 a p
  else ctTwBase n1 C2 + (twList n1 n2).idxOf (a, p)

def ctOutBase : ℕ := ctTwBase n1 C2 + twiddleCount n1 n2

noncomputable def ctGates {n1 : ℕ} (C1 : Circuit n1) : List LGate :=
  copyRow C2 (fun a c => n1 * c + a) (n1 * n2) (n1 * n2 + 1) n1 ++
  (twList n1 n2).map (fun ap =>
    LGate.scale (zeta (n1 * n2) ^ (ap.1 * ap.2)) (ctY n1 C2 ap.1 ap.2)) ++
  copyRow C1 (fun p a => ctZ n1 C2 a p) (n1 * n2) (ctOutBase n1 C2) n2

/-- Output register of frequency `k = p + n₂ q`. -/
noncomputable def ctOut {n1 : ℕ} (C1 : Circuit n1) (k : ℕ) : ℕ :=
  if h : k / n2 < n1 then
    reloc n1 (fun a => ctZ n1 C2 a (k % n2)) (n1 * n2) (ctOutBase n1 C2 + (k % n2) * C1.size)
      (C1.outputs ⟨k / n2, h⟩)
  else 0

end CT

theorem ctGates_length {n1 n2 : ℕ} (C1 : Circuit n1) (C2 : Circuit n2) :
    (ctGates C2 C1).length = n1 * C2.size + twiddleCount n1 n2 + n2 * C1.size := by
  simp [ctGates, copyRow_length, twiddleCount]; ring

/-- **Theorem 127 (the positional split).** From exact circuits for lengths `n₁` and
`n₂`, the Cooley–Tukey split gives an exact circuit for `n₁n₂` with
`n₁|C₂| + n₂|C₁| + #{(a, p) : n₁n₂ ∤ ap}` gates.

**fdrs.md**: Theorem 127 (the positional split). -/
theorem exists_ct_circuit {n1 n2 : ℕ} (hn1 : 1 ≤ n1) (hn2 : 1 ≤ n2)
    (C1 : Circuit n1) (hC1 : C1.Computes (fourierMatrix n1))
    (C2 : Circuit n2) (hC2 : C2.Computes (fourierMatrix n2)) :
    ∃ C : Circuit (n1 * n2), C.Computes (fourierMatrix (n1 * n2)) ∧
      C.size = n1 * C2.size + n2 * C1.size + twiddleCount n1 n2 := by
  set N := n1 * n2 with hN
  have hN0 : N ≠ 0 := by positivity
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
  -- bounds
  have hinIn : ∀ a < n1, ∀ c < n2, n1 * c + a < N + 1 := fun a ha c hc => by
    have : n1 * c + n1 ≤ n1 * n2 := by nlinarith
    omega
  have hY : ∀ a < n1, ∀ p < n2, ctY n1 C2 a p < ctTwBase n1 C2 := fun a ha p hp => by
    simp only [ctY, dif_pos hp, ctTwBase]
    have := reloc_lt (k := C2.size) (z0 := n1 * n2) (base := n1 * n2 + 1 + a * C2.size)
      (fun c hc => (hinIn a ha c hc).trans_le (Nat.le_add_right _ _)) (by omega)
      (C2.outputs ⟨p, hp⟩)
    have : (a + 1) * C2.size ≤ n1 * C2.size := Nat.mul_le_mul_right _ ha
    rw [add_mul, one_mul] at this
    omega
  have hZ : ∀ a < n1, ∀ p < n2, ctZ n1 C2 a p < ctOutBase n1 C2 := fun a ha p hp => by
    unfold ctZ ctOutBase twiddleCount
    split_ifs with hd
    · exact (hY a ha p hp).trans_le (Nat.le_add_right _ _)
    · exact Nat.add_lt_add_left (List.idxOf_lt_length_of_mem (mem_twList.mpr ⟨ha, hp, hd⟩)) _
  have hout : ∀ k : Fin N, ctOut C2 C1 k < N + 1 + (ctGates C2 C1).length := by
    intro k
    have hk : (k : ℕ) < n1 * n2 := k.isLt
    have hq : (k : ℕ) / n2 < n1 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by linarith)
    have hp : (k : ℕ) % n2 < n2 := Nat.mod_lt _ (by omega)
    simp only [ctOut, dif_pos hq]
    have := reloc_lt (k := C1.size) (z0 := n1 * n2) (base := ctOutBase n1 C2 + (k % n2) * C1.size)
      (fun a ha => (hZ a ha _ hp).trans_le (Nat.le_add_right _ _))
      ((show N < ctOutBase n1 C2 by simp [ctOutBase, ctTwBase]; omega).trans_le (Nat.le_add_right _ _))
      (C1.outputs ⟨(k : ℕ) / n2, hq⟩)
    have h2 : ((k : ℕ) % n2 + 1) * C1.size ≤ n2 * C1.size := Nat.mul_le_mul_right _ hp
    rw [add_mul, one_mul] at h2
    rw [ctGates_length]
    simp only [ctOutBase, ctTwBase] at this ⊢
    omega
  refine ⟨Circuit.ofGates N (ctGates C2 C1) (fun k => ctOut C2 C1 k) hout, fun x => ?_, ?_⟩
  · funext k
    rw [Circuit.ofGates_eval, mulVec_fourier_eq]
    set S0 := initState N x
    have hS0 : ∀ i, S0.val i = extend x i := fun _ => rfl
    -- inner copies
    obtain ⟨hpos1, hval1⟩ := copyRow_spec C2 (fun a c => n1 * c + a) N (N + 1) S0 rfl
      (by omega) (by simp [S0, initState]) n1 (fun a ha c hc => hinIn a ha c hc)
    set S1 := exec (copyRow C2 (fun a c => n1 * c + a) N (N + 1) n1) S0
    have hY1 : ∀ a < n1, ∀ p < n2, S1.val (ctY n1 C2 a p) =
        ∑ c ∈ Finset.range n2, zeta n2 ^ (p * c) * extend x (n1 * c + a) := by
      intro a ha p hp
      simp only [ctY, dif_pos hp]
      rw [hval1 a ha ⟨p, hp⟩, Circuit.eval_fourier hC2]
      exact sum_fin_eq_range n2 (fun c => zeta n2 ^ (p * c) * extend x (n1 * c + a))
    -- twiddles
    set TW := (twList n1 n2).map (fun ap =>
      LGate.scale (zeta N ^ (ap.1 * ap.2)) (ctY n1 C2 ap.1 ap.2))
    set S2 := exec TW S1
    have hS1pos : S1.pos = ctTwBase n1 C2 := by rw [hpos1]; rfl
    have hS2pos : S2.pos = ctOutBase n1 C2 := by
      simp [S2, exec_pos, hS1pos, TW, ctOutBase, twiddleCount]
    have hind := exec_indep TW S1 (fun g hg => by
      simp only [TW, List.mem_map] at hg
      obtain ⟨⟨a, p⟩, hap, rfl⟩ := hg
      obtain ⟨ha, hp, _⟩ := mem_twList.mp hap
      simp only [LGate.ReadsBelow, hS1pos]; exact hY a ha p hp)
    have hZ2 : ∀ a < n1, ∀ p < n2, S2.val (ctZ n1 C2 a p) =
        zeta N ^ (a * p) * S1.val (ctY n1 C2 a p) := by
      intro a ha p hp
      unfold ctZ
      split_ifs with hd
      · rw [exec_frame _ _ (by rw [hS1pos]; exact hY a ha p hp),
          zeta_pow_mod N _ hN0, hd, pow_zero, one_mul]
      · have hmem := mem_twList.mpr ⟨ha, hp, hd⟩
        have hi := List.idxOf_lt_length_of_mem hmem
        have := hind ((twList n1 n2).idxOf (a, p)) (by simpa [TW] using hi)
        rw [hS1pos] at this
        rw [this]
        simp only [TW, List.getElem_map, List.getElem_idxOf, LGate.eval]
    -- outer copies
    obtain ⟨_, hval3⟩ := copyRow_spec C1 (fun p a => ctZ n1 C2 a p) N (ctOutBase n1 C2) S2 hS2pos
      (by simp [ctOutBase, ctTwBase]; omega)
      (by rw [exec_frame _ _ (by rw [hS1pos]; simp only [ctTwBase]; omega),
            exec_frame _ _ (by simp [S0, initState])]; simp [S0, initState])
      n2 (fun p hp a ha => hZ a ha p hp)
    have hexec : exec (ctGates C2 C1) S0 =
        exec (copyRow C1 (fun p a => ctZ n1 C2 a p) N (ctOutBase n1 C2) n2) S2 := by
      simp only [ctGates, exec_append]; rfl
    have hk : (k : ℕ) < n1 * n2 := k.isLt
    have hq : (k : ℕ) / n2 < n1 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by linarith)
    have hp : (k : ℕ) % n2 < n2 := Nat.mod_lt _ (by omega)
    rw [hexec]
    simp only [ctOut, dif_pos hq]
    rw [hval3 _ hp ⟨(k : ℕ) / n2, hq⟩, Circuit.eval_fourier hC1]
    rw [sum_fin_eq_range n1 (fun a => zeta n1 ^ ((k : ℕ) / n2 * a) *
      S2.val (ctZ n1 C2 a ((k : ℕ) % n2)))]
    -- the target, re-indexed by n = n₁c + a
    have hre : ∑ j ∈ Finset.range N, zeta N ^ ((k : ℕ) * j) * extend x j =
        ∑ c ∈ Finset.range n2, ∑ a ∈ Finset.range n1,
          zeta N ^ ((k : ℕ) * (n1 * c + a)) * extend x (n1 * c + a) :=
      sum_range_mul (fun j => zeta N ^ ((k : ℕ) * j) * extend x j) n1 n2
    rw [hre, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha' : a < n1 := by simpa using ha
    rw [hZ2 a ha' _ hp, hY1 a ha' _ hp, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hk : (k : ℕ) = (k : ℕ) % n2 + n2 * ((k : ℕ) / n2) := (Nat.mod_add_div _ _).symm
    rw [hk, zeta_ct_phase n1 n2 a c _ _ (by omega) (by omega), ← hk]
    ring
  · rw [Circuit.ofGates_size, ctGates_length]; ring

/-! ## Theorem 128: the residue split -/

/-- For coprime `n₁, n₂ ≥ 1`, `(a, c) ↦ (n₂a + n₁c) mod n₁n₂` re-indexes `[0, n₁n₂)`. -/
theorem sum_range_crt {M : Type*} [AddCommMonoid M] (f : ℕ → M) {n1 n2 : ℕ}
    (hn1 : 1 ≤ n1) (hn2 : 1 ≤ n2) (hcop : Nat.Coprime n1 n2) :
    ∑ j ∈ Finset.range (n1 * n2), f j =
      ∑ a ∈ Finset.range n1, ∑ c ∈ Finset.range n2, f ((n2 * a + n1 * c) % (n1 * n2)) := by
  set N := n1 * n2 with hN
  have hNpos : 0 < N := by positivity
  set φ : ℕ × ℕ → ℕ := fun x => (n2 * x.1 + n1 * x.2) % N
  set s := Finset.range n1 ×ˢ Finset.range n2
  have hinj : Set.InjOn φ s := by
    rintro ⟨a, c⟩ hx ⟨a', c'⟩ hy hφ
    simp only [s, Finset.coe_product, Set.mem_prod, Finset.coe_range, Set.mem_Iio] at hx hy
    have hmod : n2 * a + n1 * c ≡ n2 * a' + n1 * c' [MOD N] := hφ
    -- modulo n₁: n₂a ≡ n₂a'
    have h1 : n2 * a + n1 * c ≡ n2 * a' + n1 * c' [MOD n1] :=
      Nat.ModEq.of_mul_right n2 (by rw [← hN]; exact hmod)
    have h1' : n2 * a ≡ n2 * a' [MOD n1] := by
      have e1 : n1 * c ≡ 0 [MOD n1] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right _ _)
      have e2 : n1 * c' ≡ 0 [MOD n1] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right _ _)
      have := (h1.trans (Nat.ModEq.add_left _ e2)).symm.trans (Nat.ModEq.add_left _ e1)
      simpa using this.symm
    have ha := Nat.ModEq.cancel_left_div_gcd (by omega) h1'
    rw [Nat.gcd_comm, hcop.symm.gcd_eq_one, Nat.div_one] at ha
    -- modulo n₂: n₁c ≡ n₁c'
    have h2 : n2 * a + n1 * c ≡ n2 * a' + n1 * c' [MOD n2] :=
      Nat.ModEq.of_mul_left n1 (by rw [← hN]; exact hmod)
    have h2' : n1 * c ≡ n1 * c' [MOD n2] := by
      have e1 : n2 * a ≡ 0 [MOD n2] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right _ _)
      have e2 : n2 * a' ≡ 0 [MOD n2] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right _ _)
      have := (h2.trans (Nat.ModEq.add_right _ e2)).symm.trans (Nat.ModEq.add_right _ e1)
      simpa using this.symm
    have hc := Nat.ModEq.cancel_left_div_gcd (by omega) h2'
    rw [Nat.gcd_comm, hcop.gcd_eq_one, Nat.div_one] at hc
    exact Prod.ext (ha.eq_of_lt_of_lt hx.1 hy.1) (hc.eq_of_lt_of_lt hx.2 hy.2)
  have himg : s.image φ = Finset.range N := by
    refine Finset.eq_of_subset_of_card_le (fun j hj => ?_) ?_
    · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_range.mpr (Nat.mod_lt _ hNpos)
    · rw [Finset.card_image_of_injOn hinj, Finset.card_range, Finset.card_product,
        Finset.card_range, Finset.card_range]
  rw [← himg, Finset.sum_image hinj, Finset.sum_product]

/-- The residue phase: `ζ_N^{k ((n₂a + n₁c) mod N)} = ζ_{n₁}^{(k mod n₁) a} ζ_{n₂}^{(k mod n₂) c}`. -/
theorem zeta_pfa_phase (n1 n2 a c k : ℕ) (h1 : n1 ≠ 0) (h2 : n2 ≠ 0) :
    zeta (n1 * n2) ^ (k * ((n2 * a + n1 * c) % (n1 * n2))) =
      zeta n1 ^ (k % n1 * a) * zeta n2 ^ (k % n2 * c) := by
  have hN : n1 * n2 ≠ 0 := mul_ne_zero h1 h2
  have key1 : zeta n1 ^ (k * a) = zeta n1 ^ (k % n1 * a) := by
    rw [zeta_pow_mod n1 _ h1, zeta_pow_mod n1 (k % n1 * a) h1, Nat.mul_mod,
      Nat.mul_mod (k % n1), Nat.mod_mod, Nat.mod_mod, Nat.mul_mod_mod]
  have key2 : zeta n2 ^ (k * c) = zeta n2 ^ (k % n2 * c) := by
    rw [zeta_pow_mod n2 _ h2, zeta_pow_mod n2 (k % n2 * c) h2, Nat.mul_mod,
      Nat.mul_mod (k % n2), Nat.mod_mod, Nat.mod_mod, Nat.mul_mod_mod]
  rw [zeta_pow_mod _ _ hN, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← zeta_pow_mod _ _ hN,
    show k * (n2 * a + n1 * c) = n2 * (k * a) + n1 * (k * c) by ring, pow_add,
    zeta_mul_pow_mul n1 n2 _ h1 h2,
    show zeta (n1 * n2) ^ (n1 * (k * c)) = zeta n2 ^ (k * c) by
      rw [mul_comm n1 n2]; exact zeta_mul_pow_mul n2 n1 _ h2 h1,
    key1, key2]

section PFA

variable (n1 : ℕ) {n2 : ℕ} (C2 : Circuit n2)

/-- Output `p` of inner copy `a`, on the residue-chart inputs `(n₂a + n₁c) mod N`. -/
def pfaY (a p : ℕ) : ℕ :=
  if h : p < n2 then
    reloc n2 (fun c => (n2 * a + n1 * c) % (n1 * n2)) (n1 * n2) (n1 * n2 + 1 + a * C2.size)
      (C2.outputs ⟨p, h⟩)
  else 0

def pfaOutBase : ℕ := n1 * n2 + 1 + n1 * C2.size

noncomputable def pfaGates {n1 : ℕ} (C1 : Circuit n1) : List LGate :=
  copyRow C2 (fun a c => (n2 * a + n1 * c) % (n1 * n2)) (n1 * n2) (n1 * n2 + 1) n1 ++
  copyRow C1 (fun p a => pfaY n1 C2 a p) (n1 * n2) (pfaOutBase n1 C2) n2

/-- Output register of frequency `k`: outer copy `k mod n₂`, output `k mod n₁`. -/
noncomputable def pfaOut {n1 : ℕ} (C1 : Circuit n1) (k : ℕ) : ℕ :=
  if h : k % n1 < n1 then
    reloc n1 (fun a => pfaY n1 C2 a (k % n2)) (n1 * n2) (pfaOutBase n1 C2 + (k % n2) * C1.size)
      (C1.outputs ⟨k % n1, h⟩)
  else 0

end PFA

/-- **Theorem 128 (the residue split).** For coprime `n₁, n₂`, exact circuits for
lengths `n₁` and `n₂` give an exact circuit for `n₁n₂` with `n₁|C₂| + n₂|C₁|`
gates — Good's chart in, the residue chart out, no twiddles.

**fdrs.md**: Theorem 128 (the residue split). -/
theorem exists_pfa_circuit {n1 n2 : ℕ} (hn1 : 1 ≤ n1) (hn2 : 1 ≤ n2) (hcop : Nat.Coprime n1 n2)
    (C1 : Circuit n1) (hC1 : C1.Computes (fourierMatrix n1))
    (C2 : Circuit n2) (hC2 : C2.Computes (fourierMatrix n2)) :
    ∃ C : Circuit (n1 * n2), C.Computes (fourierMatrix (n1 * n2)) ∧
      C.size = n1 * C2.size + n2 * C1.size := by
  set N := n1 * n2 with hN
  have hN0 : N ≠ 0 := by positivity
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
  have hinIn : ∀ a c : ℕ, (n2 * a + n1 * c) % (n1 * n2) < N + 1 := fun a c => by
    have := Nat.mod_lt (n2 * a + n1 * c) (show 0 < n1 * n2 by positivity); omega
  have hY : ∀ a < n1, ∀ p < n2, pfaY n1 C2 a p < pfaOutBase n1 C2 := fun a ha p hp => by
    simp only [pfaY, dif_pos hp, pfaOutBase]
    have := reloc_lt (k := C2.size) (z0 := n1 * n2) (base := n1 * n2 + 1 + a * C2.size)
      (fun c _ => (hinIn a c).trans_le (Nat.le_add_right _ _)) (by omega) (C2.outputs ⟨p, hp⟩)
    have : (a + 1) * C2.size ≤ n1 * C2.size := Nat.mul_le_mul_right _ ha
    rw [add_mul, one_mul] at this
    omega
  have hlen : (pfaGates C2 C1).length = n1 * C2.size + n2 * C1.size := by
    simp [pfaGates, copyRow_length]
  have hout : ∀ k : Fin N, pfaOut C2 C1 k < N + 1 + (pfaGates C2 C1).length := by
    intro k
    have hq : (k : ℕ) % n1 < n1 := Nat.mod_lt _ (by omega)
    have hp : (k : ℕ) % n2 < n2 := Nat.mod_lt _ (by omega)
    simp only [pfaOut, dif_pos hq]
    have := reloc_lt (k := C1.size) (z0 := n1 * n2)
      (base := pfaOutBase n1 C2 + (k % n2) * C1.size)
      (fun a ha => (hY a ha _ hp).trans_le (Nat.le_add_right _ _))
      ((show n1 * n2 < pfaOutBase n1 C2 by simp only [pfaOutBase]; omega).trans_le
        (Nat.le_add_right _ _))
      (C1.outputs ⟨(k : ℕ) % n1, hq⟩)
    have h2 : ((k : ℕ) % n2 + 1) * C1.size ≤ n2 * C1.size := Nat.mul_le_mul_right _ hp
    rw [add_mul, one_mul] at h2
    rw [hlen]
    simp only [pfaOutBase] at this ⊢
    omega
  refine ⟨Circuit.ofGates N (pfaGates C2 C1) (fun k => pfaOut C2 C1 k) hout,
    fun x => ?_, by rw [Circuit.ofGates_size, hlen]⟩
  funext k
  rw [Circuit.ofGates_eval, mulVec_fourier_eq]
  set S0 := initState N x
  -- inner copies
  obtain ⟨hpos1, hval1⟩ := copyRow_spec C2 (fun a c => (n2 * a + n1 * c) % (n1 * n2)) N (N + 1)
    S0 rfl (by omega) (by simp [S0, initState]) n1 (fun a _ c _ => hinIn a c)
  set S1 := exec (copyRow C2 (fun a c => (n2 * a + n1 * c) % (n1 * n2)) N (N + 1) n1) S0
  have hY1 : ∀ a < n1, ∀ p < n2, S1.val (pfaY n1 C2 a p) =
      ∑ c ∈ Finset.range n2, zeta n2 ^ (p * c) * extend x ((n2 * a + n1 * c) % (n1 * n2)) := by
    intro a ha p hp
    simp only [pfaY, dif_pos hp]
    rw [hval1 a ha ⟨p, hp⟩, Circuit.eval_fourier hC2]
    exact sum_fin_eq_range n2 (fun c => zeta n2 ^ (p * c) * extend x ((n2 * a + n1 * c) % (n1 * n2)))
  -- outer copies
  obtain ⟨_, hval2⟩ := copyRow_spec C1 (fun p a => pfaY n1 C2 a p) N (pfaOutBase n1 C2) S1
    (by rw [hpos1]; rfl) (by simp only [pfaOutBase]; omega)
    (by rw [exec_frame _ _ (by simp [S0, initState])]; simp [S0, initState])
    n2 (fun p hp a ha => hY a ha p hp)
  have hexec : exec (pfaGates C2 C1) S0 =
      exec (copyRow C1 (fun p a => pfaY n1 C2 a p) N (pfaOutBase n1 C2) n2) S1 := by
    simp only [pfaGates, exec_append]; rfl
  have hq : (k : ℕ) % n1 < n1 := Nat.mod_lt _ (by omega)
  have hp : (k : ℕ) % n2 < n2 := Nat.mod_lt _ (by omega)
  rw [hexec]
  simp only [pfaOut, dif_pos hq]
  rw [hval2 _ hp ⟨(k : ℕ) % n1, hq⟩, Circuit.eval_fourier hC1,
    sum_fin_eq_range n1 (fun a => zeta n1 ^ ((k : ℕ) % n1 * a) * S1.val (pfaY n1 C2 a ((k : ℕ) % n2)))]
  have hre : ∑ j ∈ Finset.range N, zeta N ^ ((k : ℕ) * j) * extend x j =
      ∑ a ∈ Finset.range n1, ∑ c ∈ Finset.range n2,
        zeta N ^ ((k : ℕ) * ((n2 * a + n1 * c) % (n1 * n2))) *
          extend x ((n2 * a + n1 * c) % (n1 * n2)) :=
    sum_range_crt (fun j => zeta N ^ ((k : ℕ) * j) * extend x j) hn1 hn2 hcop
  rw [hre]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha' : a < n1 := by simpa using ha
  rw [hY1 a ha' _ hp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [zeta_pfa_phase n1 n2 a c _ (by omega) (by omega)]
  ring

/-! ## Corollary 37: the search grammar, proven -/

theorem zeta_two' : zeta 2 = -1 := by
  rw [zeta, show (2 : ℂ) * (Real.pi : ℂ) * Complex.I / ((2 : ℕ) : ℂ) = Real.pi * Complex.I by
    push_cast; ring]
  exact Complex.exp_pi_mul_I

/-- The 2-point transform in two gates: `x₀ + x₁`, `x₀ − x₁`. -/
theorem exists_two_circuit :
    ∃ C : Circuit 2, C.Computes (fourierMatrix 2) ∧ C.size = 2 := by
  refine ⟨Circuit.ofGates 2 [.add 0 1, .sub 0 1] (fun k => 3 + k) (fun k => by
    have := k.isLt; simp; omega), fun x => ?_, by simp [Circuit.ofGates]⟩
  funext k
  rw [Circuit.ofGates_eval, mulVec_fourier_eq]
  fin_cases k
  · simp [exec, initState, LGate.eval, extend, Finset.sum_range_succ]
  · simp [exec, initState, LGate.eval, extend, Finset.sum_range_succ,
      zeta_two']
    ring

/-- A plan of the radix-schedule search: the 2-point butterfly `D2`, the
conjugate-pair kernel `P_{2h+1}`, and the positional and residue splits
(`outer` of length `n₁`, `inner` of length `n₂`). -/
inductive Plan where
  | two : Plan
  | pair (h : ℕ) : Plan
  | ct (outer inner : Plan) : Plan
  | pfa (outer inner : Plan) : Plan

/-- The transform length a plan computes. -/
def Plan.len : Plan → ℕ
  | .two => 2
  | .pair h => 2 * h + 1
  | .ct p q => p.len * q.len
  | .pfa p q => p.len * q.len

/-- The gate count of a plan — the search tool's recurrence. -/
def Plan.cost : Plan → ℕ
  | .two => 2
  | .pair h => (2 * h + 1) ^ 2 - 1
  | .ct p q => p.len * q.cost + q.len * p.cost + twiddleCount p.len q.len
  | .pfa p q => p.len * q.cost + q.len * p.cost

/-- Residue splits need coprime factors. -/
def Plan.valid : Plan → Bool
  | .two => true
  | .pair _ => true
  | .ct p q => p.valid && q.valid
  | .pfa p q => p.valid && q.valid && Nat.gcd p.len q.len == 1

theorem Plan.one_le_len : ∀ P : Plan, 1 ≤ P.len
  | .two => by simp [Plan.len]
  | .pair h => by simp [Plan.len]
  | .ct p q => Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (Nat.one_le_iff_ne_zero.mp p.one_le_len)
      (Nat.one_le_iff_ne_zero.mp q.one_le_len))
  | .pfa p q => Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (Nat.one_le_iff_ne_zero.mp p.one_le_len)
      (Nat.one_le_iff_ne_zero.mp q.one_le_len))

/-- **Corollary 37 (the search grammar is sound).** Every valid plan yields an exact
Fourier circuit of its length with exactly its cost.

**fdrs.md**: Corollary 37 (plans are circuits). -/
theorem Plan.exists_circuit : ∀ P : Plan, P.valid = true →
    ∃ C : Circuit P.len, C.Computes (fourierMatrix P.len) ∧ C.size = P.cost
  | .two, _ => exists_two_circuit
  | .pair h, _ => exists_pair_circuit h
  | .ct p q, hv => by
    simp only [Plan.valid, Bool.and_eq_true] at hv
    obtain ⟨C1, hC1, hs1⟩ := p.exists_circuit hv.1
    obtain ⟨C2, hC2, hs2⟩ := q.exists_circuit hv.2
    obtain ⟨C, hC, hs⟩ := exists_ct_circuit p.one_le_len q.one_le_len C1 hC1 C2 hC2
    exact ⟨C, hC, by rw [hs, hs1, hs2]; rfl⟩
  | .pfa p q, hv => by
    simp only [Plan.valid, Bool.and_eq_true, beq_iff_eq] at hv
    obtain ⟨C1, hC1, hs1⟩ := p.exists_circuit hv.1.1
    obtain ⟨C2, hC2, hs2⟩ := q.exists_circuit hv.1.2
    obtain ⟨C, hC, hs⟩ := exists_pfa_circuit p.one_le_len q.one_le_len hv.2 C1 hC1 C2 hC2
    exact ⟨C, hC, by rw [hs, hs1, hs2]; rfl⟩

/-- Certificates: a search result becomes a theorem once its plan's length and cost
evaluate. -/
theorem Plan.certify (P : Plan) (N c : ℕ) (hv : P.valid = true) (hN : P.len = N)
    (hc : P.cost = c) : ∃ C : Circuit N, C.Computes (fourierMatrix N) ∧ C.size = c := by
  subst hN hc
  exact P.exists_circuit hv

end FdrsFormal.NumberTheory.Characters.FourierCircuit
