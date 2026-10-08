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

# Rader and Bluestein (Phase 3 addendum, §1.12)

The radix-schedule search's extended grammar reduces a DFT to a cyclic convolution
computed through two forward DFTs. This file proves both reductions in family 130's
gate model, so the extended counts become theorems.

- **Proposition 161** (`sum_zeta_pow_mul`, `cyclic_conv`): orthogonality of the
  powers of `ζ_n`, and the convolution identity — a forward DFT, a pointwise scale
  by `F(b)/n`, and a second forward DFT read at `(n − r) mod n` give
  `Σ_q a_q b_{(r − q) mod n}`.
- **Theorem 129** (`exists_rader_circuit`): for a prime `p = n + 1`, a circuit for
  length `n` gives one for length `p` with `2|C| + 2n + 1` gates.
- **Theorem 130** (`exists_bluestein_circuit`): for `N ≥ 1` and `M ≥ 2N − 1`, a
  circuit for length `M` gives one for length `N` with
  `2|C| + M + 2·#{j < N : 2N ∤ j²}` gates.
- **Corollary 38** (`XPlan`, `XPlan.exists_circuit`): every plan of the extended
  search grammar is an exact circuit of exactly its cost.

**Honest scope.** Classical (Rader 1968; Bluestein 1970). The corpus contributes the
gate-exact statements and the link to the search's certificates. Upper bounds only.
-/

import FdrsFormal.NumberTheory.Characters.CircuitCompose
import Mathlib.FieldTheory.Finite.Basic

namespace FdrsFormal.NumberTheory.Characters.FourierCircuit

open FdrsFormal.NumberTheory.Characters.MixedRadixFFT

/-! ## Proposition 161: orthogonality and cyclic convolution -/

theorem zeta_isPrimitiveRoot (n : ℕ) (hn : n ≠ 0) : IsPrimitiveRoot (zeta n) n :=
  Complex.isPrimitiveRoot_exp n hn

/-- `Σ_{k < n} ζ_n^{ks} = n` if `n ∣ s`, else `0`.

**fdrs.md**: Proposition 161 (orthogonality; cyclic convolution). -/
theorem sum_zeta_pow_mul (n s : ℕ) (hn : n ≠ 0) :
    ∑ k ∈ Finset.range n, zeta n ^ (k * s) = if n ∣ s then (n : ℂ) else 0 := by
  have hp := zeta_isPrimitiveRoot n hn
  have hrw : ∀ k, zeta n ^ (k * s) = (zeta n ^ s) ^ k := fun k => by
    rw [← pow_mul, mul_comm]
  simp_rw [hrw]
  split_ifs with h
  · rw [(hp.pow_eq_one_iff_dvd s).mpr h]; simp
  · have hne : zeta n ^ s ≠ 1 := fun h' => h ((hp.pow_eq_one_iff_dvd s).mp h')
    rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hp.pow_eq_one, one_pow, sub_self,
      zero_div]

/-- The index selected by the convolution: `n ∣ (n − r) mod n + t + q` iff
`t = (r + n − q) mod n`, for `r, q, t < n`. -/
theorem conv_select (n r q t : ℕ) (hn : n ≠ 0) (hr : r < n) (hq : q < n) (ht : t < n) :
    n ∣ (n - r) % n + t + q ↔ t = (r + n - q) % n := by
  haveI : NeZero n := ⟨hn⟩
  rw [← ZMod.natCast_eq_zero_iff]
  have hT : (r + n - q) % n < n := Nat.mod_lt _ (Nat.pos_of_ne_zero hn)
  have hcast : t = (r + n - q) % n ↔ (t : ZMod n) = ((r + n - q) % n : ℕ) := by
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt hT]
  rw [hcast]
  push_cast [ZMod.natCast_mod, Nat.cast_sub hr.le, Nat.cast_sub (show q ≤ r + n by omega)]
  rw [ZMod.natCast_self]
  constructor <;> intro h <;> linear_combination h

/-- **Proposition 161 (cyclic convolution).** With `A = F_n a`, `B = F_n b` and
`D = F_n(B · A / n)`, the entry `D_{(n − r) mod n}` is the cyclic convolution
`Σ_q a_q b_{(r − q) mod n}`.

**fdrs.md**: Proposition 161 (orthogonality; cyclic convolution). -/
theorem cyclic_conv (n : ℕ) (hn : n ≠ 0) (a b : ℕ → ℂ) (r : ℕ) (hr : r < n) :
    ∑ k ∈ Finset.range n, zeta n ^ ((n - r) % n * k) *
        ((∑ t ∈ Finset.range n, zeta n ^ (k * t) * b t) / n *
          ∑ q ∈ Finset.range n, zeta n ^ (k * q) * a q) =
      ∑ q ∈ Finset.range n, a q * b ((r + n - q) % n) := by
  set m := (n - r) % n
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  -- expand to a triple sum
  have hexp : ∀ k, zeta n ^ (m * k) *
      ((∑ t ∈ Finset.range n, zeta n ^ (k * t) * b t) / n *
        ∑ q ∈ Finset.range n, zeta n ^ (k * q) * a q) =
      ∑ q ∈ Finset.range n, ∑ t ∈ Finset.range n,
        (n : ℂ)⁻¹ * (a q * b t) * zeta n ^ (k * (m + t + q)) := by
    intro k
    simp only [Finset.sum_div, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun t _ => ?_
    rw [show k * (m + t + q) = m * k + k * t + k * q by ring, pow_add, pow_add]
    ring
  rw [Finset.sum_congr rfl fun k _ => hexp k, Finset.sum_comm]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq' : q < n := by simpa using hq
  rw [Finset.sum_comm]
  have hinner : ∀ t ∈ Finset.range n, ∑ k ∈ Finset.range n,
      (n : ℂ)⁻¹ * (a q * b t) * zeta n ^ (k * (m + t + q)) =
        if t = (r + n - q) % n then a q * b t else 0 := by
    intro t ht
    have ht' : t < n := by simpa using ht
    rw [← Finset.mul_sum, sum_zeta_pow_mul n _ hn]
    by_cases hsel : t = (r + n - q) % n
    · rw [if_pos ((conv_select n r q t hn hr hq' ht').mpr hsel), if_pos hsel]
      field_simp
    · rw [if_neg (fun h => hsel ((conv_select n r q t hn hr hq' ht').mp h)), if_neg hsel,
        mul_zero]
  rw [Finset.sum_congr rfl hinner, Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr
    (Nat.mod_lt _ (Nat.pos_of_ne_zero hn)))]

/-! ## Theorem 129: Rader's prime transform -/

section Gen

variable {n : ℕ} (g : (ZMod (n + 1))ˣ)

/-- `g^t`, read as a residue in `[0, n]`. -/
def gpow (t : ℕ) : ℕ := ((g ^ t : (ZMod (n + 1))ˣ) : ZMod (n + 1)).val

theorem gpow_lt (t : ℕ) : gpow g t < n + 1 := ZMod.val_lt _

theorem gpow_add (a b : ℕ) : gpow g (a + b) = gpow g a * gpow g b % (n + 1) := by
  simp only [gpow, pow_add, Units.val_mul, ZMod.val_mul]

theorem gpow_mod (hg : orderOf g = n) (t : ℕ) : gpow g (t % n) = gpow g t := by
  have h := pow_mod_orderOf g t
  rw [hg] at h
  simp only [gpow, h]

theorem gpow_inj (hg : orderOf g = n) {a b : ℕ} (ha : a < n) (hb : b < n)
    (h : gpow g a = gpow g b) : a = b := by
  have h1 : g ^ a = g ^ b := Units.ext (ZMod.val_injective _ h)
  rwa [pow_inj_mod, hg, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h1

theorem gpow_ne_zero [Fact (n + 1).Prime] (t : ℕ) : gpow g t ≠ 0 := by
  simp only [gpow, ne_eq, ZMod.val_eq_zero]; exact Units.ne_zero _

/-- A generator's powers `g^0, …, g^{n−1}` run through the nonzero residues. -/
theorem image_gpow [Fact (n + 1).Prime] (hg : orderOf g = n) :
    (Finset.range n).image (gpow g) = Finset.Ico 1 (n + 1) := by
  apply Finset.eq_of_subset_of_card_le
  · intro j hj
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hj
    simp only [Finset.mem_Ico]
    exact ⟨Nat.one_le_iff_ne_zero.mpr (gpow_ne_zero g t), gpow_lt g t⟩
  · rw [Finset.card_image_of_injOn fun a ha b hb h =>
      gpow_inj g hg (by simpa using ha) (by simpa using hb) h]
    simp

end Gen

/-- The index arithmetic of the convolution: `−(−s + n − q) ≡ s + q (mod n)`. -/
theorem rader_idx (n s q : ℕ) (hs : s < n) (hq : q < n) :
    (n - ((n - s) % n + n - q) % n) % n = (s + q) % n := by
  have h1 : ((n - s) % n + n - q) % n ≤ n := (Nat.mod_lt _ (by omega)).le
  have h2 : q ≤ (n - s) % n + n := by omega
  rw [← ZMod.natCast_eq_natCast_iff', Nat.cast_sub h1, ZMod.natCast_mod, Nat.cast_sub h2,
    Nat.cast_add, ZMod.natCast_mod, Nat.cast_sub hs.le, Nat.cast_add, ZMod.natCast_self]
  ring

theorem rader_out_idx (n s : ℕ) (hs : s < n) : (n - (n - s) % n) % n = s := by
  rcases Nat.eq_zero_or_pos s with rfl | hs0
  · simp
  · rw [Nat.mod_eq_of_lt (by omega : n - s < n), show n - (n - s) = s by omega,
      Nat.mod_eq_of_lt hs]

section RaderCircuit

variable {n : ℕ} (g : (ZMod (n + 1))ˣ) (C : Circuit n)

/-- The Rader filter `b_t = ζ_p^{g^{−t}}`. -/
noncomputable def raderFilter (t : ℕ) : ℂ := zeta (n + 1) ^ gpow g ((n - t) % n)

/-- Its transform `B_k = Σ_t ζ_n^{kt} b_t` — a constant of the circuit. -/
noncomputable def raderB (k : ℕ) : ℂ :=
  ∑ t ∈ Finset.range n, zeta n ^ (k * t) * raderFilter g t

/-- Output `s` of the first copy, `A_s = Σ_q ζ_n^{sq} x_{g^q}`. -/
def raderA (s : ℕ) : ℕ :=
  if h : s < n then reloc n (gpow g) (n + 1) (n + 2) (C.outputs ⟨s, h⟩) else 0

def raderScBase : ℕ := n + 3 + C.size

def raderDBase : ℕ := n + 3 + C.size + n

/-- Output `s` of the second copy. -/
def raderD (s : ℕ) : ℕ :=
  if h : s < n then
    reloc n (fun k => raderScBase C + k) (n + 1) (raderDBase C) (C.outputs ⟨s, h⟩)
  else 0

/-- Rader's circuit: a copy of `C` on the inputs in generator order, `x₀ + A₀`, the
`n` scales `B_k/n · A_k`, a second copy of `C`, and `n` additions of `x₀`. -/
noncomputable def raderGates : List LGate :=
  C.program.toGates (gpow g) (n + 1) (n + 2) ++ [LGate.add 0 (raderA g C 0)] ++
  (List.range n).map (fun k => LGate.scale (raderB g k / n) (raderA g C k)) ++
  C.program.toGates (fun k => raderScBase C + k) (n + 1) (raderDBase C) ++
  (List.range n).map (fun s => LGate.add 0 (raderD C s))

/-- Output register of frequency `k`: `x₀ + A₀` for `k = 0`, else the final addition
at the discrete logarithm of `k`. -/
def raderOut (k : ℕ) : ℕ :=
  if k = 0 then n + 2 + C.size
  else raderDBase C + C.size + ((List.range n).map (gpow g)).idxOf k

end RaderCircuit

/-- **Theorem 129 (Rader).** For a prime `p = n + 1`, an exact circuit for length `n`
gives one for length `p` with `2|C| + 2n + 1` gates.

**fdrs.md**: Theorem 129 (Rader's prime transform). -/
theorem exists_rader_circuit {n : ℕ} (hp : (n + 1).Prime) (C : Circuit n)
    (hC : C.Computes (fourierMatrix n)) :
    ∃ C' : Circuit (n + 1), C'.Computes (fourierMatrix (n + 1)) ∧
      C'.size = 2 * C.size + 2 * n + 1 := by
  haveI := Fact.mk hp
  have hn : n ≠ 0 := by have := hp.two_le; omega
  obtain ⟨g, hgen⟩ := IsCyclic.exists_generator (α := (ZMod (n + 1))ˣ)
  have hg : orderOf g = n := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgen, Nat.card_eq_fintype_card,
      ZMod.card_units]
    simp
  have hlen : (raderGates g C).length = 2 * C.size + 2 * n + 1 := by
    simp [raderGates, Program.toGates_length]; ring
  have hA : ∀ s < n, raderA g C s < n + 2 + C.size := fun s hs => by
    simp only [raderA, dif_pos hs]
    exact reloc_lt (k := C.size) (fun i _ => by have := gpow_lt g i; omega) (by omega) _
  have hD : ∀ s < n, raderD C s < raderDBase C + C.size := fun s hs => by
    simp only [raderD, dif_pos hs]
    exact reloc_lt (k := C.size) (fun i hi => by simp only [raderScBase, raderDBase]; omega)
      (by simp only [raderDBase]; omega) _
  have hidx : ∀ k : ℕ, k ≠ 0 → k < n + 1 →
      ((List.range n).map (gpow g)).idxOf k < n ∧
        gpow g (((List.range n).map (gpow g)).idxOf k) = k := by
    intro k hk0 hk
    have hmem : k ∈ (List.range n).map (gpow g) := by
      have : k ∈ (Finset.range n).image (gpow g) := by
        rw [image_gpow g hg]; simp only [Finset.mem_Ico]; omega
      simpa using this
    have hlt := List.idxOf_lt_length_of_mem hmem
    have hget := List.getElem_idxOf hlt
    simp only [List.length_map, List.length_range] at hlt
    refine ⟨hlt, ?_⟩
    rw [List.getElem_map, List.getElem_range] at hget
    exact hget
  have hout : ∀ k : Fin (n + 1), raderOut g C k < n + 1 + 1 + (raderGates g C).length := by
    intro k
    rw [hlen]
    unfold raderOut
    split_ifs with h0
    · omega
    · have := (hidx k h0 k.isLt).1; simp only [raderDBase]; omega
  refine ⟨Circuit.ofGates (n + 1) (raderGates g C) (fun k => raderOut g C k) hout,
    fun x => ?_, by rw [Circuit.ofGates_size, hlen]⟩
  funext k
  rw [Circuit.ofGates_eval, mulVec_fourier_eq]
  -- the target, split at `j = 0` and re-indexed by `j = g^q`
  have hsplit : ∀ k' : ℕ, ∑ j ∈ Finset.range (n + 1), zeta (n + 1) ^ (k' * j) * extend x j =
      extend x 0 + ∑ q ∈ Finset.range n,
        zeta (n + 1) ^ (k' * gpow g q) * extend x (gpow g q) := by
    intro k'
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), ← image_gpow g hg,
      Finset.sum_image fun a ha b hb h =>
        gpow_inj g hg (by simpa using ha) (by simpa using hb) h]
    simp
  set S0 := initState (n + 1) x
  -- first copy
  obtain ⟨hpos1, hval1⟩ := Program.toGates_spec (gpow g) (n + 1) (n + 2) S0 rfl
    (fun i _ => by have := gpow_lt g i; omega) (by omega) (by simp [S0, initState]) C.program
  set S1 := exec (C.program.toGates (gpow g) (n + 1) (n + 2)) S0
  have hA1 : ∀ s < n, S1.val (raderA g C s) =
      ∑ q ∈ Finset.range n, zeta n ^ (s * q) * extend x (gpow g q) := by
    intro s hs
    simp only [raderA, dif_pos hs]
    rw [hval1, show C.program.eval (fun j => S0.val (gpow g j)) (C.outputs ⟨s, hs⟩) =
      C.eval (fun j => S0.val (gpow g j)) ⟨s, hs⟩ from rfl, Circuit.eval_fourier hC]
    exact sum_fin_eq_range n (fun q => zeta n ^ (s * q) * extend x (gpow g q))
  have hS1pos : S1.pos = n + 2 + C.size := hpos1
  have hS1 : ∀ j < S0.pos, S1.val j = S0.val j := fun j hj => exec_frame _ S0 hj
  -- `x₀ + A₀`
  set S2 := exec [LGate.add 0 (raderA g C 0)] S1
  have hS2pos : S2.pos = n + 3 + C.size := by simp [S2, exec_pos, hS1pos]; omega
  have hX0 : S2.val (n + 2 + C.size) = S1.val 0 + S1.val (raderA g C 0) := by
    rw [← hS1pos]; simp [S2, exec, LGate.eval]
  have hS2 : ∀ j < S1.pos, S2.val j = S1.val j := fun j hj => exec_frame _ S1 hj
  -- the scales
  set SC := (List.range n).map (fun k => LGate.scale (raderB g k / n) (raderA g C k))
  set S3 := exec SC S2
  have hS3pos : S3.pos = raderDBase C := by
    simp [S3, exec_pos, hS2pos, SC, raderDBase]
  have hS3 : ∀ j < S2.pos, S3.val j = S2.val j := fun j hj => exec_frame _ S2 hj
  have hind := exec_indep SC S2 (fun gt hgt => by
    simp only [SC, List.mem_map, List.mem_range] at hgt
    obtain ⟨k, hk, rfl⟩ := hgt
    simp only [LGate.ReadsBelow, hS2pos]; have := hA k hk; omega)
  have hSc : ∀ k < n, S3.val (raderScBase C + k) =
      raderB g k / n * S1.val (raderA g C k) := by
    intro k hk
    have := hind k (by simpa [SC] using hk)
    rw [hS2pos] at this
    rw [show raderScBase C + k = n + 3 + C.size + k from rfl, this]
    simp only [SC, List.getElem_map, List.getElem_range, LGate.eval]
    rw [hS2 _ (by rw [hS1pos]; exact hA k hk)]
  -- second copy
  obtain ⟨hpos4, hval4⟩ := Program.toGates_spec (fun k => raderScBase C + k) (n + 1)
    (raderDBase C) S3 hS3pos (fun i hi => by simp only [raderScBase, raderDBase]; omega)
    (by simp only [raderDBase]; omega)
    (by rw [hS3 _ (by rw [hS2pos]; omega), hS2 _ (by rw [hS1pos]; omega),
          hS1 _ (by simp [S0, initState])]; simp [S0, initState])
    C.program
  set S4 := exec (C.program.toGates (fun k => raderScBase C + k) (n + 1) (raderDBase C)) S3
  have hS4pos : S4.pos = raderDBase C + C.size := hpos4
  have hS4 : ∀ j < S3.pos, S4.val j = S3.val j := fun j hj => exec_frame _ S3 hj
  have hD4 : ∀ s < n, S4.val (raderD C s) = ∑ j ∈ Finset.range n,
      zeta n ^ (s * j) * (raderB g j / n * S1.val (raderA g C j)) := by
    intro s hs
    simp only [raderD, dif_pos hs]
    rw [hval4, show C.program.eval (fun j => S3.val (raderScBase C + j)) (C.outputs ⟨s, hs⟩) =
      C.eval (fun j => S3.val (raderScBase C + j)) ⟨s, hs⟩ from rfl, Circuit.eval_fourier hC,
      sum_fin_eq_range n (fun j => zeta n ^ (s * j) * S3.val (raderScBase C + j))]
    exact Finset.sum_congr rfl fun j hj => by rw [hSc j (by simpa using hj)]
  -- the final additions
  set FL := (List.range n).map (fun s => LGate.add 0 (raderD C s))
  have hind5 := exec_indep FL S4 (fun gt hgt => by
    simp only [FL, List.mem_map, List.mem_range] at hgt
    obtain ⟨s, hs, rfl⟩ := hgt
    simp only [LGate.ReadsBelow, hS4pos]
    exact ⟨by simp only [raderDBase]; omega, hD s hs⟩)
  have hexec : exec (raderGates g C) S0 = exec FL S4 := by
    simp only [raderGates, exec_append]; rfl
  have hx0 : S4.val 0 = extend x 0 := by
    rw [hS4 _ (by rw [hS3pos]; simp only [raderDBase]; omega), hS3 _ (by rw [hS2pos]; omega),
      hS2 _ (by rw [hS1pos]; omega), hS1 _ (by simp [S0, initState])]
    rfl
  have hS1x0 : S1.val 0 = extend x 0 := by rw [hS1 _ (by simp [S0, initState])]; rfl
  rw [hexec, hsplit]
  by_cases hk0 : (k : ℕ) = 0
  · simp only [raderOut, if_pos hk0]
    rw [exec_frame _ _ (by rw [hS4pos]; simp only [raderDBase]; omega),
      hS4 _ (by rw [hS3pos]; simp only [raderDBase]; omega), hS3 _ (by rw [hS2pos]; omega),
      hX0, hS1x0, hA1 0 (by omega), hk0]
    simp
  · obtain ⟨hs, hgs⟩ := hidx k hk0 k.isLt
    set s := ((List.range n).map (gpow g)).idxOf (k : ℕ)
    simp only [raderOut, if_neg hk0]
    have h5 := hind5 s (by simpa [FL] using hs)
    rw [hS4pos] at h5
    rw [h5]
    simp only [FL, List.getElem_map, List.getElem_range, LGate.eval]
    rw [hx0, hD4 s hs]
    congr 1
    have hconv := cyclic_conv n hn (fun q => extend x (gpow g q)) (raderFilter g)
      ((n - s) % n) (Nat.mod_lt _ (Nat.pos_of_ne_zero hn))
    rw [rader_out_idx n s hs] at hconv
    have hlhs : ∑ j ∈ Finset.range n,
        zeta n ^ (s * j) * (raderB g j / n * S1.val (raderA g C j)) =
        ∑ j ∈ Finset.range n, zeta n ^ (s * j) *
          ((∑ t ∈ Finset.range n, zeta n ^ (j * t) * raderFilter g t) / n *
            ∑ q ∈ Finset.range n, zeta n ^ (j * q) * extend x (gpow g q)) :=
      Finset.sum_congr rfl fun j hj => by rw [hA1 j (by simpa using hj)]; rfl
    rw [hlhs, hconv, ← hgs]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq' : q < n := by simpa using hq
    rw [mul_comm (extend x _)]
    congr 1
    rw [raderFilter, rader_idx n s q hs hq', gpow_mod g hg, gpow_add,
      ← zeta_pow_mod _ _ (Nat.succ_ne_zero n)]

/-! ## Theorem 130: Bluestein's chirp transform -/

/-- Lengths `j < N` whose chirp `ζ_{2N}^{j²}` is not `1`. -/
def chirpList (N : ℕ) : List ℕ :=
  (List.range N).filter fun j => decide (j * j % (2 * N) ≠ 0)

/-- Number of nontrivial chirp factors. -/
def chirpCount (N : ℕ) : ℕ := (chirpList N).length

theorem mem_chirpList {N j : ℕ} : j ∈ chirpList N ↔ j < N ∧ j * j % (2 * N) ≠ 0 := by
  simp [chirpList]

/-- The Bluestein filter at length `M`: `ζ_{2N}^{−t²}` at `t` and at `M − t`, `t < N`. -/
noncomputable def bluFilter (N M t : ℕ) : ℂ :=
  if t < N then (zeta (2 * N) ^ (t * t))⁻¹
  else if M - N < t then (zeta (2 * N) ^ ((M - t) * (M - t)))⁻¹ else 0

/-- Its transform, a constant of the circuit. -/
noncomputable def bluB (N M k : ℕ) : ℂ :=
  ∑ t ∈ Finset.range M, zeta M ^ (k * t) * bluFilter N M t

/-- The chirp identity: `ζ_{2N}^{k²} ζ_{2N}^{q²} h_{(k − q) mod M} = ζ_N^{kq}`. -/
theorem blu_phase (N M k q : ℕ) (hN : N ≠ 0) (hM : 2 * N - 1 ≤ M) (hk : k < N) (hq : q < N) :
    zeta (2 * N) ^ (k * k) * (zeta (2 * N) ^ (q * q) * bluFilter N M ((k + M - q) % M)) =
      zeta N ^ (k * q) := by
  have hcoarse : ∀ a, zeta (2 * N) ^ (2 * a) = zeta N ^ a := fun a => by
    rw [mul_comm 2 N]; exact zeta_mul_pow_mul N 2 a hN (by norm_num)
  -- `k² + q² = 2kq + d²`, `d = |k − q|`, and `h` at the cyclic index is `ζ_{2N}^{−d²}`
  have main : ∀ d, k * k + q * q = 2 * (k * q) + d * d →
      bluFilter N M ((k + M - q) % M) = (zeta (2 * N) ^ (d * d))⁻¹ →
      zeta (2 * N) ^ (k * k) * (zeta (2 * N) ^ (q * q) * bluFilter N M ((k + M - q) % M)) =
        zeta N ^ (k * q) := by
    intro d he hf
    have hz : zeta (2 * N) ^ (d * d) ≠ 0 := pow_ne_zero _ (zeta_ne_zero _)
    rw [hf, ← mul_assoc, ← pow_add, he, pow_add, hcoarse, mul_assoc, mul_inv_cancel₀ hz,
      mul_one]
  by_cases hqk : q ≤ k
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hqk
    refine main d (by ring) ?_
    rw [show q + d + M - q = d + M by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega),
      bluFilter, if_pos (by omega)]
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt (Nat.lt_of_not_le hqk)
    refine main (d + 1) (by ring) ?_
    rw [Nat.mod_eq_of_lt (by omega), bluFilter, if_neg (by omega), if_pos (by omega),
      show M - (k + M - (k + d + 1)) = d + 1 by omega]

section BluesteinCircuit

variable (N : ℕ) {M : ℕ} (C : Circuit M)

/-- Register of the chirped, zero-padded input `u_j = ζ_{2N}^{j²} x_j`. -/
def bluU (j : ℕ) : ℕ :=
  if j < N then (if j * j % (2 * N) = 0 then j else N + 1 + (chirpList N).idxOf j) else N

def bluABase : ℕ := N + 1 + chirpCount N

def bluA (k : ℕ) : ℕ :=
  if h : k < M then reloc M (bluU N) N (bluABase N) (C.outputs ⟨k, h⟩) else 0

def bluSBase : ℕ := bluABase N + C.size

def bluDBase : ℕ := bluSBase N C + M

def bluD (k : ℕ) : ℕ :=
  if h : k < M then reloc M (fun i => bluSBase N C + i) N (bluDBase N C) (C.outputs ⟨k, h⟩)
  else 0

def bluPBase : ℕ := bluDBase N C + C.size

/-- Bluestein's circuit: chirp the inputs, a copy of `C` at length `M` (padding read
from the zero register), `M` scales `B_k/M`, a second copy, chirp the outputs. -/
noncomputable def bluGates : List LGate :=
  (chirpList N).map (fun j => LGate.scale (zeta (2 * N) ^ (j * j)) j) ++
  C.program.toGates (bluU N) N (bluABase N) ++
  (List.range M).map (fun k => LGate.scale (bluB N M k / M) (bluA N C k)) ++
  C.program.toGates (fun i => bluSBase N C + i) N (bluDBase N C) ++
  (chirpList N).map (fun k => LGate.scale (zeta (2 * N) ^ (k * k)) (bluD N C ((M - k) % M)))

noncomputable def bluOut (k : ℕ) : ℕ :=
  if k * k % (2 * N) = 0 then bluD N C ((M - k) % M) else bluPBase N C + (chirpList N).idxOf k

end BluesteinCircuit

/-- **Theorem 130 (Bluestein).** For any `N ≥ 1` and `M ≥ 2N − 1`, an exact circuit for
length `M` gives one for length `N` with `2|C| + M + 2·#{j < N : 2N ∤ j²}` gates.

**fdrs.md**: Theorem 130 (Bluestein's chirp transform). -/
theorem exists_bluestein_circuit {N M : ℕ} (hN : 1 ≤ N) (hM : 2 * N - 1 ≤ M) (C : Circuit M)
    (hC : C.Computes (fourierMatrix M)) :
    ∃ C' : Circuit N, C'.Computes (fourierMatrix N) ∧
      C'.size = 2 * C.size + M + 2 * chirpCount N := by
  have hN0 : N ≠ 0 := by omega
  have hM0 : M ≠ 0 := by omega
  have hlen : (bluGates N C).length = 2 * C.size + M + 2 * chirpCount N := by
    simp [bluGates, Program.toGates_length, chirpCount]; ring
  have hcl : ∀ j ∈ chirpList N, j < N := fun j hj => (mem_chirpList.mp hj).1
  have hcn : chirpCount N ≤ N := by
    have := List.length_filter_le (fun j => decide (j * j % (2 * N) ≠ 0)) (List.range N)
    simpa [chirpCount, chirpList] using this
  have hU : ∀ j < M, bluU N j < bluABase N := fun j _ => by
    unfold bluU bluABase
    split_ifs with h1 h2
    · omega
    · have := List.idxOf_lt_length_of_mem (mem_chirpList.mpr ⟨h1, h2⟩)
      simp only [chirpCount]; omega
    · omega
  have hA : ∀ k < M, bluA N C k < bluSBase N C := fun k hk => by
    simp only [bluA, dif_pos hk, bluSBase]
    exact reloc_lt (k := C.size) hU (by simp only [bluABase]; omega) _
  have hD : ∀ k < M, bluD N C k < bluPBase N C := fun k hk => by
    simp only [bluD, dif_pos hk, bluPBase]
    exact reloc_lt (k := C.size) (fun i hi => by simp only [bluDBase]; omega)
      (by simp only [bluDBase, bluSBase, bluABase]; omega) _
  have hout : ∀ k : Fin N, bluOut N C k < N + 1 + (bluGates N C).length := by
    intro k
    rw [hlen]
    unfold bluOut
    split_ifs with h0
    · have := hD _ (Nat.mod_lt ((M : ℕ) - k) (by omega))
      simp only [bluPBase, bluDBase, bluSBase, bluABase] at this; omega
    · have := List.idxOf_lt_length_of_mem (mem_chirpList.mpr ⟨k.isLt, h0⟩)
      simp only [bluPBase, bluDBase, bluSBase, bluABase, chirpCount] at this ⊢; omega
  refine ⟨Circuit.ofGates N (bluGates N C) (fun k => bluOut N C k) hout, fun x => ?_,
    by rw [Circuit.ofGates_size, hlen]⟩
  funext k
  rw [Circuit.ofGates_eval, mulVec_fourier_eq]
  have htriv : ∀ j, j * j % (2 * N) = 0 → zeta (2 * N) ^ (j * j) = 1 := fun j h => by
    rw [zeta_pow_mod _ _ (by omega), h, pow_zero]
  set S0 := initState N x
  have hS0pos : S0.pos = N + 1 := rfl
  -- chirp the inputs
  set PL := (chirpList N).map (fun j => LGate.scale (zeta (2 * N) ^ (j * j)) j)
  set S1 := exec PL S0
  have hS1pos : S1.pos = bluABase N := by simp [S1, exec_pos, PL, bluABase, chirpCount, hS0pos]
  have hS1 : ∀ j < S0.pos, S1.val j = S0.val j := fun j hj => exec_frame _ S0 hj
  have hind1 := exec_indep PL S0 (fun gt hgt => by
    simp only [PL, List.mem_map] at hgt
    obtain ⟨j, hj, rfl⟩ := hgt
    simp only [LGate.ReadsBelow, hS0pos]; have := hcl j hj; omega)
  have hU1 : ∀ j < M, S1.val (bluU N j) = zeta (2 * N) ^ (j * j) * extend x j := by
    intro j _
    unfold bluU
    split_ifs with h1 h2
    · rw [hS1 _ (by omega), htriv j h2, one_mul]; rfl
    · have hmem := mem_chirpList.mpr ⟨h1, h2⟩
      have hi := List.idxOf_lt_length_of_mem hmem
      have := hind1 ((chirpList N).idxOf j) (by simpa [PL] using hi)
      rw [hS0pos] at this
      rw [this]
      simp only [PL, List.getElem_map, List.getElem_idxOf, LGate.eval]
      rfl
    · rw [hS1 _ (by omega)]
      simp [S0, initState, extend, h1]
  -- first copy
  obtain ⟨hpos2, hval2⟩ := Program.toGates_spec (bluU N) N (bluABase N) S1 hS1pos hU
    (by simp only [bluABase]; omega) (by rw [hS1 _ (by omega)]; simp [S0, initState]) C.program
  set S2 := exec (C.program.toGates (bluU N) N (bluABase N)) S1
  have hS2pos : S2.pos = bluSBase N C := hpos2
  have hS2 : ∀ j < S1.pos, S2.val j = S1.val j := fun j hj => exec_frame _ S1 hj
  have hA2 : ∀ k < M, S2.val (bluA N C k) = ∑ q ∈ Finset.range M,
      zeta M ^ (k * q) * (zeta (2 * N) ^ (q * q) * extend x q) := by
    intro k hk
    simp only [bluA, dif_pos hk]
    rw [hval2, show C.program.eval (fun j => S1.val (bluU N j)) (C.outputs ⟨k, hk⟩) =
      C.eval (fun j => S1.val (bluU N j)) ⟨k, hk⟩ from rfl, Circuit.eval_fourier hC,
      sum_fin_eq_range M (fun q => zeta M ^ (k * q) * S1.val (bluU N q))]
    exact Finset.sum_congr rfl fun q hq => by rw [hU1 q (by simpa using hq)]
  -- the scales
  set SC := (List.range M).map (fun k => LGate.scale (bluB N M k / M) (bluA N C k))
  set S3 := exec SC S2
  have hS3pos : S3.pos = bluDBase N C := by simp [S3, exec_pos, hS2pos, SC, bluDBase]
  have hS3 : ∀ j < S2.pos, S3.val j = S2.val j := fun j hj => exec_frame _ S2 hj
  have hind3 := exec_indep SC S2 (fun gt hgt => by
    simp only [SC, List.mem_map, List.mem_range] at hgt
    obtain ⟨k, hk, rfl⟩ := hgt
    simp only [LGate.ReadsBelow, hS2pos]; exact hA k hk)
  have hSc : ∀ k < M, S3.val (bluSBase N C + k) = bluB N M k / M * S2.val (bluA N C k) := by
    intro k hk
    have := hind3 k (by simpa [SC] using hk)
    rw [hS2pos] at this
    rw [this]
    simp only [SC, List.getElem_map, List.getElem_range, LGate.eval]
  -- second copy
  obtain ⟨hpos4, hval4⟩ := Program.toGates_spec (fun i => bluSBase N C + i) N (bluDBase N C) S3
    hS3pos (fun i hi => by simp only [bluDBase]; omega)
    (by simp only [bluDBase, bluSBase, bluABase]; omega)
    (by rw [hS3 _ (by rw [hS2pos]; simp only [bluSBase, bluABase]; omega),
          hS2 _ (by rw [hS1pos]; simp only [bluABase]; omega), hS1 _ (by omega)]
        simp [S0, initState])
    C.program
  set S4 := exec (C.program.toGates (fun i => bluSBase N C + i) N (bluDBase N C)) S3
  have hS4pos : S4.pos = bluPBase N C := hpos4
  have hD4 : ∀ k < M, S4.val (bluD N C k) = ∑ j ∈ Finset.range M,
      zeta M ^ (k * j) * (bluB N M j / M * S2.val (bluA N C j)) := by
    intro k hk
    simp only [bluD, dif_pos hk]
    rw [hval4, show C.program.eval (fun j => S3.val (bluSBase N C + j)) (C.outputs ⟨k, hk⟩) =
      C.eval (fun j => S3.val (bluSBase N C + j)) ⟨k, hk⟩ from rfl, Circuit.eval_fourier hC,
      sum_fin_eq_range M (fun j => zeta M ^ (k * j) * S3.val (bluSBase N C + j))]
    exact Finset.sum_congr rfl fun j hj => by rw [hSc j (by simpa using hj)]
  -- the convolution, read at `(M − k) mod M`
  have hconvk : ∀ k < N, S4.val (bluD N C ((M - k) % M)) =
      ∑ q ∈ Finset.range N, zeta (2 * N) ^ (q * q) * extend x q *
        bluFilter N M ((k + M - q) % M) := by
    intro k hk
    rw [hD4 _ (Nat.mod_lt _ (by omega))]
    have hconv := cyclic_conv M hM0 (fun q => zeta (2 * N) ^ (q * q) * extend x q)
      (bluFilter N M) k (by omega)
    have hlhs : ∑ j ∈ Finset.range M,
        zeta M ^ ((M - k) % M * j) * (bluB N M j / M * S2.val (bluA N C j)) =
        ∑ j ∈ Finset.range M, zeta M ^ ((M - k) % M * j) *
          ((∑ t ∈ Finset.range M, zeta M ^ (j * t) * bluFilter N M t) / M *
            ∑ q ∈ Finset.range M, zeta M ^ (j * q) * (zeta (2 * N) ^ (q * q) * extend x q)) :=
      Finset.sum_congr rfl fun j hj => by rw [hA2 j (by simpa using hj)]; rfl
    rw [hlhs, hconv]
    symm
    apply Finset.sum_subset (Finset.range_mono (show N ≤ M by omega))
    intro q hq hqN
    have : ¬ q < N := by simpa using hqN
    simp [extend, this]
  have htarget : ∀ k < N, zeta (2 * N) ^ (k * k) * S4.val (bluD N C ((M - k) % M)) =
      ∑ j ∈ Finset.range N, zeta N ^ (k * j) * extend x j := by
    intro k hk
    rw [hconvk k hk, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq' : q < N := by simpa using hq
    rw [← blu_phase N M k q hN0 hM hk hq']
    ring
  -- chirp the outputs
  set QL := (chirpList N).map
    (fun k => LGate.scale (zeta (2 * N) ^ (k * k)) (bluD N C ((M - k) % M)))
  have hind5 := exec_indep QL S4 (fun gt hgt => by
    simp only [QL, List.mem_map] at hgt
    obtain ⟨j, hj, rfl⟩ := hgt
    simp only [LGate.ReadsBelow, hS4pos]
    exact hD _ (Nat.mod_lt _ (by omega)))
  have hexec : exec (bluGates N C) S0 = exec QL S4 := by
    simp only [bluGates, exec_append]; rfl
  rw [hexec, ← htarget k k.isLt]
  unfold bluOut
  split_ifs with h0
  · rw [exec_frame _ _ (by rw [hS4pos]; exact hD _ (Nat.mod_lt _ (by omega))), htriv _ h0,
      one_mul]
  · have hi := List.idxOf_lt_length_of_mem (mem_chirpList.mpr ⟨k.isLt, h0⟩)
    have := hind5 ((chirpList N).idxOf (k : ℕ)) (by simpa [QL] using hi)
    rw [hS4pos] at this
    rw [this]
    simp only [QL, List.getElem_map, List.getElem_idxOf, LGate.eval]

/-! ## Corollary 38: the extended search grammar, proven -/

/-- A kernel-checkable primality test: `2 ≤ p` and no `d ∈ [2, p)` divides `p`. -/
def primeCheck (p : ℕ) : Bool :=
  2 ≤ p && (List.range p).all fun d => d < 2 || p % d != 0

theorem prime_of_primeCheck {p : ℕ} (h : primeCheck p = true) : p.Prime := by
  simp only [primeCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  refine Nat.prime_def_lt.mpr ⟨h.1, fun m hm hdvd => ?_⟩
  rcases h.2 m hm with h2 | h2
  · interval_cases m
    · rw [zero_dvd_iff] at hdvd; omega
    · rfl
  · exact absurd (Nat.mod_eq_zero_of_dvd hdvd) h2

/-- A plan of the extended search: the grammar of Corollary 37, plus Rader on a plan
of length `p − 1` and Bluestein at length `n` on a plan of length `M ≥ 2n − 1`. -/
inductive XPlan where
  | two : XPlan
  | pair (h : ℕ) : XPlan
  | ct (outer inner : XPlan) : XPlan
  | pfa (outer inner : XPlan) : XPlan
  | rader (inner : XPlan) : XPlan
  | bluestein (n : ℕ) (inner : XPlan) : XPlan

def XPlan.len : XPlan → ℕ
  | .two => 2
  | .pair h => 2 * h + 1
  | .ct p q => p.len * q.len
  | .pfa p q => p.len * q.len
  | .rader q => q.len + 1
  | .bluestein n _ => n

/-- The gate count — the extended planner's recurrence. -/
def XPlan.cost : XPlan → ℕ
  | .two => 2
  | .pair h => (2 * h + 1) ^ 2 - 1
  | .ct p q => p.len * q.cost + q.len * p.cost + twiddleCount p.len q.len
  | .pfa p q => p.len * q.cost + q.len * p.cost
  | .rader q => 2 * q.cost + 2 * q.len + 1
  | .bluestein n q => 2 * q.cost + q.len + 2 * chirpCount n

def XPlan.valid : XPlan → Bool
  | .two => true
  | .pair _ => true
  | .ct p q => p.valid && q.valid
  | .pfa p q => p.valid && q.valid && Nat.gcd p.len q.len == 1
  | .rader q => q.valid && primeCheck (q.len + 1)
  | .bluestein n q => q.valid && 1 ≤ n && 2 * n - 1 ≤ q.len

theorem XPlan.one_le_len : ∀ P : XPlan, P.valid = true → 1 ≤ P.len
  | .two, _ => by simp [XPlan.len]
  | .pair h, _ => by simp [XPlan.len]
  | .ct p q, hv => by
    simp only [XPlan.valid, Bool.and_eq_true] at hv
    exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero
      (Nat.one_le_iff_ne_zero.mp (p.one_le_len hv.1)) (Nat.one_le_iff_ne_zero.mp (q.one_le_len hv.2)))
  | .pfa p q, hv => by
    simp only [XPlan.valid, Bool.and_eq_true] at hv
    exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero
      (Nat.one_le_iff_ne_zero.mp (p.one_le_len hv.1.1))
      (Nat.one_le_iff_ne_zero.mp (q.one_le_len hv.1.2)))
  | .rader q, _ => by simp [XPlan.len]
  | .bluestein n q, hv => by
    simp only [XPlan.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    exact hv.1.2

/-- **Corollary 38 (the extended grammar is sound).** Every valid extended plan yields an
exact Fourier circuit of its length with exactly its cost.

**fdrs.md**: Corollary 38 (extended plans are circuits). -/
theorem XPlan.exists_circuit : ∀ P : XPlan, P.valid = true →
    ∃ C : Circuit P.len, C.Computes (fourierMatrix P.len) ∧ C.size = P.cost
  | .two, _ => exists_two_circuit
  | .pair h, _ => exists_pair_circuit h
  | .ct p q, hv => by
    simp only [XPlan.valid, Bool.and_eq_true] at hv
    obtain ⟨C1, hC1, hs1⟩ := p.exists_circuit hv.1
    obtain ⟨C2, hC2, hs2⟩ := q.exists_circuit hv.2
    obtain ⟨C, hC, hs⟩ := exists_ct_circuit (p.one_le_len hv.1) (q.one_le_len hv.2) C1 hC1 C2 hC2
    exact ⟨C, hC, by rw [hs, hs1, hs2]; rfl⟩
  | .pfa p q, hv => by
    simp only [XPlan.valid, Bool.and_eq_true, beq_iff_eq] at hv
    obtain ⟨C1, hC1, hs1⟩ := p.exists_circuit hv.1.1
    obtain ⟨C2, hC2, hs2⟩ := q.exists_circuit hv.1.2
    obtain ⟨C, hC, hs⟩ := exists_pfa_circuit (p.one_le_len hv.1.1) (q.one_le_len hv.1.2) hv.2
      C1 hC1 C2 hC2
    exact ⟨C, hC, by rw [hs, hs1, hs2]; rfl⟩
  | .rader q, hv => by
    simp only [XPlan.valid, Bool.and_eq_true] at hv
    obtain ⟨C1, hC1, hs1⟩ := q.exists_circuit hv.1
    obtain ⟨C, hC, hs⟩ := exists_rader_circuit (prime_of_primeCheck hv.2) C1 hC1
    exact ⟨C, hC, by rw [hs, hs1]; rfl⟩
  | .bluestein n q, hv => by
    simp only [XPlan.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨C1, hC1, hs1⟩ := q.exists_circuit hv.1.1
    obtain ⟨C, hC, hs⟩ := exists_bluestein_circuit hv.1.2 hv.2 C1 hC1
    exact ⟨C, hC, by rw [hs, hs1]; rfl⟩

/-- Certificates for the extended search. -/
theorem XPlan.certify (P : XPlan) (N c : ℕ) (hv : P.valid = true) (hN : P.len = N)
    (hc : P.cost = c) : ∃ C : Circuit N, C.Computes (fourierMatrix N) ∧ C.size = c := by
  subst hN hc
  exact P.exists_circuit hv

/-- Rader at `p = 17` over the 16-point binary transform (`81` gates, Theorem 125). -/
example : ∃ C : Circuit 17, C.Computes (fourierMatrix 17) ∧ C.size = 195 :=
  XPlan.certify (.rader (.ct .two (.ct .two (.ct .two .two)))) 17 _
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end FdrsFormal.NumberTheory.Characters.FourierCircuit
