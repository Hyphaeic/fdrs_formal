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

# The hop: a carry move between branches (Phase 1 addendum, §3.17)

§3.16 found that the carry quotient of a wrapped ring is a two-branch radix complex — a
closing ring and an open line — whose branches do not couple through products. Here they
couple through a **carry**. Build the complex as a carry network:

- **cells**: the `N` ring cells (weights `B_k`) and `D + 1` line cells (weights `B_k` of
  the open periodic schedule, read on the tied branch);
- **moves**: ring carries (Definition 230), line carries (`b_k` units at line cell `k`
  become one unit at line cell `k + 1`), and the **hop**: `ε_tied` units leave ring cell
  `0` and one unit appears at line cell `0`.

The value of a state is `Σ x_k B_k + ε_tied Σ y_k B_k (mod M)`. Then:

- **The complex keeps the arithmetic** (Theorem 158): states modulo moves are exactly
  `ℤ/M`, whatever the length of the line. Adding a line and a hop adds room, not
  residues.
- **Every state sorts onto its branches** (Corollary 55): it is move-equivalent to
  `ε_free W` units at ring cell `0` and `W` units at line cell `0` (`W` its value) — the
  free share on the ring, the tied share on the line.
- **The ring closes, the line leaks** (Theorem 159): free content is invariant under `L`
  laps of holonomy (`B^L ≡ 1` on the free branch); line content multiplied by `B^r` is
  equivalent to nothing, and anything reaching depth `r N` falls off the end.
- **The hop is the path back** (Theorem 160): for some `L' ≥ 1`, a unit at ring cell `k`
  returns — `ε_free B^{L'}` units at cell `k` plus `B_k` units parked at line cell `0` —
  while without the hop it does not return (`B^{L'}` units at cell `k` alone are not
  equivalent) whenever `B_k` carries tied residue.

Witnesses on `(2, 3, 2)` with `c = −3`: the unit at ring cell `0` comes back as
`6 · 12^4` units at cell `0` plus one unit at line cell `0`; `12^4` units at cell `0`
alone are not equivalent (`12^4 ≡ 6 ≢ 1 (mod 15)`).

Reuses `CarryQuotient.lean` (cells, carry moves, the value map, Theorem 147),
`BranchComplex.lean` (idempotents, `tied_dies_dvd`), `RingLineSplit.lean` (the split,
`free_helix_closes`, `weight_laps`) and `ProductSpread.lean` (the `(2, 3, 2)` ring).

- **Definition 236** (`lineCell`, `lineCarry`, `lineValue`, `hopVec`, `hopLattice`,
  `cxValue`, `cxEv`): the two-branch carry complex.
- **Theorem 158** (`ker_cxEv`, `cx_equiv_iff`, `cxQuotient`): the complex keeps the
  arithmetic.
- **Corollary 55** (`sort_branches`): every state sorts onto its branches.
- **Theorem 159** (`ring_closes`, `line_dies`, `line_leaks`): the ring closes, the line
  leaks.
- **Theorem 160** (`hop_path_back`): the hop is the path back.
- **Proposition 183** (`ring232_hop_back`, `ring232_no_back`): the `(2, 3, 2)`, `c = −3`
  witnesses.

**Honest scope.** Elementary (a change of presentation of `ℤ/M`). The corpus contributes
the two-branch carry complex with an explicit hop move, the sorting of residues onto
branches by carries, and the separation of paths back with and without the hop. The line
is attached at a single cell; several lines, hops at other cells, and context-chosen
radices for the line are not covered.
-/

import FdrsFormal.Modes.SyntheticPlace.BranchComplex

namespace FdrsFormal.Modes.SyntheticPlace.CarryHop

open FdrsFormal.Core.Primitives
open FdrsFormal.Modes.SyntheticPlace.RingUnrolling FdrsFormal.Modes.SyntheticPlace.CarryQuotient
open FdrsFormal.Modes.SyntheticPlace.ProductSpread FdrsFormal.Modes.SyntheticPlace.RingLineSplit
open FdrsFormal.Modes.SyntheticPlace.BranchComplex

section Complex

variable {n : ℕ} (ρ : Fin (n + 1) → ℕ) (hρ : ∀ i, 2 ≤ ρ i) (c : ℤ) (S : FreeTiedSplit ρ hρ c)
variable (D : ℕ)

/-! ## Definition 236: the two-branch carry complex -/

/-- The unit state at line cell `k`. -/
def lineCell (k : Fin (D + 1)) : Fin (D + 1) → ℤ := Pi.single k 1

/-- The line carry at cell `k < D`: `b_k` units at cell `k` become one unit at `k + 1`.

**fdrs.md**: Definition 236 (the two-branch carry complex). -/
def lineCarry (k : Fin D) : Fin (D + 1) → ℤ :=
  lineCell D k.succ - (ringSchedule ρ hρ k : ℤ) • lineCell D k.castSucc

/-- The value of a line state on the open periodic schedule: `Σ y_k B_k`. -/
def lineValue : (Fin (D + 1) → ℤ) →+ ℤ :=
  AddMonoidHom.mk' (fun y => ∑ k, y k * weight ρ hρ k)
    (by intro x y; simp [add_mul, Finset.sum_add_distrib])

/-- The hop: `ε_tied` units leave ring cell `0`, one unit appears at line cell `0`.

**fdrs.md**: Definition 236 (the two-branch carry complex). -/
noncomputable def hopVec : (Fin (n + 1) → ℤ) × (Fin (D + 1) → ℤ) :=
  (-(tiedIdem ρ hρ c S) • cell 0, lineCell D 0)

/-- The move lattice of the complex: ring carries, line carries, the hop.

**fdrs.md**: Definition 236 (the two-branch carry complex). -/
noncomputable def hopLattice : AddSubgroup ((Fin (n + 1) → ℤ) × (Fin (D + 1) → ℤ)) :=
  AddSubgroup.closure
    (Set.range (fun i => ((carryVec ρ c i, 0) : (Fin (n + 1) → ℤ) × (Fin (D + 1) → ℤ))) ∪
      Set.range (fun k : Fin D => ((0, lineCarry ρ hρ D k) : (Fin (n + 1) → ℤ) × (Fin (D + 1) → ℤ))) ∪
      {hopVec ρ hρ c S D})

/-- The value of a complex state: `Σ x_k B_k + ε_tied Σ y_k B_k`.

**fdrs.md**: Definition 236 (the two-branch carry complex). -/
noncomputable def cxValue : (Fin (n + 1) → ℤ) × (Fin (D + 1) → ℤ) →+ ℤ :=
  AddMonoidHom.mk' (fun z => value ρ hρ z.1 + tiedIdem ρ hρ c S * lineValue ρ hρ D z.2)
    (by intro x y; simp only [Prod.fst_add, Prod.snd_add, map_add]; ring)

/-- The value modulo `M`. -/
noncomputable def cxEv : (Fin (n + 1) → ℤ) × (Fin (D + 1) → ℤ) →+ ZMod (modulus ρ hρ c) :=
  (Int.castAddHom _).comp (cxValue ρ hρ c S D)

theorem cxValue_apply (z : (Fin (n + 1) → ℤ) × (Fin (D + 1) → ℤ)) :
    cxValue ρ hρ c S D z = value ρ hρ z.1 + tiedIdem ρ hρ c S * lineValue ρ hρ D z.2 := rfl

theorem cxEv_apply (z : (Fin (n + 1) → ℤ) × (Fin (D + 1) → ℤ)) :
    cxEv ρ hρ c S D z = ((cxValue ρ hρ c S D z : ℤ) : ZMod (modulus ρ hρ c)) := rfl

theorem cxValue_mk (x : Fin (n + 1) → ℤ) (y : Fin (D + 1) → ℤ) :
    cxValue ρ hρ c S D (x, y) = value ρ hρ x + tiedIdem ρ hρ c S * lineValue ρ hρ D y := rfl

theorem mod_dvd_of {x : ℤ} (h1 : (S.free : ℤ) ∣ x) (h2 : (S.tied : ℤ) ∣ x) :
    (modulus ρ hρ c : ℤ) ∣ x := by
  rw [← S.mul_eq, Nat.cast_mul]
  exact (split_coprime ρ hρ c S).mul_dvd h1 h2

theorem lineValue_cell (k : Fin (D + 1)) : lineValue ρ hρ D (lineCell D k) = weight ρ hρ k := by
  simp [lineValue, lineCell, Pi.single_apply]

theorem cxEv_eq_zero_iff (z : (Fin (n + 1) → ℤ) × (Fin (D + 1) → ℤ)) :
    cxEv ρ hρ c S D z = 0 ↔ (modulus ρ hρ c : ℤ) ∣ cxValue ρ hρ c S D z := by
  rw [cxEv_apply, CharP.intCast_eq_zero_iff (ZMod (modulus ρ hρ c)) (modulus ρ hρ c)]

/-! ## Theorem 158: the complex keeps the arithmetic -/

theorem ring_mem {z : Fin (n + 1) → ℤ} (hz : z ∈ carryLattice ρ c) :
    ((z, 0) : (Fin (n + 1) → ℤ) × (Fin (D + 1) → ℤ)) ∈ hopLattice ρ hρ c S D := by
  have : carryLattice ρ c ≤ (hopLattice ρ hρ c S D).comap (AddMonoidHom.inl _ _) := by
    rw [carryLattice, AddSubgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, AddMonoidHom.inl_apply]
    exact AddSubgroup.subset_closure (Or.inl (Or.inl ⟨i, rfl⟩))
  have h := this hz
  rwa [AddSubgroup.mem_comap, AddMonoidHom.inl_apply] at h

/-- The line part of the move lattice. -/
noncomputable def lineMoves : AddSubgroup (Fin (D + 1) → ℤ) :=
  (hopLattice ρ hρ c S D).comap (AddMonoidHom.inr _ _)

theorem mem_lineMoves {y : Fin (D + 1) → ℤ} :
    y ∈ lineMoves ρ hρ c S D ↔
      ((0, y) : (Fin (n + 1) → ℤ) × (Fin (D + 1) → ℤ)) ∈ hopLattice ρ hρ c S D := by
  rw [lineMoves, AddSubgroup.mem_comap, AddMonoidHom.inr_apply]

theorem lineCarry_mem (k : Fin D) : lineCarry ρ hρ D k ∈ lineMoves ρ hρ c S D :=
  (mem_lineMoves ρ hρ c S D).mpr (AddSubgroup.subset_closure (Or.inl (Or.inr ⟨k, rfl⟩)))

theorem weight_succ' (k : ℕ) :
    weight ρ hρ (k + 1) = weight ρ hρ k * (ringSchedule ρ hρ k : ℤ) := by
  simp [weight, placeValue.succ]

/-- Carrying down the line: line cell `k` is equivalent to `B_k` units at line cell `0`. -/
theorem lineCell_sub_mem : ∀ (k : ℕ) (hk : k < D + 1),
    lineCell D ⟨k, hk⟩ - weight ρ hρ k • lineCell D 0 ∈ lineMoves ρ hρ c S D
  | 0, _ => by
    rw [weight_zero, one_smul, show (⟨0, _⟩ : Fin (D + 1)) = 0 from rfl, sub_self]
    exact (lineMoves ρ hρ c S D).zero_mem
  | k + 1, hk => by
    have hk' : k < D := by omega
    have hv : lineCarry ρ hρ D ⟨k, hk'⟩ =
        lineCell D ⟨k + 1, hk⟩ - (ringSchedule ρ hρ k : ℤ) • lineCell D ⟨k, by omega⟩ := by
      rw [lineCarry, Fin.succ_mk, Fin.castSucc_mk]
    have h1 := lineCarry_mem ρ hρ c S D ⟨k, hk'⟩
    have h2 := (lineMoves ρ hρ c S D).zsmul_mem (lineCell_sub_mem k (by omega))
      (ringSchedule ρ hρ k : ℤ)
    have h3 := (lineMoves ρ hρ c S D).add_mem h1 h2
    rw [hv, weight_succ' ρ hρ k] at *
    convert h3 using 1
    rw [smul_sub, mul_comm, mul_smul]
    abel

theorem line_sub_value_mem (y : Fin (D + 1) → ℤ) :
    y - lineValue ρ hρ D y • lineCell D 0 ∈ lineMoves ρ hρ c S D := by
  have hy : y - lineValue ρ hρ D y • lineCell D 0 =
      ∑ k, y k • (lineCell D k - weight ρ hρ k • lineCell D 0) := by
    simp only [smul_sub, Finset.sum_sub_distrib, smul_smul]
    congr 1
    · funext j; simp [lineCell, Finset.sum_apply, Pi.single_apply]
    · rw [← Finset.sum_smul]; rfl
  rw [hy]
  refine AddSubgroup.sum_mem _ fun k _ => AddSubgroup.zsmul_mem _ ?_ _
  exact lineCell_sub_mem ρ hρ c S D k k.isLt

theorem hop_mem : hopVec ρ hρ c S D ∈ hopLattice ρ hρ c S D :=
  AddSubgroup.subset_closure (Or.inr rfl)

/-- Every complex state is equivalent to its value placed at ring cell `0`. -/
theorem cx_sub_value_mem (z : (Fin (n + 1) → ℤ) × (Fin (D + 1) → ℤ)) :
    z - ((cxValue ρ hρ c S D z • cell 0, 0) : (Fin (n + 1) → ℤ) × (Fin (D + 1) → ℤ)) ∈
      hopLattice ρ hρ c S D := by
  obtain ⟨x, y⟩ := z
  have h1 := ring_mem ρ hρ c S D (sub_value_mem ρ hρ c x)
  have h2 := (mem_lineMoves ρ hρ c S D).mp (line_sub_value_mem ρ hρ c S D y)
  have h3 := (hopLattice ρ hρ c S D).zsmul_mem (hop_mem ρ hρ c S D) (lineValue ρ hρ D y)
  have h := (hopLattice ρ hρ c S D).add_mem ((hopLattice ρ hρ c S D).add_mem h1 h2) h3
  convert h using 1
  rw [hopVec, cxValue_apply]
  ext i
  · simp only [Prod.fst_sub, Prod.fst_add, Prod.smul_fst, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    ring
  · simp only [Prod.snd_sub, Prod.snd_add, Prod.smul_snd, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    ring

/-- **Theorem 158 (the complex keeps the arithmetic: kernel).** A complex state is a
combination of ring carries, line carries and hops iff its value vanishes modulo `M`.

**fdrs.md**: Theorem 158 (the complex keeps the arithmetic). -/
theorem ker_cxEv : (cxEv ρ hρ c S D).ker = hopLattice ρ hρ c S D := by
  apply le_antisymm
  · intro z hz
    rw [AddMonoidHom.mem_ker, cxEv_eq_zero_iff] at hz
    have hring : cxValue ρ hρ c S D z • cell 0 ∈ carryLattice ρ c := by
      rw [← ker_ev ρ hρ c, AddMonoidHom.mem_ker, ev_eq_zero_iff, map_zsmul, value_cell,
        Fin.val_zero, weight_zero, smul_eq_mul, mul_one, ← Int.natAbs_dvd, ← modulus]
      exact hz
    have := (hopLattice ρ hρ c S D).add_mem (cx_sub_value_mem ρ hρ c S D z)
      (ring_mem ρ hρ c S D hring)
    rwa [sub_add_cancel] at this
  · rw [hopLattice, AddSubgroup.closure_le]
    rintro z ((⟨i, rfl⟩ | ⟨k, rfl⟩) | rfl)
    · rw [SetLike.mem_coe, AddMonoidHom.mem_ker, cxEv_eq_zero_iff, cxValue_apply, map_zero,
        mul_zero, add_zero]
      have := (ker_ev ρ hρ c).ge (AddSubgroup.subset_closure ⟨i, rfl⟩ : carryVec ρ c i ∈ carryLattice ρ c)
      rw [AddMonoidHom.mem_ker, ev_eq_zero_iff, ← Int.natAbs_dvd, ← modulus] at this
      exact this
    · rw [SetLike.mem_coe, AddMonoidHom.mem_ker, cxEv_eq_zero_iff]
      convert dvd_zero (modulus ρ hρ c : ℤ) using 1
      simp only [cxValue_mk, lineCarry, map_sub, map_zsmul, lineValue_cell, map_zero,
        Fin.val_succ, Fin.val_castSucc, weight_succ', smul_eq_mul]
      ring
    · rw [SetLike.mem_coe, AddMonoidHom.mem_ker, cxEv_eq_zero_iff]
      convert dvd_zero (modulus ρ hρ c : ℤ) using 1
      simp only [hopVec, cxValue_mk, map_zsmul, value_cell, lineValue_cell, Fin.val_zero,
        weight_zero, smul_eq_mul]
      ring

/-- **Theorem 158 (equivalence in the complex).** Two complex states differ by moves iff
their values agree modulo `M`.

**fdrs.md**: Theorem 158 (the complex keeps the arithmetic). -/
theorem cx_equiv_iff (z z' : (Fin (n + 1) → ℤ) × (Fin (D + 1) → ℤ)) :
    z - z' ∈ hopLattice ρ hρ c S D ↔ cxEv ρ hρ c S D z = cxEv ρ hρ c S D z' := by
  rw [← ker_cxEv, AddMonoidHom.mem_ker, map_sub, sub_eq_zero]

theorem cxEv_surjective : Function.Surjective (cxEv ρ hρ c S D) := by
  intro w
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective w
  refine ⟨(k • cell 0, 0), ?_⟩
  rw [cxEv_apply, cxValue_apply, map_zsmul, value_cell, Fin.val_zero, weight_zero, map_zero,
    mul_zero, add_zero, smul_eq_mul, mul_one]

/-- **Theorem 158 (the complex quotient).** Complex states modulo ring carries, line
carries and hops are `ℤ/M`, for every length of line.

**fdrs.md**: Theorem 158 (the complex keeps the arithmetic). -/
noncomputable def cxQuotient :
    ((Fin (n + 1) → ℤ) × (Fin (D + 1) → ℤ)) ⧸ hopLattice ρ hρ c S D ≃+ ZMod (modulus ρ hρ c) :=
  (QuotientAddGroup.quotientAddEquivOfEq (ker_cxEv ρ hρ c S D).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (cxEv_surjective ρ hρ c S D))

/-! ## Corollary 55: every state sorts onto its branches -/

/-- **Corollary 55 (sorting onto branches).** Every complex state is equivalent to
`ε_free W` units at ring cell `0` and `W` units at line cell `0`, `W` its value: the free
share sits on the ring, the tied share on the line.

**fdrs.md**: Corollary 55 (every state sorts onto its branches). -/
theorem sort_branches (z : (Fin (n + 1) → ℤ) × (Fin (D + 1) → ℤ)) :
    z - ((freeIdem ρ hρ c S * cxValue ρ hρ c S D z) • cell 0,
      cxValue ρ hρ c S D z • lineCell D 0) ∈ hopLattice ρ hρ c S D := by
  rw [cx_equiv_iff, cxEv_apply, cxEv_apply]
  congr 1
  set W := cxValue ρ hρ c S D z
  simp only [cxValue_mk, map_zsmul, value_cell, lineValue_cell, Fin.val_zero, weight_zero,
    smul_eq_mul, mul_one]
  have := idem_sum_int ρ hρ c S
  linear_combination (-W) * this

/-! ## Theorem 159: the ring closes, the line leaks -/

theorem lap_pow_free [NeZero S.free] :
    ∃ L, 0 < L ∧ (S.free : ℤ) ∣ lapValue ρ hρ ^ L - 1 := by
  obtain ⟨L, hL, hcl⟩ := free_helix_closes ρ hρ c (free_dvd_mod ρ hρ c S) S.free_coprime
  refine ⟨L, hL, ?_⟩
  have h := dvd_of_zmod (hcl 0)
  rwa [weight_laps, weight_zero, mul_one] at h

theorem tied_dvd_lap_pow : (S.tied : ℤ) ∣ lapValue ρ hρ ^ S.laps := by
  have h := tied_dies_dvd ρ hρ c S 0
  rwa [weight_laps, weight_zero, mul_one] at h

/-- **Theorem 159 (the ring closes).** For some `L ≥ 1`, free content on the ring is
invariant under `L` laps of holonomy: `ε_free a` units at ring cell `k` are equivalent to
`ε_free a B^L` units there.

**fdrs.md**: Theorem 159 (the ring closes, the line leaks). -/
theorem ring_closes [NeZero S.free] : ∃ L, 0 < L ∧ ∀ (a : ℤ) (k : Fin (n + 1)),
    (((freeIdem ρ hρ c S * a) • cell k, 0) : (Fin (n + 1) → ℤ) × (Fin (D + 1) → ℤ)) -
      ((freeIdem ρ hρ c S * a * lapValue ρ hρ ^ L) • cell k, 0) ∈ hopLattice ρ hρ c S D := by
  obtain ⟨L, hL, hdvd⟩ := lap_pow_free ρ hρ c S
  refine ⟨L, hL, fun a k => ?_⟩
  rw [cx_equiv_iff, cxEv_apply, cxEv_apply]
  have e : cxValue ρ hρ c S D ((freeIdem ρ hρ c S * a) • cell k, 0) -
      cxValue ρ hρ c S D ((freeIdem ρ hρ c S * a * lapValue ρ hρ ^ L) • cell k, 0) =
      -(freeIdem ρ hρ c S * (a * weight ρ hρ k * (lapValue ρ hρ ^ L - 1))) := by
    simp only [cxValue_mk, map_zsmul, value_cell, map_zero, smul_eq_mul]; ring
  refine eq_of_dvd ρ hρ c S ?_ ?_ <;> rw [e]
  · exact ((hdvd.mul_left _).mul_left _).neg_right
  · exact ((tied_dvd_freeIdem ρ hρ c S).mul_right _).neg_right

/-- **Theorem 159 (the line dies).** Line content multiplied by `B^r` is equivalent to
nothing.

**fdrs.md**: Theorem 159 (the ring closes, the line leaks). -/
theorem line_dies (a : ℤ) (k : Fin (D + 1)) :
    (((0 : Fin (n + 1) → ℤ), (lapValue ρ hρ ^ S.laps * a) • lineCell D k) :
      (Fin (n + 1) → ℤ) × (Fin (D + 1) → ℤ)) ∈ hopLattice ρ hρ c S D := by
  rw [← ker_cxEv, AddMonoidHom.mem_ker, cxEv_eq_zero_iff]
  have e : cxValue ρ hρ c S D (0, (lapValue ρ hρ ^ S.laps * a) • lineCell D k) =
      tiedIdem ρ hρ c S * (lapValue ρ hρ ^ S.laps * a * weight ρ hρ k) := by
    simp only [cxValue_mk, map_zsmul, lineValue_cell, map_zero, smul_eq_mul, zero_add]
  rw [e]
  refine mod_dvd_of ρ hρ c S ?_ ?_
  · exact (free_dvd_tiedIdem ρ hρ c S).mul_right _
  · exact (((tied_dvd_lap_pow ρ hρ c S).mul_right _).mul_right _).mul_left _

/-- **Theorem 159 (the line leaks).** On a line of depth `r N`, anything at the last cell
falls off: it is equivalent to nothing.

**fdrs.md**: Theorem 159 (the ring closes, the line leaks). -/
theorem line_leaks (a : ℤ) :
    (((0 : Fin (n + 1) → ℤ), a • lineCell (S.laps * (n + 1)) (Fin.last _)) :
      (Fin (n + 1) → ℤ) × (Fin (S.laps * (n + 1) + 1) → ℤ)) ∈
      hopLattice ρ hρ c S (S.laps * (n + 1)) := by
  rw [← ker_cxEv, AddMonoidHom.mem_ker, cxEv_eq_zero_iff]
  have e : cxValue ρ hρ c S (S.laps * (n + 1)) (0, a • lineCell (S.laps * (n + 1)) (Fin.last _)) =
      tiedIdem ρ hρ c S * (a * weight ρ hρ (S.laps * (n + 1))) := by
    simp only [cxValue_mk, map_zsmul, lineValue_cell, map_zero, smul_eq_mul, zero_add,
      Fin.val_last]
  rw [e]
  refine mod_dvd_of ρ hρ c S ?_ ?_
  · exact (free_dvd_tiedIdem ρ hρ c S).mul_right _
  · have h := tied_dies_dvd ρ hρ c S 0
    rw [zero_add] at h
    exact (h.mul_left _).mul_left _

/-! ## Theorem 160: the hop is the path back -/

/-- **Theorem 160 (the hop is the path back).** For some `L' ≥ 1`: (a) the unit at ring
cell `k` is equivalent to `ε_free B^{L'}` units at cell `k` plus `B_k` units at line cell
`0` — it returns around the ring with its tied share parked on the line; (b) whenever
`B_k` carries tied residue, it is not equivalent to `B^{L'}` units at cell `k` alone — no
path back on the ring without the hop.

**fdrs.md**: Theorem 160 (the hop is the path back). -/
theorem hop_path_back [NeZero S.free] : ∃ L', 0 < L' ∧
    (∀ k : Fin (n + 1),
      ((cell k, 0) : (Fin (n + 1) → ℤ) × (Fin (D + 1) → ℤ)) -
        ((freeIdem ρ hρ c S * lapValue ρ hρ ^ L') • cell k, weight ρ hρ k • lineCell D 0) ∈
        hopLattice ρ hρ c S D) ∧
    (∀ k : Fin (n + 1), ¬ (S.tied : ℤ) ∣ weight ρ hρ k →
      ((cell k, 0) : (Fin (n + 1) → ℤ) × (Fin (D + 1) → ℤ)) -
        ((lapValue ρ hρ ^ L') • cell k, 0) ∉ hopLattice ρ hρ c S D) := by
  obtain ⟨L, hL, hdvd⟩ := lap_pow_free ρ hρ c S
  set L' := L * (S.laps + 1)
  have hfree : (S.free : ℤ) ∣ lapValue ρ hρ ^ L' - 1 := by
    have := sub_dvd_pow_sub_pow (lapValue ρ hρ ^ L) 1 (S.laps + 1)
    rw [one_pow, ← pow_mul] at this
    exact hdvd.trans this
  have htied : (S.tied : ℤ) ∣ lapValue ρ hρ ^ L' := by
    have hle : S.laps ≤ L' := by
      have : 1 * (S.laps + 1) ≤ L * (S.laps + 1) := Nat.mul_le_mul_right _ hL
      omega
    rw [← Nat.add_sub_cancel' hle, pow_add]
    exact (tied_dvd_lap_pow ρ hρ c S).mul_right _
  refine ⟨L', Nat.mul_pos hL (Nat.succ_pos _), fun k => ?_, fun k hk => ?_⟩
  · rw [cx_equiv_iff, cxEv_apply, cxEv_apply]
    have ht : tiedIdem ρ hρ c S = 1 - freeIdem ρ hρ c S := by
      have := idem_sum_int ρ hρ c S; linarith
    have e : cxValue ρ hρ c S D (cell k, 0) -
        cxValue ρ hρ c S D ((freeIdem ρ hρ c S * lapValue ρ hρ ^ L') • cell k,
          weight ρ hρ k • lineCell D 0) =
        -(freeIdem ρ hρ c S * (weight ρ hρ k * (lapValue ρ hρ ^ L' - 1))) := by
      simp only [cxValue_mk, map_zsmul, value_cell, map_zero, lineValue_cell, smul_eq_mul,
        Fin.val_zero, weight_zero, ht]
      ring
    refine eq_of_dvd ρ hρ c S ?_ ?_ <;> rw [e]
    · exact ((hfree.mul_left _).mul_left _).neg_right
    · exact ((tied_dvd_freeIdem ρ hρ c S).mul_right _).neg_right
  · intro h
    rw [cx_equiv_iff, cxEv_apply, cxEv_apply] at h
    have hd := (Int.natCast_dvd_natCast.mpr (tied_dvd_mod ρ hρ c S)).trans (dvd_of_zmod h)
    have e : cxValue ρ hρ c S D (cell k, 0) - cxValue ρ hρ c S D ((lapValue ρ hρ ^ L') • cell k, 0) =
        weight ρ hρ k - lapValue ρ hρ ^ L' * weight ρ hρ k := by
      simp only [cxValue_mk, map_zsmul, value_cell, map_zero, smul_eq_mul]; ring
    rw [e] at hd
    apply hk
    have := dvd_add hd (htied.mul_right (weight ρ hρ k))
    rwa [sub_add_cancel] at this

end Complex

/-! ## Proposition 183: the (2, 3, 2), c = −3 witnesses -/

section Witness

/-- **Proposition 183 (the unit at ring cell 0 comes back with a hop).** It is equivalent
to `6 · 12^4` units at ring cell `0` plus one unit at line cell `0`
(`6 · 20736 + 10 · 1 ≡ 1 (mod 15)`).

**fdrs.md**: Proposition 183 (the (2,3,2), c = −3 hop). -/
theorem ring232_hop_back :
    ((cell 0, 0) : (Fin 3 → ℤ) × (Fin 4 → ℤ)) - ((6 * 12 ^ 4 : ℤ) • cell 0, lineCell 3 0) ∈
      hopLattice ring232 ring232_ge_two (-3) ring232_split 3 := by
  rw [cx_equiv_iff, cxEv_apply, cxEv_apply]
  simp only [cxValue_mk, map_zsmul, value_cell, map_zero, lineValue_cell, Fin.val_zero,
    weight_zero, smul_eq_mul]
  push_cast
  rw [← ring232_tiedIdem, ring232_modulus_15]
  decide

/-- **Proposition 183 (no way back on the ring alone).** `12^4` units at ring cell `0` are
not equivalent to the unit there (`12^4 ≡ 6 ≢ 1 (mod 15)`).

**fdrs.md**: Proposition 183 (the (2,3,2), c = −3 hop). -/
theorem ring232_no_back :
    ((cell 0, 0) : (Fin 3 → ℤ) × (Fin 4 → ℤ)) - ((12 ^ 4 : ℤ) • cell 0, 0) ∉
      hopLattice ring232 ring232_ge_two (-3) ring232_split 3 := by
  rw [cx_equiv_iff, cxEv_apply, cxEv_apply]
  simp only [cxValue_mk, map_zsmul, value_cell, map_zero, Fin.val_zero, weight_zero,
    smul_eq_mul]
  push_cast
  rw [ring232_modulus_15]
  decide

end Witness

end FdrsFormal.Modes.SyntheticPlace.CarryHop
