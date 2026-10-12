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

# Context branches: custom-sized lines for tied residues (Phase 1 addendum, §3.18)

The hop complex of §3.17 never uses the radices of its line except through the line's
place values `W_k`: any line schedule `β` keeps the arithmetic `ℤ/M` (Theorem 158 holds
for every `β`). So the line holding the tied residue can be **chosen** — by the history
of the residue types that populated it. This file asks which choices are good.

- **Dead cells** (Theorem 161): a unit at line cell `k` is equivalent to nothing iff
  `M₂ ∣ W_k`. A line keeps tied residue only above the first dead cell.
- **Custom-sized branches are faithful** (Theorem 162): if the line's radices multiply to
  exactly the tied modulus (`W_{d+1} = M₂`), digit strings on its `d + 1` cells are in
  bijection with tied residues — one string per residue, no waste.
- **Normal form** (Corollary 56): on such a branch every complex state has a unique form
  `ε_free W` units at the ring root plus a digit string on the branch: the free share on
  the ring, the tied share written exactly once on the line.
- **The history is kept** (Proposition 184): different histories with the same product
  (radices `(2, 3)` or `(3, 2)` for `M₂ = 6`) give branches that hold the same residues as
  different digit strings — the residue is the same, its record on the complex is the
  history that built the branch. The default periodic line of depth `r N` is redundant
  (a nonzero string equivalent to nothing).

A **branch history** is a list of radices; its schedule is the list followed by `2`s, and
its radix law is the position-only law of Definition 57 (`RadixLaw.ofRadixSeq`).

Reuses `CarryHop.lean` (the complex, Theorem 158, `mod_dvd_of`), `BranchComplex.lean`
(idempotents, `tied_ne_zero`), `Core/Finite/Bijection.lean` (`decodeFinite`, its
injectivity and surjectivity), `Modes/VariableRadix/Basic/RadixLaw.lean` (Definition 57)
and `ProductSpread.lean` (the `(2, 3, 2)` ring).

- **Definition 237** (`histSchedule`, `histLaw`, `lineState`): branch histories, their
  schedules and radix laws, digit strings as line states.
- **Theorem 161** (`cell_dead_iff`): dead cells.
- **Theorem 162** (`faithful`): custom-sized branches are faithful.
- **Corollary 56** (`normal_form`): the normal form of the complex.
- **Proposition 184** (`split18`, `hist23_faithful`, `hist32_faithful`, `digits_five`,
  `periodic_redundant`): the `(2, 3, 2)`, `c = −18` witnesses.

**Honest scope.** Elementary (mixed-radix bijections and CRT). The corpus contributes the
freedom to choose the line of the hop complex, the dead-cell criterion, the exactness of
custom-sized branches and the resulting normal form, and branch histories as Definition 57
radix laws. The branch law here is position-only along the branch; laws that branch on the
digits themselves (trees of lines) are not covered.
-/

import FdrsFormal.Modes.SyntheticPlace.CarryHop
import FdrsFormal.Modes.VariableRadix.Basic.RadixLaw

namespace FdrsFormal.Modes.SyntheticPlace.ContextBranch

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite
open FdrsFormal.Modes.SyntheticPlace.RingUnrolling FdrsFormal.Modes.SyntheticPlace.CarryQuotient
open FdrsFormal.Modes.SyntheticPlace.ProductSpread FdrsFormal.Modes.SyntheticPlace.RingLineSplit
open FdrsFormal.Modes.SyntheticPlace.BranchComplex FdrsFormal.Modes.SyntheticPlace.CarryHop

/-! ## Definition 237: branch histories -/

/-- The schedule of a branch history: its radices, then `2`s.

**fdrs.md**: Definition 237 (branch histories). -/
def histSchedule (hist : List ℕ) (h : ∀ x ∈ hist, 2 ≤ x) : RadixSeq where
  toFun j := hist.getD j 2
  ge_two j := by
    rw [List.getD_eq_getElem?_getD]
    cases hj : hist[j]? with
    | none => simp
    | some x => simpa using h x (List.mem_of_getElem? hj)

/-- The radix law of a branch history (Definition 57, position-only).

**fdrs.md**: Definition 237 (branch histories). -/
def histLaw (hist : List ℕ) (h : ∀ x ∈ hist, 2 ≤ x) : VariableRadix.RadixLaw :=
  VariableRadix.RadixLaw.ofRadixSeq (histSchedule hist h)

theorem histLaw_positionOnly (hist : List ℕ) (h : ∀ x ∈ hist, 2 ≤ x) :
    (histLaw hist h).isPositionOnly :=
  VariableRadix.RadixLaw.ofRadixSeq_isPositionOnly _

section Branch

variable {n : ℕ} (ρ : Fin (n + 1) → ℕ) (hρ : ∀ i, 2 ≤ ρ i) (c : ℤ) (S : FreeTiedSplit ρ hρ c)

/-- A digit string on the line, as a line state.

**fdrs.md**: Definition 237 (branch histories). -/
def lineState {d : ℕ} {β : RadixSeq} (σ : FiniteRadixSpace β d) : Fin (d + 1) → ℤ :=
  fun k => ((σ k : ℕ) : ℤ)

theorem lineValue_lineState {d : ℕ} {β : RadixSeq} (σ : FiniteRadixSpace β d) :
    lineValue d β (lineState σ) = (decodeFinite β d σ : ℤ) := by
  simp [lineValue, lineState, decodeFinite]

/-! ## Theorem 161: dead cells -/

/-- **Theorem 161 (dead cells).** A unit at line cell `k` is equivalent to nothing iff the
tied modulus divides the line's place value there.

**fdrs.md**: Theorem 161 (dead cells). -/
theorem cell_dead_iff {D : ℕ} (β : RadixSeq) (k : Fin (D + 1)) :
    (((0 : Fin (n + 1) → ℤ), lineCell D k) : (Fin (n + 1) → ℤ) × (Fin (D + 1) → ℤ)) ∈
      hopLattice ρ hρ c S D β ↔ (S.tied : ℤ) ∣ placeValue β k := by
  rw [← ker_cxEv, AddMonoidHom.mem_ker, cxEv_eq_zero_iff]
  have e : cxValue ρ hρ c S D β (0, lineCell D k) = tiedIdem ρ hρ c S * (placeValue β k : ℤ) := by
    simp only [cxValue_mk, lineValue_cell, map_zero, zero_add]
  rw [e]
  constructor
  · intro h
    have h1 := (Int.natCast_dvd_natCast.mpr (tied_dvd_mod ρ hρ c S)).trans h
    have h2 := (tied_dvd_tiedIdem_sub ρ hρ c S).mul_right (placeValue β k : ℤ)
    have := dvd_sub h1 h2
    rwa [show tiedIdem ρ hρ c S * (placeValue β k : ℤ) -
      (tiedIdem ρ hρ c S - 1) * (placeValue β k : ℤ) = (placeValue β k : ℤ) by ring] at this
  · intro h
    exact mod_dvd_of ρ hρ c S ((free_dvd_tiedIdem ρ hρ c S).mul_right _) (h.mul_left _)

/-! ## Theorem 162: custom-sized branches are faithful -/

/-- **Theorem 162 (custom-sized branches are faithful).** If the line's radices multiply to
exactly the tied modulus, `W_{d+1} = M₂`, digit strings on its `d + 1` cells are in
bijection with tied residues.

**fdrs.md**: Theorem 162 (custom-sized branches are faithful). -/
theorem faithful {d : ℕ} {β : RadixSeq} (hβ : placeValue β (d + 1) = S.tied) :
    Function.Bijective (fun σ : FiniteRadixSpace β d =>
      ((decodeFinite β d σ : ℕ) : ZMod S.tied)) := by
  haveI : NeZero S.tied := ⟨tied_ne_zero ρ hρ c S⟩
  constructor
  · intro σ τ h
    simp only at h
    rw [ZMod.natCast_eq_natCast_iff' _ _ S.tied,
      Nat.mod_eq_of_lt (hβ ▸ decodeFinite_lt d σ), Nat.mod_eq_of_lt (hβ ▸ decodeFinite_lt d τ)] at h
    exact decodeFinite_injective d h
  · intro x
    obtain ⟨σ, hσ⟩ := decodeFinite_surjective (b := β) d ⟨x.val, by rw [hβ]; exact ZMod.val_lt x⟩
    exact ⟨σ, by simp only; rw [hσ]; exact ZMod.natCast_zmod_val x⟩

/-! ## Corollary 56: the normal form -/

theorem tied_dvd_of_equiv {d : ℕ} {β : RadixSeq} {a : ℤ} (σ τ : FiniteRadixSpace β d)
    (h : (((a • cell 0, lineState σ) : (Fin (n + 1) → ℤ) × (Fin (d + 1) → ℤ)) -
      (a • cell 0, lineState τ)) ∈ hopLattice ρ hρ c S d β) :
    (S.tied : ℤ) ∣ (decodeFinite β d σ : ℤ) - decodeFinite β d τ := by
  rw [cx_equiv_iff, cxEv_apply, cxEv_apply] at h
  have h1 := (Int.natCast_dvd_natCast.mpr (tied_dvd_mod ρ hρ c S)).trans (dvd_of_zmod h)
  have e : cxValue ρ hρ c S d β (a • cell 0, lineState σ) - cxValue ρ hρ c S d β (a • cell 0, lineState τ) =
      tiedIdem ρ hρ c S * ((decodeFinite β d σ : ℤ) - decodeFinite β d τ) := by
    simp only [cxValue_mk, lineValue_lineState]; ring
  rw [e] at h1
  have h2 := (tied_dvd_tiedIdem_sub ρ hρ c S).mul_right ((decodeFinite β d σ : ℤ) - decodeFinite β d τ)
  have := dvd_sub h1 h2
  rwa [show tiedIdem ρ hρ c S * ((decodeFinite β d σ : ℤ) - decodeFinite β d τ) -
    (tiedIdem ρ hρ c S - 1) * ((decodeFinite β d σ : ℤ) - decodeFinite β d τ) =
    (decodeFinite β d σ : ℤ) - decodeFinite β d τ by ring] at this

/-- **Corollary 56 (the normal form).** On a custom-sized branch, every complex state of
value `W` is equivalent to `ε_free W` units at ring cell `0` together with exactly one
digit string on the branch.

**fdrs.md**: Corollary 56 (the normal form of the complex). -/
theorem normal_form {d : ℕ} {β : RadixSeq} (hβ : placeValue β (d + 1) = S.tied)
    (z : (Fin (n + 1) → ℤ) × (Fin (d + 1) → ℤ)) :
    ∃! σ : FiniteRadixSpace β d,
      z - ((freeIdem ρ hρ c S * cxValue ρ hρ c S d β z) • cell 0, lineState σ) ∈
        hopLattice ρ hρ c S d β := by
  set W := cxValue ρ hρ c S d β z with hW
  obtain ⟨σ, hσ⟩ := (faithful ρ hρ c S hβ).2 ((W : ℤ) : ZMod S.tied)
  simp only at hσ
  have hσd : (S.tied : ℤ) ∣ (decodeFinite β d σ : ℤ) - W := by
    have := dvd_of_zmod (D := S.tied) (x := (decodeFinite β d σ : ℤ)) (y := W) (by exact_mod_cast hσ)
    exact this
  have hmem : z - ((freeIdem ρ hρ c S * W) • cell 0, lineState σ) ∈ hopLattice ρ hρ c S d β := by
    rw [cx_equiv_iff, cxEv_apply, cxEv_apply]
    have ht : freeIdem ρ hρ c S = 1 - tiedIdem ρ hρ c S := by
      have := idem_sum_int ρ hρ c S; linarith
    have e : cxValue ρ hρ c S d β z -
        cxValue ρ hρ c S d β ((freeIdem ρ hρ c S * W) • cell 0, lineState σ) =
        -(tiedIdem ρ hρ c S * ((decodeFinite β d σ : ℤ) - W)) := by
      rw [← hW]
      simp only [cxValue_mk, map_zsmul, value_cell, Fin.val_zero, weight_zero, smul_eq_mul,
        mul_one, lineValue_lineState, ht]
      ring
    refine eq_of_dvd ρ hρ c S ?_ ?_ <;> rw [e]
    · exact ((free_dvd_tiedIdem ρ hρ c S).mul_right _).neg_right
    · exact (hσd.mul_left _).neg_right
  refine ⟨σ, hmem, fun τ hτ => ?_⟩
  · have hdiff := (hopLattice ρ hρ c S d β).sub_mem hτ hmem
    rw [sub_sub_sub_cancel_left] at hdiff
    have hd := tied_dvd_of_equiv ρ hρ c S σ τ hdiff
    haveI : NeZero S.tied := ⟨tied_ne_zero ρ hρ c S⟩
    apply (faithful ρ hρ c S hβ).1
    simp only
    have := (CharP.intCast_eq_zero_iff (ZMod S.tied) S.tied _).mpr hd
    push_cast at this
    exact (sub_eq_zero.mp this).symm

end Branch

/-! ## Proposition 184: the (2, 3, 2), c = −18 witnesses -/

section Witness

theorem ring232_modulus_30 : modulus ring232 ring232_ge_two (-18) = 30 := rfl

/-- **Proposition 184 (the split `30 = 5 · 6`).** Free part `5`, tied part `6`
(dividing `(−18)^1`).

**fdrs.md**: Proposition 184 (the (2,3,2), c = −18 branches). -/
def split18 : FreeTiedSplit ring232 ring232_ge_two (-18) where
  free := 5
  tied := 6
  laps := 1
  mul_eq := ring232_modulus_30.symm
  coprime := by decide
  free_coprime := Int.isCoprime_iff_gcd_eq_one.mpr (by decide)
  tied_dvd := ⟨-3, by norm_num⟩

/-- The branch built by the history `(2, 3)`. -/
def hist23 : RadixSeq := histSchedule [2, 3] (by decide)

/-- The branch built by the history `(3, 2)`. -/
def hist32 : RadixSeq := histSchedule [3, 2] (by decide)

/-- **Proposition 184 (both histories give faithful branches).** `2 · 3 = 3 · 2 = 6`.

**fdrs.md**: Proposition 184 (the (2,3,2), c = −18 branches). -/
theorem hist23_faithful :
    Function.Bijective (fun σ : FiniteRadixSpace hist23 1 =>
      ((decodeFinite hist23 1 σ : ℕ) : ZMod split18.tied)) :=
  faithful ring232 ring232_ge_two (-18) split18 (by decide)

theorem hist32_faithful :
    Function.Bijective (fun σ : FiniteRadixSpace hist32 1 =>
      ((decodeFinite hist32 1 σ : ℕ) : ZMod split18.tied)) :=
  faithful ring232 ring232_ge_two (-18) split18 (by decide)

/-- **Proposition 184 (the history is kept).** The tied residue `5` is written `(1, 2)` on
the `(2, 3)` branch (`1 + 2 · 2`) and `(2, 1)` on the `(3, 2)` branch (`2 + 1 · 3`).

**fdrs.md**: Proposition 184 (the (2,3,2), c = −18 branches). -/
theorem digits_five :
    ((encodeFinite hist23 1 ⟨5, by decide⟩ 0 : ℕ) = 1 ∧ (encodeFinite hist23 1 ⟨5, by decide⟩ 1 : ℕ) = 2) ∧
    ((encodeFinite hist32 1 ⟨5, by decide⟩ 0 : ℕ) = 2 ∧ (encodeFinite hist32 1 ⟨5, by decide⟩ 1 : ℕ) = 1) := by
  simp only [encodeFinite_digit]
  decide

/-- **Proposition 184 (the periodic line is redundant).** On the ring's own line, cell `2`
(weight `6`) is dead: a nonzero digit string equivalent to nothing.

**fdrs.md**: Proposition 184 (the (2,3,2), c = −18 branches). -/
theorem periodic_redundant :
    (((0 : Fin 3 → ℤ), lineCell 2 2) : (Fin 3 → ℤ) × (Fin 3 → ℤ)) ∈
      hopLattice ring232 ring232_ge_two (-18) split18 2 (ringSchedule ring232 ring232_ge_two) :=
  (cell_dead_iff ring232 ring232_ge_two (-18) split18 _ 2).mpr (by decide)

end Witness

end FdrsFormal.Modes.SyntheticPlace.ContextBranch
