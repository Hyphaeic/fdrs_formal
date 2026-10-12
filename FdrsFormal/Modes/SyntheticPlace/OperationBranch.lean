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

# Operation-driven branches (Phase 1 addendum, §3.19)

§3.18 let the history of a branch choose its radices, read as a fixed list. In the corpus a
radix law is far richer: an **extended radix oracle** reads the radix from a prefix *and*
an external context (Definitions 84–87), and a **stateful system** moves that context with
events (Definitions 88–90). Here the branches of the hop complex (§3.17) are built from
such systems, with the complex's own operations as the events.

- **The branch of a context** (Definition 238): the mixed-radix space of the current
  context (Definition 87), read along its zero path, is the line schedule of the hop
  complex. Its place values are the oracle's prefix weights.
- **Faithfulness is exact sizing** (Theorem 163): the branch holds tied residues once each
  iff its weight at depth `d + 1` is the tied modulus.
- **Structure-preserving context changes do not disturb the complex** (Theorem 164): if a
  transition preserves structure at depth `L` (Definition 93), the hop complexes built from
  the two contexts — moves and values — coincide for every line of depth `≤ L + 1`. A branch
  can grow below depth `L` without invalidating what is held above it.
- **Refinement by divisibility kills, never revives** (Proposition 185): if every weight of
  the old context divides the new one, every dead cell stays dead.
- **Terminating a branch is lossless** (Proposition 186): any line content is equivalent to
  its value, weighted by `ε_tied`, placed at the ring root — the final residue is routed
  back (Definition 126).
- **Operations as events** (Corollary 57): the *recording* system — context the list of
  residue types produced so far, event a newly produced type — spawns the branch of §3.18
  as its trace's context; it is faithful iff the recorded types multiply to the tied
  modulus.

Witnesses on `(2, 3, 2)` with `c = −18` (tied part `6`): recording `(3, 2)` gives a faithful
branch, `(2, 2)` does not; extending the record `(3, 2) → (3, 2, 5)` preserves structure at
depth `1` and leaves every complex of depth `≤ 2` unchanged.

Reuses `ContextDependent` (`ExtendedOracle`, `StatefulSystem`, `isStructurePreserving`,
Definitions 84–93), `VariableRadix` (`RadixLaw`, `prefixWeight`, `prefixWeight_append`),
`CarryHop.lean` (the complex), `ContextBranch.lean` (`faithful`, `cell_dead_iff`,
`histSchedule`, `split18`), `BranchComplex.lean` and `Core/Finite/Bijection.lean`.

- **Definition 238** (`branchSchedule`, `recordSys`): the branch of a context; the
  recording system.
- **Theorem 163** (`faithful_iff`): faithfulness is exact sizing.
- **Theorem 164** (`schedule_agree_complex`, `preserving_complex`): structure-preserving
  changes leave the complex unchanged.
- **Proposition 185** (`refining_dead`): refinement by divisibility.
- **Proposition 186** (`terminate_lossless`): terminating a branch is lossless.
- **Corollary 57** (`record_context`, `record_schedule`, `record_faithful_iff`): operations
  as events.
- **Proposition 187** (`rec32_faithful`, `rec22_not_faithful`, `rec_preserving`,
  `rec_complex_unchanged`): the witnesses.

**Honest scope.** The ingredients are elementary; the contribution is the bridge — branches
of the hop complex as context-indexed radix spaces of stateful systems, with the complex's
operations as events, and the transfer of Definition 93 (structure preservation) into
invariance of the complex. The branch is read along one path (the zero path) of the
context's tree; branches that fork on digits, coupled contexts across several branches
(Definition 98) and stochastic contexts are not covered.
-/

import FdrsFormal.Modes.SyntheticPlace.ContextBranch
import FdrsFormal.Modes.ContextDependent.ContextDependent

namespace FdrsFormal.Modes.SyntheticPlace.OperationBranch

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite
open FdrsFormal.Modes.VariableRadix FdrsFormal.Modes.ContextDependent
open FdrsFormal.Modes.SyntheticPlace.RingUnrolling FdrsFormal.Modes.SyntheticPlace.CarryQuotient
open FdrsFormal.Modes.SyntheticPlace.ProductSpread FdrsFormal.Modes.SyntheticPlace.RingLineSplit
open FdrsFormal.Modes.SyntheticPlace.BranchComplex FdrsFormal.Modes.SyntheticPlace.CarryHop
open FdrsFormal.Modes.SyntheticPlace.ContextBranch

/-! ## Definition 238: the branch of a context -/

section Branch

variable {C E : Type*} [ContextSpace C] [InitialContext C] [EventSpace E]

/-- The zero path of depth `k`. -/
abbrev zeroPath (k : ℕ) : PrefixWord := List.replicate k 0

/-- The branch of a context: the mixed-radix space of `ω_c` (Definition 87) read along its
zero path, as a line schedule.

**fdrs.md**: Definition 238 (the branch of a context). -/
def branchSchedule (𝒮 : StatefulSystem C E) (c : C) : RadixSeq where
  toFun k := (𝒮.radixAt c).radix (zeroPath k)
  ge_two _ := (𝒮.radixAt c).radix_ge_two _

/-- The branch's place values are the oracle's prefix weights along the zero path. -/
theorem branch_placeValue (𝒮 : StatefulSystem C E) (c : C) :
    ∀ k, placeValue (branchSchedule 𝒮 c) k = prefixWeight (𝒮.radixAt c) (zeroPath k)
  | 0 => by simp
  | k + 1 => by
    rw [placeValue.succ, branch_placeValue 𝒮 c k]
    show _ = prefixWeight _ (List.replicate (k + 1) 0)
    rw [List.replicate_succ', prefixWeight_append]
    rfl

end Branch

section Complex

variable {n : ℕ} (ρ : Fin (n + 1) → ℕ) (hρ : ∀ i, 2 ≤ ρ i) (c : ℤ) (S : FreeTiedSplit ρ hρ c)

/-! ## Theorem 163: faithfulness is exact sizing -/

/-- **Theorem 163 (faithfulness is exact sizing).** Digit strings on a line of `d + 1`
cells are in bijection with tied residues iff `W_{d+1} = M₂`.

**fdrs.md**: Theorem 163 (faithfulness is exact sizing). -/
theorem faithful_iff {d : ℕ} (β : RadixSeq) :
    Function.Bijective (fun σ : FiniteRadixSpace β d => ((decodeFinite β d σ : ℕ) : ZMod S.tied)) ↔
      placeValue β (d + 1) = S.tied := by
  haveI : NeZero S.tied := ⟨tied_ne_zero ρ hρ c S⟩
  refine ⟨fun h => ?_, faithful ρ hρ c S⟩
  have h1 := Fintype.card_of_bijective h
  rw [ZMod.card, Fintype.card_congr (finiteRadixEquiv β d), Fintype.card_fin] at h1
  exact h1

/-! ## Theorem 164: structure-preserving changes leave the complex unchanged -/

/-- Two line schedules that agree below depth `D` build the same complex of depth `D`:
the same moves and the same values. -/
theorem schedule_agree_complex {D : ℕ} {β β' : RadixSeq} (h : ∀ j < D, β j = β' j) :
    hopLattice ρ hρ c S D β = hopLattice ρ hρ c S D β' ∧
      cxValue ρ hρ c S D β = cxValue ρ hρ c S D β' := by
  have hpv : ∀ k ≤ D, placeValue β k = placeValue β' k := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih => rw [placeValue.succ, placeValue.succ, ih (by omega), h k (by omega)]
  have hcarry : ∀ k : Fin D, lineCarry D β k = lineCarry D β' k := by
    intro k; simp only [lineCarry, h k k.isLt]
  have hline : lineValue D β = lineValue D β' := by
    refine AddMonoidHom.ext fun y => ?_
    show ∑ k, y k * (placeValue β k : ℤ) = ∑ k, y k * (placeValue β' k : ℤ)
    refine Finset.sum_congr rfl fun k _ => ?_
    have := k.isLt
    rw [hpv k (by omega)]
  refine ⟨?_, ?_⟩
  · simp only [hopLattice, hcarry]
  · ext z
    simp only [cxValue_apply, hline]

/-- **Theorem 164 (structure-preserving changes leave the complex unchanged).** If a context
transition `c → c'` preserves structure at depth `L` (Definition 93), the hop complexes built
from the two branches coincide — moves and values — for every line of depth `D ≤ L + 1`.

**fdrs.md**: Theorem 164 (structure-preserving changes leave the complex unchanged). -/
theorem preserving_complex {C E : Type*} [ContextSpace C] [InitialContext C] [EventSpace E]
    (𝒮 : StatefulSystem C E) {a a' : C} {L D : ℕ} (hp : isStructurePreserving 𝒮 a a' L)
    (hD : D ≤ L + 1) :
    hopLattice ρ hρ c S D (branchSchedule 𝒮 a) = hopLattice ρ hρ c S D (branchSchedule 𝒮 a') ∧
      cxValue ρ hρ c S D (branchSchedule 𝒮 a) = cxValue ρ hρ c S D (branchSchedule 𝒮 a') :=
  schedule_agree_complex ρ hρ c S fun j hj =>
    hp (zeroPath j) (by simp only [zeroPath, List.length_replicate]; omega)

/-! ## Proposition 185: refinement by divisibility -/

/-- **Proposition 185 (refinement by divisibility kills, never revives).** If every weight
of `β` divides the corresponding weight of `β'`, every cell dead on `β` is dead on `β'`.

**fdrs.md**: Proposition 185 (refinement by divisibility). -/
theorem refining_dead {D : ℕ} {β β' : RadixSeq}
    (hdiv : ∀ k, placeValue β k ∣ placeValue β' k) (k : Fin (D + 1))
    (hk : (((0 : Fin (n + 1) → ℤ), lineCell D k) : (Fin (n + 1) → ℤ) × (Fin (D + 1) → ℤ)) ∈
      hopLattice ρ hρ c S D β) :
    (((0 : Fin (n + 1) → ℤ), lineCell D k) : (Fin (n + 1) → ℤ) × (Fin (D + 1) → ℤ)) ∈
      hopLattice ρ hρ c S D β' := by
  rw [cell_dead_iff] at hk ⊢
  exact hk.trans (Int.natCast_dvd_natCast.mpr (hdiv k))

/-! ## Proposition 186: terminating a branch is lossless -/

/-- **Proposition 186 (terminating a branch is lossless).** Any line content `y` is
equivalent to `ε_tied · Σ y_k W_k` units at the ring root: closing the branch routes its
final residue back to the ring (Definition 126) without loss.

**fdrs.md**: Proposition 186 (terminating a branch is lossless). -/
theorem terminate_lossless {D : ℕ} (β : RadixSeq) (y : Fin (D + 1) → ℤ) :
    (((0 : Fin (n + 1) → ℤ), y) : (Fin (n + 1) → ℤ) × (Fin (D + 1) → ℤ)) -
      ((tiedIdem ρ hρ c S * lineValue D β y) • cell 0, 0) ∈ hopLattice ρ hρ c S D β := by
  have h := cx_sub_value_mem ρ hρ c S D β (0, y)
  rwa [cxValue_mk, map_zero, zero_add] at h

end Complex

/-! ## Corollary 57: operations as events — the recording system -/

section Recording

/-- Residue-type records (lists of radices) form a context space; the empty record is
initial. -/
instance : ContextSpace (List ℕ) := ⟨⟨[]⟩⟩
instance : InitialContext (List ℕ) := ⟨[]⟩
/-- Produced residue types form an event space. -/
instance : EventSpace ℕ := ⟨⟨0⟩⟩

/-- The recording system: an operation that produces a residue type `q ≥ 2` appends it to
the record; the radix at depth `k` is the `k`-th recorded type (`2` beyond the record).

**fdrs.md**: Definition 238 (the branch of a context). -/
def recordSys : StatefulSystem (List ℕ) ℕ where
  oracle := ⟨fun s rec => max 2 (rec.getD s.length 2), fun _ _ => le_max_left _ _⟩
  dynamics := ⟨fun rec q => if 2 ≤ q then rec ++ [q] else rec⟩

/-- **Corollary 57 (the record is the context).** After events `qs` (all `≥ 2`), the
context of the recording system is `qs`.

**fdrs.md**: Corollary 57 (operations as events). -/
theorem record_context (qs : List ℕ) (h : ∀ q ∈ qs, 2 ≤ q) :
    qs.foldl recordSys.dynamics.transition ([] : List ℕ) = qs := by
  suffices ∀ acc : List ℕ, qs.foldl recordSys.dynamics.transition acc = acc ++ qs by
    simpa using this ([] : List ℕ)
  induction qs with
  | nil => simp
  | cons q qs ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [show recordSys.dynamics.transition acc q = acc ++ [q] from if_pos (h q (by simp)),
      ih (fun x hx => h x (by simp [hx]))]
    simp

/-- **Corollary 57 (the recorded branch is the history branch of §3.18).**

**fdrs.md**: Corollary 57 (operations as events). -/
theorem record_schedule (qs : List ℕ) (h : ∀ q ∈ qs, 2 ≤ q) (k : ℕ) :
    branchSchedule recordSys qs k = histSchedule qs h k := by
  show max 2 (qs.getD (List.replicate k 0).length 2) = qs.getD k 2
  rw [List.length_replicate]
  exact max_eq_right ((histSchedule qs h).ge_two k)

theorem record_placeValue (qs : List ℕ) (h : ∀ q ∈ qs, 2 ≤ q) :
    ∀ k ≤ qs.length, placeValue (branchSchedule recordSys qs) k = (qs.take k).prod
  | 0, _ => by simp
  | k + 1, hk => by
    rw [placeValue.succ, record_placeValue qs h k (by omega), record_schedule qs h k,
      List.prod_take_succ _ _ (by omega)]
    show (qs.take k).prod * qs.getD k 2 = _
    rw [List.getD_eq_getElem _ _ (by omega)]

/-- **Corollary 57 (operations as events).** The branch spawned by recording the residue
types `qs` (`d + 1` of them) is faithful iff they multiply to the tied modulus.

**fdrs.md**: Corollary 57 (operations as events). -/
theorem record_faithful_iff {n : ℕ} (ρ : Fin (n + 1) → ℕ) (hρ : ∀ i, 2 ≤ ρ i) (c : ℤ)
    (S : FreeTiedSplit ρ hρ c) (qs : List ℕ) (h : ∀ q ∈ qs, 2 ≤ q) {d : ℕ}
    (hd : qs.length = d + 1) :
    Function.Bijective (fun σ : FiniteRadixSpace (branchSchedule recordSys qs) d =>
      ((decodeFinite _ d σ : ℕ) : ZMod S.tied)) ↔ qs.prod = S.tied := by
  rw [faithful_iff ρ hρ c S, record_placeValue qs h (d + 1) (by omega), ← hd, List.take_length]

end Recording

/-! ## Proposition 187: the (2, 3, 2), c = −18 witnesses -/

section Witness

/-- **Proposition 187 (recording `(3, 2)` spawns a faithful branch).**

**fdrs.md**: Proposition 187 (operation-driven witnesses). -/
theorem rec32_faithful :
    Function.Bijective (fun σ : FiniteRadixSpace (branchSchedule recordSys ([3, 2] : List ℕ)) 1 =>
      ((decodeFinite _ 1 σ : ℕ) : ZMod split18.tied)) :=
  (record_faithful_iff ring232 ring232_ge_two (-18) split18 ([3, 2] : List ℕ) (by decide) (d := 1) rfl).mpr rfl

/-- **Proposition 187 (recording `(2, 2)` does not).** `2 · 2 = 4 ≠ 6`.

**fdrs.md**: Proposition 187 (operation-driven witnesses). -/
theorem rec22_not_faithful :
    ¬ Function.Bijective (fun σ : FiniteRadixSpace (branchSchedule recordSys ([2, 2] : List ℕ)) 1 =>
      ((decodeFinite _ 1 σ : ℕ) : ZMod split18.tied)) := by
  rw [record_faithful_iff ring232 ring232_ge_two (-18) split18 ([2, 2] : List ℕ) (by decide) (d := 1) rfl]
  decide

/-- **Proposition 187 (a new residue type at depth 2 preserves structure at depth 1).**

**fdrs.md**: Proposition 187 (operation-driven witnesses). -/
theorem rec_preserving : isStructurePreserving recordSys ([3, 2] : List ℕ) ([3, 2, 5] : List ℕ) 1 := by
  intro s hs
  show max 2 ([3, 2].getD s.length 2) = max 2 ([3, 2, 5].getD s.length 2)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hs with h | h <;> rw [h] <;> rfl

/-- **Proposition 187 (so the complex is unchanged to depth 2).**

**fdrs.md**: Proposition 187 (operation-driven witnesses). -/
theorem rec_complex_unchanged :
    hopLattice ring232 ring232_ge_two (-18) split18 2 (branchSchedule recordSys ([3, 2] : List ℕ)) =
        hopLattice ring232 ring232_ge_two (-18) split18 2 (branchSchedule recordSys ([3, 2, 5] : List ℕ)) ∧
      cxValue ring232 ring232_ge_two (-18) split18 2 (branchSchedule recordSys ([3, 2] : List ℕ)) =
        cxValue ring232 ring232_ge_two (-18) split18 2 (branchSchedule recordSys ([3, 2, 5] : List ℕ)) :=
  preserving_complex ring232 ring232_ge_two (-18) split18 recordSys rec_preserving le_rfl

end Witness

end FdrsFormal.Modes.SyntheticPlace.OperationBranch
