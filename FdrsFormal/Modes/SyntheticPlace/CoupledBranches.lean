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

# Coupled branches: one branch per residue type (Phase 1 addendum, §3.20)

§3.19 grew one branch from a stateful system. Here the tied part splits into **two residue
types** — `M = F · T_A · T_B`, pairwise coprime — and each type gets its own branch, with
its own context, coupled to the other in the sense of the corpus's multi-context observer
complex (Definitions 95–98): the free ring plays the interpreter, the branches play the
timelines, and each branch's context is fed by the residue **in flight** to the branches
(Theorem 57: residual payload = undelivered junction accumulation).

- **The two-branch complex** (Definition 239): ring cells, line `A` and line `B` (any
  schedules), ring carries, line carries, and two hops — `ε_A` units off the ring root onto
  `A`'s root, `ε_B` units onto `B`'s.
- **It keeps the arithmetic** (Theorem 165): states modulo moves are exactly `ℤ/M`, for any
  two line schedules and lengths.
- **Joint normal form** (Theorem 166): with both branches exactly sized (`W^A_{d_A+1} = T_A`,
  `W^B_{d_B+1} = T_B`), every state is equivalent to `ε_F W` units at the ring root plus
  exactly one digit string on each branch — each residue type written once, on its own
  branch.
- **Payloads and coupling** (Definition 240, Theorem 167): the payload of an operation to a
  branch is its residue modulo that branch's type. Payloads are invariant under every
  move, and branches are **opaque** to each other: content on `A` carries no payload to
  `B`, and conversely. A coupled branch system feeds each context with both payloads (the
  general form of Definition 98); its evolution therefore depends only on the residue
  classes of the operations — carries and hops never change what a branch is told.

Witnesses on `(2, 3, 2)` with `c = −18` (`M = 30 = 5 · 2 · 3`): with the cross-feeding rule
"a branch allocates a radix of its own type when the *other* type is in flight", the
operation `5` grows both branches to exact size, `15` grows only `B`, and `35 ≡ 5` drives
exactly the same evolution as `5`; after `5` the complex has a unique joint normal form.

Reuses `CarryQuotient.lean` (ring cells, carries, Theorem 147), `CarryHop.lean` (line cells,
line carries, line values), `ContextBranch.lean` (`lineState`, `ring232_modulus_30`),
`OperationBranch.lean` (`zeroPath`, `recordSys`), `BranchComplex.lean` (`dvd_of_zmod`),
`ContextDependent` (`ContextSpace`, `ExtendedOracle`) and `Core/Finite/Bijection.lean`.

- **Definition 239** (`TwoTiedSplit`, `epsF`, `epsA`, `epsB`, `cpLattice`, `cpValue`): the
  two-branch complex.
- **Theorem 165** (`ker_cpEv`, `cp_equiv_iff`, `cpQuotient`): it keeps the arithmetic.
- **Theorem 166** (`joint_normal_form`): the joint normal form.
- **Definition 240** (`Coupling`, `Coupling.run`): payloads and coupled branch systems.
- **Theorem 167** (`payload_invariant`, `opaque_AB`, `opaque_BA`, `payload_A_of_A`,
  `run_gauge`): payloads are move-invariant and branch-opaque; coupled evolution is
  gauge-invariant.
- **Proposition 188** (`split30`, `cross_run_five`, `cross_run_fifteen`, `cross_run_gauge`,
  `cross_normal_form`): the witnesses.

**Honest scope.** Elementary (three-factor CRT and its idempotents). The corpus contributes
the multi-branch hop complex, its joint normal form, and the reading of Definition 98's
payload feedback on it, with the gauge invariance of the coupled evolution. Two tied types
are treated (not an arbitrary family); branches fork on no digits; stochastic contexts are
not covered.
-/

import FdrsFormal.Modes.SyntheticPlace.OperationBranch

namespace FdrsFormal.Modes.SyntheticPlace.CoupledBranches

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite
open FdrsFormal.Modes.VariableRadix FdrsFormal.Modes.ContextDependent
open FdrsFormal.Modes.SyntheticPlace.RingUnrolling FdrsFormal.Modes.SyntheticPlace.CarryQuotient
open FdrsFormal.Modes.SyntheticPlace.ProductSpread
open FdrsFormal.Modes.SyntheticPlace.CarryHop FdrsFormal.Modes.SyntheticPlace.ContextBranch
open FdrsFormal.Modes.SyntheticPlace.OperationBranch

/-! ## Definition 239: the split and its idempotents -/

/-- A split of the modulus into a free part and two tied residue types, pairwise coprime.

**fdrs.md**: Definition 239 (the two-branch complex). -/
structure TwoTiedSplit {n : ℕ} (ρ : Fin (n + 1) → ℕ) (hρ : ∀ i, 2 ≤ ρ i) (c : ℤ) where
  free : ℕ
  tA : ℕ
  tB : ℕ
  laps : ℕ
  mul_eq : free * tA * tB = modulus ρ hρ c
  cop_fA : Nat.Coprime free tA
  cop_fB : Nat.Coprime free tB
  cop_AB : Nat.Coprime tA tB
  free_coprime : IsCoprime c (free : ℤ)
  tA_dvd : (tA : ℤ) ∣ c ^ laps
  tB_dvd : (tB : ℤ) ∣ c ^ laps

/-- The Bézout idempotent `≡ 1 (mod p)`, `≡ 0 (mod q)`. -/
noncomputable def idemOf (p q : ℕ) (h : Nat.Coprime p q) : ℤ :=
  Classical.choose (Classical.choose_spec (Nat.isCoprime_iff_coprime.mpr h)) * q

theorem idemOf_spec (p q : ℕ) (h : Nat.Coprime p q) :
    (q : ℤ) ∣ idemOf p q h ∧ (p : ℤ) ∣ idemOf p q h - 1 := by
  have hs := Classical.choose_spec (Classical.choose_spec (Nat.isCoprime_iff_coprime.mpr h))
  refine ⟨dvd_mul_left _ _, ⟨-(Classical.choose (Nat.isCoprime_iff_coprime.mpr h)), ?_⟩⟩
  rw [idemOf]; linear_combination hs

theorem idemOf_one (p q : ℕ) (h : Nat.Coprime p q) : ((idemOf p q h : ℤ) : ZMod p) = 1 := by
  have := (CharP.intCast_eq_zero_iff (ZMod p) p _).mpr (idemOf_spec p q h).2
  rwa [Int.cast_sub, Int.cast_one, sub_eq_zero] at this

theorem idemOf_zero (p q : ℕ) (h : Nat.Coprime p q) {r : ℕ} (hr : r ∣ q) :
    ((idemOf p q h : ℤ) : ZMod r) = 0 :=
  (CharP.intCast_eq_zero_iff (ZMod r) r _).mpr
    ((Int.natCast_dvd_natCast.mpr hr).trans (idemOf_spec p q h).1)

section Split

variable {n : ℕ} {ρ : Fin (n + 1) → ℕ} {hρ : ∀ i, 2 ≤ ρ i} {c : ℤ} (S : TwoTiedSplit ρ hρ c)

/-- The free idempotent. -/
noncomputable def epsF : ℤ := idemOf S.free (S.tA * S.tB) (Nat.Coprime.mul_right S.cop_fA S.cop_fB)
/-- The idempotent of residue type `A`. -/
noncomputable def epsA : ℤ := idemOf S.tA (S.free * S.tB) (Nat.Coprime.mul_right S.cop_fA.symm S.cop_AB)
/-- The idempotent of residue type `B`. -/
noncomputable def epsB : ℤ :=
  idemOf S.tB (S.free * S.tA) (Nat.Coprime.mul_right S.cop_fB.symm S.cop_AB.symm)

theorem epsF_F : ((epsF S : ℤ) : ZMod S.free) = 1 := idemOf_one _ _ _
theorem epsF_A : ((epsF S : ℤ) : ZMod S.tA) = 0 := idemOf_zero _ _ _ (dvd_mul_right _ _)
theorem epsF_B : ((epsF S : ℤ) : ZMod S.tB) = 0 := idemOf_zero _ _ _ (dvd_mul_left _ _)
theorem epsA_F : ((epsA S : ℤ) : ZMod S.free) = 0 := idemOf_zero _ _ _ (dvd_mul_right _ _)
theorem epsA_A : ((epsA S : ℤ) : ZMod S.tA) = 1 := idemOf_one _ _ _
theorem epsA_B : ((epsA S : ℤ) : ZMod S.tB) = 0 := idemOf_zero _ _ _ (dvd_mul_left _ _)
theorem epsB_F : ((epsB S : ℤ) : ZMod S.free) = 0 := idemOf_zero _ _ _ (dvd_mul_right _ _)
theorem epsB_A : ((epsB S : ℤ) : ZMod S.tA) = 0 := idemOf_zero _ _ _ (dvd_mul_left _ _)
theorem epsB_B : ((epsB S : ℤ) : ZMod S.tB) = 1 := idemOf_one _ _ _

theorem tA_dvd_mod : S.tA ∣ modulus ρ hρ c := ⟨S.free * S.tB, by rw [← S.mul_eq]; ring⟩
theorem tB_dvd_mod : S.tB ∣ modulus ρ hρ c := ⟨S.free * S.tA, by rw [← S.mul_eq]; ring⟩
theorem free_dvd_mod' : S.free ∣ modulus ρ hρ c := ⟨S.tA * S.tB, by rw [← S.mul_eq]; ring⟩

/-- Congruent modulo the three parts, congruent modulo `M`. -/
theorem eq_of_three {x y : ℤ} (h1 : (x : ZMod S.free) = y) (h2 : (x : ZMod S.tA) = y)
    (h3 : (x : ZMod S.tB) = y) : (x : ZMod (modulus ρ hρ c)) = y := by
  rw [← sub_eq_zero, ← Int.cast_sub, CharP.intCast_eq_zero_iff (ZMod _) (modulus ρ hρ c),
    ← S.mul_eq, Nat.cast_mul, Nat.cast_mul]
  have hc1 : IsCoprime ((S.free : ℤ) * S.tA) (S.tB : ℤ) := by
    rw [← Nat.cast_mul]; exact Nat.isCoprime_iff_coprime.mpr (Nat.coprime_mul_iff_left.mpr ⟨S.cop_fB, S.cop_AB⟩)
  have hc2 : IsCoprime (S.free : ℤ) (S.tA : ℤ) := Nat.isCoprime_iff_coprime.mpr S.cop_fA
  exact hc1.mul_dvd (hc2.mul_dvd (BranchComplex.dvd_of_zmod h1) (BranchComplex.dvd_of_zmod h2))
    (BranchComplex.dvd_of_zmod h3)

theorem zmod_of_mod {D : ℕ} (hD : D ∣ modulus ρ hρ c) {x y : ℤ}
    (h : (x : ZMod (modulus ρ hρ c)) = y) : (x : ZMod D) = y := by
  rw [← sub_eq_zero, ← Int.cast_sub, CharP.intCast_eq_zero_iff (ZMod D) D]
  exact (Int.natCast_dvd_natCast.mpr hD).trans (BranchComplex.dvd_of_zmod h)

end Split

/-! ## Definition 239: the two-branch complex -/

/-- States of the two-branch complex: ring cells, line `A` cells, line `B` cells. -/
abbrev St (n DA DB : ℕ) := (Fin (n + 1) → ℤ) × (Fin (DA + 1) → ℤ) × (Fin (DB + 1) → ℤ)

/-- A generic fact about lines: carrying down collapses any line state to its value at
cell `0`, inside any subgroup containing the line carries. -/
theorem line_collapse {D : ℕ} (β : RadixSeq) (H : AddSubgroup (Fin (D + 1) → ℤ))
    (hH : ∀ k, lineCarry D β k ∈ H) (y : Fin (D + 1) → ℤ) :
    y - lineValue D β y • lineCell D 0 ∈ H := by
  have cell_sub : ∀ (k : ℕ) (hk : k < D + 1),
      lineCell D ⟨k, hk⟩ - (placeValue β k : ℤ) • lineCell D 0 ∈ H := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [placeValue.zero, Nat.cast_one, one_smul, show (⟨0, _⟩ : Fin (D + 1)) = 0 from rfl,
        sub_self]
      exact H.zero_mem
    | succ k ih =>
      intro hk
      have hk' : k < D := by omega
      have hv : lineCarry D β ⟨k, hk'⟩ =
          lineCell D ⟨k + 1, hk⟩ - (β k : ℤ) • lineCell D ⟨k, by omega⟩ := by
        rw [lineCarry, Fin.succ_mk, Fin.castSucc_mk]
      have h3 := H.add_mem (hH ⟨k, hk'⟩) (H.zsmul_mem (ih (by omega)) (β k : ℤ))
      rw [hv, lineWeight_succ β k] at *
      convert h3 using 1
      rw [smul_sub, mul_comm, mul_smul]
      abel
  have hy : y - lineValue D β y • lineCell D 0 =
      ∑ k, y k • (lineCell D k - (placeValue β k : ℤ) • lineCell D 0) := by
    simp only [smul_sub, Finset.sum_sub_distrib, smul_smul]
    congr 1
    · funext j; simp [lineCell, Finset.sum_apply, Pi.single_apply]
    · rw [← Finset.sum_smul]; rfl
  rw [hy]
  exact H.sum_mem fun k _ => H.zsmul_mem (cell_sub k k.isLt) _

/-- Ring states inside the complex. -/
def ringEmb (n DA DB : ℕ) : (Fin (n + 1) → ℤ) →+ St n DA DB := AddMonoidHom.inl _ _
/-- Line-`A` states inside the complex. -/
def lineAEmb (n DA DB : ℕ) : (Fin (DA + 1) → ℤ) →+ St n DA DB :=
  (AddMonoidHom.inr _ _).comp (AddMonoidHom.inl _ _)
/-- Line-`B` states inside the complex. -/
def lineBEmb (n DA DB : ℕ) : (Fin (DB + 1) → ℤ) →+ St n DA DB :=
  (AddMonoidHom.inr _ _).comp (AddMonoidHom.inr _ _)

theorem ringEmb_apply {n DA DB : ℕ} (x : Fin (n + 1) → ℤ) : ringEmb n DA DB x = (x, 0, 0) := rfl
theorem lineAEmb_apply {n DA DB : ℕ} (y : Fin (DA + 1) → ℤ) : lineAEmb n DA DB y = (0, y, 0) := rfl
theorem lineBEmb_apply {n DA DB : ℕ} (y : Fin (DB + 1) → ℤ) : lineBEmb n DA DB y = (0, 0, y) := rfl

section Complex

variable {n : ℕ} (ρ : Fin (n + 1) → ℕ) (hρ : ∀ i, 2 ≤ ρ i) (c : ℤ) (S : TwoTiedSplit ρ hρ c)
variable (DA DB : ℕ) (βA βB : RadixSeq)

/-- The hop onto branch `A`: `ε_A` units leave the ring root, one unit appears at `A`'s root. -/
noncomputable def hopA : St n DA DB := (-(epsA S) • cell 0, lineCell DA 0, 0)
/-- The hop onto branch `B`. -/
noncomputable def hopB : St n DA DB := (-(epsB S) • cell 0, 0, lineCell DB 0)

/-- The move lattice of the two-branch complex.

**fdrs.md**: Definition 239 (the two-branch complex). -/
noncomputable def cpLattice : AddSubgroup (St n DA DB) :=
  AddSubgroup.closure
    (Set.range (fun i => ringEmb n DA DB (carryVec ρ c i)) ∪
      Set.range (fun k => lineAEmb n DA DB (lineCarry DA βA k)) ∪
      Set.range (fun k => lineBEmb n DA DB (lineCarry DB βB k)) ∪
      {hopA ρ hρ c S DA DB} ∪ {hopB ρ hρ c S DA DB})

/-- The value of a state: `Σ x_k B_k + ε_A Σ y^A_k W^A_k + ε_B Σ y^B_k W^B_k`.

**fdrs.md**: Definition 239 (the two-branch complex). -/
noncomputable def cpValue : St n DA DB →+ ℤ :=
  AddMonoidHom.mk' (fun z => value ρ hρ z.1 + epsA S * lineValue DA βA z.2.1 +
      epsB S * lineValue DB βB z.2.2)
    (by intro x y; simp only [Prod.fst_add, Prod.snd_add, map_add]; ring)

/-- The value modulo `M`. -/
noncomputable def cpEv : St n DA DB →+ ZMod (modulus ρ hρ c) :=
  (Int.castAddHom _).comp (cpValue ρ hρ c S DA DB βA βB)

theorem cpValue_mk (x : Fin (n + 1) → ℤ) (yA : Fin (DA + 1) → ℤ) (yB : Fin (DB + 1) → ℤ) :
    cpValue ρ hρ c S DA DB βA βB (x, yA, yB) =
      value ρ hρ x + epsA S * lineValue DA βA yA + epsB S * lineValue DB βB yB := rfl

theorem cpEv_apply (z : St n DA DB) :
    cpEv ρ hρ c S DA DB βA βB z = ((cpValue ρ hρ c S DA DB βA βB z : ℤ) : ZMod (modulus ρ hρ c)) :=
  rfl

theorem cpEv_eq_zero_iff (z : St n DA DB) :
    cpEv ρ hρ c S DA DB βA βB z = 0 ↔ (modulus ρ hρ c : ℤ) ∣ cpValue ρ hρ c S DA DB βA βB z := by
  rw [cpEv_apply, CharP.intCast_eq_zero_iff (ZMod (modulus ρ hρ c)) (modulus ρ hρ c)]

/-! ## Theorem 165: the two-branch complex keeps the arithmetic -/

theorem ring_mem {z : Fin (n + 1) → ℤ} (hz : z ∈ carryLattice ρ c) :
    ringEmb n DA DB z ∈ cpLattice ρ hρ c S DA DB βA βB := by
  have : carryLattice ρ c ≤ (cpLattice ρ hρ c S DA DB βA βB).comap (ringEmb n DA DB) := by
    rw [carryLattice, AddSubgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact AddSubgroup.subset_closure (Or.inl (Or.inl (Or.inl (Or.inl ⟨i, rfl⟩))))
  exact this hz

theorem lineA_mem (y : Fin (DA + 1) → ℤ) :
    lineAEmb n DA DB (y - lineValue DA βA y • lineCell DA 0) ∈ cpLattice ρ hρ c S DA DB βA βB :=
  line_collapse βA ((cpLattice ρ hρ c S DA DB βA βB).comap (lineAEmb n DA DB))
    (fun k => AddSubgroup.subset_closure (Or.inl (Or.inl (Or.inl (Or.inr ⟨k, rfl⟩))))) y

theorem lineB_mem (y : Fin (DB + 1) → ℤ) :
    lineBEmb n DA DB (y - lineValue DB βB y • lineCell DB 0) ∈ cpLattice ρ hρ c S DA DB βA βB :=
  line_collapse βB ((cpLattice ρ hρ c S DA DB βA βB).comap (lineBEmb n DA DB))
    (fun k => AddSubgroup.subset_closure (Or.inl (Or.inl (Or.inr ⟨k, rfl⟩)))) y

theorem hopA_mem : hopA ρ hρ c S DA DB ∈ cpLattice ρ hρ c S DA DB βA βB :=
  AddSubgroup.subset_closure (Or.inl (Or.inr rfl))

theorem hopB_mem : hopB ρ hρ c S DA DB ∈ cpLattice ρ hρ c S DA DB βA βB :=
  AddSubgroup.subset_closure (Or.inr rfl)

/-- Every state is equivalent to its value placed at the ring root. -/
theorem cp_sub_value_mem (z : St n DA DB) :
    z - ringEmb n DA DB (cpValue ρ hρ c S DA DB βA βB z • cell 0) ∈
      cpLattice ρ hρ c S DA DB βA βB := by
  obtain ⟨x, yA, yB⟩ := z
  have h1 := ring_mem ρ hρ c S DA DB βA βB (sub_value_mem ρ hρ c x)
  have h2 := lineA_mem ρ hρ c S DA DB βA βB yA
  have h3 := lineB_mem ρ hρ c S DA DB βA βB yB
  have h4 := (cpLattice ρ hρ c S DA DB βA βB).zsmul_mem (hopA_mem ρ hρ c S DA DB βA βB)
    (lineValue DA βA yA)
  have h5 := (cpLattice ρ hρ c S DA DB βA βB).zsmul_mem (hopB_mem ρ hρ c S DA DB βA βB)
    (lineValue DB βB yB)
  have h := (cpLattice ρ hρ c S DA DB βA βB).add_mem
    ((cpLattice ρ hρ c S DA DB βA βB).add_mem
      ((cpLattice ρ hρ c S DA DB βA βB).add_mem
        ((cpLattice ρ hρ c S DA DB βA βB).add_mem h1 h2) h3) h4) h5
  convert h using 1
  rw [cpValue_mk, ringEmb_apply, ringEmb_apply, lineAEmb_apply, lineBEmb_apply, hopA, hopB]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> funext i <;>
    simp only [Prod.fst_sub, Prod.fst_add, Prod.snd_sub, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] <;> ring

/-- **Theorem 165 (the two-branch complex keeps the arithmetic: kernel).** A state is a
combination of ring carries, line carries and the two hops iff its value vanishes modulo `M`.

**fdrs.md**: Theorem 165 (the two-branch complex keeps the arithmetic). -/
theorem ker_cpEv : (cpEv ρ hρ c S DA DB βA βB).ker = cpLattice ρ hρ c S DA DB βA βB := by
  apply le_antisymm
  · intro z hz
    rw [AddMonoidHom.mem_ker, cpEv_eq_zero_iff] at hz
    have hring : cpValue ρ hρ c S DA DB βA βB z • cell 0 ∈ carryLattice ρ c := by
      rw [← ker_ev ρ hρ c, AddMonoidHom.mem_ker, ev_eq_zero_iff, map_zsmul, value_cell,
        Fin.val_zero, weight_zero, smul_eq_mul, mul_one, ← Int.natAbs_dvd, ← modulus]
      exact hz
    have := (cpLattice ρ hρ c S DA DB βA βB).add_mem (cp_sub_value_mem ρ hρ c S DA DB βA βB z)
      (ring_mem ρ hρ c S DA DB βA βB hring)
    rwa [sub_add_cancel] at this
  · rw [cpLattice, AddSubgroup.closure_le]
    rintro z ((((⟨i, rfl⟩ | ⟨k, rfl⟩) | ⟨k, rfl⟩) | rfl) | rfl)
    · dsimp only
      rw [SetLike.mem_coe, AddMonoidHom.mem_ker, cpEv_eq_zero_iff, ringEmb_apply, cpValue_mk,
        map_zero, map_zero, mul_zero, mul_zero, add_zero, add_zero]
      have := (ker_ev ρ hρ c).ge
        (AddSubgroup.subset_closure ⟨i, rfl⟩ : carryVec ρ c i ∈ carryLattice ρ c)
      rw [AddMonoidHom.mem_ker, ev_eq_zero_iff, ← Int.natAbs_dvd, ← modulus] at this
      exact this
    all_goals
      rw [SetLike.mem_coe, AddMonoidHom.mem_ker, cpEv_eq_zero_iff]
      convert dvd_zero (modulus ρ hρ c : ℤ) using 1
    · simp only [lineAEmb_apply, cpValue_mk, lineCarry, map_sub, map_zsmul, lineValue_cell,
        map_zero, Fin.val_succ, Fin.val_castSucc, lineWeight_succ, smul_eq_mul]
      ring
    · simp only [lineBEmb_apply, cpValue_mk, lineCarry, map_sub, map_zsmul, lineValue_cell,
        map_zero, Fin.val_succ, Fin.val_castSucc, lineWeight_succ, smul_eq_mul]
      ring
    · simp only [hopA, cpValue_mk, map_zsmul, value_cell, lineValue_cell, map_zero,
        Fin.val_zero, weight_zero, placeValue.zero, Nat.cast_one, smul_eq_mul]
      ring
    · simp only [hopB, cpValue_mk, map_zsmul, value_cell, lineValue_cell, map_zero,
        Fin.val_zero, weight_zero, placeValue.zero, Nat.cast_one, smul_eq_mul]
      ring

/-- **Theorem 165 (equivalence in the two-branch complex).**

**fdrs.md**: Theorem 165 (the two-branch complex keeps the arithmetic). -/
theorem cp_equiv_iff (z z' : St n DA DB) :
    z - z' ∈ cpLattice ρ hρ c S DA DB βA βB ↔
      cpEv ρ hρ c S DA DB βA βB z = cpEv ρ hρ c S DA DB βA βB z' := by
  rw [← ker_cpEv, AddMonoidHom.mem_ker, map_sub, sub_eq_zero]

theorem cpEv_surjective : Function.Surjective (cpEv ρ hρ c S DA DB βA βB) := by
  intro w
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective w
  refine ⟨ringEmb n DA DB (k • cell 0), ?_⟩
  rw [cpEv_apply, ringEmb_apply, cpValue_mk, map_zsmul, value_cell, Fin.val_zero, weight_zero,
    map_zero, map_zero, mul_zero, mul_zero, add_zero, add_zero, smul_eq_mul, mul_one]

/-- **Theorem 165 (the two-branch quotient).** States modulo all moves are `ℤ/M`, for any two
line schedules and lengths.

**fdrs.md**: Theorem 165 (the two-branch complex keeps the arithmetic). -/
noncomputable def cpQuotient :
    St n DA DB ⧸ cpLattice ρ hρ c S DA DB βA βB ≃+ ZMod (modulus ρ hρ c) :=
  (QuotientAddGroup.quotientAddEquivOfEq (ker_cpEv ρ hρ c S DA DB βA βB).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (cpEv_surjective ρ hρ c S DA DB βA βB))

/-! ## Theorem 166: the joint normal form -/

/-- Exactly sized lines are faithful (any modulus). -/
theorem faithful_gen {d : ℕ} {β : RadixSeq} (t : ℕ) [NeZero t] (hβ : placeValue β (d + 1) = t) :
    Function.Bijective (fun σ : FiniteRadixSpace β d => ((decodeFinite β d σ : ℕ) : ZMod t)) := by
  constructor
  · intro σ τ h
    simp only at h
    rw [ZMod.natCast_eq_natCast_iff' _ _ t,
      Nat.mod_eq_of_lt (hβ ▸ decodeFinite_lt d σ), Nat.mod_eq_of_lt (hβ ▸ decodeFinite_lt d τ)] at h
    exact decodeFinite_injective d h
  · intro x
    obtain ⟨σ, hσ⟩ := decodeFinite_surjective (b := β) d ⟨x.val, by rw [hβ]; exact ZMod.val_lt x⟩
    exact ⟨σ, by simp only; rw [hσ]; exact ZMod.natCast_zmod_val x⟩

/-- The normal-form representative of a pair of digit strings. -/
noncomputable def nfState (W : ℤ) (σA : FiniteRadixSpace βA DA) (σB : FiniteRadixSpace βB DB) :
    St n DA DB :=
  ((epsF S * W) • cell 0, lineState σA, lineState σB)

theorem cpValue_nf (W : ℤ) (σA : FiniteRadixSpace βA DA) (σB : FiniteRadixSpace βB DB) :
    cpValue ρ hρ c S DA DB βA βB (nfState ρ hρ c S DA DB βA βB W σA σB) =
      epsF S * W + epsA S * (decodeFinite βA DA σA : ℤ) + epsB S * (decodeFinite βB DB σB : ℤ) := by
  simp only [nfState, cpValue_mk, map_zsmul, value_cell, Fin.val_zero, weight_zero, smul_eq_mul,
    mul_one, lineValue_lineState]

/-- **Theorem 166 (the joint normal form).** If both branches are exactly sized
(`W^A_{d_A+1} = T_A`, `W^B_{d_B+1} = T_B`), every state of value `W` is equivalent to
`ε_F W` units at the ring root together with exactly one pair of digit strings — one on
each branch.

**fdrs.md**: Theorem 166 (the joint normal form). -/
theorem joint_normal_form (hA : placeValue βA (DA + 1) = S.tA) (hB : placeValue βB (DB + 1) = S.tB)
    (z : St n DA DB) :
    ∃! p : FiniteRadixSpace βA DA × FiniteRadixSpace βB DB,
      z - nfState ρ hρ c S DA DB βA βB (cpValue ρ hρ c S DA DB βA βB z) p.1 p.2 ∈
        cpLattice ρ hρ c S DA DB βA βB := by
  haveI : NeZero S.tA := ⟨by rw [← hA]; exact placeValue.ne_zero _⟩
  haveI : NeZero S.tB := ⟨by rw [← hB]; exact placeValue.ne_zero _⟩
  set W := cpValue ρ hρ c S DA DB βA βB z with hW
  obtain ⟨σA, hσA⟩ := (faithful_gen S.tA hA).2 ((W : ℤ) : ZMod S.tA)
  obtain ⟨σB, hσB⟩ := (faithful_gen S.tB hB).2 ((W : ℤ) : ZMod S.tB)
  simp only at hσA hσB
  have hmem : z - nfState ρ hρ c S DA DB βA βB W σA σB ∈ cpLattice ρ hρ c S DA DB βA βB := by
    rw [cp_equiv_iff, cpEv_apply, cpEv_apply, cpValue_nf, ← hW]
    refine (eq_of_three S ?_ ?_ ?_).symm <;> push_cast
    · rw [epsF_F, epsA_F, epsB_F]; ring
    · rw [epsF_A, epsA_A, epsB_A, hσA]; ring
    · rw [epsF_B, epsA_B, epsB_B, hσB]; ring
  refine ⟨(σA, σB), hmem, fun p hp => ?_⟩
  have hdiff := (cpLattice ρ hρ c S DA DB βA βB).sub_mem hp hmem
  rw [sub_sub_sub_cancel_left, cp_equiv_iff, cpEv_apply, cpEv_apply, cpValue_nf, cpValue_nf] at hdiff
  have hA' := zmod_of_mod (tA_dvd_mod S) hdiff
  have hB' := zmod_of_mod (tB_dvd_mod S) hdiff
  push_cast at hA' hB'
  rw [epsF_A, epsA_A, epsB_A] at hA'
  rw [epsF_B, epsA_B, epsB_B] at hB'
  simp only [zero_mul, one_mul, zero_add, add_zero] at hA' hB'
  refine Prod.ext ((faithful_gen S.tA hA).1 ?_) ((faithful_gen S.tB hB).1 ?_)
  · simp only; exact hA'.symm
  · simp only; exact hB'.symm

/-! ## Theorem 167: payloads -/

/-- **Theorem 167 (payloads are move-invariant).** States that differ by moves send the same
payload to every residue type.

**fdrs.md**: Theorem 167 (payloads and coupled evolution). -/
theorem payload_invariant {z z' : St n DA DB} (h : z - z' ∈ cpLattice ρ hρ c S DA DB βA βB) :
    ((cpValue ρ hρ c S DA DB βA βB z : ℤ) : ZMod S.tA) = (cpValue ρ hρ c S DA DB βA βB z' : ℤ) ∧
      ((cpValue ρ hρ c S DA DB βA βB z : ℤ) : ZMod S.tB) = (cpValue ρ hρ c S DA DB βA βB z' : ℤ) := by
  rw [cp_equiv_iff, cpEv_apply, cpEv_apply] at h
  exact ⟨zmod_of_mod (tA_dvd_mod S) h, zmod_of_mod (tB_dvd_mod S) h⟩

/-- **Theorem 167 (branches are opaque).** Content on branch `A` carries no payload to `B`.

**fdrs.md**: Theorem 167 (payloads and coupled evolution). -/
theorem opaque_AB (y : Fin (DA + 1) → ℤ) :
    ((cpValue ρ hρ c S DA DB βA βB (lineAEmb n DA DB y) : ℤ) : ZMod S.tB) = 0 := by
  rw [lineAEmb_apply, cpValue_mk, map_zero, map_zero]
  push_cast
  rw [epsA_B]; ring

/-- **Theorem 167 (branches are opaque).** Content on branch `B` carries no payload to `A`.

**fdrs.md**: Theorem 167 (payloads and coupled evolution). -/
theorem opaque_BA (y : Fin (DB + 1) → ℤ) :
    ((cpValue ρ hρ c S DA DB βA βB (lineBEmb n DA DB y) : ℤ) : ZMod S.tA) = 0 := by
  rw [lineBEmb_apply, cpValue_mk, map_zero, map_zero]
  push_cast
  rw [epsB_A]; ring

/-- **Theorem 167 (a branch's payload is its own content).**

**fdrs.md**: Theorem 167 (payloads and coupled evolution). -/
theorem payload_A_of_A (y : Fin (DA + 1) → ℤ) :
    ((cpValue ρ hρ c S DA DB βA βB (lineAEmb n DA DB y) : ℤ) : ZMod S.tA) =
      ((lineValue DA βA y : ℤ) : ZMod S.tA) := by
  rw [lineAEmb_apply, cpValue_mk, map_zero, map_zero]
  push_cast
  rw [epsA_A]; ring

end Complex

/-! ## Definition 240: coupled branch systems -/

/-- A **coupled branch system** (Definitions 95–98): a context and an extended radix oracle
per branch, and feed rules updating each branch's context from the payloads in flight to
**both** types (payload feedback, Definition 98).

**fdrs.md**: Definition 240 (coupled branch systems). -/
structure Coupling (CA CB : Type*) [ContextSpace CA] [ContextSpace CB] (tA tB : ℕ) where
  oracleA : ExtendedOracle CA
  oracleB : ExtendedOracle CB
  feedA : CA → ZMod tA → ZMod tB → CA
  feedB : CB → ZMod tA → ZMod tB → CB

namespace Coupling

variable {CA CB : Type*} [ContextSpace CA] [ContextSpace CB] {tA tB : ℕ} (K : Coupling CA CB tA tB)

/-- The payloads of an operation with residue `w`. -/
def payload (w : ℤ) : ZMod tA × ZMod tB := ((w : ZMod tA), (w : ZMod tB))

/-- One step: both contexts are fed the payloads. -/
def stepPay (p : CA × CB) (q : ZMod tA × ZMod tB) : CA × CB :=
  (K.feedA p.1 q.1 q.2, K.feedB p.2 q.1 q.2)

/-- The coupled evolution under a sequence of operation residues.

**fdrs.md**: Definition 240 (coupled branch systems). -/
def run (p : CA × CB) (ws : List ℤ) : CA × CB := (ws.map payload).foldl K.stepPay p

/-- The branch of a context of type `A` (read along the zero path, as in Definition 238). -/
def branchA (cA : CA) : RadixSeq := ⟨fun k => K.oracleA.radix (zeroPath k) cA, fun _ => K.oracleA.radix_ge_two _ _⟩
/-- The branch of a context of type `B`. -/
def branchB (cB : CB) : RadixSeq := ⟨fun k => K.oracleB.radix (zeroPath k) cB, fun _ => K.oracleB.radix_ge_two _ _⟩

end Coupling

/-- **Theorem 167 (coupled evolution is gauge-invariant).** Feeding the coupled system with
the values of two sequences of states that differ step by step by moves of the complex
gives the same evolution: carries and hops never change what a branch is told.

**fdrs.md**: Theorem 167 (payloads and coupled evolution). -/
theorem run_gauge {n : ℕ} (ρ : Fin (n + 1) → ℕ) (hρ : ∀ i, 2 ≤ ρ i) (c : ℤ) (S : TwoTiedSplit ρ hρ c)
    {DA DB : ℕ} {βA βB : RadixSeq} {CA CB : Type*} [ContextSpace CA] [ContextSpace CB]
    (K : Coupling CA CB S.tA S.tB) (p : CA × CB) {T : ℕ} (zs zs' : Fin T → St n DA DB)
    (h : ∀ t, zs t - zs' t ∈ cpLattice ρ hρ c S DA DB βA βB) :
    K.run p (List.ofFn fun t => cpValue ρ hρ c S DA DB βA βB (zs t)) =
      K.run p (List.ofFn fun t => cpValue ρ hρ c S DA DB βA βB (zs' t)) := by
  simp only [Coupling.run, List.map_ofFn]
  congr 2
  funext t
  simp only [Function.comp, Coupling.payload]
  obtain ⟨h1, h2⟩ := payload_invariant ρ hρ c S DA DB βA βB (h t)
  rw [h1, h2]

/-! ## Proposition 188: witnesses on (2, 3, 2), c = −18 -/

section Witness

/-- **Proposition 188 (the split `30 = 5 · 2 · 3`).**

**fdrs.md**: Proposition 188 (coupled-branch witnesses). -/
def split30 : TwoTiedSplit ring232 ring232_ge_two (-18) where
  free := 5
  tA := 2
  tB := 3
  laps := 1
  mul_eq := ring232_modulus_30.symm
  cop_fA := by decide
  cop_fB := by decide
  cop_AB := by decide
  free_coprime := Int.isCoprime_iff_gcd_eq_one.mpr (by decide)
  tA_dvd := ⟨-9, by norm_num⟩
  tB_dvd := ⟨-6, by norm_num⟩

/-- The cross-feeding rule: a branch records a radix of its own type when the **other** type
is in flight.

**fdrs.md**: Proposition 188 (coupled-branch witnesses). -/
def crossRec : Coupling (List ℕ) (List ℕ) 2 3 where
  oracleA := recordSys.oracle
  oracleB := recordSys.oracle
  feedA rec _ pB := if pB ≠ 0 then rec ++ [2] else rec
  feedB rec pA _ := if pA ≠ 0 then rec ++ [3] else rec

/-- **Proposition 188 (operation `5` grows both branches).** `5 ≡ 1 (mod 2)`,
`5 ≡ 2 (mod 3)`: both types are in flight.

**fdrs.md**: Proposition 188 (coupled-branch witnesses). -/
theorem cross_run_five : crossRec.run (([] : List ℕ), ([] : List ℕ)) ([5] : List ℤ) = ([2], [3]) := by
  decide

/-- **Proposition 188 (operation `15` grows only `B`).** `15 ≡ 0 (mod 3)`: no `B`-residue is
in flight, so `A` does not grow.

**fdrs.md**: Proposition 188 (coupled-branch witnesses). -/
theorem cross_run_fifteen : crossRec.run (([] : List ℕ), ([] : List ℕ)) ([15] : List ℤ) = ([], [3]) := by
  decide

/-- **Proposition 188 (gauge).** `35 ≡ 5 (mod 30)` drives the same evolution.

**fdrs.md**: Proposition 188 (coupled-branch witnesses). -/
theorem cross_run_gauge :
    crossRec.run (([] : List ℕ), ([] : List ℕ)) ([35] : List ℤ) = crossRec.run (([] : List ℕ), ([] : List ℕ)) ([5] : List ℤ) := by
  decide

/-- **Proposition 188 (after `5`, a unique joint normal form).** The branches grown by `5`
are exactly sized, so every state of the complex has a unique joint normal form.

**fdrs.md**: Proposition 188 (coupled-branch witnesses). -/
theorem cross_normal_form (z : St 2 0 0) :
    ∃! p : FiniteRadixSpace (crossRec.branchA ([2] : List ℕ)) 0 ×
        FiniteRadixSpace (crossRec.branchB ([3] : List ℕ)) 0,
      z - nfState ring232 ring232_ge_two (-18) split30 0 0 (crossRec.branchA ([2] : List ℕ)) (crossRec.branchB ([3] : List ℕ))
          (cpValue ring232 ring232_ge_two (-18) split30 0 0 (crossRec.branchA ([2] : List ℕ))
            (crossRec.branchB ([3] : List ℕ)) z) p.1 p.2 ∈
        cpLattice ring232 ring232_ge_two (-18) split30 0 0 (crossRec.branchA ([2] : List ℕ))
          (crossRec.branchB ([3] : List ℕ)) :=
  joint_normal_form ring232 ring232_ge_two (-18) split30 0 0 _ _ (by decide) (by decide) z

end Witness

end FdrsFormal.Modes.SyntheticPlace.CoupledBranches
