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

# Families of residue types: one branch per type, and a rule that grows them
(Phase 1 addendum, §3.21)

§3.20 coupled two branches. Here the tied part splits into an **arbitrary finite family**
of residue types `(T_i)_{i ∈ ι}`, pairwise coprime, `M = F · ∏_i T_i`, each with its own
branch — its own schedule, its own length, its own context — and a **rule** that grows the
branches from the operations alone.

- **The family complex** (Definition 241): ring cells, one line per type, ring carries,
  line carries, and one hop per type (`ε_i` units off the ring root onto branch `i`'s root).
- **It keeps the arithmetic** (Theorem 168): states modulo moves are exactly `ℤ/M`, for any
  family of schedules and lengths.
- **Family normal form** (Theorem 169): with every branch exactly sized
  (`W^i_{d_i+1} = T_i`), every state is equivalent to `ε_F W` units at the ring root plus
  exactly one digit string per branch.
- **Payloads and coupling** (Definition 242, Theorem 170): an operation's payload is its
  residue modulo every type; payloads are move-invariant, branches are mutually opaque
  (content on branch `i` sends nothing to any `j ≠ i`), and the coupled evolution is
  gauge-invariant.
- **The rule** (Definition 243, Theorem 171): *a branch records a radix of its own type
  whenever some other type is in flight.* From empty records, one operation grows branch
  `i` iff its residue is nonzero modulo some other type; an operation nonzero modulo at least
  two types grows **every** branch to exact size at once, so the complex acquires its family
  normal form in one step.

Witnesses on the ring `(2, 3, 5)` with wrap gain `−180` (`M = 210 = 7 · 2 · 3 · 5`, three
tied types): operation `1` grows all three branches to exact size, `15` (nonzero only
modulo `2`) leaves branch `2` empty and grows the other two, and `211 ≡ 1` drives the same
run as `1`.

Reuses `CoupledBranches.lean` (`idemOf`, `line_collapse`, `faithful_gen`, `zmod_of_mod`),
`CarryQuotient.lean`, `CarryHop.lean`, `ContextBranch.lean` (`lineState`),
`OperationBranch.lean` (`zeroPath`, `recordSys`), `BranchComplex.lean` (`dvd_of_zmod`),
`ContextDependent` and `Core/Finite/Bijection.lean`.

- **Definition 241** (`FamilySplit`, `eps`, `epsF`, `famLattice`, `famValue`): the family
  complex.
- **Theorem 168** (`ker_famEv`, `fam_equiv_iff`, `famQuotient`): it keeps the arithmetic.
- **Theorem 169** (`family_normal_form`): the family normal form.
- **Definition 242** (`FamCoupling`, `FamCoupling.run`): family coupling.
- **Theorem 170** (`fam_payload_invariant`, `famValue_lineE`, `fam_opaque`, `fam_own`,
  `fam_run_gauge`): payloads and coupled evolution.
- **Definition 243 / Theorem 171** (`crossRule`, `rule_one_step`, `rule_all_grow`,
  `rule_exact`, `rule_normal_form`): the rule.
- **Proposition 189** (`split210`, `rule_run_one`, `rule_run_fifteen`, `rule_run_gauge`):
  witnesses.

**Honest scope.** Elementary (CRT for a finite family and its idempotents). The corpus
contributes the family hop complex with its normal form, the reading of Definition 98's
payload feedback for any number of residue types, and a concrete growth rule with its
exact growth law. The split is supplied as data; branches fork on no digits; contexts are
deterministic.
-/

import FdrsFormal.Modes.SyntheticPlace.CoupledBranches

namespace FdrsFormal.Modes.SyntheticPlace.FamilyBranches

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite
open FdrsFormal.Modes.VariableRadix FdrsFormal.Modes.ContextDependent
open FdrsFormal.Modes.SyntheticPlace.RingUnrolling FdrsFormal.Modes.SyntheticPlace.CarryQuotient
open FdrsFormal.Modes.SyntheticPlace.CarryHop FdrsFormal.Modes.SyntheticPlace.ContextBranch
open FdrsFormal.Modes.SyntheticPlace.OperationBranch FdrsFormal.Modes.SyntheticPlace.CoupledBranches

/-! ## Definition 241: the family split and its idempotents -/

/-- A split of the modulus into a free part and a finite family of tied residue types,
pairwise coprime.

**fdrs.md**: Definition 241 (the family complex). -/
structure FamilySplit {n : ℕ} (ρ : Fin (n + 1) → ℕ) (hρ : ∀ i, 2 ≤ ρ i) (c : ℤ)
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  free : ℕ
  T : ι → ℕ
  laps : ℕ
  mul_eq : free * ∏ i, T i = modulus ρ hρ c
  cop_free : ∀ i, Nat.Coprime free (T i)
  cop_pair : ∀ i j, i ≠ j → Nat.Coprime (T i) (T j)
  free_coprime : IsCoprime c (free : ℤ)
  tied_dvd : ∀ i, (T i : ℤ) ∣ c ^ laps

section Split

variable {n : ℕ} {ρ : Fin (n + 1) → ℕ} {hρ : ∀ i, 2 ≤ ρ i} {c : ℤ}
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (S : FamilySplit ρ hρ c ι)

theorem cop_others (i : ι) :
    Nat.Coprime (S.T i) (S.free * ∏ j ∈ Finset.univ.erase i, S.T j) :=
  Nat.Coprime.mul_right (S.cop_free i).symm
    (Nat.Coprime.prod_right fun j hj => S.cop_pair i j (Finset.ne_of_mem_erase hj).symm)

/-- The idempotent of residue type `i`: `≡ 1 (mod T_i)`, `≡ 0` modulo `F` and every other
type. -/
noncomputable def eps (i : ι) : ℤ := idemOf (S.T i) _ (cop_others S i)

/-- The free idempotent. -/
noncomputable def epsF : ℤ :=
  idemOf S.free (∏ j, S.T j) (Nat.Coprime.prod_right fun j _ => S.cop_free j)

theorem eps_self (i : ι) : ((eps S i : ℤ) : ZMod (S.T i)) = 1 := idemOf_one _ _ _

theorem eps_other {i j : ι} (h : j ≠ i) : ((eps S i : ℤ) : ZMod (S.T j)) = 0 :=
  idemOf_zero _ _ _ (dvd_mul_of_dvd_right
    (Finset.dvd_prod_of_mem S.T (Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩)) _)

theorem eps_free (i : ι) : ((eps S i : ℤ) : ZMod S.free) = 0 :=
  idemOf_zero _ _ _ (dvd_mul_right _ _)

theorem epsF_free : ((epsF S : ℤ) : ZMod S.free) = 1 := idemOf_one _ _ _

theorem epsF_T (j : ι) : ((epsF S : ℤ) : ZMod (S.T j)) = 0 :=
  idemOf_zero _ _ _ (Finset.dvd_prod_of_mem S.T (Finset.mem_univ j))

theorem T_dvd_mod (i : ι) : S.T i ∣ modulus ρ hρ c :=
  ⟨S.free * ∏ j ∈ Finset.univ.erase i, S.T j, by
    rw [← S.mul_eq, ← Finset.mul_prod_erase Finset.univ S.T (Finset.mem_univ i)]; ring⟩

theorem free_dvd_mod : S.free ∣ modulus ρ hρ c := ⟨∏ j, S.T j, S.mul_eq.symm⟩

/-- Congruent modulo the free part and every type, congruent modulo `M`. -/
theorem eq_of_parts {x y : ℤ} (h0 : (x : ZMod S.free) = y) (h : ∀ i, (x : ZMod (S.T i)) = y) :
    (x : ZMod (modulus ρ hρ c)) = y := by
  rw [← sub_eq_zero, ← Int.cast_sub, CharP.intCast_eq_zero_iff (ZMod _) (modulus ρ hρ c),
    ← S.mul_eq, Nat.cast_mul, Nat.cast_prod]
  have hT : (∏ i, (S.T i : ℤ)) ∣ x - y :=
    Finset.prod_dvd_of_coprime
      (fun i _ j _ hij => Nat.isCoprime_iff_coprime.mpr (S.cop_pair i j hij))
      (fun i _ => BranchComplex.dvd_of_zmod (h i))
  have hc : IsCoprime (S.free : ℤ) (∏ i, (S.T i : ℤ)) :=
    IsCoprime.prod_right fun i _ => Nat.isCoprime_iff_coprime.mpr (S.cop_free i)
  exact hc.mul_dvd (BranchComplex.dvd_of_zmod h0) hT

end Split

/-! ## Definition 241: the family complex -/

/-- States of the family complex: ring cells and one line per type. -/
abbrev FSt {ι : Type*} (n : ℕ) (D : ι → ℕ) := (Fin (n + 1) → ℤ) × ((i : ι) → Fin (D i + 1) → ℤ)

/-- Ring states inside the family complex. -/
def ringE {ι : Type*} (n : ℕ) (D : ι → ℕ) : (Fin (n + 1) → ℤ) →+ FSt n D := AddMonoidHom.inl _ _

/-- Branch-`i` states inside the family complex. -/
def lineE {ι : Type*} [DecidableEq ι] (n : ℕ) (D : ι → ℕ) (i : ι) :
    (Fin (D i + 1) → ℤ) →+ FSt n D :=
  (AddMonoidHom.inr _ _).comp (AddMonoidHom.single (fun i => Fin (D i + 1) → ℤ) i)

theorem ringE_apply {ι : Type*} {n : ℕ} {D : ι → ℕ} (x : Fin (n + 1) → ℤ) :
    ringE n D x = (x, 0) := rfl

theorem lineE_apply {ι : Type*} [DecidableEq ι] {n : ℕ} {D : ι → ℕ} (i : ι) (y : Fin (D i + 1) → ℤ) :
    lineE n D i y = (0, Pi.single i y) := rfl

section Complex

variable {n : ℕ} (ρ : Fin (n + 1) → ℕ) (hρ : ∀ i, 2 ≤ ρ i) (c : ℤ)
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (S : FamilySplit ρ hρ c ι)
variable (D : ι → ℕ) (β : ι → RadixSeq)

/-- The hop onto branch `i`. -/
noncomputable def famHop (i : ι) : FSt n D := (-(eps S i) • cell 0, Pi.single i (lineCell (D i) 0))

/-- The move lattice of the family complex: ring carries, line carries on every branch, and
one hop per branch.

**fdrs.md**: Definition 241 (the family complex). -/
noncomputable def famLattice : AddSubgroup (FSt n D) :=
  AddSubgroup.closure
    (Set.range (fun k => ringE n D (carryVec ρ c k)) ∪
      Set.range (fun p : (i : ι) × Fin (D i) => lineE n D p.1 (lineCarry (D p.1) (β p.1) p.2)) ∪
      Set.range (famHop ρ hρ c S D))

/-- The value of a family state: `Σ x_k B_k + Σ_i ε_i Σ_k y^i_k W^i_k`.

**fdrs.md**: Definition 241 (the family complex). -/
noncomputable def famValue : FSt n D →+ ℤ :=
  AddMonoidHom.mk' (fun z => value ρ hρ z.1 + ∑ i, eps S i * lineValue (D i) (β i) (z.2 i))
    (by
      intro a b
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add, mul_add,
        Finset.sum_add_distrib]
      ring)

/-- The value modulo `M`. -/
noncomputable def famEv : FSt n D →+ ZMod (modulus ρ hρ c) :=
  (Int.castAddHom _).comp (famValue ρ hρ c S D β)

theorem famValue_mk (x : Fin (n + 1) → ℤ) (y : (i : ι) → Fin (D i + 1) → ℤ) :
    famValue ρ hρ c S D β (x, y) = value ρ hρ x + ∑ i, eps S i * lineValue (D i) (β i) (y i) := rfl

theorem famEv_apply (z : FSt n D) :
    famEv ρ hρ c S D β z = ((famValue ρ hρ c S D β z : ℤ) : ZMod (modulus ρ hρ c)) := rfl

theorem famValue_ringE (x : Fin (n + 1) → ℤ) :
    famValue ρ hρ c S D β (ringE n D x) = value ρ hρ x := by
  rw [ringE_apply, famValue_mk]
  simp

theorem famValue_lineE (i : ι) (y : Fin (D i + 1) → ℤ) :
    famValue ρ hρ c S D β (lineE n D i y) = eps S i * lineValue (D i) (β i) y := by
  rw [lineE_apply, famValue_mk, map_zero, zero_add, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hj; rw [Pi.single_eq_of_ne hj, map_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

/-! ## Theorem 168: the family complex keeps the arithmetic -/

theorem fam_ring_mem {z : Fin (n + 1) → ℤ} (hz : z ∈ carryLattice ρ c) :
    ringE n D z ∈ famLattice ρ hρ c S D β := by
  have : carryLattice ρ c ≤ (famLattice ρ hρ c S D β).comap (ringE n D) := by
    rw [carryLattice, AddSubgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    exact AddSubgroup.subset_closure (Or.inl (Or.inl ⟨k, rfl⟩))
  exact this hz

theorem fam_line_mem (i : ι) (y : Fin (D i + 1) → ℤ) :
    lineE n D i (y - lineValue (D i) (β i) y • lineCell (D i) 0) ∈ famLattice ρ hρ c S D β :=
  line_collapse (β i) ((famLattice ρ hρ c S D β).comap (lineE n D i))
    (fun k => AddSubgroup.subset_closure (Or.inl (Or.inr ⟨⟨i, k⟩, rfl⟩))) y

theorem fam_hop_mem (i : ι) : famHop ρ hρ c S D i ∈ famLattice ρ hρ c S D β :=
  AddSubgroup.subset_closure (Or.inr ⟨i, rfl⟩)

/-- Every family state is equivalent to its value placed at the ring root. -/
theorem fam_sub_value_mem (z : FSt n D) :
    z - ringE n D (famValue ρ hρ c S D β z • cell 0) ∈ famLattice ρ hρ c S D β := by
  obtain ⟨x, y⟩ := z
  set L := famLattice ρ hρ c S D β
  have hterm : ∀ i, lineE n D i (y i - lineValue (D i) (β i) (y i) • lineCell (D i) 0) +
      lineValue (D i) (β i) (y i) • famHop ρ hρ c S D i =
      ((-(eps S i * lineValue (D i) (β i) (y i))) • cell 0, Pi.single i (y i)) := by
    intro i
    rw [lineE_apply, famHop]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.smul_fst, smul_neg, smul_smul, neg_smul, zero_add]
      rw [mul_comm]
    · simp only [Prod.snd_add, Prod.smul_snd]
      funext j
      by_cases hj : j = i
      · subst hj; simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same]; abel
      · simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hj, smul_zero, add_zero]
  have hmem : ringE n D (x - value ρ hρ x • cell 0) +
      ∑ i, (lineE n D i (y i - lineValue (D i) (β i) (y i) • lineCell (D i) 0) +
        lineValue (D i) (β i) (y i) • famHop ρ hρ c S D i) ∈ L :=
    L.add_mem (fam_ring_mem ρ hρ c S D β (sub_value_mem ρ hρ c x))
      (L.sum_mem fun i _ => L.add_mem (fam_line_mem ρ hρ c S D β i (y i))
        (L.zsmul_mem (fam_hop_mem ρ hρ c S D β i) _))
  convert hmem using 1
  simp only [hterm]
  rw [ringE_apply, ringE_apply, famValue_mk]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_sub, Prod.fst_add, Prod.fst_sum, add_smul, Finset.sum_smul, neg_smul,
      Finset.sum_neg_distrib]
    abel
  · simp only [Prod.snd_sub, Prod.snd_add, Prod.snd_sum, sub_zero, zero_add]
    exact (Finset.univ_sum_single y).symm

/-- **Theorem 168 (the family complex keeps the arithmetic: kernel).**

**fdrs.md**: Theorem 168 (the family complex keeps the arithmetic). -/
theorem ker_famEv : (famEv ρ hρ c S D β).ker = famLattice ρ hρ c S D β := by
  apply le_antisymm
  · intro z hz
    rw [AddMonoidHom.mem_ker, famEv_apply,
      CharP.intCast_eq_zero_iff (ZMod (modulus ρ hρ c)) (modulus ρ hρ c)] at hz
    have hring : famValue ρ hρ c S D β z • cell 0 ∈ carryLattice ρ c := by
      rw [← ker_ev ρ hρ c, AddMonoidHom.mem_ker, ev_eq_zero_iff, map_zsmul, value_cell,
        Fin.val_zero, weight_zero, smul_eq_mul, mul_one, ← Int.natAbs_dvd, ← modulus]
      exact hz
    have := (famLattice ρ hρ c S D β).add_mem (fam_sub_value_mem ρ hρ c S D β z)
      (fam_ring_mem ρ hρ c S D β hring)
    rwa [sub_add_cancel] at this
  · rw [famLattice, AddSubgroup.closure_le]
    rintro z ((⟨k, rfl⟩ | ⟨⟨i, k⟩, rfl⟩) | ⟨i, rfl⟩) <;>
      rw [SetLike.mem_coe, AddMonoidHom.mem_ker, famEv_apply,
        CharP.intCast_eq_zero_iff (ZMod (modulus ρ hρ c)) (modulus ρ hρ c)]
    · rw [famValue_ringE]
      have := (ker_ev ρ hρ c).ge
        (AddSubgroup.subset_closure ⟨k, rfl⟩ : carryVec ρ c k ∈ carryLattice ρ c)
      rwa [AddMonoidHom.mem_ker, ev_eq_zero_iff, ← Int.natAbs_dvd, ← modulus] at this
    · rw [famValue_lineE]
      convert dvd_zero (modulus ρ hρ c : ℤ) using 1
      simp only [lineCarry, map_sub, map_zsmul, lineValue_cell, Fin.val_succ, Fin.val_castSucc,
        lineWeight_succ, smul_eq_mul]
      ring
    · convert dvd_zero (modulus ρ hρ c : ℤ) using 1
      have h := famValue_lineE ρ hρ c S D β i (lineCell (D i) 0)
      have hr := famValue_ringE ρ hρ c S D β (-(eps S i) • cell 0)
      have hsplit : famHop ρ hρ c S D i = ringE n D (-(eps S i) • cell 0) + lineE n D i (lineCell (D i) 0) := by
        rw [famHop, ringE_apply, lineE_apply]
        exact Prod.ext (by simp) (by simp)
      rw [hsplit, map_add, h, hr, map_zsmul, value_cell, lineValue_cell, Fin.val_zero, Fin.val_zero,
        weight_zero, placeValue.zero, Nat.cast_one, smul_eq_mul]
      ring

/-- **Theorem 168 (equivalence in the family complex).**

**fdrs.md**: Theorem 168 (the family complex keeps the arithmetic). -/
theorem fam_equiv_iff (z z' : FSt n D) :
    z - z' ∈ famLattice ρ hρ c S D β ↔ famEv ρ hρ c S D β z = famEv ρ hρ c S D β z' := by
  rw [← ker_famEv, AddMonoidHom.mem_ker, map_sub, sub_eq_zero]

theorem famEv_surjective : Function.Surjective (famEv ρ hρ c S D β) := by
  intro w
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective w
  refine ⟨ringE n D (k • cell 0), ?_⟩
  rw [famEv_apply, famValue_ringE, map_zsmul, value_cell, Fin.val_zero, weight_zero, smul_eq_mul,
    mul_one]

/-- **Theorem 168 (the family quotient).** States modulo all moves are `ℤ/M`, for any family of
line schedules and lengths.

**fdrs.md**: Theorem 168 (the family complex keeps the arithmetic). -/
noncomputable def famQuotient : FSt n D ⧸ famLattice ρ hρ c S D β ≃+ ZMod (modulus ρ hρ c) :=
  (QuotientAddGroup.quotientAddEquivOfEq (ker_famEv ρ hρ c S D β).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (famEv_surjective ρ hρ c S D β))

/-! ## Theorem 169: the family normal form -/

/-- The normal-form representative of a family of digit strings. -/
noncomputable def famNF (W : ℤ) (σ : (i : ι) → FiniteRadixSpace (β i) (D i)) : FSt n D :=
  ((epsF S * W) • cell 0, fun i => lineState (σ i))

theorem famValue_nf (W : ℤ) (σ : (i : ι) → FiniteRadixSpace (β i) (D i)) :
    famValue ρ hρ c S D β (famNF ρ hρ c S D β W σ) =
      epsF S * W + ∑ i, eps S i * (decodeFinite (β i) (D i) (σ i) : ℤ) := by
  simp only [famNF, famValue_mk, map_zsmul, value_cell, Fin.val_zero, weight_zero, smul_eq_mul,
    mul_one, lineValue_lineState]

/-- The value of a normal form, read on type `j`, is its `j`-th digit string. -/
theorem nf_on_type (W : ℤ) (σ : (i : ι) → FiniteRadixSpace (β i) (D i)) (j : ι) :
    ((famValue ρ hρ c S D β (famNF ρ hρ c S D β W σ) : ℤ) : ZMod (S.T j)) =
      ((decodeFinite (β j) (D j) (σ j) : ℕ) : ZMod (S.T j)) := by
  rw [famValue_nf]
  push_cast
  rw [epsF_T, zero_mul, zero_add, Finset.sum_eq_single j]
  · rw [eps_self, one_mul]
  · intro i _ hi; rw [eps_other S (Ne.symm hi), zero_mul]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem nf_on_free (W : ℤ) (σ : (i : ι) → FiniteRadixSpace (β i) (D i)) :
    ((famValue ρ hρ c S D β (famNF ρ hρ c S D β W σ) : ℤ) : ZMod S.free) = (W : ZMod S.free) := by
  rw [famValue_nf]
  push_cast
  rw [epsF_free, one_mul, Finset.sum_eq_zero, add_zero]
  intro i _; rw [eps_free, zero_mul]

/-- **Theorem 169 (the family normal form).** If every branch is exactly sized
(`W^i_{d_i+1} = T_i`), every state of value `W` is equivalent to `ε_F W` units at the ring
root together with exactly one family of digit strings — one per branch.

**fdrs.md**: Theorem 169 (the family normal form). -/
theorem family_normal_form (hfit : ∀ i, placeValue (β i) (D i + 1) = S.T i) (z : FSt n D) :
    ∃! σ : (i : ι) → FiniteRadixSpace (β i) (D i),
      z - famNF ρ hρ c S D β (famValue ρ hρ c S D β z) σ ∈ famLattice ρ hρ c S D β := by
  have hnz : ∀ i, NeZero (S.T i) := fun i => ⟨by rw [← hfit i]; exact placeValue.ne_zero _⟩
  set W := famValue ρ hρ c S D β z with hW
  have hsurj : ∀ i, ∃ σi : FiniteRadixSpace (β i) (D i),
      ((decodeFinite (β i) (D i) σi : ℕ) : ZMod (S.T i)) = ((W : ℤ) : ZMod (S.T i)) := fun i =>
    (faithful_gen (S.T i) (hfit i)).2 _
  choose σ hσ using hsurj
  have hmem : z - famNF ρ hρ c S D β W σ ∈ famLattice ρ hρ c S D β := by
    rw [fam_equiv_iff, famEv_apply, famEv_apply, ← hW]
    refine (eq_of_parts S ?_ fun j => ?_).symm
    · exact nf_on_free ρ hρ c S D β W σ
    · rw [nf_on_type, hσ j]
  refine ⟨σ, hmem, fun σ' hσ' => ?_⟩
  have hdiff := (famLattice ρ hρ c S D β).sub_mem hσ' hmem
  rw [sub_sub_sub_cancel_left, fam_equiv_iff, famEv_apply, famEv_apply] at hdiff
  funext j
  have hj := zmod_of_mod (T_dvd_mod S j) hdiff
  rw [nf_on_type, nf_on_type] at hj
  exact (faithful_gen (S.T j) (hfit j)).1 hj.symm

/-! ## Theorem 170: payloads -/

/-- **Theorem 170 (payloads are move-invariant).**

**fdrs.md**: Theorem 170 (payloads and coupled evolution, families). -/
theorem fam_payload_invariant {z z' : FSt n D} (h : z - z' ∈ famLattice ρ hρ c S D β) (i : ι) :
    ((famValue ρ hρ c S D β z : ℤ) : ZMod (S.T i)) = (famValue ρ hρ c S D β z' : ℤ) := by
  rw [fam_equiv_iff, famEv_apply, famEv_apply] at h
  exact zmod_of_mod (T_dvd_mod S i) h

/-- **Theorem 170 (branches are mutually opaque).** Content on branch `i` sends no payload to
any other type.

**fdrs.md**: Theorem 170 (payloads and coupled evolution, families). -/
theorem fam_opaque {i j : ι} (h : j ≠ i) (y : Fin (D i + 1) → ℤ) :
    ((famValue ρ hρ c S D β (lineE n D i y) : ℤ) : ZMod (S.T j)) = 0 := by
  rw [famValue_lineE]; push_cast; rw [eps_other S h, zero_mul]

/-- **Theorem 170 (a branch's payload is its own content).**

**fdrs.md**: Theorem 170 (payloads and coupled evolution, families). -/
theorem fam_own (i : ι) (y : Fin (D i + 1) → ℤ) :
    ((famValue ρ hρ c S D β (lineE n D i y) : ℤ) : ZMod (S.T i)) =
      ((lineValue (D i) (β i) y : ℤ) : ZMod (S.T i)) := by
  rw [famValue_lineE]; push_cast; rw [eps_self, one_mul]

end Complex

/-! ## Definition 242: family coupling -/

/-- A **family coupling** (Definitions 95–98 for any number of branches): an extended radix
oracle per branch, and a feed rule updating each branch's context from the whole payload
vector in flight.

**fdrs.md**: Definition 242 (family coupling). -/
structure FamCoupling (ι : Type*) (C : Type*) [ContextSpace C] (T : ι → ℕ) where
  oracle : ι → ExtendedOracle C
  feed : ι → C → ((j : ι) → ZMod (T j)) → C

namespace FamCoupling

variable {ι C : Type*} [ContextSpace C] {T : ι → ℕ} (K : FamCoupling ι C T)

/-- The payload vector of an operation of residue `w`. -/
def payload (w : ℤ) : (j : ι) → ZMod (T j) := fun j => (w : ZMod (T j))

/-- One step: every branch's context is fed the payload vector. -/
def step (ctx : ι → C) (q : (j : ι) → ZMod (T j)) : ι → C := fun i => K.feed i (ctx i) q

/-- The coupled evolution under a sequence of operation residues.

**fdrs.md**: Definition 242 (family coupling). -/
def run (ctx : ι → C) (ws : List ℤ) : ι → C := (ws.map payload).foldl K.step ctx

/-- The branch of a context of type `i`, read along the zero path (Definition 238). -/
def branch (i : ι) (cx : C) : RadixSeq :=
  ⟨fun k => (K.oracle i).radix (zeroPath k) cx, fun _ => (K.oracle i).radix_ge_two _ _⟩

end FamCoupling

/-- **Theorem 170 (coupled evolution is gauge-invariant, families).**

**fdrs.md**: Theorem 170 (payloads and coupled evolution, families). -/
theorem fam_run_gauge {n : ℕ} (ρ : Fin (n + 1) → ℕ) (hρ : ∀ i, 2 ≤ ρ i) (c : ℤ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (S : FamilySplit ρ hρ c ι) {D : ι → ℕ}
    {β : ι → RadixSeq} {C : Type*} [ContextSpace C] (K : FamCoupling ι C S.T) (ctx : ι → C)
    {N : ℕ} (zs zs' : Fin N → FSt n D) (h : ∀ t, zs t - zs' t ∈ famLattice ρ hρ c S D β) :
    K.run ctx (List.ofFn fun t => famValue ρ hρ c S D β (zs t)) =
      K.run ctx (List.ofFn fun t => famValue ρ hρ c S D β (zs' t)) := by
  simp only [FamCoupling.run, List.map_ofFn]
  congr 2
  funext t
  funext i
  simp only [Function.comp, FamCoupling.payload]
  exact fam_payload_invariant ρ hρ c S D β (h t) i

/-! ## Definition 243 and Theorem 171: the rule -/

/-- **The rule**: branch `i` records a radix of its own type `T_i` whenever some other type
is in flight (its payload is nonzero).

**fdrs.md**: Definition 243 (the cross-feeding rule). -/
def crossRule {ι : Type*} [Fintype ι] [DecidableEq ι] (T : ι → ℕ) : FamCoupling ι (List ℕ) T where
  oracle _ := recordSys.oracle
  feed i rec q := if ∃ j, j ≠ i ∧ q j ≠ 0 then rec ++ [T i] else rec

section Rule

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (T : ι → ℕ)

/-- **Theorem 171 (the growth law).** From empty records, one operation of residue `w` grows
branch `i` (to the record `[T_i]`) iff `w` is nonzero modulo some other type.

**fdrs.md**: Theorem 171 (the rule). -/
theorem rule_one_step (w : ℤ) :
    (crossRule T).run (fun _ => ([] : List ℕ)) ([w] : List ℤ) =
      fun i => if ∃ j, j ≠ i ∧ (w : ZMod (T j)) ≠ 0 then ([T i] : List ℕ) else [] := by
  funext i
  simp only [FamCoupling.run, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
    FamCoupling.step, crossRule, FamCoupling.payload, List.nil_append]

/-- **Theorem 171 (an operation hitting two types grows every branch).**

**fdrs.md**: Theorem 171 (the rule). -/
theorem rule_all_grow (w : ℤ) {j k : ι} (hjk : j ≠ k) (hj : (w : ZMod (T j)) ≠ 0)
    (hk : (w : ZMod (T k)) ≠ 0) :
    (crossRule T).run (fun _ => ([] : List ℕ)) ([w] : List ℤ) = fun i => ([T i] : List ℕ) := by
  rw [rule_one_step]
  funext i
  rw [if_pos]
  by_cases hij : j = i
  · exact ⟨k, by rw [← hij]; exact hjk.symm, hk⟩
  · exact ⟨j, hij, hj⟩

/-- **Theorem 171 (a grown branch is exactly sized).** The branch recorded as `[T_i]` has
weight `T_i` at depth `1` (for `T_i ≥ 2`).

**fdrs.md**: Theorem 171 (the rule). -/
theorem rule_exact (h2 : ∀ i, 2 ≤ T i) (i : ι) :
    placeValue ((crossRule T).branch i ([T i] : List ℕ)) (0 + 1) = T i := by
  show 1 * max 2 (([T i] : List ℕ).getD 0 2) = T i
  simp [max_eq_right (h2 i)]

/-- **Theorem 171 (one operation hitting two types gives the family normal form).** After an
operation nonzero modulo two distinct types, every branch is exactly sized, so every state of
the family complex built from the grown branches has a unique family normal form.

**fdrs.md**: Theorem 171 (the rule). -/
theorem rule_normal_form {n : ℕ} (ρ : Fin (n + 1) → ℕ) (hρ : ∀ i, 2 ≤ ρ i) (c : ℤ)
    (S : FamilySplit ρ hρ c ι) (h2 : ∀ i, 2 ≤ S.T i) (z : FSt n (fun _ : ι => 0)) :
    ∃! σ : (i : ι) → FiniteRadixSpace ((crossRule S.T).branch i ([S.T i] : List ℕ)) 0,
      z - famNF ρ hρ c S (fun _ => 0) (fun i => (crossRule S.T).branch i ([S.T i] : List ℕ))
          (famValue ρ hρ c S (fun _ => 0) (fun i => (crossRule S.T).branch i ([S.T i] : List ℕ)) z) σ ∈
        famLattice ρ hρ c S (fun _ => 0) (fun i => (crossRule S.T).branch i ([S.T i] : List ℕ)) :=
  family_normal_form ρ hρ c S _ _ (fun i => rule_exact S.T h2 i) z

end Rule

/-! ## Proposition 189: three residue types on the ring (2, 3, 5) -/

section Witness

/-- The ring with radices `(2, 3, 5)`: lap value `30`. -/
def ring235 : Fin 3 → ℕ := ![2, 3, 5]

theorem ring235_ge_two (i : Fin 3) : 2 ≤ ring235 i := by
  fin_cases i <;> decide

theorem ring235_modulus : modulus ring235 ring235_ge_two (-180) = 210 := rfl

/-- **Proposition 189 (three residue types).** `210 = 7 · 2 · 3 · 5`: free part `7`, tied
types `2, 3, 5` (each dividing `−180`).

**fdrs.md**: Proposition 189 (three residue types). -/
def split210 : FamilySplit ring235 ring235_ge_two (-180) (Fin 3) where
  free := 7
  T := ![2, 3, 5]
  laps := 1
  mul_eq := by rw [ring235_modulus, Fin.prod_univ_three]; rfl
  cop_free := by decide
  cop_pair := by decide
  free_coprime := Int.isCoprime_iff_gcd_eq_one.mpr (by decide)
  tied_dvd := by intro i; fin_cases i <;> decide

/-- **Proposition 189 (operation `1` grows all three branches).**

**fdrs.md**: Proposition 189 (three residue types). -/
theorem rule_run_one :
    (crossRule split210.T).run (fun _ => ([] : List ℕ)) ([1] : List ℤ) =
      fun i => ([split210.T i] : List ℕ) :=
  rule_all_grow split210.T 1 (j := 0) (k := 1) (by decide) (by decide) (by decide)

/-- **Proposition 189 (operation `15` leaves branch `2` empty).** `15` is nonzero only
modulo `2`: no other type is in flight for branch `2`, while branches `3` and `5` see the
`2`-residue and grow.

**fdrs.md**: Proposition 189 (three residue types). -/
theorem rule_run_fifteen :
    (crossRule split210.T).run (fun _ => ([] : List ℕ)) ([15] : List ℤ) =
      ![([] : List ℕ), [3], [5]] := by
  rw [rule_one_step]
  funext i
  fin_cases i <;> decide

/-- **Proposition 189 (gauge).** `211 ≡ 1 (mod 210)` drives the same run as `1`.

**fdrs.md**: Proposition 189 (three residue types). -/
theorem rule_run_gauge :
    (crossRule split210.T).run (fun _ => ([] : List ℕ)) ([211] : List ℤ) =
      (crossRule split210.T).run (fun _ => ([] : List ℕ)) ([1] : List ℤ) := by
  rw [rule_one_step, rule_one_step]
  funext i
  fin_cases i <;> decide

end Witness

end FdrsFormal.Modes.SyntheticPlace.FamilyBranches
