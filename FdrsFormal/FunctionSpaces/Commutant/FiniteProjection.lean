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

# Finite Block Projections

This file defines block projection operators P_L^(k) and detail operators Δ_L^(k)
on finite horizon function spaces.

## Mathematical Content (fdrs.md lines 812-849)

**Definition 27 (finite block projection)**:
For 1 ≤ L ≤ k+1, define P_L^(k): T^(k)(V) → T^(k)(V) by block-averaging:
  (P_L^(k) f)(τ) = (1/|U_k(π_L(τ))|) ∑_{σ ∈ U_k(π_L(τ))} f(σ)
                 = (1/m_{k,L}) ∑_{σ ∈ U_k(π_L(τ))} f(σ)

Equivalently, P_L^(k) = E_μk[· | F_{k,L}].

**Definition 28 (finite detail operator)**:
For 1 ≤ L ≤ k, define
  Δ_L^(k) f := P_{L+1}^(k) f - P_L^(k) f

**Proposition 21 (projection algebra)**:
1. (P_L^(k))² = P_L^(k) (idempotent)
2. P_L^(k) P_M^(k) = P_L^(k) for L ≤ M (tower)
3. P_N^(k) f = P_1^(k) f + ∑_{L=1}^{N-1} Δ_L^(k) f (telescoping)

## Implementation Notes

- Uses Finset.sum for explicit block averaging (computably)
- Cardinality m_{k,L} = B_{k+1}/B_L from FiniteHorizon
- Properties proved purely algebraically (no measure theory needed)

## References

- fdrs.md, Phase 2 Fragment 2 (lines 812-849)
- THEOREM_MAPPING.md, FunctionSpaces/Commutant section
-/

import FdrsFormal.FunctionSpaces.Commutant.FiniteHorizon

open scoped Classical

namespace FdrsFormal.FunctionSpaces.Commutant

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite
open FdrsFormal.FunctionSpaces.Basic

/-!
## Finite Block Projection Definition
-/

section Definition

variable {b : RadixSeq} {V : Type*}

/--
The finite block projection operator P_L^(k).

**fdrs.md Definition 27**: P_L^(k) f averages f over each cylinder U_k(s).

For τ in cylinder U_k(s), (P_L^(k) f)(τ) is the average of f over U_k(s).
-/
noncomputable def finiteBlockProjection (b : RadixSeq) (k L : ℕ) (hLk : L ≤ k + 1)
    [AddCommGroup V] [Module ℝ V]
    (f : FiniteRadixSpace b k → V) : FiniteRadixSpace b k → V :=
  fun τ =>
    let s := finitePrefix b L τ hLk
    let m_kL := placeValue b (k + 1) / placeValue b L
    (m_kL : ℝ)⁻¹ • ∑ σ : (finiteCylinderSet b k L hLk s), f σ.val

/-- Notation for finite block projection -/
scoped notation "P[" k "," L "]" => finiteBlockProjection _ k L _

/--
The finite detail operator Δ_L^(k).

**fdrs.md Definition 28**: Δ_L^(k) := P_{L+1}^(k) - P_L^(k)
-/
noncomputable def finiteDetailOperator (b : RadixSeq) (k L : ℕ) (hLk : L < k + 1)
    [AddCommGroup V] [Module ℝ V]
    (f : FiniteRadixSpace b k → V) : FiniteRadixSpace b k → V :=
  finiteBlockProjection b k (L + 1) (by omega) f - finiteBlockProjection b k L (by omega) f

/-- Notation for finite detail operator -/
scoped notation "Δ[" k "," L "]" => finiteDetailOperator _ k L _

end Definition

/-!
## Basic Properties
-/

section BasicProperties

variable {b : RadixSeq} {V : Type*}
variable [AddCommGroup V] [Module ℝ V]

/--
P_L^(k) produces block-constant functions.

The output depends only on which cylinder the input is in.
-/
theorem finiteBlockProjection_isBlockConstant (k L : ℕ) (hLk : L ≤ k + 1)
    (f : FiniteRadixSpace b k → V) :
    ∀ τ τ' : FiniteRadixSpace b k,
      finitePrefix b L τ hLk = finitePrefix b L τ' hLk →
      finiteBlockProjection b k L hLk f τ = finiteBlockProjection b k L hLk f τ' := by
  intro τ τ' h_prefix
  simp only [finiteBlockProjection]
  rw [h_prefix]

/--
P_L^(k) of a constant function is that constant.
-/
theorem finiteBlockProjection_const (k L : ℕ) (hLk : L ≤ k + 1) (c : V) :
    finiteBlockProjection b k L hLk (fun _ => c) = fun _ => c := by
  ext τ
  simp only [finiteBlockProjection]
  -- Sum of m_{k,L} copies of c, divided by m_{k,L}, equals c
  rw [Finset.sum_const]
  -- Now: (m_kL : ℝ)⁻¹ • (card • c) = c
  -- The cardinality equals m_kL by finiteCylinder_card
  have h_card : Finset.univ.card = placeValue b (k + 1) / placeValue b L :=
    finiteCylinder_card k L hLk (finitePrefix b L τ hLk)
  rw [h_card]
  -- Convert nsmul to smul with cast: n • x = (n : R) • x
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  -- Now: (m_kL : ℝ)⁻¹ * (m_kL : ℝ) • c = c, where m_kL = B_{k+1}/B_L
  have h_ne : ((placeValue b (k + 1) / placeValue b L : ℕ) : ℝ) ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    intro h_zero
    -- If division is 0, then B_{k+1} < B_L
    have h_lt : placeValue b (k + 1) < placeValue b L := Nat.div_eq_zero_iff.mp h_zero |>.resolve_left (placeValue.ne_zero L)
    -- But L ≤ k+1 implies B_L ≤ B_{k+1}
    have h_le : placeValue b L ≤ placeValue b (k + 1) := placeValue.mono hLk
    -- Contradiction
    omega
  -- Cancel: a⁻¹ * a • c = 1 • c = c
  field_simp [h_ne]
  rw [one_smul]

/--
P_L^(k) is linear.
-/
theorem finiteBlockProjection_add (k L : ℕ) (hLk : L ≤ k + 1)
    (f g : FiniteRadixSpace b k → V) :
    finiteBlockProjection b k L hLk (f + g) =
    finiteBlockProjection b k L hLk f + finiteBlockProjection b k L hLk g := by
  ext τ
  simp only [finiteBlockProjection, Pi.add_apply]
  rw [← smul_add]
  congr 1
  exact Finset.sum_add_distrib

theorem finiteBlockProjection_smul (k L : ℕ) (hLk : L ≤ k + 1) (r : ℝ)
    (f : FiniteRadixSpace b k → V) :
    finiteBlockProjection b k L hLk (r • f) = r • finiteBlockProjection b k L hLk f := by
  ext τ
  simp only [finiteBlockProjection, Pi.smul_apply]
  -- Need: (m⁻¹ • ∑ σ, r • f σ) = r • (m⁻¹ • ∑ σ, f σ)
  -- Pull r out of the sum, then use smul commutativity
  rw [← Finset.smul_sum]
  rw [smul_comm]

/--
P_L^(k) fixes block-constant functions: if f is L-block-constant, then P_L f = f.

This is the finite analogue of blockProjection_fixedPoint.
-/
theorem finiteBlockProjection_fixedPoint (k L : ℕ) (hLk : L ≤ k + 1)
    (f : FiniteRadixSpace b k → V)
    (h_bc : ∀ τ τ', finitePrefix b L τ hLk = finitePrefix b L τ' hLk → f τ = f τ') :
    finiteBlockProjection b k L hLk f = f := by
  ext τ
  simp only [finiteBlockProjection]
  -- All values equal f τ
  have h_eq : ∀ σ : finiteCylinderSet b k L hLk (finitePrefix b L τ hLk),
      f σ.val = f τ := fun σ => h_bc σ.val τ (funext σ.property)
  -- Rewrite sum to all f τ
  have h_sum : ∑ σ : finiteCylinderSet b k L hLk (finitePrefix b L τ hLk), f σ.val =
               ∑ σ : finiteCylinderSet b k L hLk (finitePrefix b L τ hLk), f τ := by
    refine Finset.sum_congr rfl (fun σ _ => h_eq σ)
  rw [h_sum, Finset.sum_const]
  -- Now: (m_kL)⁻¹ • (card • f τ) = f τ where card = m_kL
  have h_card : Finset.univ.card = placeValue b (k + 1) / placeValue b L :=
    finiteCylinder_card k L hLk (finitePrefix b L τ hLk)
  rw [← Nat.cast_smul_eq_nsmul ℝ, h_card, smul_smul]
  have h_ne : ((placeValue b (k + 1) / placeValue b L : ℕ) : ℝ) ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    intro h_zero
    have : placeValue b (k + 1) < placeValue b L :=
      Nat.div_eq_zero_iff.mp h_zero |>.resolve_left (placeValue.ne_zero L)
    have : placeValue b L ≤ placeValue b (k + 1) := placeValue.mono hLk
    omega
  field_simp [h_ne]
  rw [one_smul]

end BasicProperties

/-!
## Tower Properties
-/

section TowerProperties

variable {b : RadixSeq} {V : Type*}
variable [AddCommGroup V] [Module ℝ V]

/--
**Proposition 21(1)**: P_L^(k) is idempotent.

(P_L^(k))² = P_L^(k)
-/
theorem finiteBlockProjection_idempotent (k L : ℕ) (hLk : L ≤ k + 1)
    (f : FiniteRadixSpace b k → V) :
    finiteBlockProjection b k L hLk (finiteBlockProjection b k L hLk f) =
    finiteBlockProjection b k L hLk f := by
  ext τ
  simp only [finiteBlockProjection]
  -- Goal: (m⁻¹ • ∑ σ, (P_L f)(σ)) = (m⁻¹ • ∑ σ, f(σ))
  -- Since P_L f is constant on the cylinder, ∑ σ, (P_L f)(σ) = card * (P_L f)(τ)
  -- And (P_L f)(τ) = (m⁻¹ • ∑ σ, f(σ)), so:
  -- LHS = m⁻¹ • (card * m⁻¹ • ∑ σ, f(σ)) = m⁻¹ • card • m⁻¹ • ∑ σ, f(σ)
  -- Since card = m, this simplifies to: m⁻¹ • m • m⁻¹ • ∑ = m⁻¹ • ∑ = RHS

  -- Step 1: P_L f is constant on the cylinder
  have h_const : ∀ σ : finiteCylinderSet b k L hLk (finitePrefix b L τ hLk),
      finiteBlockProjection b k L hLk f σ.val = finiteBlockProjection b k L hLk f τ := by
    intro σ
    apply finiteBlockProjection_isBlockConstant
    funext i
    exact σ.property i

  -- Step 2: Rewrite the sum
  congr 1
  calc ∑ σ : finiteCylinderSet b k L hLk (finitePrefix b L τ hLk),
          finiteBlockProjection b k L hLk f σ.val
      = ∑ σ : finiteCylinderSet b k L hLk (finitePrefix b L τ hLk),
          finiteBlockProjection b k L hLk f τ := by
        apply Finset.sum_congr rfl
        intro σ _
        exact h_const σ
    _ = ∑ σ : finiteCylinderSet b k L hLk (finitePrefix b L τ hLk), f σ.val := by
        -- Each term (P_L f)(τ) is constant = (m⁻¹ • ∑ ρ, f(ρ))
        -- So ∑ σ, (P_L f)(τ) = card • (P_L f)(τ)
        -- But (P_L f)(τ) = m⁻¹ • ∑ ρ, f(ρ), so:
        -- = card • (m⁻¹ • ∑ ρ, f(ρ))
        -- Since card = m and ρ ranges over the same set as σ:
        -- = m • (m⁻¹ • ∑ σ, f(σ)) = ∑ σ, f(σ)
        rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ]
        simp only [finiteBlockProjection]
        rw [smul_smul]
        have h_card : Finset.univ.card = placeValue b (k + 1) / placeValue b L :=
          finiteCylinder_card k L hLk (finitePrefix b L τ hLk)
        rw [h_card]
        have h_ne : ((placeValue b (k + 1) / placeValue b L : ℕ) : ℝ) ≠ 0 := by
          apply Nat.cast_ne_zero.mpr
          intro h_zero
          have h_lt : placeValue b (k + 1) < placeValue b L :=
            Nat.div_eq_zero_iff.mp h_zero |>.resolve_left (placeValue.ne_zero L)
          have h_le : placeValue b L ≤ placeValue b (k + 1) := placeValue.mono hLk
          omega
        field_simp [h_ne]
        rw [one_smul]

/--
The "middle digits" type: digits from position L to M-1.

When L ≤ M, an M-prefix extending an L-prefix s is determined by the additional
digits at positions L, L+1, ..., M-1.
-/
def MiddleDigits (b : RadixSeq) (L M : ℕ) : Type :=
  (i : Fin (M - L)) → Fin (b (L + i.val))

instance middleDigitsFintype (L M : ℕ) : Fintype (MiddleDigits b L M) := by
  unfold MiddleDigits
  infer_instance

/--
Extend an L-prefix to an M-prefix using middle digits.
-/
def extendPrefix (L M : ℕ) (hLM : L ≤ M) (s : PrefixSet b L) (mid : MiddleDigits b L M) :
    PrefixSet b M :=
  fun i =>
    if h : i.val < L then
      s ⟨i.val, h⟩
    else
      Fin.cast (by congr 1; exact Nat.add_sub_cancel' (Nat.le_of_not_lt h))
        (mid ⟨i.val - L, by have := i.isLt; omega⟩)

/--
Extract the middle digits from an element of the L-cylinder.

For σ in the L-cylinder, this gives the digits at positions L, L+1, ..., M-1.
-/
def extractMiddle (k L M : ℕ) (hLk : L ≤ k + 1) (hMk : M ≤ k + 1) (hLM : L ≤ M)
    (s : PrefixSet b L) (σ : finiteCylinderSet b k L hLk s) : MiddleDigits b L M :=
  fun i => σ.val ⟨L + i.val, by have := i.isLt; omega⟩

/--
The M-prefix of an element of the L-cylinder.
-/
def getMPrefix (k L M : ℕ) (hLk : L ≤ k + 1) (hMk : M ≤ k + 1) (_hLM : L ≤ M)
    (s : PrefixSet b L) (σ : finiteCylinderSet b k L hLk s) : PrefixSet b M :=
  finitePrefix b M σ.val hMk

/--
The M-prefix of an L-cylinder element extends the L-prefix.
-/
theorem getMPrefix_extends (k L M : ℕ) (hLk : L ≤ k + 1) (hMk : M ≤ k + 1) (hLM : L ≤ M)
    (s : PrefixSet b L) (σ : finiteCylinderSet b k L hLk s) :
    ∀ i : Fin L, getMPrefix k L M hLk hMk hLM s σ ⟨i.val, Nat.lt_of_lt_of_le i.isLt hLM⟩ = s i := by
  intro i
  simp only [getMPrefix, finitePrefix]
  exact σ.property i

/--
**Proposition 21(2)**: Tower property P_L^(k) P_M^(k) = P_L^(k) for L ≤ M.

**Proof**: P_M f is constant on each M-cylinder. When we sum (P_M f)(σ) over an
L-cylinder, each M-cylinder within it contributes m_{k,M} copies of the same value.
That value is (m_{k,M})⁻¹ • ∑_{ρ ∈ M-cyl} f(ρ), so each M-cylinder contributes
∑_{ρ ∈ M-cyl} f(ρ). Summing over all M-cylinders gives ∑_{σ ∈ L-cyl} f(σ).
-/
theorem finiteBlockProjection_tower (k L M : ℕ) (hLk : L ≤ k + 1) (hMk : M ≤ k + 1)
    (hLM : L ≤ M) (f : FiniteRadixSpace b k → V) :
    finiteBlockProjection b k L hLk (finiteBlockProjection b k M hMk f) =
    finiteBlockProjection b k L hLk f := by
  ext τ
  simp only [finiteBlockProjection]
  -- After simp, the goal is:
  -- (m_kL)⁻¹ • ∑_{σ : L-cyl} (m_kM)⁻¹ • ∑_{ρ : M-cyl(σ)} f(ρ) = (m_kL)⁻¹ • ∑_{σ : L-cyl} f(σ)
  -- We need to show the inner sums are equal.

  -- Use set to create names for the prefixes and cardinalities
  set s := finitePrefix b L τ hLk with hs
  set m_kL := placeValue b (k + 1) / placeValue b L with hm_kL
  set m_kM := placeValue b (k + 1) / placeValue b M with hm_kM

  -- After simp, the form is already unfolded, so we work with it directly
  -- Goal: (m_kL)⁻¹ • ∑_{σ} ((m_kM)⁻¹ • ∑_{ρ} f(ρ)) = (m_kL)⁻¹ • ∑_{σ} f(σ)
  congr 1
  -- Goal: ∑_{σ} ((m_kM)⁻¹ • ∑_{ρ} f(ρ)) = ∑_{σ} f(σ)

  -- Factor out the scalar from the sum using Finset.smul_sum
  rw [← Finset.smul_sum]
  -- Goal: (m_kM)⁻¹ • ∑_{σ} ∑_{ρ} f(ρ) = ∑_{σ} f(σ)

  -- Goal: (m_kM)⁻¹ • ∑_{σ} ∑_{ρ} f(ρ) = ∑_{σ} f(σ)
  -- The double sum counts each f(ρ) once for each σ with the same M-prefix as ρ
  -- For each ρ in the L-cylinder, there are m_kM elements σ in the L-cylinder
  -- with the same M-prefix as ρ (namely, all elements of the M-cylinder containing ρ)
  -- So ∑_{σ} ∑_{ρ : M-cyl(σ)} f(ρ) = m_kM • ∑_{ρ} f(ρ)
  -- Then m_kM⁻¹ • (m_kM • ∑ f(ρ)) = ∑ f(ρ)

  have h_m_kM_pos : 0 < (m_kM : ℝ) := by
    apply Nat.cast_pos.mpr
    apply Nat.div_pos
    · exact placeValue.mono hMk
    · exact placeValue.pos M

  have h_m_kM_ne : (m_kM : ℝ) ≠ 0 := ne_of_gt h_m_kM_pos

  -- Key: each ρ in L-cylinder is counted m_kM times in the double sum
  -- (once for each σ in its M-cylinder)
  --
  -- **Mathematical argument**:
  -- The double sum ∑_{σ : L-cyl} ∑_{ρ : M-cyl(σ)} f(ρ) counts each f(ρ) once for each
  -- σ in the L-cylinder that shares the same M-prefix as ρ. Since M ≥ L, the M-cylinder
  -- of ρ is contained in the L-cylinder, and has exactly m_kM elements. So each ρ in
  -- the L-cylinder is counted exactly m_kM times.
  --
  -- This requires partition-based Finset.sum_fiberwise arguments that are technically
  -- complex to formalize. The mathematical content is identical to the already-proven
  -- infinite case; see blockProjection_tower in Projections/Properties.lean.
  have h_double_sum : ∑ σ : finiteCylinderSet b k L hLk s,
      ∑ ρ : finiteCylinderSet b k M hMk (finitePrefix b M σ.val hMk), f ρ.val =
      (m_kM : ℕ) • ∑ ρ : finiteCylinderSet b k L hLk s, f ρ.val := by
    -- **Double counting**: Each ρ ∈ L-cyl appears in the double sum once for each
    -- σ ∈ L-cyl with the same M-prefix. The set of such σ is exactly M-cyl(ρ),
    -- which has cardinality m_kM.

    -- M-cylinder elements are in L-cylinder (since M ≥ L, finer cylinders are subsets)
    have h_M_cyl_subset : ∀ σ : finiteCylinderSet b k L hLk s,
        ∀ ρ : finiteCylinderSet b k M hMk (finitePrefix b M σ.val hMk),
        ρ.val ∈ finiteCylinderSet b k L hLk s := by
      intro σ ρ i
      have hi_M : i.val < M := Nat.lt_of_lt_of_le i.isLt hLM
      have h_rho_M := ρ.property ⟨i.val, hi_M⟩
      have h_sigma_L := σ.property i
      simp only [finitePrefix] at h_rho_M h_sigma_L ⊢
      have h1 : ρ.val ⟨i.val, by omega⟩ = σ.val ⟨i.val, by omega⟩ := by convert h_rho_M using 2
      have h2 : σ.val ⟨i.val, by omega⟩ = s i := by convert h_sigma_L using 2
      convert h1.trans h2 using 2

    -- M-prefix symmetry: ρ ∈ M-cyl(σ) implies σ ∈ M-cyl(ρ)
    have h_M_prefix_symm : ∀ σ : finiteCylinderSet b k L hLk s,
        ∀ ρ : finiteCylinderSet b k M hMk (finitePrefix b M σ.val hMk),
        σ.val ∈ finiteCylinderSet b k M hMk (finitePrefix b M ρ.val hMk) := by
      intro σ ρ i
      have h_rho := ρ.property i
      simp only [finiteCylinderSet, Set.mem_setOf_eq, finitePrefix] at h_rho ⊢
      convert h_rho.symm using 2

    -- Define the pair type and lift function
    let PairType := (σ : finiteCylinderSet b k L hLk s) ×
                    finiteCylinderSet b k M hMk (finitePrefix b M σ.val hMk)
    let liftToLCyl (σ : finiteCylinderSet b k L hLk s)
        (ρ : finiteCylinderSet b k M hMk (finitePrefix b M σ.val hMk)) :
        finiteCylinderSet b k L hLk s := ⟨ρ.val, h_M_cyl_subset σ ρ⟩

    -- Helper for the inverse direction: σ ∈ M-cyl(ρ) and ρ ∈ L-cyl implies σ ∈ L-cyl
    have h_inv_in_L : ∀ (ρ : finiteCylinderSet b k L hLk s)
        (σ : finiteCylinderSet b k M hMk (finitePrefix b M ρ.val hMk)),
        σ.val ∈ finiteCylinderSet b k L hLk s := by
      intro ρ σ i
      have hi_M : i.val < M := Nat.lt_of_lt_of_le i.isLt hLM
      have h_sigma_M := σ.property ⟨i.val, hi_M⟩
      have h_rho_L := ρ.property i
      simp only [finitePrefix] at h_sigma_M h_rho_L ⊢
      have h1 : σ.val ⟨i.val, by omega⟩ = ρ.val ⟨i.val, by omega⟩ := by convert h_sigma_M using 2
      have h2 : ρ.val ⟨i.val, by omega⟩ = s i := by convert h_rho_L using 2
      convert h1.trans h2 using 2

    -- Helper for the inverse direction: if ρ ∈ L-cyl and σ ∈ M-cyl(ρ), then ρ ∈ M-cyl(σ)
    have h_inv_rho_in_M : ∀ (ρ : finiteCylinderSet b k L hLk s)
        (σ : finiteCylinderSet b k M hMk (finitePrefix b M ρ.val hMk)),
        ρ.val ∈ finiteCylinderSet b k M hMk (finitePrefix b M σ.val hMk) := by
      intro ρ σ i
      have h_sigma := σ.property i
      simp only [finitePrefix] at h_sigma ⊢
      convert h_sigma.symm using 2

    -- The equivalence swapping (σ, ρ) and (ρ, σ)
    let swapEquiv : PairType ≃
        (ρ : finiteCylinderSet b k L hLk s) ×
        finiteCylinderSet b k M hMk (finitePrefix b M ρ.val hMk) := {
      toFun := fun ⟨σ, ρ⟩ => ⟨liftToLCyl σ ρ, ⟨σ.val, h_M_prefix_symm σ ρ⟩⟩
      invFun := fun ⟨ρ, σ⟩ => ⟨⟨σ.val, h_inv_in_L ρ σ⟩, ⟨ρ.val, h_inv_rho_in_M ρ σ⟩⟩
      left_inv := fun ⟨σ, ρ⟩ => rfl
      right_inv := fun ⟨ρ, σ⟩ => rfl
    }

    -- Step 1: Rewrite nested sum as sum over sigma type
    have h_step1 : ∑ σ' : finiteCylinderSet b k L hLk s,
          ∑ ρ : finiteCylinderSet b k M hMk (finitePrefix b M σ'.val hMk), f ρ.val
        = ∑ p : PairType, f p.2.val := by
      exact (Fintype.sum_sigma' (fun (σ' : finiteCylinderSet b k L hLk s)
        (ρ : finiteCylinderSet b k M hMk (finitePrefix b M σ'.val hMk)) => f ρ.val)).symm

    -- Step 2 + 3 combined: Reindex using the equivalence
    -- swapEquiv maps (σ, ρ) where ρ ∈ M-cyl(σ) to (liftToLCyl σ ρ, σ') where σ' ∈ M-cyl(ρ)
    -- The key: f(p.2.val) = f(ρ.val) = f((swapEquiv p).1.val) because liftToLCyl σ ρ = ⟨ρ.val, _⟩
    have h_step2_3 : ∑ p : PairType, f p.2.val =
        ∑ ρ : finiteCylinderSet b k L hLk s,
          ∑ _σ : finiteCylinderSet b k M hMk (finitePrefix b M ρ.val hMk), f ρ.val := by
      -- Define the target sigma type
      let TargetType := (ρ : finiteCylinderSet b k L hLk s) ×
                        finiteCylinderSet b k M hMk (finitePrefix b M ρ.val hMk)
      -- Use sum_equiv with swapEquiv, then unfold to nested sum
      have h1 : ∑ p : PairType, f p.2.val = ∑ q : TargetType, f q.1.val := by
        refine Fintype.sum_equiv swapEquiv (fun p => f p.2.val) (fun q => f q.1.val) ?_
        intro ⟨σ', ρ⟩
        rfl
      have h2 : ∑ q : TargetType, f q.1.val =
          ∑ ρ : finiteCylinderSet b k L hLk s,
            ∑ _σ : finiteCylinderSet b k M hMk (finitePrefix b M ρ.val hMk), f ρ.val := by
        simp only [TargetType]
        rw [← Fintype.sum_sigma']
      exact h1.trans h2

    -- Step 4: Inner sum is constant, so equals card • value
    have h_step4 : ∑ ρ : finiteCylinderSet b k L hLk s,
          ∑ _σ : finiteCylinderSet b k M hMk (finitePrefix b M ρ.val hMk), f ρ.val =
        ∑ ρ : finiteCylinderSet b k L hLk s,
          Fintype.card (finiteCylinderSet b k M hMk (finitePrefix b M ρ.val hMk)) • f ρ.val := by
      congr 1
      ext ρ
      rw [Finset.sum_const, Finset.card_univ]

    -- Step 5: Card = m_kM by finiteCylinder_card
    have h_step5 : ∑ ρ : finiteCylinderSet b k L hLk s,
          Fintype.card (finiteCylinderSet b k M hMk (finitePrefix b M ρ.val hMk)) • f ρ.val =
        ∑ ρ : finiteCylinderSet b k L hLk s, m_kM • f ρ.val := by
      congr 1
      ext ρ
      congr 1
      exact finiteCylinder_card k M hMk (finitePrefix b M ρ.val hMk)

    -- Step 6: Factor out the constant
    have h_step6 : ∑ ρ : finiteCylinderSet b k L hLk s, m_kM • f ρ.val =
        (m_kM : ℕ) • ∑ ρ : finiteCylinderSet b k L hLk s, f ρ.val := by
      -- Convert Fintype sums to Finset sums
      simp only [← Finset.univ.sum_coe_sort (fun ρ : finiteCylinderSet b k L hLk s => m_kM • f ρ.val)]
      simp only [← Finset.univ.sum_coe_sort (fun ρ : finiteCylinderSet b k L hLk s => f ρ.val)]
      rw [← Finset.sum_nsmul]

    exact h_step1.trans (h_step2_3.trans (h_step4.trans (h_step5.trans h_step6)))

  rw [h_double_sum]
  -- Goal: m_kM⁻¹ • (m_kM • ∑_ρ f(ρ)) = ∑_ρ f(ρ)
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  simp only [inv_mul_cancel₀ h_m_kM_ne, one_smul]

/--
Projections commute: P_L^(k) P_M^(k) = P_M^(k) P_L^(k) = P_{min(L,M)}^(k).

**Proof**: Use tower property in both directions plus block-constancy.
-/
theorem finiteBlockProjection_comm (k L M : ℕ) (hLk : L ≤ k + 1) (hMk : M ≤ k + 1)
    (f : FiniteRadixSpace b k → V) :
    finiteBlockProjection b k L hLk (finiteBlockProjection b k M hMk f) =
    finiteBlockProjection b k M hMk (finiteBlockProjection b k L hLk f) := by
  rcases Nat.le_total L M with hLM | hML
  · -- L ≤ M: P_L(P_M f) = P_L f [tower]; P_M(P_L f) = P_L f [fixedPoint]
    rw [finiteBlockProjection_tower k L M hLk hMk hLM f]
    -- P_L f is L-block-constant
    have h_bc_L : ∀ τ τ', finitePrefix b L τ hLk = finitePrefix b L τ' hLk →
                            finiteBlockProjection b k L hLk f τ = finiteBlockProjection b k L hLk f τ' :=
      finiteBlockProjection_isBlockConstant k L hLk f
    -- When M ≥ L, L-block-constant ⊆ M-block-constant (coarse ⊆ fine)
    have h_bc_M : ∀ τ τ', finitePrefix b M τ hMk = finitePrefix b M τ' hMk →
                            finiteBlockProjection b k L hLk f τ = finiteBlockProjection b k L hLk f τ' := by
      intro τ τ' h_prefix_M
      apply h_bc_L
      -- Prefixes agree at M, so they agree at L (L ≤ M)
      funext i
      have h_i_bound : i.val < L := i.isLt
      have hi_M : i.val < M := Nat.lt_of_lt_of_le h_i_bound hLM
      exact congr_fun h_prefix_M ⟨i.val, hi_M⟩
    -- So P_M(P_L f) = P_L f by fixedPoint
    exact (finiteBlockProjection_fixedPoint k M hMk (finiteBlockProjection b k L hLk f) h_bc_M).symm
  · -- M ≤ L: symmetric
    rw [finiteBlockProjection_tower k M L hMk hLk hML f]
    have h_bc_M : ∀ τ τ', finitePrefix b M τ hMk = finitePrefix b M τ' hMk →
                            finiteBlockProjection b k M hMk f τ = finiteBlockProjection b k M hMk f τ' :=
      finiteBlockProjection_isBlockConstant k M hMk f
    have h_bc_L : ∀ τ τ', finitePrefix b L τ hLk = finitePrefix b L τ' hLk →
                            finiteBlockProjection b k M hMk f τ = finiteBlockProjection b k M hMk f τ' := by
      intro τ τ' h_prefix_L
      apply h_bc_M
      funext i
      have h_i_bound : i.val < M := i.isLt
      have hi_L : i.val < L := Nat.lt_of_lt_of_le h_i_bound hML
      exact congr_fun h_prefix_L ⟨i.val, hi_L⟩
    exact finiteBlockProjection_fixedPoint k L hLk (finiteBlockProjection b k M hMk f) h_bc_L

end TowerProperties

/-!
## Telescoping Identity
-/

section Telescoping

variable {b : RadixSeq} {V : Type*}
variable [AddCommGroup V] [Module ℝ V]

/--
**Proposition 21(3)**: Telescoping identity (finite version).

P_N^(k) f = P_1^(k) f + ∑_{L=1}^{N-1} Δ_L^(k) f

**Proof**: By induction on N:
- Base (N=1): P_1 = P_1 + ∑_{L : Fin 0} Δ_{L+1} (empty sum) ✓
- Step: P_{N+1} = P_1 + ∑_{L : Fin N} Δ_{L+1}
         = (P_1 + ∑_{L : Fin (N-1)} Δ_{L+1}) + Δ_N  [split last term]
         = P_N + Δ_N  [by IH]
         = P_N + (P_{N+1} - P_N)  [by definition]
         = P_{N+1} ✓
-/
theorem finiteBlockProjection_telescoping (k N : ℕ) (hNk : 1 ≤ N) (hNk' : N ≤ k + 1)
    (f : FiniteRadixSpace b k → V) :
    finiteBlockProjection b k N hNk' f = finiteBlockProjection b k 1 (by omega) f +
      ∑ L : Fin (N - 1), finiteDetailOperator b k (L.val + 1) (by omega) f := by
  -- **Telescoping sum**: P_N = P_1 + Δ_1 + Δ_2 + ... + Δ_{N-1}
  -- where Δ_L = P_{L+1} - P_L
  --
  -- Expanding: P_1 + (P_2 - P_1) + (P_3 - P_2) + ... + (P_N - P_{N-1}) = P_N
  --
  -- **Proof structure**:
  -- By induction on N:
  -- - Base (N=1): P_1 = P_1 + ∑_{Fin 0} = P_1 + 0 ✓
  -- - Step: P_{N+1} = P_N + Δ_N = (P_1 + ∑_{L<N-1} Δ_{L+1}) + Δ_N = P_1 + ∑_{L<N} Δ_{L+1} ✓
  --
  -- **Technical note**: The induction involves rewriting Fin sums with dependent bounds
  -- (Fin (N-1) vs Fin N). This requires Fintype.sum_equiv or careful conv_rhs tactics.
  -- The infinite version is proven identically in Projections/Properties.lean.
  --
  -- The core identity P_N = P_{N-1} + Δ_{N-1} follows directly from finiteDetailOperator:
  -- Proof: Use the fact that Δ_L = P_{L+1} - P_L, so the sum telescopes
  -- P_1 + Δ_1 + Δ_2 + ... + Δ_{N-1} = P_1 + (P_2 - P_1) + (P_3 - P_2) + ... + (P_N - P_{N-1}) = P_N
  --
  -- Direct induction on N
  induction N with
  | zero => omega  -- 1 ≤ 0 is impossible
  | succ N ih =>
    cases N with
    | zero =>
      -- N = 0, so succ N = 1
      -- Goal: P_1 = P_1 + ∑_{Fin 0} Δ_...
      simp only [Nat.succ_sub_one, Fintype.sum_empty, add_zero]
    | succ M =>
      -- N = M + 1, so succ N = M + 2
      -- Goal: P_{M+2} = P_1 + ∑_{L : Fin (M+1)} Δ_{L+1}
      -- Use IH for M + 1 (which exists since M + 1 ≥ 1)
      have hNpos : 1 ≤ M + 1 := by omega
      have hNk'' : M + 1 ≤ k + 1 := by omega
      have h_ih := ih hNpos hNk''
      -- Split the sum: ∑_{L : Fin (M+1)} = ∑_{L : Fin M} + last term
      simp only [Nat.succ_sub_one] at h_ih ⊢
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [← add_assoc, ← h_ih]
      -- Goal: P_{M+2} = P_{M+1} + Δ_{M+1} = P_{M+1} + (P_{M+2} - P_{M+1})
      simp only [finiteDetailOperator]
      ext x
      simp only [Pi.add_apply, Pi.sub_apply]
      -- Goal: a = b + (a - b)
      abel

end Telescoping

end FdrsFormal.FunctionSpaces.Commutant
