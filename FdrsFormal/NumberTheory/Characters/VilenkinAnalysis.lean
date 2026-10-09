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

# Analysis on the carry-free group (Phase 3 addendum, §1.15)

Harmonic analysis of functions on `𝓡^{(k)} ≅ ∏ ℤ/b_i` through the Vilenkin kernel
`V(τ, σ) = ∏_i ζ_{b_i}^{τ_i σ_i}` (§1.4): the Efron–Stein / influence calculus used by
OpenAI family 106 (hardness of coloring three-colorable graphs), on the corpus's
schedules.

- **Definition 221** (`vHat`, `digitAvg`, `influenceSq`, `halfShift`): Vilenkin
  coefficients, averaging over one digit, influences, and the half-shift.
- **Theorem 133** (`vilenkin_orthogonal`, `vilenkin_inversion`, `vilenkin_parseval`,
  `vilenkin_plancherel`): orthogonality, inversion, Parseval and Plancherel.
- **Theorem 134** (`vHat_digitAvg`, `influenceSq_eq`): averaging over digit `i` keeps
  exactly the coefficients with `σ_i = 0`; hence `D_i(f)² = Σ_{σ_i ≠ 0} |f̂(σ)|²`.
- **Proposition 165** (`variance_le_sum_influence`): the Poincaré inequality
  `(1/N) Σ |f − E f|² ≤ Σ_i D_i(f)²`, with constant 1.
- **Proposition 166** (`kernel_halfShift`, `odd_iff_vHat`): on an even schedule the
  half-shift multiplies `V(·, σ)` by `(−1)^{Σ σ_i}`; `f ∘ h = −f` iff `f̂` vanishes on
  even digit sums.
- **Corollary 43** (`odd_mean_zero`, `odd_energy_le_sum_influence`): a sign-changing
  function has mean zero and energy at most its total influence.

**Honest scope.** Classical (Vilenkin 1947; Efron–Stein 1981; the Fourier-analytic
proof of Poincaré). The corpus contributes the statements on mixed-radix schedules.
The dimension-free junta theorem of family 106 is not formalized.
-/

import FdrsFormal.NumberTheory.Characters.Negacyclic
import FdrsFormal.NumberTheory.Characters.RaderBluestein

namespace FdrsFormal.NumberTheory.Characters.MixedRadixFFT

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite
open FdrsFormal.NumberTheory.Characters.FourierCircuit

variable {b : RadixSeq}

local notation "conj" => starRingEnd ℂ

local instance (k : ℕ) : DecidableEq (FiniteRadixSpace b k) :=
  inferInstanceAs (DecidableEq ((i : Fin (k + 1)) → Fin (b i)))

/-! ## Roots of unity: conjugation and coordinate orthogonality -/

theorem conj_zeta (n : ℕ) : conj (zeta n) = (zeta n)⁻¹ := by
  rw [zeta, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp only [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_natCast, map_ofNat]
  ring

theorem zeta_pow_inv (n a : ℕ) (hn : n ≠ 0) : (zeta n ^ a)⁻¹ = zeta n ^ (a * (n - 1)) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_add, show a + a * (n - 1) = n * a by
    rcases Nat.exists_eq_succ_of_ne_zero hn with ⟨m, rfl⟩; simp; ring]
  exact zeta_pow_self_mul n a hn

/-- `Σ_{t<n} ζ_n^{ts} conj(ζ_n^{ts'}) = n·[s = s']` for `s, s' < n`. -/
theorem sum_zeta_mul_conj (n : ℕ) (hn : n ≠ 0) {s s' : ℕ} (hs : s < n) (hs' : s' < n) :
    ∑ t ∈ Finset.range n, zeta n ^ (t * s) * conj (zeta n ^ (t * s')) =
      if s = s' then (n : ℂ) else 0 := by
  have hterm : ∀ t, zeta n ^ (t * s) * conj (zeta n ^ (t * s')) =
      zeta n ^ (t * (s + s' * (n - 1))) := fun t => by
    rw [map_pow, conj_zeta, inv_pow, zeta_pow_inv n _ hn, ← pow_add]
    congr 1; ring
  simp_rw [hterm]
  rw [sum_zeta_pow_mul n _ hn]
  haveI : NeZero n := ⟨hn⟩
  have key : n ∣ s + s' * (n - 1) ↔ s = s' := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_mul,
      Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn), ZMod.natCast_self, Nat.cast_one]
    rw [show (s : ZMod n) + s' * (0 - 1) = s - s' by ring, sub_eq_zero]
    constructor
    · intro h
      have := (ZMod.natCast_eq_natCast_iff' s s' n).mp h
      rwa [Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hs'] at this
    · rintro rfl; rfl
  by_cases h : s = s'
  · rw [if_pos (key.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (key.mp h')), if_neg h]

/-- Sums over `𝓡^{(k)}` of product functions factor. -/
theorem sum_prod_frs (k : ℕ) (g : (i : Fin (k + 1)) → Fin (b i) → ℂ) :
    ∑ τ : FiniteRadixSpace b k, ∏ i, g i (τ i) = ∏ i, ∑ t, g i t :=
  (Fintype.prod_sum g).symm

theorem vilenkinKernel_symm (k : ℕ) (τ σ : FiniteRadixSpace b k) :
    vilenkinKernel k τ σ = vilenkinKernel k σ τ := by
  simp only [vilenkinKernel, mul_comm]

theorem vilenkinKernel_zero_right (k : ℕ) (τ : FiniteRadixSpace b k) :
    vilenkinKernel k τ (fun i => ⟨0, b.pos i⟩) = 1 := by
  simp [vilenkinKernel]

/-! ## Theorem 133: orthogonality, inversion, Parseval -/

/-- **Theorem 133 (Vilenkin orthogonality).**
`Σ_τ V(τ, σ) conj V(τ, σ') = N·[σ = σ']`, `N = B_{k+1}`.

**fdrs.md**: Theorem 133 (Vilenkin orthogonality and Plancherel). -/
theorem vilenkin_orthogonal (k : ℕ) (σ σ' : FiniteRadixSpace b k) :
    ∑ τ : FiniteRadixSpace b k, vilenkinKernel k τ σ * conj (vilenkinKernel k τ σ') =
      if σ = σ' then (placeValue b (k + 1) : ℂ) else 0 := by
  have hfac : ∀ τ : FiniteRadixSpace b k,
      vilenkinKernel k τ σ * conj (vilenkinKernel k τ σ') =
        ∏ i : Fin (k + 1),
          zeta (b i) ^ ((τ i : ℕ) * σ i) * conj (zeta (b i) ^ ((τ i : ℕ) * σ' i)) := by
    intro τ
    rw [vilenkinKernel, vilenkinKernel, map_prod, ← Finset.prod_mul_distrib]
  simp_rw [hfac]
  rw [sum_prod_frs k (fun i t => zeta (b i) ^ ((t : ℕ) * σ i) *
    conj (zeta (b i) ^ ((t : ℕ) * σ' i)))]
  have hcoord : ∀ i : Fin (k + 1), ∑ t : Fin (b i), zeta (b i) ^ ((t : ℕ) * σ i) *
      conj (zeta (b i) ^ ((t : ℕ) * σ' i)) = if σ i = σ' i then (b i : ℂ) else 0 := by
    intro i
    rw [Fin.sum_univ_eq_sum_range (fun t => zeta (b i) ^ (t * σ i) *
      conj (zeta (b i) ^ (t * σ' i))), sum_zeta_mul_conj _ (b.ne_zero i) (σ i).isLt (σ' i).isLt]
    simp only [Fin.val_inj]
  simp_rw [hcoord]
  by_cases h : σ = σ'
  · subst h
    simp only [if_true]
    rw [← prod_univ_eq_placeValue]; push_cast; rfl
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, σ i ≠ σ' i := by
      by_contra hc; push_neg at hc; exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- Vilenkin coefficients `f̂(σ) = (1/N) Σ_τ f(τ) conj V(τ, σ)`.

**fdrs.md**: Definition 221 (Vilenkin coefficients, digit averaging, influence). -/
noncomputable def vHat (k : ℕ) (f : FiniteRadixSpace b k → ℂ) (σ : FiniteRadixSpace b k) : ℂ :=
  (1 / (placeValue b (k + 1) : ℂ)) * ∑ τ, f τ * conj (vilenkinKernel k τ σ)

theorem placeValue_ne_zero_complex (k : ℕ) : (placeValue b (k + 1) : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (placeValue.ne_zero _)

/-- A finite Vilenkin expansion has its coefficients as Vilenkin coefficients. -/
theorem vHat_expansion (k : ℕ) (c : FiniteRadixSpace b k → ℂ) (σ : FiniteRadixSpace b k) :
    vHat k (fun τ => ∑ ρ, c ρ * vilenkinKernel k τ ρ) σ = c σ := by
  rw [vHat]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, vilenkin_orthogonal]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  field_simp [placeValue_ne_zero_complex (b := b) k]
  exact mul_div_cancel_left₀ _ (placeValue_ne_zero_complex k)

/-- **Theorem 133 (inversion).** `f = Σ_σ f̂(σ) V(·, σ)`.

**fdrs.md**: Theorem 133 (Vilenkin orthogonality and Plancherel). -/
theorem vilenkin_inversion (k : ℕ) (f : FiniteRadixSpace b k → ℂ) (τ : FiniteRadixSpace b k) :
    f τ = ∑ σ, vHat k f σ * vilenkinKernel k τ σ := by
  simp only [vHat]
  simp_rw [mul_assoc, Finset.sum_mul, mul_assoc]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hdual : ∀ τ' : FiniteRadixSpace b k,
      ∑ σ, f τ' * (conj (vilenkinKernel k τ' σ) * vilenkinKernel k τ σ) =
        f τ' * (if τ = τ' then (placeValue b (k + 1) : ℂ) else 0) := by
    intro τ'
    rw [← Finset.mul_sum, ← vilenkin_orthogonal k τ τ']
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [vilenkinKernel_symm k τ' σ, vilenkinKernel_symm k τ σ, mul_comm]
  simp_rw [hdual]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  field_simp [placeValue_ne_zero_complex (b := b) k]
  exact (mul_div_cancel_right₀ _ (placeValue_ne_zero_complex k)).symm

/-- **Theorem 133 (Parseval).** `(1/N) Σ_τ f(τ) conj g(τ) = Σ_σ f̂(σ) conj ĝ(σ)`.

**fdrs.md**: Theorem 133 (Vilenkin orthogonality and Plancherel). -/
theorem vilenkin_parseval (k : ℕ) (f g : FiniteRadixSpace b k → ℂ) :
    (1 / (placeValue b (k + 1) : ℂ)) * ∑ τ, f τ * conj (g τ) =
      ∑ σ, vHat k f σ * conj (vHat k g σ) := by
  have hg : ∀ τ, conj (g τ) = ∑ σ, conj (vHat k g σ) * conj (vilenkinKernel k τ σ) :=
    fun τ => by
      conv_lhs => rw [vilenkin_inversion k g τ]
      simp only [map_sum, map_mul]
  simp_rw [hg, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hf : vHat k f σ = (1 / (placeValue b (k + 1) : ℂ)) *
      ∑ τ, f τ * conj (vilenkinKernel k τ σ) := rfl
  rw [hf, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun τ _ => ?_
  ring

/-- **Theorem 133 (Plancherel).** `(1/N) Σ_τ |f(τ)|² = Σ_σ |f̂(σ)|²`.

**fdrs.md**: Theorem 133 (Vilenkin orthogonality and Plancherel). -/
theorem vilenkin_plancherel (k : ℕ) (f : FiniteRadixSpace b k → ℂ) :
    (1 / (placeValue b (k + 1) : ℝ)) * ∑ τ, Complex.normSq (f τ) =
      ∑ σ, Complex.normSq (vHat k f σ) := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.mul_conj]
  exact vilenkin_parseval k f f

/-! ## Theorem 134: digit averaging and influence -/

/-- Averaging over digit `i`: `(E_i f)(τ) = (1/b_i) Σ_{t < b_i} f(τ[i := t])`.

**fdrs.md**: Definition 221 (Vilenkin coefficients, digit averaging, influence). -/
noncomputable def digitAvg (k : ℕ) (i : Fin (k + 1)) (f : FiniteRadixSpace b k → ℂ)
    (τ : FiniteRadixSpace b k) : ℂ :=
  (1 / (b i : ℂ)) * ∑ t : Fin (b i), f (Function.update τ i t)

/-- The influence of digit `i`: `D_i(f)² = (1/N) Σ_τ |f(τ) − (E_i f)(τ)|²`.

**fdrs.md**: Definition 221 (Vilenkin coefficients, digit averaging, influence). -/
noncomputable def influenceSq (k : ℕ) (i : Fin (k + 1)) (f : FiniteRadixSpace b k → ℂ) : ℝ :=
  (1 / (placeValue b (k + 1) : ℝ)) * ∑ τ, Complex.normSq (f τ - digitAvg k i f τ)

/-- The zero digit vector. -/
def vZero (k : ℕ) : FiniteRadixSpace b k := fun i => ⟨0, b.pos i⟩

theorem kernel_update (k : ℕ) (i : Fin (k + 1)) (τ σ : FiniteRadixSpace b k) (t : Fin (b i)) :
    vilenkinKernel k (Function.update τ i t) σ =
      zeta (b i) ^ ((t : ℕ) * σ i) *
        ∏ j ∈ Finset.univ.erase i, zeta (b j) ^ ((τ j : ℕ) * σ j) := by
  rw [vilenkinKernel, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

theorem sum_zeta_fin (n s : ℕ) (hn : n ≠ 0) (hs : s < n) :
    ∑ t : Fin n, zeta n ^ ((t : ℕ) * s) = if s = 0 then (n : ℂ) else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun t => zeta n ^ (t * s)), sum_zeta_pow_mul n s hn]
  by_cases h : s = 0
  · simp [h]
  · rw [if_neg (fun hd => h (Nat.eq_zero_of_dvd_of_lt hd hs)), if_neg h]

/-- Averaging over digit `i` keeps a character iff it ignores digit `i`. -/
theorem digitAvg_kernel (k : ℕ) (i : Fin (k + 1)) (σ τ : FiniteRadixSpace b k) :
    digitAvg k i (fun τ => vilenkinKernel k τ σ) τ =
      if (σ i : ℕ) = 0 then vilenkinKernel k τ σ else 0 := by
  simp only [digitAvg]
  simp_rw [kernel_update]
  rw [← Finset.sum_mul, sum_zeta_fin (b i) _ (b.ne_zero i) (σ i).isLt]
  split_ifs with h
  · rw [vilenkinKernel, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), h, mul_zero,
      pow_zero, one_mul]
    field_simp [Nat.cast_ne_zero.mpr (b.ne_zero i)]
  · simp

theorem vHat_sub (k : ℕ) (f g : FiniteRadixSpace b k → ℂ) (σ : FiniteRadixSpace b k) :
    vHat k (fun τ => f τ - g τ) σ = vHat k f σ - vHat k g σ := by
  simp only [vHat, sub_mul, Finset.sum_sub_distrib, mul_sub]

theorem digitAvg_expansion (k : ℕ) (i : Fin (k + 1)) (c : FiniteRadixSpace b k → ℂ)
    (τ : FiniteRadixSpace b k) :
    digitAvg k i (fun τ => ∑ ρ, c ρ * vilenkinKernel k τ ρ) τ =
      ∑ ρ, c ρ * digitAvg k i (fun τ => vilenkinKernel k τ ρ) τ := by
  simp only [digitAvg, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun t _ => ?_
  ring

/-- **Theorem 134 (averaging is a coefficient mask).** `(E_i f)^(σ) = [σ_i = 0] f̂(σ)`.

**fdrs.md**: Theorem 134 (the spectral formula for influences). -/
theorem vHat_digitAvg (k : ℕ) (i : Fin (k + 1)) (f : FiniteRadixSpace b k → ℂ)
    (σ : FiniteRadixSpace b k) :
    vHat k (digitAvg k i f) σ = if (σ i : ℕ) = 0 then vHat k f σ else 0 := by
  have hexp : digitAvg k i f = fun τ =>
      ∑ ρ, (if (ρ i : ℕ) = 0 then vHat k f ρ else 0) * vilenkinKernel k τ ρ := by
    funext τ
    conv_lhs => rw [show f = fun τ => ∑ ρ, vHat k f ρ * vilenkinKernel k τ ρ from
      funext (vilenkin_inversion k f)]
    rw [digitAvg_expansion]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [digitAvg_kernel]
    split_ifs <;> simp
  rw [hexp, vHat_expansion]

/-- **Theorem 134 (the spectral formula for influences).**
`D_i(f)² = Σ_{σ : σ_i ≠ 0} |f̂(σ)|²`.

**fdrs.md**: Theorem 134 (the spectral formula for influences). -/
theorem influenceSq_eq (k : ℕ) (i : Fin (k + 1)) (f : FiniteRadixSpace b k → ℂ) :
    influenceSq k i f =
      ∑ σ, if (σ i : ℕ) = 0 then 0 else Complex.normSq (vHat k f σ) := by
  have h := vilenkin_plancherel k (fun τ => f τ - digitAvg k i f τ)
  simp only at h
  rw [influenceSq, h]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [vHat_sub, vHat_digitAvg]
  split_ifs <;> simp

/-! ## Proposition 165: Poincaré -/

theorem vHat_const (k : ℕ) (c : ℂ) (σ : FiniteRadixSpace b k) :
    vHat k (fun _ => c) σ = if σ = vZero k then c else 0 := by
  have : (fun _ : FiniteRadixSpace b k => c) = fun τ =>
      ∑ ρ, (if ρ = vZero k then c else 0) * vilenkinKernel k τ ρ := by
    funext τ
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [show vZero k = (fun i => ⟨0, b.pos i⟩ : FiniteRadixSpace b k) from rfl,
      vilenkinKernel_zero_right, mul_one]
  rw [this, vHat_expansion]

theorem exists_digit_ne_zero {k : ℕ} {σ : FiniteRadixSpace b k} (h : σ ≠ vZero k) :
    ∃ i, (σ i : ℕ) ≠ 0 := by
  by_contra hc
  push_neg at hc
  exact h (funext fun i => Fin.ext (by simp [vZero, hc i]))

/-- **Proposition 165 (Poincaré).** The variance is at most the total influence:
`(1/N) Σ_τ |f(τ) − f̂(0)|² ≤ Σ_i D_i(f)²`, where `f̂(0)` is the mean.

**fdrs.md**: Proposition 165 (the Poincaré inequality). -/
theorem variance_le_sum_influence (k : ℕ) (f : FiniteRadixSpace b k → ℂ) :
    (1 / (placeValue b (k + 1) : ℝ)) * ∑ τ, Complex.normSq (f τ - vHat k f (vZero k)) ≤
      ∑ i, influenceSq k i f := by
  have h := vilenkin_plancherel k (fun τ => f τ - vHat k f (vZero k))
  simp only at h
  rw [h]
  simp_rw [influenceSq_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro σ _
  rw [vHat_sub, vHat_const]
  by_cases hσ : σ = vZero k
  · rw [if_pos hσ, hσ, sub_self, Complex.normSq_zero]
    exact Finset.sum_nonneg fun i _ => by split_ifs <;> simp [Complex.normSq_nonneg]
  · rw [if_neg hσ, sub_zero]
    obtain ⟨i, hi⟩ := exists_digit_ne_zero hσ
    calc Complex.normSq (vHat k f σ)
        = (if (σ i : ℕ) = 0 then 0 else Complex.normSq (vHat k f σ)) := by rw [if_neg hi]
      _ ≤ ∑ j, (if (σ j : ℕ) = 0 then 0 else Complex.normSq (vHat k f σ)) :=
          Finset.single_le_sum (f := fun j => if (σ j : ℕ) = 0 then 0 else
            Complex.normSq (vHat k f σ))
            (fun j _ => by dsimp only; split_ifs <;> simp [Complex.normSq_nonneg])
            (Finset.mem_univ i)

/-! ## Proposition 166 and Corollary 43: the half-shift -/

/-- The half-shift `h(τ)_i = τ_i + b_i/2 mod b_i`.

**fdrs.md**: Definition 221 (Vilenkin coefficients, digit averaging, influence). -/
def halfShift (k : ℕ) (τ : FiniteRadixSpace b k) : FiniteRadixSpace b k :=
  fun i => ⟨((τ i : ℕ) + b i / 2) % b i, Nat.mod_lt _ (b.pos i)⟩

/-- On an even schedule the half-shift is an involution. -/
theorem halfShift_involutive {k : ℕ} (heven : ∀ i : Fin (k + 1), 2 ∣ b i) :
    Function.Involutive (halfShift (b := b) k) := fun τ => by
  funext i
  apply Fin.ext
  have hh : b i / 2 + b i / 2 = b i := by obtain ⟨c, hc⟩ := heven i; omega
  simp only [halfShift]
  rw [Nat.mod_add_mod, add_assoc, hh, Nat.add_mod_right, Nat.mod_eq_of_lt (τ i).isLt]

theorem zeta_pow_half (n : ℕ) (hn : n ≠ 0) (he : 2 ∣ n) : zeta n ^ (n / 2) = -1 := by
  obtain ⟨c, rfl⟩ := he
  rw [Nat.mul_div_cancel_left c (by norm_num)]
  exact zeta_two_mul_pow c (by omega)

theorem zeta_pow_mod_mul (n a s : ℕ) (hn : n ≠ 0) : zeta n ^ (a % n * s) = zeta n ^ (a * s) := by
  rw [zeta_pow_mod n _ hn, zeta_pow_mod n (a * s) hn, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

/-- **Proposition 166 (the half-shift on characters).** On an even schedule,
`V(h τ, σ) = (−1)^{Σ_i σ_i} V(τ, σ)`.

**fdrs.md**: Proposition 166 (half-shift parity). -/
theorem kernel_halfShift {k : ℕ} (heven : ∀ i : Fin (k + 1), 2 ∣ b i)
    (τ σ : FiniteRadixSpace b k) :
    vilenkinKernel k (halfShift k τ) σ = (-1) ^ (∑ i, (σ i : ℕ)) * vilenkinKernel k τ σ := by
  rw [vilenkinKernel, vilenkinKernel, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  show zeta (b i) ^ (((τ i : ℕ) + b i / 2) % b i * σ i) = _
  rw [zeta_pow_mod_mul _ _ _ (b.ne_zero i), add_mul, pow_add,
    pow_mul (zeta (b i)) (b i / 2) (σ i), zeta_pow_half _ (b.ne_zero i) (heven i)]
  ring

theorem vHat_comp_halfShift {k : ℕ} (heven : ∀ i : Fin (k + 1), 2 ∣ b i)
    (f : FiniteRadixSpace b k → ℂ) (σ : FiniteRadixSpace b k) :
    vHat k (fun τ => f (halfShift k τ)) σ = (-1) ^ (∑ i, (σ i : ℕ)) * vHat k f σ := by
  have hinv := halfShift_involutive (b := b) heven
  have hterm : ∀ τ, f (halfShift k τ) * conj (vilenkinKernel k τ σ) =
      (-1) ^ (∑ i, (σ i : ℕ)) *
        (f (halfShift k τ) * conj (vilenkinKernel k (halfShift k τ) σ)) := fun τ => by
    rw [show vilenkinKernel k τ σ = vilenkinKernel k (halfShift k (halfShift k τ)) σ by
      rw [hinv τ], kernel_halfShift heven (halfShift k τ) σ, map_mul, map_pow, map_neg,
      map_one]
    ring
  simp only [vHat]
  simp_rw [hterm]
  rw [← Finset.mul_sum, Fintype.sum_bijective (halfShift k) hinv.bijective
    (fun τ => f (halfShift k τ) * conj (vilenkinKernel k (halfShift k τ) σ))
    (fun ρ => f ρ * conj (vilenkinKernel k ρ σ)) (fun _ => rfl)]
  ring

/-- **Proposition 166 (half-shift parity).** On an even schedule, `f ∘ h = −f` iff
`f̂(σ) = 0` for every `σ` of even digit sum.

**fdrs.md**: Proposition 166 (half-shift parity). -/
theorem odd_iff_vHat {k : ℕ} (heven : ∀ i : Fin (k + 1), 2 ∣ b i)
    (f : FiniteRadixSpace b k → ℂ) :
    (∀ τ, f (halfShift k τ) = -f τ) ↔ ∀ σ, Even (∑ i, (σ i : ℕ)) → vHat k f σ = 0 := by
  constructor
  · intro hodd σ he
    have h1 := vHat_comp_halfShift heven f σ
    rw [show (fun τ => f (halfShift k τ)) = fun τ => -f τ from funext hodd, he.neg_one_pow,
      one_mul] at h1
    have h2 : vHat k (fun τ => -f τ) σ = -vHat k f σ := by
      simp only [vHat, neg_mul, Finset.sum_neg_distrib, mul_neg]
    rw [h2] at h1
    exact self_eq_neg.mp h1.symm
  · intro hσ τ
    rw [vilenkin_inversion k f (halfShift k τ), vilenkin_inversion k f τ,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [kernel_halfShift heven]
    rcases Nat.even_or_odd (∑ i, (σ i : ℕ)) with he | ho
    · rw [hσ σ he]; simp
    · rw [ho.neg_one_pow]; ring

/-- **Corollary 43 (sign-changing functions have mean zero).**

**fdrs.md**: Corollary 43 (sign-changing functions). -/
theorem odd_mean_zero {k : ℕ} (heven : ∀ i : Fin (k + 1), 2 ∣ b i)
    (f : FiniteRadixSpace b k → ℂ) (hodd : ∀ τ, f (halfShift k τ) = -f τ) :
    vHat k f (vZero k) = 0 :=
  (odd_iff_vHat heven f).mp hodd _ (by simp [vZero])

/-- **Corollary 43 (sign-changing functions).** A function that changes sign under the
half-shift has energy at most its total influence:
`(1/N) Σ_τ |f(τ)|² ≤ Σ_i D_i(f)²`.

**fdrs.md**: Corollary 43 (sign-changing functions). -/
theorem odd_energy_le_sum_influence {k : ℕ} (heven : ∀ i : Fin (k + 1), 2 ∣ b i)
    (f : FiniteRadixSpace b k → ℂ) (hodd : ∀ τ, f (halfShift k τ) = -f τ) :
    (1 / (placeValue b (k + 1) : ℝ)) * ∑ τ, Complex.normSq (f τ) ≤ ∑ i, influenceSq k i f := by
  have h := variance_le_sum_influence k f
  rw [odd_mean_zero heven f hodd] at h
  simpa only [sub_zero] using h

end FdrsFormal.NumberTheory.Characters.MixedRadixFFT
