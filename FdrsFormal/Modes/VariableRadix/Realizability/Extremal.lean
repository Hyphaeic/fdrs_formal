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

# Extremal Ultrametrics

This file studies extremal elements in the spectrum of ultrametrics.

## Mathematical Content (fdrs.md Section 6.6)

The p-adic ultrametrics are minimal in the spectrum ordering:
- Constant radix p gives the p-adic distance
- These are "maximally fine" - cannot be further refined while staying SU
- General variable radix ultrametrics are coarsenings of p-adic ones

## References

- fdrs.md, Phase 6, Section 6.6
- DEPENDENCY_BASED_STRUCTURE.md, Modes/VariableRadix/Realizability
- Paper: Theorem B (§6.3)
-/

import FdrsFormal.Modes.VariableRadix.Realizability.Spectrum

namespace FdrsFormal.Modes.VariableRadix

/-!
## p-adic RadixLaw
-/

/-- The p-adic radix law: constant radix p at all positions -/
def padicRadixLaw (p : ℕ) (hp : 2 ≤ p) : RadixLaw where
  radix := fun _ => p
  radix_ge_two := fun _ => hp

/-- p-adic radix law is sibling uniform -/
theorem padic_siblingUniform (p : ℕ) (hp : 2 ≤ p) (k : ℕ) :
    isSiblingUniform (padicRadixLaw p hp) k :=
  positionOnly_siblingUniform (padicRadixLaw p hp) k (fun _ _ _ => rfl)

/-- The p-adic ultrametric spectrum element -/
def padicSpectrum (p : ℕ) (hp : 2 ≤ p) : UltrametricSpectrum :=
  ⟨padicRadixLaw p hp, padic_siblingUniform p hp⟩

/-- For constant radix b, prefixWeight s = b^{s.length} -/
theorem prefixWeight_constant' (b : ℕ) (hb : 2 ≤ b) (s : PrefixWord) :
    prefixWeight (padicRadixLaw b hb) s = b ^ s.length := by
  induction s with
  | nil => simp [prefixWeight]
  | cons d ds ih =>
    simp only [prefixWeight, List.length_cons]
    have h_radix : (padicRadixLaw b hb).radix [] = b := rfl
    rw [h_radix]
    suffices h : prefixWeight { radix := fun s' => (padicRadixLaw b hb).radix (d :: s'),
                                radix_ge_two := fun s' => (padicRadixLaw b hb).radix_ge_two (d :: s') }
                 ds = b ^ ds.length by
      rw [h]; ring
    convert ih using 2

/-!
## p-adic is Minimal
-/

-- NOTE: padic_minimal_aux and padic_minimal were removed because the claim
-- "p-adic is minimal in the SU spectrum" is false. Counterexample: the SU
-- radix law with R(0) = p+1, R(n≥1) = p (position-only, hence SU) satisfies
-- ω' ≤ padicSpectrum p hp (since W(n) = (p+1)·p^{n-1} ≥ p^n for all n),
-- but prefixWeight(ω', [d]) = p+1 > p = p^1, violating the upper bound.
-- The p-adic metric is minimal among *constant-radix* SU laws, but not
-- among all SU laws. A correct statement would restrict to constant radix.

/-- Different primes give incomparable ultrametrics -/
theorem padic_incomparable (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (hne : p ≠ q) :
    ¬(padicSpectrum p hp ≤ padicSpectrum q hq) ∨
    ¬(padicSpectrum q hq ≤ padicSpectrum p hp) := by
  -- padicSpectrum p ≤ padicSpectrum q iff q ≤ p (larger radix = finer = lower in order)
  -- If p ≠ q, then either p < q or q < p, so one direction fails
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · -- p < q: padicSpectrum p ≤ padicSpectrum q requires q ≤ p, which fails
    left
    intro h
    -- h says for all s, (p^{s.length})⁻¹ ≤ (q^{s.length})⁻¹
    -- This means q^{s.length} ≤ p^{s.length} for all s
    -- For s of length 1: q ≤ p, contradicting p < q
    have h1 := h [0]  -- s = [0], length 1
    simp only [padicSpectrum, variableRadixRadius] at h1
    rw [prefixWeight_constant' p hp, prefixWeight_constant' q hq] at h1
    simp only [List.length_singleton] at h1
    -- h1 : (p ^ 1)⁻¹ ≤ (q ^ 1)⁻¹ means q ≤ p
    simp only [pow_one] at h1
    have hq_pos : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hq)
    have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hp)
    rw [inv_le_inv₀ hp_pos hq_pos] at h1
    have hle : q ≤ p := Nat.cast_le.mp h1
    omega
  · -- p > q: padicSpectrum q ≤ padicSpectrum p requires p ≤ q, which fails
    right
    intro h
    have h1 := h [0]
    simp only [padicSpectrum, variableRadixRadius] at h1
    rw [prefixWeight_constant' q hq, prefixWeight_constant' p hp] at h1
    simp only [List.length_singleton] at h1
    simp only [pow_one] at h1
    have hq_pos : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hq)
    have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hp)
    rw [inv_le_inv₀ hq_pos hp_pos] at h1
    have hle : p ≤ q := Nat.cast_le.mp h1
    omega

/-!
## Maximally Coarse Ultrametrics
-/

/-- The trivial radix law: radix 2 everywhere -/
def trivialRadixLaw : RadixLaw where
  radix := fun _ => 2
  radix_ge_two := fun _ => Nat.le_refl 2

/-- Trivial radix law is sibling uniform -/
theorem trivial_siblingUniform (k : ℕ) :
    isSiblingUniform trivialRadixLaw k :=
  positionOnly_siblingUniform trivialRadixLaw k (fun _ _ _ => rfl)

/-- The trivial ultrametric spectrum element -/
def trivialSpectrum : UltrametricSpectrum :=
  ⟨trivialRadixLaw, trivial_siblingUniform⟩

/-- For constant radix b, prefixWeight s = b^{s.length} -/
theorem prefixWeight_constant (b : ℕ) (hb : 2 ≤ b) (s : PrefixWord) :
    prefixWeight (padicRadixLaw b hb) s = b ^ s.length := by
  induction s with
  | nil => simp [prefixWeight]
  | cons d ds ih =>
    simp only [prefixWeight, List.length_cons]
    -- Need to show the inline struct equals padicRadixLaw b hb
    -- Both have radix = fun _ => b, so they're definitionally equal
    have h_radix : (padicRadixLaw b hb).radix [] = b := rfl
    rw [h_radix]
    -- Now need to show prefixWeight of the shifted law equals b ^ ds.length
    -- The shifted law has the same radix function
    suffices h : prefixWeight { radix := fun s' => (padicRadixLaw b hb).radix (d :: s'),
                                radix_ge_two := fun s' => (padicRadixLaw b hb).radix_ge_two (d :: s') }
                 ds = b ^ ds.length by
      rw [h]; ring
    -- The shifted law has radix = fun _ => b (definitionally)
    convert ih using 2

/-- For any radix law ω, prefixWeight ω s ≥ 2^{s.length} -/
theorem prefixWeight_ge_two_pow (ω : RadixLaw) (s : PrefixWord) :
    prefixWeight ω s ≥ 2 ^ s.length := by
  induction s generalizing ω with
  | nil => simp [prefixWeight]
  | cons d ds ih =>
    simp only [prefixWeight, List.length_cons]
    -- The shifted radix law
    let ω' : RadixLaw := {
      radix := fun s' => ω.radix (d :: s')
      radix_ge_two := fun s' => ω.radix_ge_two (d :: s')
    }
    have h_ih := ih ω'
    have h_radix : ω.radix [] ≥ 2 := ω.radix_ge_two []
    calc ω.radix [] * prefixWeight ω' ds
        ≥ 2 * prefixWeight ω' ds := Nat.mul_le_mul_right _ h_radix
      _ ≥ 2 * 2 ^ ds.length := Nat.mul_le_mul_left _ h_ih
      _ = 2 ^ (ds.length + 1) := by ring

/-- For trivialRadixLaw, prefixWeight s = 2^{s.length} -/
theorem prefixWeight_trivial (s : PrefixWord) :
    prefixWeight trivialRadixLaw s = 2 ^ s.length := by
  induction s with
  | nil => simp [prefixWeight]
  | cons d ds ih =>
    simp only [prefixWeight, List.length_cons]
    have h_radix : trivialRadixLaw.radix [] = 2 := rfl
    rw [h_radix]
    suffices h : prefixWeight { radix := fun s' => trivialRadixLaw.radix (d :: s'),
                                radix_ge_two := fun s' => trivialRadixLaw.radix_ge_two (d :: s') }
                 ds = 2 ^ ds.length by
      rw [h]; ring
    convert ih using 2

/-- The trivial ultrametric is maximal in the 2-adic chain -/
theorem trivial_maximal_2adic :
    isMaximalInSpectrum trivialSpectrum := by
  intro ω' hle
  intro s
  -- Need: variableRadixRadius ω'.val s ≤ variableRadixRadius trivialSpectrum.val s
  -- ω'.val has the coercion to RadixLaw, trivialSpectrum.val = trivialRadixLaw
  have hle_s := hle s
  simp only [variableRadixRadius, trivialSpectrum] at hle_s ⊢
  -- hle_s : (prefixWeight trivialRadixLaw s)⁻¹ ≤ (prefixWeight ω'.val s)⁻¹
  have h_trivial : prefixWeight trivialRadixLaw s = 2 ^ s.length := prefixWeight_trivial s
  have h_ge := prefixWeight_ge_two_pow ω'.val s
  rw [h_trivial] at hle_s ⊢
  -- hle_s : (2 ^ s.length : ℝ)⁻¹ ≤ (prefixWeight ω'.val s : ℝ)⁻¹
  -- h_ge : prefixWeight ω'.val s ≥ 2 ^ s.length
  have hpw_pos : (0 : ℝ) < prefixWeight ω'.val s :=
    Nat.cast_pos.mpr (prefixWeight_pos ω'.val s)
  have h2_pos : (0 : ℝ) < (2 ^ s.length : ℕ) :=
    Nat.cast_pos.mpr (Nat.pow_pos (by norm_num : 0 < 2))
  -- From hle_s and inv_le_inv₀: (2 ^ s.length)⁻¹ ≤ (prefixWeight ω'.val s)⁻¹ ↔ prefixWeight ω'.val s ≤ 2 ^ s.length
  have h_le : (prefixWeight ω'.val s : ℝ) ≤ (2 ^ s.length : ℕ) := by
    rw [← inv_le_inv₀ h2_pos hpw_pos]
    exact hle_s
  have h_eq : prefixWeight ω'.val s = 2 ^ s.length := by
    have h_le_nat : prefixWeight ω'.val s ≤ 2 ^ s.length := Nat.cast_le.mp h_le
    exact Nat.le_antisymm h_le_nat h_ge
  rw [h_eq]

/-!
## Comparison with Fixed Radix
-/

/-- Fixed radix b gives a chain from trivial (b=2) toward minimality -/
theorem fixedRadix_chain (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hle : b₁ ≤ b₂) :
    padicSpectrum b₂ hb₂ ≤ padicSpectrum b₁ hb₁ := by
  -- Larger radix = finer metric = lower in the dominance order
  -- Need: variableRadixRadius (padicRadixLaw b₂) s ≤ variableRadixRadius (padicRadixLaw b₁) s
  intro s
  simp only [padicSpectrum, variableRadixRadius]
  -- Use the prefixWeight_constant helper
  rw [prefixWeight_constant b₁ hb₁, prefixWeight_constant b₂ hb₂]
  -- Goal: (b₂ ^ s.length : ℝ)⁻¹ ≤ (b₁ ^ s.length : ℝ)⁻¹
  -- Goal: (b₂ ^ s.length : ℝ)⁻¹ ≤ (b₁ ^ s.length : ℝ)⁻¹
  have h_b₁_pos : (0 : ℝ) < (b₁ ^ s.length : ℕ) := by
    have h : 0 < b₁ := Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hb₁
    exact Nat.cast_pos.mpr (Nat.pow_pos h)
  have h_b₂_pos : (0 : ℝ) < (b₂ ^ s.length : ℕ) := by
    have h : 0 < b₂ := Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hb₂
    exact Nat.cast_pos.mpr (Nat.pow_pos h)
  rw [inv_le_inv₀ h_b₂_pos h_b₁_pos]
  exact Nat.cast_le.mpr (Nat.pow_le_pow_left hle s.length)

/-- The constant-2 radix (binary) is maximal among constant radix laws -/
theorem binary_maximal_constant :
    ∀ (p : ℕ) (hp : 2 ≤ p), padicSpectrum p hp ≤ padicSpectrum 2 (Nat.le_refl 2) := by
  intro p hp
  exact fixedRadix_chain 2 p (Nat.le_refl 2) hp hp

end FdrsFormal.Modes.VariableRadix
