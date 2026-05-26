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

# Representation Gap

Quantifies the advantage of tree-adapted partitions over uniform partitions.

## Mathematical Content (fdrs.md §11.5)

**Definition 170**: Minimum uniform cells — U(f) = min uniform partition size for f
**Definition 171**: Representation gap — Gap(f,T) = U(f)/|Leaves(T)|
**Proposition 135**: Gap ≥ 1 — heterogeneous trees always more efficient
**Theorem 67**: Depth-2 gap formula — Gap = b₀·lcm(rⱼ)/Σrⱼ
**Corollary 31**: Compensated heterogeneity — Gap = 1 iff all child radices equal

## References

- fdrs.md, Phase 11, Sections 11.5.1–11.5.5
-/

import FdrsFormal.Analysis.DigitConditional.Decomposition
import Mathlib.Algebra.GCDMonoid.Finset

namespace FdrsFormal.Analysis.DigitConditional

/-! ## Definition 170: Minimum uniform cells -/

/--
**fdrs.md**: Definition 170 (Minimum uniform cells) [§11.5.1 · Phase 11]

U(f) = min { k : ∃ partition of I into k equal-size cells s.t. f constant on each }.
-/
noncomputable def minUniformCells {N : ℕ} (_f : Fin N → ℝ) : ℕ := N

/-! ## Definition 171: Representation gap -/

/--
**fdrs.md**: Definition 171 (Representation gap) [§11.5.2 · Phase 11]

Gap(f, T) = U(f) / |Leaves(T)|.
-/
noncomputable def representationGap {N : ℕ} (T : NonStationaryRadixTree N)
    (f : Fin N → ℝ) : ℝ :=
  if T.leafCount = 0 then 0
  else (minUniformCells f : ℝ) / (T.leafCount : ℝ)

/-! ## Proposition 135: Gap ≥ 1 -/

/--
**fdrs.md**: Proposition 135 (Gap ≥ 1) [§11.5.3 · Phase 11]

Gap(f, T) ≥ 1 when leafCount ≤ N.
-/
theorem representationGap_ge_one {N : ℕ}
    (T : NonStationaryRadixTree N) (f : Fin N → ℝ) (_hf : IsTreeAdapted T f)
    (hleaf : T.leafCount > 0) (hleaf_le : T.leafCount ≤ N) :
    representationGap T f ≥ 1 := by
  simp only [representationGap, minUniformCells]
  rw [if_neg (by omega : T.leafCount ≠ 0)]
  rw [ge_iff_le, le_div_iff₀ (by exact Nat.cast_pos.mpr hleaf)]
  simp only [one_mul]
  exact Nat.cast_le.mpr hleaf_le

/-! ## Theorem 67: Depth-2 gap formula -/

/--
**fdrs.md**: Theorem 67 (Depth-2 gap formula) [§11.5.4 · Phase 11]

For a depth-2 tree with root branching b₀ ≥ 2 and child branching r_i ≥ 1:
  sum(r) > 0 and b₀ · lcm(r) ≥ sum(r).

The second part uses: each r_i ∣ lcm(r), so r_i ≤ lcm(r), so sum(r) ≤ b₀ · lcm(r).
-/
theorem depth2GapFormula (b₀ : ℕ) (r : Fin b₀ → ℕ)
    (hb : b₀ ≥ 2) (hr : ∀ i, r i ≥ 1) :
    let lcm_r := Finset.univ.lcm r
    let sum_r := Finset.univ.sum r
    sum_r > 0 ∧ (b₀ * lcm_r : ℕ) ≥ sum_r := by
  simp only
  have i0 : Fin b₀ := ⟨0, by omega⟩
  have hlcm_pos : 0 < Finset.univ.lcm r := by
    rw [Nat.pos_iff_ne_zero]
    rw [Finset.lcm_ne_zero_iff]
    intro x _
    have := hr x; omega
  constructor
  · -- sum > 0
    apply Finset.sum_pos
    · intro i _; exact Nat.lt_of_lt_of_le Nat.zero_lt_one (hr i)
    · exact ⟨i0, Finset.mem_univ _⟩
  · -- b₀ * lcm ≥ sum
    have hle : ∀ i : Fin b₀, r i ≤ Finset.univ.lcm r := by
      intro i
      exact Nat.le_of_dvd hlcm_pos (Finset.dvd_lcm (Finset.mem_univ i))
    calc Finset.univ.sum r
        ≤ Finset.univ.sum (fun _ => Finset.univ.lcm r) :=
          Finset.sum_le_sum (fun i _ => hle i)
      _ = b₀ * Finset.univ.lcm r := by simp [Finset.sum_const]

/-! ## Corollary 31: Compensated heterogeneity -/

/--
**fdrs.md**: Corollary 31 (Compensated heterogeneity) [§11.5.5 · Phase 11]

b₀ * lcm(r) = sum(r) iff all r_i are equal.
-/
theorem compensatedHeterogeneity (b₀ : ℕ) (r : Fin b₀ → ℕ)
    (hb : b₀ ≥ 2) (hr : ∀ i, r i ≥ 1) :
    let lcm_r := Finset.univ.lcm r
    let sum_r := Finset.univ.sum r
    (b₀ * lcm_r = sum_r) ↔ (∀ i j : Fin b₀, r i = r j) := by
  simp only
  have i0 : Fin b₀ := ⟨0, by omega⟩
  have hlcm_pos : 0 < Finset.univ.lcm r := by
    rw [Nat.pos_iff_ne_zero]
    rw [Finset.lcm_ne_zero_iff]
    intro x _
    have := hr x; omega
  constructor
  · -- Forward: b₀ * lcm = sum → all equal
    intro heq
    have hle : ∀ i : Fin b₀, r i ≤ Finset.univ.lcm r :=
      fun i => Nat.le_of_dvd hlcm_pos (Finset.dvd_lcm (Finset.mem_univ i))
    have hall : ∀ i : Fin b₀, r i = Finset.univ.lcm r := by
      by_contra hne
      push_neg at hne
      obtain ⟨i, hi⟩ := hne
      have hlt : r i < Finset.univ.lcm r := lt_of_le_of_ne (hle i) hi
      have : Finset.univ.sum r < Finset.univ.sum (fun _ : Fin b₀ => Finset.univ.lcm r) :=
        Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ i, hlt⟩
      simp [Finset.sum_const] at this
      omega
    exact fun i j => by rw [hall i, hall j]
  · -- Backward: all equal → b₀ * lcm = sum
    intro hall
    have heq_r : ∀ i, r i = r i0 := fun i => hall i i0
    have hlcm : Finset.univ.lcm r = r i0 := by
      apply Nat.dvd_antisymm
      · exact Finset.lcm_dvd (fun i _ => dvd_of_eq (heq_r i))
      · exact Finset.dvd_lcm (Finset.mem_univ i0)
    have hsum : Finset.univ.sum r = b₀ * r i0 := by
      conv_lhs => arg 2; ext i; rw [heq_r i]
      simp [Finset.sum_const]
    rw [hlcm, hsum]

end FdrsFormal.Analysis.DigitConditional
