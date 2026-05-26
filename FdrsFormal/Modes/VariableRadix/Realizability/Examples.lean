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

# Engineered Ultrametric Examples

This file provides examples of engineered ultrametrics via variable radix.

## Mathematical Content (fdrs.md Section 6.4, Example 6.4.2)

**Prescribed cylinder volumes**: Given a desired volume function V: ⋃_L Σ_L → ℝ_{>0},
we can find ω such that β_ω(s) = V(s) when V satisfies the consistency condition:
  V(s∥d) / V(s) is independent of digit d

This shows the flexibility of variable radix systems for metric design.

## References

- fdrs.md, Phase 6, Section 6.4 (lines 5260-5275)
- DEPENDENCY_BASED_STRUCTURE.md, Modes/VariableRadix/Realizability
-/

import FdrsFormal.Modes.VariableRadix.Realizability.Spectrum
import FdrsFormal.Modes.VariableRadix.Encoding.SubtreeCards

namespace FdrsFormal.Modes.VariableRadix

/-!
## General Lemma for Position-Only Radix Laws

For radix laws that depend only on prefix length, completionCount is a product.
-/

/-- Helper: create a list of length n filled with 0s -/
private def zeroPrefix (n : ℕ) : PrefixWord := List.replicate n 0

/-- For position-only laws, ω.shift d and ω.shift e have the same radix function -/
theorem shift_radix_eq_of_positionOnly (ω : RadixLaw)
    (h_posOnly : ∀ s t : PrefixWord, s.length = t.length → ω.radix s = ω.radix t)
    (d e : ℕ) (s : PrefixWord) :
    (ω.shift d).radix s = (ω.shift e).radix s := by
  simp only [RadixLaw.shift]
  apply h_posOnly
  simp

/-- For position-only laws, completionCount is the same for all shifted laws at the same depth -/
theorem completionCount_shift_eq_of_positionOnly (ω : RadixLaw) (k : ℕ)
    (h_posOnly : ∀ s t : PrefixWord, s.length = t.length → ω.radix s = ω.radix t)
    (d e : ℕ) (s : PrefixWord) (hs : s.length ≤ k + 1) :
    completionCount (ω.shift d) k s = completionCount (ω.shift e) k s := by
  -- Induction on k + 1 - s.length
  obtain ⟨n, hn⟩ : ∃ n, n = k + 1 - s.length := ⟨_, rfl⟩
  induction n using Nat.strongRecOn generalizing s with
  | _ n ih =>
    by_cases heq : s.length = k + 1
    · -- Base case: s has full length
      rw [completionCount_of_length_eq (ω.shift d) k s heq]
      rw [completionCount_of_length_eq (ω.shift e) k s heq]
    · -- Recursive case
      have hlt : s.length < k + 1 := Nat.lt_of_le_of_ne hs heq
      rw [completionCount_rec (ω.shift d) k s hlt]
      rw [completionCount_rec (ω.shift e) k s hlt]
      -- Show the ranges are equal
      have h_radix_eq : (ω.shift d).radix s = (ω.shift e).radix s :=
        shift_radix_eq_of_positionOnly ω h_posOnly d e s
      rw [h_radix_eq]
      -- Show the terms are equal
      apply Finset.sum_congr rfl
      intro j _
      -- Need: completionCount (ω.shift d) k (s ++ [j]) = completionCount (ω.shift e) k (s ++ [j])
      have hle_ext : (s ++ [j]).length ≤ k + 1 := by simp; omega
      have hdec : k + 1 - (s ++ [j]).length < n := by simp at hn ⊢; omega
      exact ih (k + 1 - (s ++ [j]).length) hdec (s ++ [j]) hle_ext rfl

/-- For position-only radix laws, completionCount equals the product of radices at each depth -/
theorem completionCount_positionOnly_prod (ω : RadixLaw) (k : ℕ)
    (h_posOnly : ∀ s t : PrefixWord, s.length = t.length → ω.radix s = ω.radix t) :
    completionCount ω k [] = (Finset.range (k + 1)).prod (fun i => ω.radix (zeroPrefix i)) := by
  induction k generalizing ω with
  | zero =>
    -- completionCount ω 0 [] = ω.radix []
    rw [completionCount_rec ω 0 [] (by simp)]
    simp only [List.nil_append]
    have h : ∀ d ∈ Finset.range (ω.radix []), completionCount ω 0 [d] = 1 := by
      intro d _; exact completionCount_of_length_eq ω 0 [d] (by simp)
    calc (Finset.range (ω.radix [])).sum (fun d => completionCount ω 0 [d])
        = (Finset.range (ω.radix [])).sum (fun _ => 1) := by
            apply Finset.sum_congr rfl; intro d hd; exact h d hd
      _ = ω.radix [] := by simp [Finset.sum_const, Finset.card_range]
      _ = ω.radix (zeroPrefix 0) := by simp [zeroPrefix]
      _ = (Finset.range 1).prod (fun i => ω.radix (zeroPrefix i)) := by
            simp [Finset.range_one, Finset.prod_singleton]
  | succ k ih =>
    -- completionCount ω (k+1) [] = ∑_{d < ω.radix []} completionCount ω (k+1) [d]
    rw [completionCount_rec ω (k + 1) [] (by simp)]
    simp only [List.nil_append]
    -- For position-only, all terms in the sum are equal
    have h_shift : ∀ d, completionCount ω (k + 1) [d] = completionCount (ω.shift d) k [] := by
      intro d
      have h := completionCount_shift_general ω k d []
      simp at h; exact h
    have h_same : ∀ d, completionCount (ω.shift d) k [] = completionCount (ω.shift 0) k [] := by
      intro d
      exact completionCount_shift_eq_of_positionOnly ω k h_posOnly d 0 [] (by simp)
    have h_posOnly' : ∀ s t : PrefixWord, s.length = t.length → (ω.shift 0).radix s = (ω.shift 0).radix t := by
      intro s t hlen
      simp only [RadixLaw.shift]
      apply h_posOnly
      simp [hlen]
    have h_radix_shift : ∀ i, (ω.shift 0).radix (zeroPrefix i) = ω.radix (zeroPrefix (i + 1)) := by
      intro i
      simp only [RadixLaw.shift, zeroPrefix]
      apply h_posOnly
      simp [List.length_replicate]
    calc (Finset.range (ω.radix [])).sum (fun d => completionCount ω (k + 1) [d])
        = (Finset.range (ω.radix [])).sum (fun d => completionCount (ω.shift d) k []) := by
            apply Finset.sum_congr rfl; intro d _; exact h_shift d
      _ = (Finset.range (ω.radix [])).sum (fun _ => completionCount (ω.shift 0) k []) := by
            apply Finset.sum_congr rfl; intro d _; exact h_same d
      _ = ω.radix [] * completionCount (ω.shift 0) k [] := by
            simp [Finset.sum_const, Finset.card_range]
      _ = ω.radix [] * (Finset.range (k + 1)).prod (fun i => (ω.shift 0).radix (zeroPrefix i)) := by
            rw [ih (ω.shift 0) h_posOnly']
      _ = ω.radix [] * (Finset.range (k + 1)).prod (fun i => ω.radix (zeroPrefix (i + 1))) := by
            have h_eq : (Finset.range (k + 1)).prod (fun i => (ω.shift 0).radix (zeroPrefix i)) =
                        (Finset.range (k + 1)).prod (fun i => ω.radix (zeroPrefix (i + 1))) := by
              apply Finset.prod_congr rfl; intro j _; exact h_radix_shift j
            rw [h_eq]
      _ = (Finset.range (k + 1 + 1)).prod (fun i => ω.radix (zeroPrefix i)) := by
            have h := Finset.prod_range_succ' (fun i => ω.radix (zeroPrefix i)) (k + 1)
            rw [h]
            simp only [zeroPrefix, List.replicate_zero]
            ring

/-!
## Example 1: Factorial Radix
-/

/-- Factorial radix: ω(s) = |s| + 2 (radix grows with depth) -/
def factorialRadixLaw : RadixLaw where
  radix := fun s => s.length + 2
  radix_ge_two := fun s => Nat.le_add_left 2 s.length

/-- Factorial radix is sibling uniform (depends only on depth) -/
theorem factorial_siblingUniform (k : ℕ) :
    isSiblingUniform factorialRadixLaw k :=
  positionOnly_siblingUniform factorialRadixLaw k (fun s t heq => by
    simp only [factorialRadixLaw, heq])

/-- Helper: shifted factorial radix with base n has radix s.length + n -/
private def shiftedFactorialRadix (n : ℕ) (hn : 2 ≤ n) : RadixLaw where
  radix := fun s => s.length + n
  radix_ge_two := fun s => Nat.le_add_left n s.length |> Nat.le_trans hn

/-- factorialRadixLaw equals shiftedFactorialRadix 2 -/
private theorem factorial_eq_shifted : factorialRadixLaw = shiftedFactorialRadix 2 (Nat.le_refl 2) := by
  simp only [factorialRadixLaw, shiftedFactorialRadix]

/-- Shifting the shifted factorial radix increases n by 1 -/
private theorem shiftedFactorial_shift (n : ℕ) (hn : 2 ≤ n) (d : ℕ) :
    (shiftedFactorialRadix n hn).shift d = shiftedFactorialRadix (n + 1) (Nat.le_succ_of_le hn) := by
  simp only [RadixLaw.shift, shiftedFactorialRadix]
  congr 1
  ext s
  simp only [List.length_cons]
  omega

/-- Card of shifted factorial radix: card (shiftedFactorialRadix n) depth = n * (n+1) * ... * (n+depth) -/
private theorem shiftedFactorial_card (n : ℕ) (hn : 2 ≤ n) (depth : ℕ) :
    FiniteVariableSpace.card (shiftedFactorialRadix n hn) depth =
      (Finset.range (depth + 1)).prod (fun i => n + i) := by
  induction depth generalizing n with
  | zero =>
    -- card 0 = radix [] = n
    -- RHS = prod over {0} of (n + i) = n + 0 = n
    unfold FiniteVariableSpace.card shiftedFactorialRadix
    simp only [List.length_nil, Finset.range_one, Finset.prod_singleton, Nat.add_zero, Nat.zero_add]
  | succ d ih =>
    -- card (d+1) = sum_{x < radix []} card (shift x) d
    unfold FiniteVariableSpace.card
    -- For shifted factorial, radix [] = n and shift x = shiftedFactorialRadix (n+1)
    have h_radix : (shiftedFactorialRadix n hn).radix [] = n := by
      unfold shiftedFactorialRadix
      simp
    have h_shift_eq : ∀ x, (shiftedFactorialRadix n hn).shift x =
        shiftedFactorialRadix (n + 1) (Nat.le_succ_of_le hn) :=
      shiftedFactorial_shift n hn
    -- Each term in the sum equals prod_{i=0}^{d} (n+1+i)
    have h_term : ∀ x, FiniteVariableSpace.card ((shiftedFactorialRadix n hn).shift x) d =
          (Finset.range (d + 1)).prod (fun i => n + 1 + i) := by
      intro x
      rw [h_shift_eq x]
      exact ih (n + 1) (Nat.le_succ_of_le hn)
    -- Sum of n copies of the same value
    rw [h_radix]
    have hsum : (Finset.range n).sum (fun x => FiniteVariableSpace.card ((shiftedFactorialRadix n hn).shift x) d)
        = n * (Finset.range (d + 1)).prod (fun i => n + 1 + i) := by
      calc (Finset.range n).sum (fun x => FiniteVariableSpace.card ((shiftedFactorialRadix n hn).shift x) d)
          = (Finset.range n).sum (fun _ => (Finset.range (d + 1)).prod (fun i => n + 1 + i)) := by
              apply Finset.sum_congr rfl; intro x _; exact h_term x
        _ = n * (Finset.range (d + 1)).prod (fun i => n + 1 + i) := by
              simp [Finset.sum_const, Finset.card_range]
    rw [hsum]
    -- n * prod_{i=0}^{d} (n+1+i) = prod_{i=0}^{d+1} (n+i)
    -- First transform LHS: n + 1 + i = n + (i + 1)
    have h_lhs : (Finset.range (d + 1)).prod (fun i => n + 1 + i) =
                 (Finset.range (d + 1)).prod (fun i => n + (i + 1)) := by
      apply Finset.prod_congr rfl; intro j _; ring
    rw [h_lhs]
    -- Now use prod_range_succ' on RHS
    have h_rhs := Finset.prod_range_succ' (fun i => n + i) (d + 1)
    -- h_rhs : ∏ i ∈ Finset.range (d + 2), (n + i) = (n + 0) * ∏ k ∈ Finset.range (d + 1), (n + (k + 1))
    simp only [Nat.add_zero] at h_rhs
    rw [h_rhs]
    ring

/--
The factorial radix space has size (k+2)!

With factorial radix ω(s) = |s| + 2, the space size is:
∏_{i=0}^{k} (i + 2) = 2 × 3 × 4 × ... × (k+2) = (k+2)!
-/
theorem factorial_spaceSize (k : ℕ) :
    completionCount factorialRadixLaw k [] = Nat.factorial (k + 2) := by
  rw [completionCount_nil, factorial_eq_shifted, shiftedFactorial_card]
  -- Need: prod_{i=0}^{k} (2 + i) = (k+2)!
  induction k with
  | zero =>
    native_decide
  | succ k ih =>
    rw [Finset.prod_range_succ, Nat.factorial_succ, ← ih]
    ring

/-!
## Example 2: Primorial Radix
-/

/-- The nth prime (placeholder - should use mathlib) -/
def nthPrime : ℕ → ℕ
  | 0 => 2
  | 1 => 3
  | 2 => 5
  | 3 => 7
  | 4 => 11
  | 5 => 13
  | _ => 17  -- Placeholder for larger primes

/-- Primorial radix: ω(s) = p_{|s|} (radix is the |s|th prime) -/
def primorialRadixLaw : RadixLaw where
  radix := fun s => nthPrime s.length
  radix_ge_two := fun s => by
    -- All primes are ≥ 2 by definition
    simp only [nthPrime]
    split <;> omega

/-- Primorial radix is sibling uniform -/
theorem primorial_siblingUniform (k : ℕ) :
    isSiblingUniform primorialRadixLaw k :=
  positionOnly_siblingUniform primorialRadixLaw k (fun s t heq => by
    simp only [primorialRadixLaw, heq])

/-!
## Example 3: Custom Volume Function
-/

/-- A volume function on prefixes with integer branching factors.

A volume function V assigns a positive real volume to each prefix, with V(∅) = 1.
The consistency condition ensures all children of a node have equal volume.
The branching factor provides the integer number of children at each node,
with the relationship V(s) = branchingFactor(s) · V(s ++ [0]). -/
structure VolumeFunction where
  volume : PrefixWord → ℝ
  volume_pos : ∀ s, 0 < volume s
  volume_root : volume [] = 1
  /-- Consistency: V(s∥d)/V(s) independent of d -/
  consistent : ∀ s d₁ d₂, volume (s ++ [d₁]) / volume s = volume (s ++ [d₂]) / volume s
  /-- Integer branching factor at each prefix -/
  branchingFactor : PrefixWord → ℕ
  branching_ge_two : ∀ s, 2 ≤ branchingFactor s
  /-- Volume decomposes as branching factor times child volume -/
  volume_ratio : ∀ s, volume s = ↑(branchingFactor s) * volume (s ++ [0])

/-- Construct a RadixLaw from a volume function -/
def radixLawFromVolume (V : VolumeFunction) : RadixLaw where
  radix := V.branchingFactor
  radix_ge_two := V.branching_ge_two

/-- All children of a node have equal volume (from consistency). -/
private theorem VolumeFunction.volume_children_eq (V : VolumeFunction)
    (s : PrefixWord) (d₁ d₂ : ℕ) :
    V.volume (s ++ [d₁]) = V.volume (s ++ [d₂]) := by
  have hc := V.consistent s d₁ d₂
  have hs_ne := ne_of_gt (V.volume_pos s)
  rw [div_eq_div_iff hs_ne hs_ne] at hc
  exact mul_right_cancel₀ hs_ne hc

/-- Child volume formula: V(s ++ [d]) = V(s) / branchingFactor(s). -/
private theorem VolumeFunction.volume_child (V : VolumeFunction)
    (s : PrefixWord) (d : ℕ) :
    V.volume (s ++ [d]) = V.volume s / ↑(V.branchingFactor s) := by
  have h_eq := V.volume_children_eq s d 0
  have h_ratio := V.volume_ratio s
  have hbf_ne : (V.branchingFactor s : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by linarith [V.branching_ge_two s])
  rw [h_eq, h_ratio]
  field_simp

/--
The induced prefix weight is the reciprocal of the volume.

For ω = radixLawFromVolume V: prefixWeight(ω, s) · V(s) = 1.

**Proof**: By induction on s (snoc pattern). For s = ∅: 1 · 1 = 1.
For s = s' ++ [d]: by `prefixWeight_append`, the prefix weight factors as
prefixWeight(ω, s') · ω.radix(s'), and by `volume_child`, the volume is
V(s') / bf(s'). Since ω.radix = bf by construction, the factor cancels
and the result reduces to the inductive hypothesis.
-/
theorem radixFromVolume_prefixWeight (V : VolumeFunction) (s : PrefixWord) :
    (prefixWeight (radixLawFromVolume V) s : ℝ) * V.volume s = 1 := by
  induction s using List.reverseRecOn with
  | nil => simp [V.volume_root]
  | append_singleton s d ih =>
    rw [prefixWeight_append, Nat.cast_mul, V.volume_child s d,
      show (radixLawFromVolume V).radix s = V.branchingFactor s from rfl]
    have hbf_ne : (V.branchingFactor s : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (by linarith [V.branching_ge_two s])
    field_simp
    exact ih

/-!
## Example 4: Geometric Radix
-/

/-- Geometric radix: ω(s) = 2^{|s|+1} (exponentially growing) -/
def geometricRadixLaw : RadixLaw where
  radix := fun s => 2 ^ (s.length + 1)
  radix_ge_two := fun s => by
    have h1 : 1 ≤ s.length + 1 := Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero _)
    calc 2 = 2 ^ 1 := (Nat.pow_one 2).symm
      _ ≤ 2 ^ (s.length + 1) := Nat.pow_le_pow_right (by omega) h1

/-- Geometric radix is sibling uniform -/
theorem geometric_siblingUniform (k : ℕ) :
    isSiblingUniform geometricRadixLaw k :=
  positionOnly_siblingUniform geometricRadixLaw k (fun s t heq => by
    simp only [geometricRadixLaw, heq])

/-- Helper: shifted geometric radix with base exponent n -/
private def shiftedGeometricRadix (n : ℕ) (hn : 1 ≤ n) : RadixLaw where
  radix := fun s => 2 ^ (s.length + n)
  radix_ge_two := fun s => by
    have h : 1 ≤ s.length + n := Nat.le_add_left n s.length |> Nat.le_trans hn
    calc 2 = 2 ^ 1 := (Nat.pow_one 2).symm
      _ ≤ 2 ^ (s.length + n) := Nat.pow_le_pow_right (by omega) h

/-- geometricRadixLaw equals shiftedGeometricRadix 1 -/
private theorem geometric_eq_shifted : geometricRadixLaw = shiftedGeometricRadix 1 (Nat.le_refl 1) := by
  simp only [geometricRadixLaw, shiftedGeometricRadix]

/-- Shifting the shifted geometric radix increases n by 1 -/
private theorem shiftedGeometric_shift (n : ℕ) (hn : 1 ≤ n) (d : ℕ) :
    (shiftedGeometricRadix n hn).shift d = shiftedGeometricRadix (n + 1) (Nat.le_succ_of_le hn) := by
  simp only [RadixLaw.shift, shiftedGeometricRadix]
  congr 1
  ext s
  simp only [List.length_cons]
  ring

/-- Card of shifted geometric radix -/
private theorem shiftedGeometric_card (n : ℕ) (hn : 1 ≤ n) (depth : ℕ) :
    FiniteVariableSpace.card (shiftedGeometricRadix n hn) depth =
      2 ^ (Finset.range (depth + 1)).sum (fun i => n + i) := by
  induction depth generalizing n with
  | zero =>
    unfold FiniteVariableSpace.card shiftedGeometricRadix
    simp
  | succ d ih =>
    unfold FiniteVariableSpace.card
    have h_radix : (shiftedGeometricRadix n hn).radix [] = 2 ^ n := by
      unfold shiftedGeometricRadix; simp
    have h_shift_eq : ∀ x, (shiftedGeometricRadix n hn).shift x =
        shiftedGeometricRadix (n + 1) (Nat.le_succ_of_le hn) :=
      shiftedGeometric_shift n hn
    have h_term : ∀ x, FiniteVariableSpace.card ((shiftedGeometricRadix n hn).shift x) d =
          2 ^ (Finset.range (d + 1)).sum (fun i => n + 1 + i) := by
      intro x
      rw [h_shift_eq x]
      exact ih (n + 1) (Nat.le_succ_of_le hn)
    rw [h_radix]
    have hsum : (Finset.range (2 ^ n)).sum (fun x => FiniteVariableSpace.card ((shiftedGeometricRadix n hn).shift x) d)
        = 2 ^ n * 2 ^ (Finset.range (d + 1)).sum (fun i => n + 1 + i) := by
      calc (Finset.range (2 ^ n)).sum (fun x => FiniteVariableSpace.card ((shiftedGeometricRadix n hn).shift x) d)
          = (Finset.range (2 ^ n)).sum (fun _ => 2 ^ (Finset.range (d + 1)).sum (fun i => n + 1 + i)) := by
              apply Finset.sum_congr rfl; intro x _; exact h_term x
        _ = 2 ^ n * 2 ^ (Finset.range (d + 1)).sum (fun i => n + 1 + i) := by
              simp [Finset.sum_const, Finset.card_range]
    rw [hsum, ← Nat.pow_add]
    congr 1
    -- n + ∑ i ∈ Finset.range (d+1), (n+1+i) = ∑ i ∈ Finset.range (d+2), (n+i)
    have h_sum_eq : (Finset.range (d + 1)).sum (fun i => n + 1 + i) =
                    (Finset.range (d + 1)).sum (fun i => n + (i + 1)) := by
      apply Finset.sum_congr rfl; intro j _; ring
    rw [h_sum_eq]
    have h_rhs := Finset.sum_range_succ' (fun i => n + i) (d + 1)
    simp only [Nat.add_zero] at h_rhs
    -- h_rhs : ∑ k ∈ Finset.range (d + 2), (n + k) = n + ∑ k ∈ Finset.range (d + 1), (n + (k + 1))
    linarith [h_rhs]

/-- Space size for geometric radix -/
theorem geometric_spaceSize (k : ℕ) :
    completionCount geometricRadixLaw k [] = 2 ^ ((k + 1) * (k + 2) / 2) := by
  rw [completionCount_nil, geometric_eq_shifted, shiftedGeometric_card]
  -- Need: 2 ^ ∑ i ∈ Finset.range (k+1), (1 + i) = 2 ^ ((k+1) * (k+2) / 2)
  congr 1
  -- ∑ i ∈ Finset.range (k+1), (1 + i) = ∑ j ∈ Finset.range (k+1), (j + 1) = (k+1)(k+2)/2
  have h_sum : (Finset.range (k + 1)).sum (fun i => 1 + i) = (k + 1) * (k + 2) / 2 := by
    -- Induction on k
    induction k with
    | zero => native_decide
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      -- Goal: (k + 1) * (k + 2) / 2 + (1 + (k + 1)) = (k + 2) * (k + 3) / 2
      -- One of k+1 or k+2 is even, so (k+1)*(k+2) is divisible by 2
      have h_even : 2 ∣ (k + 1) * (k + 2) := by
        rcases Nat.even_or_odd (k + 1) with ⟨m, hm⟩ | ⟨m, hm⟩
        · exact ⟨m * (k + 2), by rw [hm]; ring⟩
        · have hk2 : k + 2 = 2 * (m + 1) := by omega
          exact ⟨(k + 1) * (m + 1), by rw [hk2]; ring⟩
      -- Similar divisibility for (k+2)*(k+3)
      have h_even2 : 2 ∣ (k + 2) * (k + 3) := by
        rcases Nat.even_or_odd (k + 2) with ⟨m, hm⟩ | ⟨m, hm⟩
        · exact ⟨m * (k + 3), by rw [hm]; ring⟩
        · have hk3 : k + 3 = 2 * (m + 1) := by omega
          exact ⟨(k + 2) * (m + 1), by rw [hk3]; ring⟩
      -- Extract the quotients
      obtain ⟨q1, hq1⟩ := h_even
      obtain ⟨q2, hq2⟩ := h_even2
      -- Rewrite using the quotients
      have h1 : (k + 1) * (k + 2) / 2 = q1 := by rw [hq1]; exact Nat.mul_div_cancel_left q1 (by omega)
      have h2 : (k + 2) * (k + 3) / 2 = q2 := by rw [hq2]; exact Nat.mul_div_cancel_left q2 (by omega)
      rw [h1, h2]
      -- Now prove q1 + (1 + (k + 1)) = q2, i.e., q1 + k + 2 = q2
      -- From hq1: (k + 1) * (k + 2) = 2 * q1
      -- From hq2: (k + 2) * (k + 3) = 2 * q2
      -- So 2 * q2 - 2 * q1 = (k + 2) * (k + 3) - (k + 1) * (k + 2) = (k + 2) * 2
      -- Thus q2 - q1 = k + 2, so q1 + k + 2 = q2
      have hkey : q2 = q1 + (k + 2) := by
        have h3 : 2 * q2 = 2 * q1 + 2 * (k + 2) := by
          calc 2 * q2 = (k + 2) * (k + 3) := hq2.symm
            _ = (k + 2) * (k + 1 + 2) := by ring
            _ = (k + 2) * (k + 1) + (k + 2) * 2 := by ring
            _ = (k + 1) * (k + 2) + 2 * (k + 2) := by ring
            _ = 2 * q1 + 2 * (k + 2) := by rw [hq1]
        omega
      omega
  exact h_sum

end FdrsFormal.Modes.VariableRadix
