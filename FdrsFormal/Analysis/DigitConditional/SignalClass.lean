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

# The Digit-Conditional Signal Class

Signal taxonomy: constant ⊂ periodic ⊂ Vilenkin ⊂ digit-conditional ⊂ ℝ^I.

## Mathematical Content (fdrs.md §11.3)

**Definition 168**: Signal taxonomy — five nested signal classes
**Proposition 133**: Strict class hierarchy — each inclusion strict for N ≥ 6

## References

- fdrs.md, Phase 11, Sections 11.3.1–11.3.2
-/

import FdrsFormal.Analysis.DigitConditional.Decomposition

namespace FdrsFormal.Analysis.DigitConditional

/-! ## Definition 168: Signal taxonomy -/

/--
**fdrs.md**: Definition 168 (Signal taxonomy) [§11.3.1 · Phase 11]

Nested signal classes on I = Fin N:
1. Constant signals C
2. Periodic signals Per (depend only on n mod b₀)
3. Vilenkin-measurable signals Vil (measurable w.r.t. product filtration)
4. Digit-conditional signals DC (adapted to a non-trivial partition)
5. All signals ℝ^I
-/
def IsConstantSignal {N : ℕ} (f : Fin N → ℝ) : Prop :=
  ∀ i j : Fin N, f i = f j

def IsPeriodicSignal {N : ℕ} (b₀ : ℕ) (f : Fin N → ℝ) : Prop :=
  ∀ i j : Fin N, i.val % b₀ = j.val % b₀ → f i = f j

/--
A signal is **digit-conditional** if there exists an assignment of the N points
into k < N classes such that f is constant on each class. Equivalently, f is
piecewise constant on a partition of Fin N into fewer than N blocks.

This generalizes the tree-adapted notion (Definition 166) to arbitrary (possibly
non-contiguous) partitions, which is necessary to capture periodic/coset
structure. Any tree-adapted signal with leafCount < N satisfies this definition.
-/
def IsDigitConditional {N : ℕ} (f : Fin N → ℝ) : Prop :=
  ∃ k : ℕ, k < N ∧ ∃ assign : Fin N → Fin k,
    ∀ i j : Fin N, assign i = assign j → f i = f j

/-- The signal taxonomy forms nested inclusions. -/
theorem constant_subset_periodic {N : ℕ} (b₀ : ℕ) (f : Fin N → ℝ)
    (hf : IsConstantSignal f) : IsPeriodicSignal b₀ f :=
  fun i j _ => hf i j

theorem periodic_implies_digitConditional {N : ℕ} (b₀ : ℕ)
    (hb : b₀ ≥ 1) (hbN : b₀ < N) (f : Fin N → ℝ)
    (hf : IsPeriodicSignal b₀ f) : IsDigitConditional f := by
  -- Assign each element to its residue class mod b₀
  refine ⟨b₀, hbN, fun i => ⟨i.val % b₀, Nat.mod_lt _ (by omega)⟩, ?_⟩
  intro i j hij
  exact hf i j (congr_arg Fin.val hij)

/-! ## Proposition 133: Strict class hierarchy -/

/--
**fdrs.md**: Proposition 133 (Strict class hierarchy) [§11.3.2 · Phase 11]

For N ≥ 6 with b₀ ≥ 2 a proper divisor (b₀ < N),
each inclusion in the taxonomy is strict.
-/
theorem strictClassHierarchy (N : ℕ) (hN : N ≥ 6) (b₀ : ℕ) (hb : b₀ ≥ 2)
    (hbN : b₀ < N) (_hdiv : b₀ ∣ N) :
    -- There exist signals separating each adjacent pair of classes
    (∃ f : Fin N → ℝ, IsPeriodicSignal b₀ f ∧ ¬IsConstantSignal f) ∧
    (∃ f : Fin N → ℝ, IsDigitConditional f ∧ ¬IsPeriodicSignal b₀ f) ∧
    (∃ f : Fin N → ℝ, ¬IsDigitConditional f) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1: Periodic but not constant: f(i) = if i % b₀ = 0 then 1 else 0
    refine ⟨fun i => if i.val % b₀ = 0 then 1 else 0, ?_, ?_⟩
    · intro i j hij; simp only [hij]
    · intro hconst
      have h01 := hconst ⟨0, by omega⟩ ⟨1, by omega⟩
      have hmod1 : (1 : ℕ) % b₀ = 1 := Nat.mod_eq_of_lt (by omega)
      simp [Nat.zero_mod, hmod1] at h01
  · -- Part 2: DC but not periodic: f(i) = if i < b₀ then 0 else 1
    refine ⟨fun i => if i.val < b₀ then (0 : ℝ) else 1, ?_, ?_⟩
    · -- IsDigitConditional: assign to 2 classes (< b₀ or ≥ b₀), and 2 < N
      refine ⟨2, by omega, fun i => if i.val < b₀ then ⟨0, by omega⟩ else ⟨1, by omega⟩, ?_⟩
      intro i j hij
      -- hij has the form (fun i => if ...) i = (fun i => if ...) j; beta-reduce
      dsimp only at hij
      by_cases hi : i.val < b₀ <;> by_cases hj : j.val < b₀
      · simp [hi, hj]
      · exfalso; rw [if_pos hi, if_neg hj] at hij; simp at hij
      · exfalso; rw [if_neg hi, if_pos hj] at hij; simp at hij
      · simp [hi, hj]
    · -- ¬IsPeriodicSignal b₀: f(0) = 0 but f(b₀) = 1, yet 0 ≡ b₀ (mod b₀)
      intro hper
      have h := hper ⟨0, by omega⟩ ⟨b₀, hbN⟩ (by
        simp only [Nat.zero_mod, Nat.mod_self])
      change (if (⟨0, _⟩ : Fin N).val < b₀ then (0 : ℝ) else 1) =
             (if (⟨b₀, _⟩ : Fin N).val < b₀ then 0 else 1) at h
      have h0 : (0 : ℕ) < b₀ := by omega
      have hb₀ : ¬(b₀ < b₀) := by omega
      rw [if_pos h0, if_neg hb₀] at h
      exact absurd h (by norm_num)
  · -- Part 3: Not DC: f(i) = i (injective, so needs N classes)
    refine ⟨fun i => (i.val : ℝ), ?_⟩
    intro ⟨k, hk, assign, hconst⟩
    -- f is injective (Fin.val cast to ℝ is injective)
    -- But assign : Fin N → Fin k with k < N cannot be injective (pigeonhole)
    -- So ∃ i ≠ j with assign i = assign j, giving f i = f j, i.e. i.val = j.val, i.e. i = j — contradiction
    have : ∃ i j : Fin N, i ≠ j ∧ assign i = assign j := by
      by_contra hall
      push_neg at hall
      -- hall says assign is injective
      have hinj : Function.Injective assign := by
        intro a b heq
        by_contra hne
        exact hall a b hne heq
      have := Fintype.card_le_of_injective assign hinj
      simp at this
      omega
    obtain ⟨i, j, hne, heq⟩ := this
    have hfij : (i.val : ℝ) = (j.val : ℝ) := hconst i j heq
    have : i = j := Fin.ext (by exact_mod_cast hfij)
    exact absurd this hne

end FdrsFormal.Analysis.DigitConditional
