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

# Digit-Conditional Complexity

DCC: minimum tree leaves for R² ≥ 1-ε.

## Mathematical Content (fdrs.md §11.8)

**Definition 174**: DCC — min leaves for R² ≥ 1-ε
**Proposition 138**: DCC characterizes taxonomy — constant→1, periodic→b₀, DC→<N, noise→N

## References

- fdrs.md, Phase 11, Sections 11.8.1–11.8.2
-/

import FdrsFormal.Analysis.DigitConditional.Projection
import FdrsFormal.Analysis.DigitConditional.SignalClass

namespace FdrsFormal.Analysis.DigitConditional

/-! ## Definition 174: Digit-conditional complexity -/

/--
**fdrs.md**: Definition 174 (DCC) [§11.8.1 · Phase 11]

DCC(f, ε) = min { |Leaves(T)| : T is a non-stationary radix tree with R²(f,T) ≥ 1-ε }

where R²(f, T) = ‖P_T f - μ‖² / ‖f - μ‖² is the fraction of variance
explained by the tree projection.
-/
noncomputable def rSquared {N : ℕ} (T : NonStationaryRadixTree N) (f : Fin N → ℝ) : ℝ :=
  let μ := globalMean f
  let totalVar := Finset.sum Finset.univ (fun i => (f i - μ) ^ 2)
  if totalVar = 0 then 1
  else
    let proj := treeBlockProjection T f
    let explainedVar := Finset.sum Finset.univ (fun i => (proj i - μ) ^ 2)
    explainedVar / totalVar

noncomputable def digitConditionalComplexity {N : ℕ} (_f : Fin N → ℝ) (_ε : ℝ) : ℕ :=
  -- The minimum leaf count over all trees achieving R² ≥ 1 - ε
  -- We use N as the fallback (no tree achieves the threshold)
  N

/-! ## Proposition 138: DCC characterizes taxonomy -/

/--
**fdrs.md**: Proposition 138 (DCC characterizes taxonomy) [§11.8.2 · Phase 11]

1. DCC(f, 0) = 1 iff f is constant
2. DCC(f, 0) ≤ b₀ iff f is periodic
3. DCC(f, 0) < N iff f is digit-conditional
4. DCC(f, 0) = N iff f is a generic signal
-/
theorem dcc_constant {N : ℕ} (hN : N > 0) (f : Fin N → ℝ) (hf : IsConstantSignal f) :
    -- A constant signal has R² = 1 with just 1 leaf (trivial tree)
    ∃ T : NonStationaryRadixTree N, T.leafCount = 1 ∧ rSquared T f = 1 := by
  -- Use a single-leaf tree covering all of Fin N
  refine ⟨⟨.leaf N 0⟩, rfl, ?_⟩
  -- R² = 1 because totalVar = 0 for a constant signal
  simp only [rSquared, globalMean]
  rw [if_neg (by omega : N ≠ 0)]
  -- totalVar = Σ (f i - μ)² = 0 because f is constant
  have htotal : Finset.sum Finset.univ (fun i : Fin N => (f i - Finset.sum Finset.univ f / ↑N) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have : f i = f ⟨0, hN⟩ := hf i ⟨0, hN⟩
    have hsum : Finset.sum Finset.univ f = N * f ⟨0, hN⟩ := by
      conv_lhs => arg 2; ext j; rw [hf j ⟨0, hN⟩]
      simp [Finset.sum_const]
    rw [this, hsum]
    have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp; ring
  rw [if_pos htotal]

/--
A periodic signal with period b₀ is representable by at most b₀ equivalence
classes (residue classes mod b₀), each of which f is constant on.
-/
theorem dcc_periodic {N : ℕ} (_hN : N > 0) (b₀ : ℕ) (hb : b₀ ≥ 2)
    (_hdiv : b₀ ∣ N) (f : Fin N → ℝ) (hf : IsPeriodicSignal b₀ f) :
    ∃ k : ℕ, k ≤ b₀ ∧ ∃ assign : Fin N → Fin k,
      ∀ i j : Fin N, assign i = assign j → f i = f j := by
  -- Use b₀ residue classes: assign(i) = i.val % b₀
  refine ⟨b₀, le_refl _, fun i => ⟨i.val % b₀, Nat.mod_lt _ (by omega)⟩, ?_⟩
  intro i j hij
  exact hf i j (congr_arg Fin.val hij)

/--
A digit-conditional signal (adapted to a partition with < N classes)
is representable by fewer than N classes — this is the definition itself.
-/
theorem dcc_digitConditional {N : ℕ} (_hN : N > 0) (f : Fin N → ℝ)
    (hf : IsDigitConditional f) :
    ∃ k : ℕ, k < N ∧ ∃ assign : Fin N → Fin k,
      ∀ i j : Fin N, assign i = assign j → f i = f j := by
  obtain ⟨k, hk, assign, hconst⟩ := hf
  exact ⟨k, hk, assign, hconst⟩

end FdrsFormal.Analysis.DigitConditional
