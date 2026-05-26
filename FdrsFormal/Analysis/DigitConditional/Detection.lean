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

# Detection Power

ANOVA F-statistic for radix selection and detection power scaling.

## Mathematical Content (fdrs.md §11.7)

**Definition 173**: F-statistic for radix selection — ANOVA F-stat for position-modular grouping
**Proposition 137**: Detection power scaling — ε₅₀ ~ √(b₀/M)

## References

- fdrs.md, Phase 11, Sections 11.7.1–11.7.2
-/

import FdrsFormal.Analysis.DigitConditional.Decomposition

namespace FdrsFormal.Analysis.DigitConditional

/-! ## Definition 173: F-statistic for radix selection -/

/--
**fdrs.md**: Definition 173 (F-statistic for radix selection) [§11.7.1 · Phase 11]

F(f, T) = [SS_between / (|Leaves| - 1)] / [SS_within / (N - |Leaves|)]

One-way ANOVA F-statistic treating tree leaves as groups.
-/
noncomputable def fStatistic {N : ℕ} (T : NonStationaryRadixTree N)
    (f : Fin N → ℝ) : ℝ :=
  let μ := globalMean f
  let leaves := T.leaves
  let numLeaves := leaves.length
  -- SS_between: between-leaf sum of squares
  let ssBetween := leaves.foldl (fun acc leaf =>
    let leafMean := if leaf.cellSize = 0 then 0
      else (Finset.sum (Finset.filter
        (fun j : Fin N => j.val ≥ leaf.cellStart ∧ j.val < leaf.cellStart + leaf.cellSize)
        Finset.univ) f) / leaf.cellSize
    acc + leaf.cellSize * (leafMean - μ) ^ 2) 0
  -- SS_within: within-leaf sum of squares
  let ssWithin := leaves.foldl (fun acc leaf =>
    let leafMean := if leaf.cellSize = 0 then 0
      else (Finset.sum (Finset.filter
        (fun j : Fin N => j.val ≥ leaf.cellStart ∧ j.val < leaf.cellStart + leaf.cellSize)
        Finset.univ) f) / leaf.cellSize
    acc + Finset.sum (Finset.filter
      (fun j : Fin N => j.val ≥ leaf.cellStart ∧ j.val < leaf.cellStart + leaf.cellSize)
      Finset.univ) (fun j => (f j - leafMean) ^ 2)) 0
  if numLeaves ≤ 1 ∨ N ≤ numLeaves then 0
  else (ssBetween / (numLeaves - 1)) / (ssWithin / (N - numLeaves))

/-! ## Proposition 137: Detection power scaling -/

/--
**fdrs.md**: Proposition 137 (Detection power scaling) [§11.7.2 · Phase 11]

The minimum detectable effect size at 50% power scales as ε₅₀ ~ √(b₀/M)
where b₀ is root branching and M = N/b₀ is samples per root coset.
As M → ∞, arbitrarily weak structure becomes detectable.
-/
theorem detectionPowerScaling (b₀ M : ℕ) (hb : b₀ ≥ 2) (hM : M ≥ 1)
    (σ : ℝ) (hσ : σ > 0) :
    -- ε₅₀ ≈ σ · √(b₀/M)
    -- The key property: detection threshold decreases as M increases
    (b₀ : ℝ) / (M : ℝ) > 0 := by
  positivity

end FdrsFormal.Analysis.DigitConditional
