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

# Parry measure on the golden-mean (Zeckendorf) shift — the transition kernel

The bounded-Parry timeline: the golden-mean shift on alphabet `{0,1}` (Zeckendorf,
"no two consecutive 1s"), transition matrix `[[1,1],[1,0]]`, whose fixed place
values are the Fibonacci numbers `Fₙ` — i.e. the committed `RemainderState` ledger
at constant quotient `1`. This file defines the **Parry transition kernel** (the
one-step probabilities of the measure of maximal entropy) and locks in the two
facts the eventual path-measure rests on:

* `goldenP_nonneg`  — probabilities are non-negative (`goldenRatio_pos`);
* `goldenP_sum_one` — **mass conservation**: each row sums to `1`. The non-trivial
  (state-0) row is exactly the golden identity `1/φ + 1/φ² = 1 ⟺ φ² = φ + 1`,
  proved *exactly* (no real-analysis limits), so the integration engine cannot leak
  probability mass.

Eigenvector handling (Option C): `φ = Real.goldenRatio`, characterized purely by
`goldenRatio_sq`. The Perron eigenpair `[[1,1],[1,0]]·(φ,1)ᵀ = φ·(φ,1)ᵀ` is implicit
in the transition probabilities `p_{ij} = A_{ij} r_j /(λ r_i)` and is never computed
abstractly (Mathlib's Perron–Frobenius is not needed). Next: the Fibonacci-gauge
metric on the digit space, then the Ionescu–Tulcea path measure (`Kernel.traj`) and
the Group-G lift.
-/
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.LinearCombination
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace FdrsFormal.Modes.VariableRadix.Subshift.Parry

open Real
open scoped goldenRatio

/-- Parry transition kernel of the golden-mean shift `[[1,1],[1,0]]`:
from state `0` → `0` with prob `1/φ`, → `1` with prob `1/φ²`; from state `1` → `0`
with prob `1` (a `1` must be followed by a `0` — the Zeckendorf "no 11" rule). -/
noncomputable def goldenP (i j : Fin 2) : ℝ :=
  if i = 0 then (if j = 0 then φ⁻¹ else (φ ^ 2)⁻¹)
  else (if j = 0 then 1 else 0)

@[simp] theorem goldenP_00 : goldenP 0 0 = φ⁻¹ := by simp [goldenP]
@[simp] theorem goldenP_01 : goldenP 0 1 = (φ ^ 2)⁻¹ := by simp [goldenP]
@[simp] theorem goldenP_10 : goldenP 1 0 = 1 := by simp [goldenP]
@[simp] theorem goldenP_11 : goldenP 1 1 = 0 := by simp [goldenP]

/-- `φ⁻¹ = φ - 1` — the inverse is itself an element of `ℤ[φ]`, no real-analysis. -/
theorem inv_gold_eq : φ⁻¹ = φ - 1 := by
  rw [inv_goldenRatio]; linarith [goldenRatio_add_goldenConj]

/-- The kernel is non-negative (`φ > 0`). -/
theorem goldenP_nonneg (i j : Fin 2) : 0 ≤ goldenP i j := by
  have h := goldenRatio_pos
  unfold goldenP
  split <;> split <;> first | positivity | norm_num

/-- **Mass conservation.** Each row of the Parry kernel sums to `1`. The state-0 row
is exactly the golden identity `1/φ + 1/φ² = 1` (`= goldenRatio_sq`), proved exactly. -/
theorem goldenP_sum_one (i : Fin 2) : ∑ j, goldenP i j = 1 := by
  fin_cases i
  · -- state 0:  1/φ + 1/φ² = 1
    show ∑ j, goldenP 0 j = 1
    rw [Fin.sum_univ_two, goldenP_00, goldenP_01, inv_gold_eq, ← inv_pow, inv_gold_eq]
    linear_combination goldenRatio_sq
  · -- state 1:  1 + 0 = 1
    show ∑ j, goldenP 1 j = 1
    rw [Fin.sum_univ_two, goldenP_10, goldenP_11]; norm_num

/-! ## The Markov kernel (Chunk 2, step 1) -/

open MeasureTheory ProbabilityTheory

/-- The per-state law of the Parry kernel as a `PMF (Fin 2)`. Summation to `1` is the
mass-conservation identity `goldenP_sum_one`; non-negativity is `goldenP_nonneg`. -/
noncomputable def goldenPMF (i : Fin 2) : PMF (Fin 2) :=
  PMF.ofFintype (fun j => ENNReal.ofReal (goldenP i j)) <| by
    rw [← ENNReal.ofReal_one, ← goldenP_sum_one i,
      ENNReal.ofReal_sum_of_nonneg (fun j _ => goldenP_nonneg i j)]

/-- The Parry transition kernel as a `ProbabilityTheory.Kernel (Fin 2) (Fin 2)`. -/
noncomputable def goldenKernel : Kernel (Fin 2) (Fin 2) :=
  Kernel.ofFunOfCountable (fun i => (goldenPMF i).toMeasure)

/-- It is a Markov kernel — the sole obligation `∀ i, IsProbabilityMeasure (κ i)` is
discharged by `goldenPMF` being a genuine probability mass function. -/
instance : IsMarkovKernel goldenKernel := by
  refine ⟨fun i => ?_⟩
  change IsProbabilityMeasure ((goldenPMF i).toMeasure)
  infer_instance

end FdrsFormal.Modes.VariableRadix.Subshift.Parry
