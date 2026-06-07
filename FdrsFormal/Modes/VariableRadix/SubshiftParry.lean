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
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Martingale.Convergence

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

/-! ## The Parry stationary initial law `π ∝ (φ², 1)` (defined upfront, isolated) -/

/-- Parry stationary weights `π ∝ (φ², 1)`, normalized by `φ² + 1`. For the symmetric
golden-mean matrix this is `lᵢ rᵢ`; equivalently the unique law with `π · goldenP = π`. -/
noncomputable def goldenStat (j : Fin 2) : ℝ :=
  if j = 0 then φ ^ 2 / (φ ^ 2 + 1) else 1 / (φ ^ 2 + 1)

theorem golden_sq_add_one_pos : 0 < φ ^ 2 + 1 := by positivity

@[simp] theorem goldenStat_0 : goldenStat 0 = φ ^ 2 / (φ ^ 2 + 1) := by simp [goldenStat]
@[simp] theorem goldenStat_1 : goldenStat 1 = 1 / (φ ^ 2 + 1) := by simp [goldenStat]

theorem goldenStat_nonneg (j : Fin 2) : 0 ≤ goldenStat j := by
  unfold goldenStat; split <;> positivity

/-- Normalization: the stationary weights sum to `1`. -/
theorem goldenStat_sum_one : ∑ j, goldenStat j = 1 := by
  rw [Fin.sum_univ_two, goldenStat_0, goldenStat_1, div_add_div_same,
    div_self (ne_of_gt golden_sq_add_one_pos)]

/-- **Stationarity**: `π · goldenP = π`, i.e. `π` is `goldenP`-invariant — so the trajectory
measure built from it is genuinely the (shift-invariant) Parry measure. Each row reduces to
the golden identity `φ² = φ + 1`. -/
theorem goldenStat_stationary (j : Fin 2) :
    ∑ i, goldenStat i * goldenP i j = goldenStat j := by
  have hd : φ ^ 2 + 1 ≠ 0 := ne_of_gt golden_sq_add_one_pos
  have hsq : φ ^ 2 = φ + 1 := goldenRatio_sq
  fin_cases j
  · show ∑ i, goldenStat i * goldenP i 0 = goldenStat 0
    rw [Fin.sum_univ_two, goldenStat_0, goldenStat_1, goldenP_00, goldenP_10, inv_gold_eq]
    -- make φ opaque so `field_simp`/`ring` don't unfold the abbrev to √5
    set p := φ with hp
    field_simp
    linear_combination (p - 1) * hsq
  · show ∑ i, goldenStat i * goldenP i 1 = goldenStat 1
    rw [Fin.sum_univ_two, goldenStat_0, goldenStat_1, goldenP_01, goldenP_11, ← inv_pow, inv_gold_eq]
    set p := φ with hp
    field_simp
    linear_combination (p ^ 2 - p + 1) * hsq

/-- The Parry stationary law as a `PMF (Fin 2)`. -/
noncomputable def goldenStatPMF : PMF (Fin 2) :=
  PMF.ofFintype (fun j => ENNReal.ofReal (goldenStat j)) <| by
    rw [← ENNReal.ofReal_one, ← goldenStat_sum_one,
      ENNReal.ofReal_sum_of_nonneg (fun j _ => goldenStat_nonneg j)]

/-! ## Injecting the homogeneous chain into the `traj` family shape (Chunk 2, step 2) -/

/-- Extract the current (time-`n`) state from a history `Π i : Iic n, Fin 2`. The index
`⟨n, mem_Iic.2 le_rfl⟩` pulls the exact `n`-th coordinate (`Iic n` is `Finset.Iic n = [0,n]`). -/
def coord (n : ℕ) : (Π _i : Finset.Iic n, Fin 2) → Fin 2 :=
  fun x => x ⟨n, Finset.mem_Iic.2 le_rfl⟩

theorem measurable_coord (n : ℕ) : Measurable (coord n) := measurable_pi_apply _

/-- The golden kernel as the history-dependent family `Kernel.traj` expects: the law of the
next state depends only on the current one (`comap` along `coord`). This is where the
homogeneous Markov chain is injected into the general history-dependent API. -/
noncomputable def goldenFam (n : ℕ) : Kernel (Π _i : Finset.Iic n, Fin 2) (Fin 2) :=
  goldenKernel.comap (coord n) (measurable_coord n)

/-- Each `goldenFam n` is Markov — `comap` of a Markov kernel by a measurable map. -/
instance instMarkovGoldenFam (n : ℕ) : IsMarkovKernel (goldenFam n) := by
  unfold goldenFam; infer_instance

/-! ## The Parry path measure via Ionescu–Tulcea (Chunk 2, step 3) -/

/-- The Ionescu–Tulcea trajectory kernel for the golden-mean chain: from a state at time `0`
to the whole path `ℕ → Fin 2`, with countable additivity supplied by Mathlib's `Kernel.traj`. -/
noncomputable def parryTraj := Kernel.traj (X := fun _ => Fin 2) goldenFam 0

/-- The stationary law on the time-`0` history space `Π i : Iic 0, Fin 2` (a single
coordinate, `Iic 0 = {0}`) — the product of the one factor `goldenStatPMF`. -/
noncomputable def parryInit : Measure (Π _i : Finset.Iic 0, Fin 2) :=
  Measure.pi (fun _ => goldenStatPMF.toMeasure)

/-- **The Parry path measure** on `ℕ → Fin 2`: the stationary law `π` pushed through the
Ionescu–Tulcea trajectory kernel. Countably additive on the canonical `MeasurableSpace.pi`,
and (by stationarity of `π`) the genuine shift-invariant measure of maximal entropy. -/
noncomputable def parryMeasure : Measure (Π _n : ℕ, Fin 2) :=
  parryInit.bind parryTraj

instance : IsMarkovKernel parryTraj := by unfold parryTraj; infer_instance
instance : IsProbabilityMeasure parryInit := by unfold parryInit; infer_instance
instance : IsProbabilityMeasure parryMeasure := by unfold parryMeasure; infer_instance

/-! ## Group G on the golden timeline: the Lévy upward engine (Chunk 3) -/

/-- The coordinate filtration `piLE` exhausts the product σ-algebra: `⨆ L, piLE L = pi`.
This is the lone obligation Lévy's upward theorem requires. (Each `piLE L ≤ pi`; conversely
`pi = ⨆ j, comap (eval j)` and `eval j` factors through `frestrictLe j`, so
`comap (eval j) ≤ piLE j`.) -/
theorem iSup_piLE_eq_pi :
    ⨆ L : ℕ, (Filtration.piLE (X := fun _ : ℕ => Fin 2) L : MeasurableSpace (ℕ → Fin 2))
      = MeasurableSpace.pi := by
  refine le_antisymm (iSup_le fun L => (Filtration.piLE (X := fun _ => Fin 2)).le L) ?_
  unfold MeasurableSpace.pi
  refine iSup_le fun j => le_iSup_of_le j ?_
  rw [Filtration.piLE_eq_comap_frestrictLe]
  have hfac : (fun f : ℕ → Fin 2 => f j)
      = (fun g : (i : Finset.Iic j) → Fin 2 => g ⟨j, Finset.mem_Iic.2 le_rfl⟩)
        ∘ Preorder.frestrictLe j := rfl
  calc MeasurableSpace.comap (fun f : ℕ → Fin 2 => f j) inferInstance
      = MeasurableSpace.comap (Preorder.frestrictLe j)
          (MeasurableSpace.comap (fun g : (i : Finset.Iic j) → Fin 2 => g ⟨j, Finset.mem_Iic.2 le_rfl⟩)
            inferInstance) := by rw [hfac, MeasurableSpace.comap_comp]
    _ ≤ MeasurableSpace.comap (Preorder.frestrictLe j) MeasurableSpace.pi :=
        MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le

/-- **Group G on the golden timeline (Lévy upward).** For any integrable, measurable `f`, the
block conditional expectations over the coordinate filtration converge to `f` in `L¹` under the
Parry measure: `E[f | ℱ_L] → f`. This is the integration engine, running natively on the
generated golden-mean timeline — no metric, no bespoke topology, just Mathlib's classical
martingale convergence on the canonical `pi` σ-algebra. -/
theorem parry_condExp_tendsto {f : (ℕ → Fin 2) → ℝ} (hf : Integrable f parryMeasure)
    (hf' : StronglyMeasurable f) :
    Filter.Tendsto
      (fun L => eLpNorm (parryMeasure[f|Filtration.piLE (X := fun _ => Fin 2) L] - f) 1 parryMeasure)
      Filter.atTop (nhds 0) := by
  refine hf.tendsto_eLpNorm_condExp ?_
  rw [iSup_piLE_eq_pi]
  exact hf'

end FdrsFormal.Modes.VariableRadix.Subshift.Parry
