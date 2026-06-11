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

# Synthetic place complex SU4a — the partition law (refinement conserves mass)

First piece of the conservation arc (`docs/synthetic-place/00-thesis.md` §3). The
charge is **completion mass**: the number of admissible runs of a given horizon from
a state. The law is a species-(iii) conservation law — a continuity equation in the
sense of the thesis: *no anonymous change*; mass is partitioned by the observed
symbol, never created or destroyed by refinement.

* **`setMass_partition`** — THE PARTITION LAW: the mass of an uncertainty set at
  horizon `n+1` is exactly the sum, over the candidate observations, of the mass
  flowing into each observation class (`setFlux`). Exactness: every unit of mass is
  accounted to exactly one observed symbol. Locality: the per-state flux is computed
  from that state's allowed digits alone.
* **`certified_mass_conservation`** — ZERO LEAK: when the trap fires
  (`candidates = {o}`, SU2's certified emission), the *entire* mass flows through the
  emitted symbol. A certified emission is conditioning on a sure event — it transfers
  mass exactly. Uncertain refinement *partitions* mass; forced emission *transports*
  it.

**Honest scope.** The conserved object is the **edge flow** (sum over `(state, digit)`
pairs), not the post-step uncertainty *set*: `stepSet` is an image and may merge
states, so the set abstraction is sound for the trap but lossy for accounting — the
flux, not the set's mass, is the charge. This is finite-horizon counting (no measure,
no Parry claim; the Fibonacci demos are counts, with the measure connection left as
prose). Leaf module over SU2. No `sorry`; axiom-clean; kernel `decide` only.
-/
import FdrsFormal.Modes.SyntheticPlace.AdmissibilityTrap
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

namespace FdrsFormal.Modes.SyntheticPlace

namespace TransferStructure

open Finset

variable {Q D O : Type*} [DecidableEq Q] [Fintype D] [DecidableEq O]
variable (T : TransferStructure Q D O)

/-! ## 1. Completion mass (the charge) and observed flux (the transfer) -/

/-- **Completion mass**: the number of admissible runs of horizon `n` from `q`. The
recursion *is* the continuity equation: a state's mass is the sum of its admissible
children's masses (Definition 61's `W`, on the transfer substrate). -/
def mass : ℕ → Q → ℕ
  | 0, _ => 1
  | n + 1, q => ∑ d ∈ Finset.univ.filter (fun d => T.allowed q d = true),
      mass n (T.step q d)

/-- Mass of an uncertainty set: total over the consistent states. -/
def setMass (n : ℕ) (S : Finset Q) : ℕ := ∑ q ∈ S, T.mass n q

/-- **Observed flux**: the mass from `q` that flows into observation class `o` — the
admissible one-step continuations whose next observation is `o`, weighted by the
remaining mass. The transfer rule `τ` of the partition law: computed from the state's
local data alone. -/
def flux (n : ℕ) (q : Q) (o : O) : ℕ :=
  ∑ d ∈ Finset.univ.filter
      (fun d => T.allowed q d = true ∧ T.obs (T.step q d) = o),
    T.mass n (T.step q d)

/-- Flux of an uncertainty set into an observation class. -/
def setFlux (n : ℕ) (S : Finset Q) (o : O) : ℕ := ∑ q ∈ S, T.flux n q o

/-! ## 2. The partition law -/

/-- Per-state partition: a state's mass at horizon `n+1` is exactly the sum of its
fluxes into the candidate observation classes of any uncertainty set containing it. -/
theorem mass_partition_state {q : Q} {S : Finset Q} (hq : q ∈ S) (n : ℕ) :
    T.mass (n + 1) q = ∑ o ∈ T.candidates S, T.flux n q o := by
  have hmaps : ∀ d ∈ Finset.univ.filter (fun d => T.allowed q d = true),
      T.obs (T.step q d) ∈ T.candidates S := by
    intro d hd
    rw [Finset.mem_filter] at hd
    exact Finset.mem_image_of_mem _ (T.mem_stepSet.mpr ⟨q, hq, d, hd.2, rfl⟩)
  rw [show T.mass (n + 1) q
      = ∑ d ∈ Finset.univ.filter (fun d => T.allowed q d = true),
          T.mass n (T.step q d) from rfl,
    ← Finset.sum_fiberwise_of_maps_to hmaps (fun d => T.mass n (T.step q d))]
  exact Finset.sum_congr rfl (fun o _ => by
    simp only [flux, Finset.filter_filter])

/-- **SU4a — THE PARTITION LAW (the continuity equation of refinement).** The mass of
an uncertainty set at horizon `n+1` is EXACTLY the sum of its observed fluxes over the
candidate symbols: refinement partitions completion mass by the emitted observation —
no anonymous creation, no anonymous loss. Exact (an equation, not a bound), local
(each flux reads one state's allowed digits), and schedule-free (a state function). -/
theorem setMass_partition (n : ℕ) (S : Finset Q) :
    T.setMass (n + 1) S = ∑ o ∈ T.candidates S, T.setFlux n S o := by
  unfold setMass setFlux
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun q hq => T.mass_partition_state hq n)

/-! ## 3. Zero leak — certified emission transfers mass exactly -/

/-- **ZERO LEAK.** When the admissibility trap fires (`candidates T S = {o}` — SU2's
certified emission), the partition has a single class: the ENTIRE mass of the
uncertainty set flows through the emitted symbol. Certified emission = conditioning
on a sure event = exact mass transport. -/
theorem certified_mass_conservation {S : Finset Q} {o : O}
    (h : T.candidates S = {o}) (n : ℕ) :
    T.setMass (n + 1) S = T.setFlux n S o := by
  rw [T.setMass_partition n S, h, Finset.sum_singleton]

/-- The executable form: whenever `ready` fires, some symbol carries all the mass. -/
theorem ready_mass_conservation {S : Finset Q} (h : T.ready S = true) (n : ℕ) :
    ∃ o : O, T.candidates S = {o} ∧ T.setMass (n + 1) S = T.setFlux n S o := by
  obtain ⟨o, ho⟩ := T.ready_iff.mp h
  exact ⟨o, ho, T.certified_mass_conservation ho n⟩

end TransferStructure

/-! ## 4. Demos — the golden structure: Fibonacci mass, partitioned and conserved -/

-- The golden-mean completion masses ARE the Fibonacci numbers (Zeckendorf counts) —
-- the counting shadow of the gauge growth `fib(n+2) ≤ qₙ` used by M4b:
#eval (List.range 7).map fun n => goldenTransfer.mass n 0   -- [1, 2, 3, 5, 8, 13, 21]
#eval (List.range 7).map fun n => goldenTransfer.mass n 1   -- [1, 1, 2, 3, 5, 8, 13]
-- Partition at the UNCERTAIN state {0}: mass 8 splits as 5 (next obs 0) + 3 (next obs 1):
#eval goldenTransfer.setMass 4 {0}                                       -- 8
#eval (goldenTransfer.setFlux 3 {0} 0, goldenTransfer.setFlux 3 {0} 1)   -- (5, 3)
-- ZERO LEAK at the CERTIFIED state {1}: all mass 5 flows through the forced symbol 0:
#eval goldenTransfer.setMass 4 {1}                                       -- 5
#eval goldenTransfer.setFlux 3 {1} 0                                     -- 5

/-- The zero-leak law, kernel-checked on the golden instance (thesis ledger item 6:
`decide`, never `native_decide`). -/
theorem golden_zero_leak :
    goldenTransfer.setMass 4 {1} = goldenTransfer.setFlux 3 {1} 0 := by decide

/-- And the partition at the uncertain state, kernel-checked: `8 = 5 + 3`. -/
theorem golden_partition :
    goldenTransfer.setMass 4 {0}
      = goldenTransfer.setFlux 3 {0} 0 + goldenTransfer.setFlux 3 {0} 1 := by decide

end FdrsFormal.Modes.SyntheticPlace
