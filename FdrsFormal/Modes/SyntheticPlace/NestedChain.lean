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

# Synthetic place complex SU6d — the nested chart (synthetic fractions; gauge half of dilation)

The within-digit coupling of `docs/synthetic-place/03-digit-coupling.md` §6, in its
chain core: **one digit of an outer line is implemented by an inner chain** — the
digit's value range is the inner structure's state set, with the recorded exactness
decision: the outer fiber equals the inner mass *on the nose*
(`b p = ∏ c j`). `refineBase` splices the inner block into the outer line; the
theorems say what the splice does to the gauge:

* **`refined_potential_below`** — below the refined position, nothing changes.
* **`refined_potential_inside` — THE SYNTHETIC FRACTION.** Inside the block, the
  gauge is composite: `B_p · C_j` — the inner states sit at resolutions strictly
  between the outer digit's `B_p` and `B_{p+1}`. A synthetic fraction is exactly a
  position inside one outer unit whose denominator is the inner chain's gauge,
  scaled by the outer place value.
* **`refined_potential_top` / `refined_potential_above`** — at the top of the block
  and beyond, the refined gauge REJOINS the outer gauge exactly: under the exactness
  condition, **the chart is gauge-lossless** — the outer line cannot tell, by
  resolution, that one of its digits is secretly a whole structure.
* **`nested_dilation_gauge`** — the gauge half of the dilation theorem: crossing the
  block multiplies resolution by `b p` — one outer increment is worth the inner
  chain's full mass of unit steps. *The gauge is the clock; coupling re-clocks.*

**Honest scope.** This is the position-indexed (chain) core; the prefix-dependent
(`RadixLaw`) version follows the same telescope and is deferred with the general
`NestedLaw`. The DYNAMIC half of dilation — conjugating the tick through the chart,
`tick_outer ∘ φ = φ ∘ tick_inner^k` — remains open (03 §7). Exact charts only
(fiber = inner mass); lossy/quotient charts are the sea's regime, declared not
built. Leaf module over SU6a. No `sorry`; axiom-clean; computable demos. -/
import FdrsFormal.Modes.SyntheticPlace.Grading
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace FdrsFormal.Modes.SyntheticPlace

open Finset

/-! ## 1. Splicing an inner chain into one outer digit -/

/-- Refine position `p` of the outer base sequence `b` by an inner block of `k`
bases `c 0, …, c (k-1)`: positions below `p` unchanged, then the inner block, then
the remaining outer positions, shifted. -/
def refineBase (b : ℕ → ℕ) (p k : ℕ) (c : ℕ → ℕ) : ℕ → ℕ := fun i =>
  if i < p then b i
  else if i < p + k then c (i - p)
  else b (i - k + 1)

/-! ## 2. The gauge through the splice -/

/-- Below the refined position, the gauge is untouched. -/
theorem refined_potential_below (b : ℕ → ℕ) (p k : ℕ) (c : ℕ → ℕ) :
    ∀ i, i ≤ p → chainPotential (refineBase b p k c) i = chainPotential b i := by
  intro i hi
  induction i with
  | zero => rfl
  | succ j ih =>
    have hj : j < p := hi
    simp only [chainPotential, refineBase, if_pos hj]
    rw [ih (Nat.le_of_lt hj)]

/-- **THE SYNTHETIC FRACTION.** Inside the block, the gauge is composite:
`B_p · C_j` — the outer place value times the inner running mass. The inner states
are positions strictly inside one outer unit, at denominators interpolating between
`B_p` and `B_{p+1}`. -/
theorem refined_potential_inside (b : ℕ → ℕ) (p k : ℕ) (c : ℕ → ℕ) :
    ∀ j, j ≤ k → chainPotential (refineBase b p k c) (p + j)
      = chainPotential b p * ∏ i ∈ Finset.range j, (c i : ℚ) := by
  intro j hj
  induction j with
  | zero =>
    simpa using refined_potential_below b p k c p (le_refl p)
  | succ m ih =>
    have hm : m < k := hj
    have hidx : ¬ (p + m < p) := by omega
    have hidx2 : p + m < p + k := by omega
    show chainPotential (refineBase b p k c) (p + m + 1) = _
    simp only [chainPotential, refineBase, if_neg hidx, if_pos hidx2]
    rw [ih (Nat.le_of_lt hm)]
    have hsub : p + m - p = m := by omega
    rw [hsub, Finset.prod_range_succ]
    ring

/-- **The chart is gauge-lossless at the top.** Under exactness (`b p = ∏ c` — the
fiber equals the inner mass on the nose), the refined gauge at the top of the block
equals the outer gauge one position up: the splice rejoins the line exactly. -/
theorem refined_potential_top (b : ℕ → ℕ) (p k : ℕ) (c : ℕ → ℕ)
    (hx : b p = ∏ i ∈ Finset.range k, c i) :
    chainPotential (refineBase b p k c) (p + k) = chainPotential b (p + 1) := by
  rw [refined_potential_inside b p k c k (le_refl k)]
  simp only [chainPotential]
  have hprod : ∀ n, ((∏ i ∈ Finset.range n, c i : ℕ) : ℚ)
      = ∏ i ∈ Finset.range n, (c i : ℚ) := by
    intro n
    induction n with
    | zero => simp
    | succ m ih => rw [Finset.prod_range_succ, Finset.prod_range_succ, Nat.cast_mul, ih]
  have hcast : ((b p : ℚ)) = ∏ i ∈ Finset.range k, (c i : ℚ) := by
    rw [hx, hprod]
  rw [hcast]
  ring

/-- Beyond the block, the refined gauge tracks the outer gauge exactly, forever. -/
theorem refined_potential_above (b : ℕ → ℕ) (p k : ℕ) (c : ℕ → ℕ)
    (hx : b p = ∏ i ∈ Finset.range k, c i) :
    ∀ m, chainPotential (refineBase b p k c) (p + k + m) = chainPotential b (p + 1 + m) := by
  intro m
  induction m with
  | zero => simpa using refined_potential_top b p k c hx
  | succ n ih =>
    have h1 : ¬ (p + k + n < p) := by omega
    have h2 : ¬ (p + k + n < p + k) := by omega
    have h3 : p + k + n - k + 1 = p + 1 + n := by omega
    show chainPotential (refineBase b p k c) (p + k + n + 1) = _
    simp only [chainPotential, refineBase, if_neg h1, if_neg h2, h3]
    rw [ih]
    show (b (p + 1 + n) : ℚ) * _ = chainPotential b (p + 1 + n + 1)
    simp [chainPotential]

/-- **The gauge half of dilation.** Crossing the block multiplies resolution by
exactly `b p`: one outer increment at position `p` is worth the inner chain's full
mass of unit advances. Lipschitz constants are gauge-relative — in the composite
gauge the inner steps are the unit steps, and the outer tick is their `b p`-fold
composite. -/
theorem nested_dilation_gauge (b : ℕ → ℕ) (p k : ℕ) (c : ℕ → ℕ)
    (hx : b p = ∏ i ∈ Finset.range k, c i) :
    chainPotential (refineBase b p k c) (p + k)
      = (b p : ℚ) * chainPotential (refineBase b p k c) p := by
  rw [refined_potential_top b p k c hx,
      refined_potential_below b p k c p (le_refl p)]
  simp [chainPotential]

/-! ## 3. Demo — a decimal digit secretly made of 2 × 5 (exact ℚ, computable) -/

-- outer line: base 10 everywhere; position 1 refined by the inner chain [2, 5]
-- (exactness: 10 = 2 · 5). The refined gauges interpolate: 1, 10, 20, 100, 1000 —
-- the state "20" is a SYNTHETIC FRACTION: two-tenths of the way through the tens
-- digit, denominator B_1 · c_0 = 10 · 2.
#eval (List.range 5).map
  (chainPotential (refineBase (fun _ => 10) 1 2 (fun i => if i = 0 then 2 else 5)))
  -- [1, 10, 20, 100, 1000]
#eval (List.range 5).map (chainPotential (fun _ => (10 : ℕ)))
  -- [1, 10, 100, 1000, 10000]

end FdrsFormal.Modes.SyntheticPlace
