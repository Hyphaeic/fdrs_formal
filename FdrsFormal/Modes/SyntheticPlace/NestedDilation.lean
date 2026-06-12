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

# Synthetic place complex SU6d′ — dilation, dynamic half: exact nesting is conservative

Closes the "dilation theorem, dynamic half" row of
`docs/synthetic-place/03-digit-coupling.md` §7 — by the observation that makes it
nearly free: **the exact splice never leaves Mode 0.** `refineBase` with the
exactness condition produces a bona fide ordinary radix line
(`refineBase_ge_two`), so the chart between the outer and refined lines is
VALUE-PRESERVING — both lines enumerate the same ℕ — and tick conjugation is
definitional at the value level (both ticks are `+1` under decode, the Core
transport). The certified content is therefore the three identities that make the
chart digit-faithful:

* **`chainPlace_refine_above`** (ℕ moduli agreement): above the block, the refined
  line's place values equal the outer line's — same moduli ⟹ same congruence
  structure ⟹ same cylinders (Prop 6) at every depth beyond the block.
* **`refined_digit_reblock`** — THE RE-BLOCKING IDENTITY: for every value `n`, the
  outer digit at position `p` is exactly the inner mixed-radix decode of the refined
  line's block digits. The chart is digit *grouping* — classical (base 10 read as
  base 2×5), here certified against the spliced gauge.
* **`dilation_tick`** — the `k`-fold tick reading: advancing the value by one outer
  unit (`B_p` — under exactness, the inner block's full mass of unit ticks)
  increments the outer digit at `p` by exactly one. The outer tick IS the
  `B_p`-fold inner tick, read through the chart.

Together: **exact nesting is conservative over classical FDRS — it adds resolution,
never arithmetic.** The synthetic-fraction machinery (SU6d) refines what a line can
*see*, not what it *computes*. This is the anchor the network arc builds hierarchical
nodes on.

**Honest scope.** Digit grouping is classical positional arithmetic; the artifact is
the certified statement against `refineBase`/`chainPlace`. The chart here is stated
on values and digit extractions (`(n / B) % b` — the corpus's Prop-1 extraction
shape), not re-threaded through `DirectLimitSpace`; with equal moduli and Prop 6,
the topological transfer is the corpus's existing machinery and is cited, not
re-proven. Inexact/lossy splices (the sea's regime) remain open. Leaf module over
SU6d. No `sorry`; axiom-clean; computable demos.
-/
import FdrsFormal.Modes.SyntheticPlace.NestedChain

namespace FdrsFormal.Modes.SyntheticPlace

open Finset

/-! ## 1. ℕ place values, and the splice through them -/

/-- The place value of a function-form chain (`Core`'s `placeValue`, function form;
`chainPotential` is its ℚ cast — `chainPotential_eq_chainPlace`). -/
def chainPlace (b : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | i + 1 => b i * chainPlace b i

theorem chainPlace_pos (b : ℕ → ℕ) (hb : ∀ i, 0 < b i) : ∀ i, 0 < chainPlace b i := by
  intro i
  induction i with
  | zero => norm_num [chainPlace]
  | succ j ih => simpa [chainPlace] using Nat.mul_pos (hb j) ih

theorem chainPotential_eq_chainPlace (b : ℕ → ℕ) (i : ℕ) :
    chainPotential b i = (chainPlace b i : ℚ) := by
  induction i with
  | zero => simp [chainPotential, chainPlace]
  | succ j ih =>
    simp only [chainPotential, chainPlace, ih]
    push_cast
    ring

/-- **Conservativity at the type level**: the exact splice of a valid inner block
into a valid radix line is again a valid radix line — within-digit coupling with
exact charts never leaves Mode 0. -/
theorem refineBase_ge_two (b : ℕ → ℕ) (p k : ℕ) (c : ℕ → ℕ)
    (hb : ∀ i, 2 ≤ b i) (hc : ∀ j, j < k → 2 ≤ c j) :
    ∀ i, 2 ≤ refineBase b p k c i := by
  intro i
  by_cases h1 : i < p
  · simpa [refineBase, h1] using hb i
  · by_cases h2 : i < p + k
    · have hik : i - p < k := by omega
      simpa [refineBase, h1, h2] using hc _ hik
    · simpa [refineBase, h1, h2] using hb _

theorem chainPlace_refine_below (b : ℕ → ℕ) (p k : ℕ) (c : ℕ → ℕ) :
    ∀ i, i ≤ p → chainPlace (refineBase b p k c) i = chainPlace b i := by
  intro i hi
  induction i with
  | zero => rfl
  | succ j ih =>
    have hj : j < p := hi
    simp only [chainPlace, refineBase, if_pos hj]
    rw [ih (Nat.le_of_lt hj)]

/-- The ℕ synthetic fraction: inside the block the place value is composite,
`B_p · C_j`. -/
theorem chainPlace_refine_inside (b : ℕ → ℕ) (p k : ℕ) (c : ℕ → ℕ) :
    ∀ j, j ≤ k → chainPlace (refineBase b p k c) (p + j)
      = chainPlace b p * ∏ i ∈ Finset.range j, c i := by
  intro j hj
  induction j with
  | zero => simpa using chainPlace_refine_below b p k c p (le_refl p)
  | succ m ih =>
    have hm : m < k := hj
    have hidx : ¬ (p + m < p) := by omega
    have hidx2 : p + m < p + k := by omega
    show chainPlace (refineBase b p k c) (p + m + 1) = _
    simp only [chainPlace, refineBase, if_neg hidx, if_pos hidx2]
    rw [ih (Nat.le_of_lt hm)]
    have hsub : p + m - p = m := by omega
    rw [hsub, Finset.prod_range_succ]
    ring

/-- **ℕ moduli agreement above the block**: under exactness, the refined line and
the outer line carry the SAME place values from the top of the block on — same
moduli, same congruence structure, same cylinders (Prop 6). -/
theorem chainPlace_refine_above (b : ℕ → ℕ) (p k : ℕ) (c : ℕ → ℕ)
    (hx : b p = ∏ i ∈ Finset.range k, c i) :
    ∀ m, chainPlace (refineBase b p k c) (p + k + m) = chainPlace b (p + 1 + m) := by
  intro m
  induction m with
  | zero =>
    show chainPlace (refineBase b p k c) (p + k) = chainPlace b (p + 1)
    rw [chainPlace_refine_inside b p k c k (le_refl k), ← hx]
    simp only [chainPlace]
    ring
  | succ n ih =>
    have h1 : ¬ (p + k + n < p) := by omega
    have h2 : ¬ (p + k + n < p + k) := by omega
    have h3 : p + k + n - k + 1 = p + 1 + n := by omega
    show chainPlace (refineBase b p k c) (p + k + n + 1) = _
    simp only [chainPlace, refineBase, if_neg h1, if_neg h2, h3]
    rw [ih]
    show b (p + 1 + n) * _ = chainPlace b (p + 1 + n + 1)
    simp [chainPlace]

/-! ## 2. The re-blocking identity (the chart is digit grouping) -/

/-- The finite mixed-radix decomposition of a residue — the digits of a digit:
`m mod ∏c = Σ_j (block digit j) · C_j`. -/
theorem mod_prod_eq_sum_digits (c : ℕ → ℕ) :
    ∀ (k m : ℕ), m % (∏ i ∈ Finset.range k, c i)
      = ∑ j ∈ Finset.range k,
          ((m / ∏ i ∈ Finset.range j, c i) % c j) * ∏ i ∈ Finset.range j, c i := by
  intro k
  induction k with
  | zero => intro m; simp [Nat.mod_one]
  | succ n ih =>
    intro m
    rw [Finset.prod_range_succ, Nat.mod_mul, Finset.sum_range_succ, ih m]
    ring

/-- **SU6d′ — THE RE-BLOCKING IDENTITY (the dynamic content of dilation).** For
every value `n`, the outer digit at position `p` equals the inner mixed-radix decode
of the refined line's block digits. The chart between the outer line and the exactly
spliced line is value-preserving digit GROUPING — both lines compute the same
arithmetic; the refined one merely resolves it finer. -/
theorem refined_digit_reblock (b : ℕ → ℕ) (p k : ℕ) (c : ℕ → ℕ)
    (hx : b p = ∏ i ∈ Finset.range k, c i) (n : ℕ) :
    (n / chainPlace b p) % b p
      = ∑ j ∈ Finset.range k,
          ((n / chainPlace (refineBase b p k c) (p + j)) % c j)
            * ∏ i ∈ Finset.range j, c i := by
  rw [hx, mod_prod_eq_sum_digits c k]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [chainPlace_refine_inside b p k c j (le_of_lt (Finset.mem_range.mp hj)),
      ← Nat.div_div_eq_div_mul]

/-! ## 3. The k-fold tick -/

/-- **DILATION, DYNAMIC READING.** Advancing the value by one outer unit at position
`p` — `B_p` unit ticks, which under exactness is the inner block's full mass —
increments the outer digit at `p` by exactly one (mod its base). The outer tick is
the `B_p`-fold inner tick, read through the value-preserving chart: *exact nesting
adds resolution, never arithmetic.* -/
theorem dilation_tick (b : ℕ → ℕ) (p : ℕ) (hb : ∀ i, 2 ≤ b i) (n : ℕ) :
    ((n + chainPlace b p) / chainPlace b p) % b p
      = (((n / chainPlace b p) % b p) + 1) % b p := by
  have hpos : 0 < chainPlace b p :=
    chainPlace_pos b (fun i => by have := hb i; omega) p
  rw [Nat.add_div_right n hpos, Nat.add_mod, Nat.mod_eq_of_lt (show 1 < b p by
    have := hb p; omega)]

/-! ## 4. Demos — the chart, live on the 10 = 2×5 refined decimal line -/

-- n = 47 on the refined line (places [1, 10, 20, 100]): block digits 0 (base 2)
-- and 2 (base 5); the re-blocking identity reassembles the outer tens digit:
-- 0·1 + 2·2 = 4 = (47/10) % 10.
#eval ((47 / 10) % 10, ((47 / 10) % 2) * 1 + ((47 / 20) % 5) * 2)   -- (4, 4)
-- the k-fold tick: one outer unit (10 = the block's full mass) advances the tens
-- digit by one: 95 + 10 = 105, tens digit 9 → 0 (mod 10).
#eval (((95 + 10) / 10) % 10, (((95 / 10) % 10) + 1) % 10)          -- (0, 0)
-- the refined line is a genuine radix line (conservativity, type level):
#eval (List.range 5).map (refineBase (fun _ => 10) 1 2 (fun i => if i = 0 then 2 else 5))
  -- [10, 2, 5, 10, 10] — all ≥ 2

end FdrsFormal.Modes.SyntheticPlace
