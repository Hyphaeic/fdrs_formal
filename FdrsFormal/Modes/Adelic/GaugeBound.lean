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

# Adelic complex M4b — the finite-precision gauge bound (Axis-II conservation, in Lean)

The cross-place conservation law, certified at finite precision. The exact product formula
(`ProductFormula.lean`, M4a) says `∏_v |x|_v = 1` for the *identified* value. A running
machine works with *finite prefixes*: the p-adic legs are exact (their Hensel digits
stabilise finitely), but the Archimedean leg is only a continued-fraction **convergent**
`pₙ/qₙ → x`. So the finite-precision adelic product `Πₙ = |pₙ/qₙ|_∞ · ∏_S |x|_p` is **not**
exactly `1` — it converges to `1`, the deviation controlled by the CF gauge `qₙ`.

> **`gauge_bound` (M4b).** For `x ∈ ℚ*` with the product-formula constant `P = ∏_S |x|_p`
> (so `|x|·P = 1`), the finite-precision deviation is gauge-controlled:
> `| |pₙ/qₙ|·P − 1 | ≤ P / qₙ`, where `qₙ = densₙ` is the convergent denominator.

This is the bound the scratch probe (`docs/archive/adelic-machine/scratch/gauge_bound_probe.py`) confirmed empirically
(`C = 1`, `Θ(1/qₙ²)`, Hurwitz) — now machine-checked. As that probe showed, it **is** the
classical CF convergent bound `|x − pₙ/qₙ| < 1/(qₙ qₙ₊₁)` (the non-Archimedean legs are the
exact constant `P`, which never interacts with the limit): *mechanical assembly of
classical facts*, not new mathematics, exactly as the archived design `04`/`06` records.

The proof chain is the one the FDRS engine carries natively, taken pre-packaged from
Mathlib's continued fractions: `abs_sub_convs_le` (`|x − pₙ/qₙ| ≤ 1/(qₙqₙ₊₁)`, whose own
proof runs through `fib(n+2) ≤ denom` — the gauge growth, FDRS's `steps_qCur_unbounded` /
`bracket_invariant` in Mathlib form) + `succ_nth_fib_le_of_nth_den` (`qₙ ≥ 1`). The Axis-II
invariant `|x|·P = 1` enters as a hypothesis — discharged for *every* nonzero rational by
the `ℚˣ` lift (`ProductFormulaRat.lean`: `gauge_bound_rat` instantiates
`P := ∏_{p ∈ ratSupport x} |x|_p` and supplies the proof).

Also: **`gauge_product_tendsto`** — the conservation law in the limit: `Πₙ → 1`. Leaf
module. No `sorry`; axiom-clean.
-/
import FdrsFormal.Modes.Adelic.ProductFormula
import Mathlib.Algebra.ContinuedFractions.Computation.ApproximationCorollaries

namespace FdrsFormal.Modes.Adelic

open GenContFract Filter Topology

/-- **M4b — the finite-precision gauge bound.** For a rational `x ≠ 0` whose p-adic product
`P = ∏_S |x|_p` satisfies the product formula `|x|·P = 1`, the running adelic product
`Πₙ = |pₙ/qₙ|·P` deviates from `1` by at most `P/qₙ`, where `qₙ = densₙ` is the continued
-fraction gauge. The Archimedean convergent error (`abs_sub_convs_le`) scaled by the exact
p-adic constant `P` — the cross-place coupling conserved up to the vanishing gauge. -/
theorem gauge_bound (x : ℚ) (hx : x ≠ 0) (P : ℚ) (hpf : |x| * P = 1) (n : ℕ)
    (hn : ¬ (GenContFract.of x).TerminatedAt n) :
    |(|(GenContFract.of x).convs n| * P) - 1| ≤ P / (GenContFract.of x).dens n := by
  have hxpos : 0 < |x| := abs_pos.mpr hx
  have hP : 0 < P := by
    have hne : |x| ≠ 0 := ne_of_gt hxpos
    have hPe : P = 1 / |x| := by field_simp; linear_combination hpf
    rw [hPe]; positivity
  -- the gauge `qₙ ≥ 1` and `qₙ₊₁ ≥ 1` (Mathlib `succ_nth_fib_le_of_nth_den`, the gauge growth)
  have hyp_n : n = 0 ∨ ¬ (GenContFract.of x).TerminatedAt (n - 1) := by
    rcases Nat.eq_zero_or_pos n with h0 | _
    · exact Or.inl h0
    · exact Or.inr fun ht => hn (GenContFract.terminated_stable (Nat.sub_le n 1) ht)
  have hfn : (Nat.fib (n + 1) : ℚ) ≤ (GenContFract.of x).dens n :=
    GenContFract.succ_nth_fib_le_of_nth_den hyp_n
  have hfn1 : (Nat.fib (n + 2) : ℚ) ≤ (GenContFract.of x).dens (n + 1) :=
    GenContFract.succ_nth_fib_le_of_nth_den (Or.inr hn)
  have hdn : (1 : ℚ) ≤ (GenContFract.of x).dens n :=
    le_trans (by exact_mod_cast Nat.fib_pos.mpr (Nat.succ_pos n)) hfn
  have hdn1 : (1 : ℚ) ≤ (GenContFract.of x).dens (n + 1) :=
    le_trans (by exact_mod_cast Nat.fib_pos.mpr (Nat.succ_pos (n + 1))) hfn1
  have hdn0 : 0 < (GenContFract.of x).dens n := lt_of_lt_of_le one_pos hdn
  -- the classical convergent error bound
  have hconv : |x - (GenContFract.of x).convs n|
      ≤ 1 / ((GenContFract.of x).dens n * (GenContFract.of x).dens (n + 1)) :=
    GenContFract.abs_sub_convs_le hn
  -- rewrite the deviation through the product formula (`1 = |x|·P`)
  have hkey : |(|(GenContFract.of x).convs n| * P) - 1|
      = abs (|(GenContFract.of x).convs n| - |x|) * P := by
    rw [← hpf, ← sub_mul, abs_mul, abs_of_pos hP]
  rw [hkey]
  -- reverse triangle, then drop the `qₙ₊₁` factor
  have h1 : abs (|(GenContFract.of x).convs n| - |x|) ≤ |x - (GenContFract.of x).convs n| := by
    rw [abs_sub_comm x]; exact abs_abs_sub_abs_le_abs_sub _ _
  have hle2 : 1 / ((GenContFract.of x).dens n * (GenContFract.of x).dens (n + 1))
      ≤ 1 / (GenContFract.of x).dens n :=
    one_div_le_one_div_of_le hdn0 (le_mul_of_one_le_right hdn0.le hdn1)
  calc abs (|(GenContFract.of x).convs n| - |x|) * P
      ≤ |x - (GenContFract.of x).convs n| * P := by gcongr
    _ ≤ (1 / ((GenContFract.of x).dens n * (GenContFract.of x).dens (n + 1))) * P :=
        mul_le_mul_of_nonneg_right hconv hP.le
    _ ≤ (1 / (GenContFract.of x).dens n) * P := mul_le_mul_of_nonneg_right hle2 hP.le
    _ = P / (GenContFract.of x).dens n := by ring

/-- **The conservation law in the limit.** The running adelic product `Πₙ = |pₙ/qₙ|·P`
converges to `1` — the exact product formula recovered as the gauge `qₙ → ∞`. (With
`gauge_bound`: `Πₙ → 1` at rate `O(1/qₙ)`.) -/
theorem gauge_product_tendsto (x : ℚ) (P : ℚ) (hpf : |x| * P = 1) :
    Tendsto (fun n => |(GenContFract.of x).convs n| * P) atTop (𝓝 1) := by
  have hconv : Tendsto (fun n => (GenContFract.of x).convs n) atTop (𝓝 x) :=
    GenContFract.of_convergence x
  have hlim : Tendsto (fun n => |(GenContFract.of x).convs n| * P) atTop (𝓝 (|x| * P)) :=
    hconv.abs.mul_const P
  rwa [hpf] at hlim

/-! ## Demo — the gauge controls the finite-precision deviation (exact ℚ) -/

-- `x = 355/113` (CF `[3;7,16]`), with the exact p-adic product `P = 113/355 = 1/|x|`
-- (the product formula, here `norm_num`).  The convergent denominators — the gauge `qₙ`:
#eval (List.range 3).map fun n => (GenContFract.of (355/113 : ℚ)).dens n        -- [1, 7, 113]
-- the finite-precision adelic product `Πₙ = |pₙ/qₙ|·(113/355)`, → 1 as qₙ grows:
#eval (List.range 3).map fun n =>
  |(GenContFract.of (355/113 : ℚ)).convs n| * (113/355 : ℚ)                      -- [339/355, 2486/2485, 1]

end FdrsFormal.Modes.Adelic
