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

# Adelic complex M4a′ — the multiplicative lift: the product formula on all of `ℚˣ`

`ProductFormula.lean` (M4a) proves `∏_v |n|_v = 1` for positive integers, bottoming
out in unique factorization (`Nat.factorization_prod_pow_eq_self`). This file performs
the **standard multiplicative lift** to every nonzero rational — the extension the
`AdelicInterface` honest-scope note recorded as "noted but not formalized": write
`x = num/den` in lowest terms, split each `|x|_p` through `padicNorm.div`, and apply
the integer formula to numerator and denominator separately.

The structural fact that makes the lift *mechanical assembly* rather than work is
**reducedness**: `Rat.reduced` says `num.natAbs` and `den` are coprime, so their prime
supports are **disjoint** (`Nat.Coprime.disjoint_primeFactors`) and the product over
the joint support `ratSupport x = supp(num) ∪ supp(den)` splits with no interaction
terms — at a numerator prime the denominator's norm is exactly `1`, and vice versa
(`padicNorm.nat_eq_one_iff`). Everything stays in exact `ℚ`; no float, no `ℝ`, no
heavyweight adele-ring import (the no-floats discipline, archived design `02` §7 / `06` §5).

Contents:

* `ratSupport` — the support of a rational: primes of the numerator ∪ primes of the
  denominator (disjoint by reducedness; `= n.factorization.support` on `ℕ`-casts).
* **`product_formula_rat`** — the conservation law on `ℚ \ {0}`:
  `|x| · ∏_{p ∈ ratSupport x} |x|_p = 1`. (`product_formula_place_rat`: the same over
  `Place.absValue`.)
* **`ratAdelicLaw : AdelicLaw Place ℚˣ`** — the classical instance upgraded from `ℕ+`
  to the group where Artin–Whaples actually lives, conservation discharged by the lift.
* **`gauge_bound_rat` / `gauge_product_tendsto_rat`** — the payoff: M4b's gauge bound
  no longer takes the conservation law as a *hypothesis*; it is **discharged** for every
  nonzero rational by instantiating `P := ∏_{p ∈ ratSupport x} |x|_p`. The
  finite-precision Axis-II invariant is now self-contained on `ℚˣ`.

**Honest scope.** The lift is classical bookkeeping over the already-proven M4a core —
no new mathematics, exactly as the archived design `04`/`06` records. Still open and untouched
here: M3 (the restricted product over all places), the genuinely synthetic instances
(global function fields — the empty, correctly-typed `AdelicLaw` slot), and the live
Archimedean stream side of M4b beyond what `GaugeBound.lean` already proves. Leaf
module (imports M4a/M4b + the V2.0 interface). No `sorry`; axiom-clean.
-/
import FdrsFormal.Modes.Adelic.AdelicInterface
import FdrsFormal.Modes.Adelic.GaugeBound

namespace FdrsFormal.Modes.Adelic

open Finset

/-! ## 1. The support of a rational and its disjoint split -/

/-- The **support of a nonzero rational**: the primes dividing the numerator together
with the primes dividing the denominator. By reducedness these two halves are disjoint
(`ratSupport_disjoint`); off this set every `|x|_p = 1`. -/
def ratSupport (x : ℚ) : Finset ℕ :=
  x.num.natAbs.factorization.support ∪ x.den.factorization.support

/-- **The split is disjoint.** `x.num.natAbs` and `x.den` are coprime (`Rat.reduced` —
lowest terms), so no prime divides both: the numerator and denominator halves of
`ratSupport` never interact. This is what makes the lift mechanical. -/
theorem ratSupport_disjoint (x : ℚ) :
    Disjoint x.num.natAbs.factorization.support x.den.factorization.support := by
  rw [Nat.support_factorization, Nat.support_factorization]
  exact x.reduced.disjoint_primeFactors

/-- Membership in `ratSupport` forces primality (both halves are prime supports). -/
theorem prime_of_mem_ratSupport {x : ℚ} {p : ℕ} (hp : p ∈ ratSupport x) : p.Prime := by
  rcases Finset.mem_union.mp hp with h | h <;>
  · rw [Nat.support_factorization] at h
    exact Nat.prime_of_mem_primeFactors h

/-- On `ℕ`-casts the rational support is the integer support: the denominator is `1`,
contributing nothing. So the lift literally *extends* M4a rather than replacing it. -/
@[simp] theorem ratSupport_natCast (n : ℕ) :
    ratSupport (n : ℚ) = n.factorization.support := by
  unfold ratSupport
  simp [Rat.num_natCast, Rat.den_natCast]

/-! ## 2. The per-prime split `|x|_p = |num|_p / |den|_p` -/

/-- `padicNorm` only sees the absolute value of an integer numerator
(`padicNorm.neg`): the norm of `(m : ℚ)` equals the norm of `(m.natAbs : ℚ)`. -/
theorem padicNorm_intCast_natAbs (p : ℕ) (m : ℤ) :
    padicNorm p (m : ℚ) = padicNorm p (m.natAbs : ℚ) := by
  rcases Int.natAbs_eq m with h | h
  · nth_rewrite 1 [h]
    rw [Int.cast_natCast]
  · nth_rewrite 1 [h]
    rw [Int.cast_neg, Int.cast_natCast, padicNorm.neg]

/-- **The per-prime split.** Writing `x = num/den` (lowest terms), the p-adic norm
factors through `padicNorm.div`: `|x|_p = |num.natAbs|_p / |den|_p`. -/
theorem padicNorm_rat_eq (x : ℚ) {p : ℕ} [Fact p.Prime] :
    padicNorm p x = padicNorm p (x.num.natAbs : ℚ) / padicNorm p (x.den : ℚ) := by
  conv_lhs => rw [← Rat.num_div_den x, padicNorm.div]
  rw [padicNorm_intCast_natAbs]

/-! ## 3. The product over the support -/

/-- **The non-Archimedean product on `ℚˣ`.** Over the (disjoint) joint support, the
p-adic norms of `x` multiply to exactly `den/|num|`: the numerator half contributes
`|num.natAbs|⁻¹` (M4a applied to the numerator), the denominator half contributes
`den` (M4a applied to the denominator, inverted by `padicNorm.div`), and each half is
invisible to the other (`padicNorm.nat_eq_one_iff` + disjointness). Exact `ℚ`. -/
theorem prod_padicNorm_ratSupport (x : ℚ) (hx : x ≠ 0) :
    ∏ p ∈ ratSupport x, padicNorm p x = (x.den : ℚ) / (x.num.natAbs : ℚ) := by
  have hnum : x.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hx)
  have hden : x.den ≠ 0 := x.den_nz
  have hdisj := ratSupport_disjoint x
  -- split every factor as numerator-norm / denominator-norm
  have hsplit : ∏ p ∈ ratSupport x, padicNorm p x
      = (∏ p ∈ ratSupport x, padicNorm p (x.num.natAbs : ℚ)) /
        (∏ p ∈ ratSupport x, padicNorm p (x.den : ℚ)) := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    haveI : Fact p.Prime := ⟨prime_of_mem_ratSupport hp⟩
    exact padicNorm_rat_eq x
  -- the numerator product collapses to its own half of the support
  have hA : ∏ p ∈ ratSupport x, padicNorm p (x.num.natAbs : ℚ)
      = ((x.num.natAbs : ℚ))⁻¹ := by
    rw [ratSupport, Finset.prod_union hdisj]
    have hB1 : ∏ p ∈ x.den.factorization.support, padicNorm p (x.num.natAbs : ℚ) = 1 := by
      refine Finset.prod_eq_one (fun p hp => ?_)
      have hpp : p.Prime := by
        rw [Nat.support_factorization] at hp
        exact Nat.prime_of_mem_primeFactors hp
      haveI : Fact p.Prime := ⟨hpp⟩
      rw [padicNorm.nat_eq_one_iff]
      intro hdvd
      have hpA : p ∈ x.num.natAbs.factorization.support := by
        rw [Nat.support_factorization]
        exact Nat.mem_primeFactors.mpr ⟨hpp, hdvd, hnum⟩
      exact (Finset.disjoint_left.mp hdisj hpA) hp
    rw [hB1, mul_one]
    exact (inv_eq_of_mul_eq_one_right (product_formula_nat x.num.natAbs hnum)).symm
  -- the denominator product collapses to its own half of the support
  have hB : ∏ p ∈ ratSupport x, padicNorm p (x.den : ℚ) = ((x.den : ℚ))⁻¹ := by
    rw [ratSupport, Finset.prod_union hdisj]
    have hA1 : ∏ p ∈ x.num.natAbs.factorization.support, padicNorm p (x.den : ℚ) = 1 := by
      refine Finset.prod_eq_one (fun p hp => ?_)
      have hpp : p.Prime := by
        rw [Nat.support_factorization] at hp
        exact Nat.prime_of_mem_primeFactors hp
      haveI : Fact p.Prime := ⟨hpp⟩
      rw [padicNorm.nat_eq_one_iff]
      intro hdvd
      have hpB : p ∈ x.den.factorization.support := by
        rw [Nat.support_factorization]
        exact Nat.mem_primeFactors.mpr ⟨hpp, hdvd, hden⟩
      exact (Finset.disjoint_left.mp hdisj.symm hpB) hp
    rw [hA1, one_mul]
    exact (inv_eq_of_mul_eq_one_right (product_formula_nat x.den hden)).symm
  have hnum' : ((x.num.natAbs : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hnum
  have hden' : ((x.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hden
  rw [hsplit, hA, hB]
  field_simp

/-! ## 4. The product formula on `ℚˣ` (the multiplicative lift of M4a) -/

/-- **The product formula for every nonzero rational.** `|x| · ∏_{p} |x|_p = 1`, the
product over `ratSupport x`. The Archimedean size `|x| = |num|/den` is cancelled
exactly by the p-adic norms `den/|num|` — unique factorization of numerator and
denominator, read as one conservation law across places. Exact `ℚ`; no float. -/
theorem product_formula_rat (x : ℚ) (hx : x ≠ 0) :
    |x| * ∏ p ∈ ratSupport x, padicNorm p x = 1 := by
  have hnum : x.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hx)
  have hden : x.den ≠ 0 := x.den_nz
  have habs : |x| = (x.num.natAbs : ℚ) / (x.den : ℚ) := by
    conv_lhs => rw [← Rat.num_div_den x]
    rw [abs_div, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast,
        abs_of_nonneg (by positivity : (0 : ℚ) ≤ (x.den : ℚ))]
  have hnum' : ((x.num.natAbs : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hnum
  have hden' : ((x.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hden
  rw [prod_padicNorm_ratSupport x hx, habs]
  field_simp

/-- The product formula over `Place.absValue`: `|x|_∞ · ∏_p |x|_p = 1` for every
nonzero rational — the Axis-II conserved invariant, now on all of `ℚˣ`. -/
theorem product_formula_place_rat (x : ℚ) (hx : x ≠ 0) :
    Place.infinite.absValue x
        * ∏ p ∈ ratSupport x, (Place.prime p).absValue x = 1 := by
  simpa only [Place.absValue] using product_formula_rat x hx

/-! ## 5. The `AdelicLaw` instance on `ℚˣ` (the interface, on the right group) -/

/-- The support of a unit, as places: `{∞}` together with the primes of `ratSupport`. -/
def ratSupportPlaces (u : ℚˣ) : Finset Place :=
  insert Place.infinite ((ratSupport (u : ℚ)).image Place.prime)

/-- **The classical instance on `ℚˣ`.** The places `{∞} ∪ {primes}` with the ordinary /
p-adic absolute values instantiate `AdelicLaw` over the full unit group of `ℚ` — the
group where Artin–Whaples actually lives — with the `conservation` obligation
discharged by `product_formula_place_rat`. Upgrades `classicalAdelicLaw` from `ℕ+`. -/
def ratAdelicLaw : AdelicLaw Place ℚˣ where
  val v u := v.absValue (u : ℚ)
  support := ratSupportPlaces
  conservation u := by
    rw [ratSupportPlaces,
        Finset.prod_insert (by simp), Finset.prod_image (fun a _ b _ h => by injection h)]
    exact product_formula_place_rat (u : ℚ) u.ne_zero

/-! ## 6. The payoff — M4b's hypothesis discharged on `ℚˣ` -/

open GenContFract Filter Topology

/-- **The gauge bound, self-contained.** `GaugeBound.gauge_bound` (M4b) took the
conservation law `|x| · P = 1` as a *hypothesis*. With the lift, `P` is instantiated as
the actual p-adic product over `ratSupport x` and the hypothesis is **discharged** for
every nonzero rational: the finite-precision adelic product deviates from `1` by at
most `P / qₙ`, unconditionally on `ℚˣ`. -/
theorem gauge_bound_rat (x : ℚ) (hx : x ≠ 0) (n : ℕ)
    (hn : ¬ (GenContFract.of x).TerminatedAt n) :
    |(|(GenContFract.of x).convs n| * ∏ p ∈ ratSupport x, padicNorm p x) - 1|
      ≤ (∏ p ∈ ratSupport x, padicNorm p x) / (GenContFract.of x).dens n :=
  gauge_bound x hx _ (product_formula_rat x hx) n hn

/-- **The conservation law in the limit, self-contained.** The running adelic product
`Πₙ = |pₙ/qₙ| · ∏_p |x|_p` converges to `1` for every nonzero rational — no
conservation hypothesis left to supply. -/
theorem gauge_product_tendsto_rat (x : ℚ) (hx : x ≠ 0) :
    Tendsto (fun n => |(GenContFract.of x).convs n| * ∏ p ∈ ratSupport x, padicNorm p x)
      atTop (𝓝 1) :=
  gauge_product_tendsto x _ (product_formula_rat x hx)

/-! ## 7. Demos — conservation on genuine rationals (exact ℚ, no float) -/

-- `x = -12/5`: support `{2, 3, 5}`; `|x|·|x|_2·|x|_3·|x|_5 = (12/5)·(1/4)·(1/3)·5 = 1`.
#eval ratSupport (-12/5 : ℚ)
#eval |(-12/5 : ℚ)| * ∏ p ∈ ratSupport (-12/5 : ℚ), padicNorm p (-12/5 : ℚ)
-- `x = 355/113` (the M4b demo value): the p-adic product is `113/355` — the constant
-- `GaugeBound.lean`'s demo supplies by hand, here computed from the support:
#eval ∏ p ∈ ratSupport (355/113 : ℚ), padicNorm p (355/113 : ℚ)
#eval |(355/113 : ℚ)| * ∏ p ∈ ratSupport (355/113 : ℚ), padicNorm p (355/113 : ℚ)
-- the running adelic product of `355/113` along its convergents, → 1 (cf. `gauge_bound_rat`):
#eval (List.range 3).map fun n =>
  |(GenContFract.of (355/113 : ℚ)).convs n|
    * ∏ p ∈ ratSupport (355/113 : ℚ), padicNorm p (355/113 : ℚ)
-- conservation on the `ℚˣ` interface instance:
#eval ∏ v ∈ ratAdelicLaw.support (Units.mk0 (-12/5 : ℚ) (by norm_num)),
        ratAdelicLaw.val v (Units.mk0 (-12/5 : ℚ) (by norm_num))

end FdrsFormal.Modes.Adelic
