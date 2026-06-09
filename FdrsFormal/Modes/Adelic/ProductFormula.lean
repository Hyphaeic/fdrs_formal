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

# Adelic complex M2 / M4a — the product formula (the Axis-II coupling invariant)

The cross-place conserved law that ties one quantity across its positions: the **product
formula** `∏_v |x|_v = 1`. This is what makes the complex *adelic* rather than two
side-by-side ledgers — the adelic analogue of the within-place `|det| = 1` (a structural
rhyme, **not** the same invariant; design `04` §3.1).

Per `04` §7 the reachable prize (**M4a**) is the *exact, value-identified* product formula,
which "bottoms out in unique factorization." This file proves exactly that, the honest
lightweight way: directly from `Nat.factorization_prod_pow_eq_self`, staying in exact `ℚ`
with `padicNorm` as `|·|_p` — **not** importing Mathlib's heavyweight number-field /
adele-ring `Height.AdmissibleAbsValues` machinery (the no-floats discipline, `02` §7,
`06` §5). The Archimedean factor is exact because the value is *identified* (a given
rational), as M4a requires — the `04` §3.3 finite-precision gauge bound (M4b, where the
Archimedean stream only converges) is the genuinely-open piece and is **not** attempted
here.

* `Place`, `Place.absValue` — the places of `ℚ` (`∞` and the primes) and their absolute
  values (`|x|_∞ = |x|`, `|x|_p = padicNorm p x`).
* `product_formula_nat` (**M4a core**) — for a positive integer `n`, the product of `|n|_v`
  over `∞` and the prime factors of `n` is exactly `1`.
* `product_formula_place` — the same, phrased over `Place.absValue`.

**Honest scope.** This is the *value-identified, `S`-integral* product formula (M4a). The
quantity is a *given* rational, so every `|·|_v` is exact; the conserved law is then unique
factorization. **Not** included: the live-prefix gauge bound (M4b, open); the bridge
`padic_valuation_from_stream` reading `v_p(x)` off the *emitted* Hensel stream (the
emission certificate M0d pins each digit, but assembling the full-valuation read is left as
the next bridge); the restricted product over all primes (M3). Those keep their `🔬`/`🔨`
tags. Leaf module. No `sorry`; axiom-clean.
-/
import FdrsFormal.Modes.Adelic.Complex
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.Data.Nat.Factorization.Basic

namespace FdrsFormal.Modes.Adelic

open Finset

/-! ## 1. Places of `ℚ` and their absolute values -/

/-- A place of `ℚ`: the Archimedean place `∞`, or the non-Archimedean place at a prime. By
Ostrowski these are all the places; the complex tracks a quantity at each. -/
inductive Place where
  | infinite
  | prime (p : ℕ)
  deriving DecidableEq

/-- The absolute value at a place: `|x|_∞ = |x|` (ordinary), `|x|_p = padicNorm p x`
(`= p^{−v_p(x)}`). Exact `ℚ` throughout — no float. -/
def Place.absValue : Place → ℚ → ℚ
  | .infinite, x => |x|
  | .prime p, x => padicNorm p x

/-! ## 2. The product formula for a positive integer (M4a core) -/

/-- Each prime-factor `p` of `n` contributes `|n|_p = (p^{v_p(n)})⁻¹` — the p-adic norm of
the integer `n`, written through its factorization exponent. -/
theorem padicNorm_natCast_eq (n : ℕ) (hn : n ≠ 0) {p : ℕ} (hp : p ∈ n.factorization.support) :
    padicNorm p (n : ℚ) = ((p : ℚ) ^ (n.factorization p))⁻¹ := by
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hp_prime : p.Prime := by
    rw [Nat.support_factorization] at hp; exact Nat.prime_of_mem_primeFactors hp
  rw [padicNorm.eq_zpow_of_nonzero hn']
  have hval : padicValRat p (n : ℚ) = (n.factorization p : ℤ) := by
    rw [padicValRat.of_nat, Nat.factorization_def n hp_prime]
  rw [hval, zpow_neg, zpow_natCast]

/-- **The product formula for a positive integer (M4a core).** The product of `|n|_v` over
the Archimedean place and the prime factors of `n` is exactly `1`. The Archimedean size of
`n` is cancelled exactly by its p-adic norms — unique factorization, read as a conservation
law across places. Exact `ℚ`; no float. -/
theorem product_formula_nat (n : ℕ) (hn : n ≠ 0) :
    (n : ℚ) * ∏ p ∈ n.factorization.support, padicNorm p (n : ℚ) = 1 := by
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  -- the non-Archimedean factors multiply to `(n)⁻¹`
  have hfact : ∏ p ∈ n.factorization.support, (p : ℚ) ^ (n.factorization p) = (n : ℚ) := by
    have : (∏ p ∈ n.factorization.support, p ^ (n.factorization p) : ℕ) = n :=
      Nat.factorization_prod_pow_eq_self hn
    calc ∏ p ∈ n.factorization.support, (p : ℚ) ^ (n.factorization p)
        = ((∏ p ∈ n.factorization.support, p ^ (n.factorization p) : ℕ) : ℚ) := by push_cast; rfl
      _ = (n : ℚ) := by rw [this]
  rw [Finset.prod_congr rfl (fun p hp => padicNorm_natCast_eq n hn hp),
      Finset.prod_inv_distrib, hfact]
  field_simp

/-- **The product formula over `Place.absValue`.** The same conservation law, phrased with
the place absolute values: `|n|_∞ · ∏_p |n|_p = 1`, the product running over `∞` and the
prime factors of `n`. This is the complex's Axis-II conserved invariant for an identified
(integer) quantity. -/
theorem product_formula_place (n : ℕ) (hn : n ≠ 0) :
    Place.infinite.absValue (n : ℚ)
        * ∏ p ∈ n.factorization.support, (Place.prime p).absValue (n : ℚ) = 1 := by
  have hpos : (0 : ℚ) ≤ (n : ℚ) := by positivity
  simp only [Place.absValue, abs_of_nonneg hpos]
  exact product_formula_nat n hn

/-! ## 3. Demos — the product formula on concrete integers (exact ℚ, no float) -/

-- `12 = 2²·3`: places `{∞, 2, 3}`, `|12|_∞·|12|_2·|12|_3 = 12 · 1/4 · 1/3 = 1`.
#eval (12 : ℚ) * ∏ p ∈ (12 : ℕ).factorization.support, padicNorm p (12 : ℚ)
-- `360 = 2³·3²·5`: places `{∞,2,3,5}`, product `= 1`.
#eval (360 : ℚ) * ∏ p ∈ (360 : ℕ).factorization.support, padicNorm p (360 : ℚ)
-- the individual p-adic norms of 12 (`|12|_2 = 1/4`, `|12|_3 = 1/3`):
#eval (padicNorm 2 (12 : ℚ), padicNorm 3 (12 : ℚ))

end FdrsFormal.Modes.Adelic
