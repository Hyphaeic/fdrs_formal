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

# Adelic complex — the bridge `padic_valuation_from_stream` (Axis-II, non-Archimedean half)

M4a (`ProductFormula.lean`) proves `∏_v |x|_v = 1` reading the valuations `v_p(x)` from
`Nat.factorization`. This file makes the network read them **blindly off the emitted
stream**: the p-adic valuation is exactly the **leading-zero count** of the base-`p` Hensel
digits a p-adic node emits. So the conserved product formula can be computed from the
machine's *output*, with no appeal to factorization.

* `streamValuation` — the valuation read off a digit stream: the index of the first
  nonzero digit (number of leading zeros). What a node computes by *watching its output*.
* **`streamValuation_digits`** (the bridge) — for a prime `p`, `streamValuation` of the
  emitted base-`p` Hensel digits of `n` equals `padicValNat p n = v_p(n)`. Proved by the
  digit recurrence `digits_eq_cons_digits_div` and the valuation recurrence
  `padicValNat (p·m) = padicValNat m + 1` — the same finite-prefix pinning as the corpus
  `residue_depends_on_prefix`, here read as the *leading zeros forced by the prefix*.
* **`product_formula_from_stream`** — the M4a product formula with every p-adic exponent
  replaced by the stream-read `streamValuation`. The Axis-II invariant, computed from the
  machine output.

**Honest scope (the bright line).** This closes the **non-Archimedean** half: `v_p(x)` is
read *exactly* off a *finite* emitted prefix (the p-adic digits stabilize finitely). It
does **not** close the **Archimedean** half — the running product `= 1` over *live*
prefixes, where `|x|_∞` only *converges* — that is **M4b**, proven in `GaugeBound.lean`
(its conservation hypothesis discharged on `ℚˣ` by `ProductFormulaRat.lean`). And the bridge is proved for the *canonical* digit list `Nat.digits p n`, which
the p-adic engine emits (demonstrated below by `#eval`); the *full* driver-correctness proof
(`PlaceEngine.run` output ≡ `Nat.digits` as a prefix) is a separate obligation, not claimed
here. Leaf module. No `sorry`; axiom-clean.
-/
import FdrsFormal.Modes.Adelic.ProductFormula
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace FdrsFormal.Modes.Adelic

open Finset

/-! ## 1. The valuation read off a digit stream -/

/-- The valuation read **blindly off an emitted digit stream**: the index of the first
nonzero digit (the number of leading zeros). A p-adic node computes `v_p` by this alone —
watching how many `0`s its Hensel output opens with. Exact `ℤ`-list arithmetic, no float. -/
def streamValuation : List ℤ → ℕ
  | [] => 0
  | d :: ds => if d = 0 then streamValuation ds + 1 else 0

@[simp] theorem streamValuation_nil : streamValuation [] = 0 := rfl

theorem streamValuation_cons (d : ℤ) (ds : List ℤ) :
    streamValuation (d :: ds) = if d = 0 then streamValuation ds + 1 else 0 := rfl

/-! ## 2. The bridge: stream-read valuation = `v_p` -/

/-- **`padic_valuation_from_stream`.** The valuation read off the emitted base-`p` Hensel
digits of `n` is exactly `padicValNat p n = v_p(n)`. The network reads `v_p` blindly from
its output — the non-Archimedean half of "compute `∏_v |x|_v = 1` from the live stream."
Proved by the digit recurrence + the valuation recurrence (the leading zeros are pinned by
the prefix, the dual of `residue_depends_on_prefix`). -/
theorem streamValuation_digits (p : ℕ) [hp : Fact p.Prime] (n : ℕ) :
    streamValuation ((Nat.digits p n).map (fun d => (d : ℤ))) = padicValNat p n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hp1 : 1 < p := hp.out.one_lt
      rw [Nat.digits_eq_cons_digits_div hp1 hn]
      -- `(a :: l).map f` is defeq to `f a :: l.map f`, so the head digit surfaces:
      show streamValuation (((n % p : ℕ) : ℤ) :: (Nat.digits p (n / p)).map (fun d => (d : ℤ)))
            = padicValNat p n
      rw [streamValuation_cons]
      by_cases hdvd : p ∣ n
      · -- `n % p = 0`: a leading zero; recurse on `n / p`
        have hmodnat : n % p = 0 := (Nat.dvd_iff_mod_eq_zero ..).mp hdvd
        have hmod : ((n % p : ℕ) : ℤ) = 0 := by exact_mod_cast hmodnat
        have hlt : n / p < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) hp1
        have hnp : n / p ≠ 0 := fun h =>
          hn (by rw [← Nat.mul_div_cancel' hdvd, h, Nat.mul_zero])
        have hrec : padicValNat p n = padicValNat p (n / p) + 1 := by
          conv_lhs => rw [← Nat.mul_div_cancel' hdvd]
          rw [padicValNat.mul hp.out.ne_zero hnp, padicValNat_self]
          omega
        rw [if_pos hmod, ih (n / p) hlt, hrec]
      · -- `n % p ≠ 0`: the first digit is nonzero, so zero leading zeros, and `v_p = 0`
        have hmod : ((n % p : ℕ) : ℤ) ≠ 0 := by
          simp only [ne_eq, Nat.cast_eq_zero]
          exact fun h => hdvd ((Nat.dvd_iff_mod_eq_zero ..).mpr h)
        rw [if_neg hmod, padicValNat.eq_zero_of_not_dvd hdvd]

/-! ## 3. The product formula, computed from stream-read valuations -/

/-- **The product formula from the live stream.** The Axis-II conserved invariant
`∏_v |n|_v = 1`, with every p-adic exponent `v_p(n)` replaced by `streamValuation` of the
emitted base-`p` digits — the product formula computed *blindly from the machine output*,
no factorization invoked. (Archimedean half still M4b.) -/
theorem product_formula_from_stream (n : ℕ) (hn : n ≠ 0) :
    (n : ℚ) * ∏ p ∈ n.factorization.support,
        (p : ℚ) ^ (-(streamValuation ((Nat.digits p n).map (fun d => (d : ℤ))) : ℤ)) = 1 := by
  rw [← product_formula_nat n hn]
  refine congrArg _ (Finset.prod_congr rfl (fun p hp => ?_))
  have hp_prime : p.Prime := by
    rw [Nat.support_factorization] at hp; exact Nat.prime_of_mem_primeFactors hp
  haveI : Fact p.Prime := ⟨hp_prime⟩
  rw [streamValuation_digits p n, padicNorm_natCast_eq n hn hp,
      Nat.factorization_def n hp_prime, zpow_neg, zpow_natCast]

/-! ## 4. Demos — the LIVE engine output, read for `v_p` (exact, no float) -/

-- The p-adic node, given the constant ledger `⟨0,n,0,1⟩` (value `n`), emits the base-`p`
-- Hensel digits of `n`. For `n = 12`, `p = 5`: `12 = 2 + 2·5`, so it emits `[2,2,0,…]`.
#eval PlaceEngine.run (padicEngine 5) ⟨0, 12, 0, 1⟩ [] 8        -- [2, 2, 0, 0, 0, 0, 0, 0]
#eval Nat.digits 5 12                                           -- [2, 2]
-- `v₅(12) = 0` read off the stream (no leading zero); `v₅(10) = 1` (one leading zero):
#eval streamValuation (PlaceEngine.run (padicEngine 5) ⟨0, 12, 0, 1⟩ [] 8)   -- 0
#eval streamValuation (PlaceEngine.run (padicEngine 5) ⟨0, 10, 0, 1⟩ [] 8)   -- 1
-- the product formula on 360, with valuations read from the digit streams, = 1:
#eval (360 : ℚ) * ∏ p ∈ (360 : ℕ).factorization.support,
        (p : ℚ) ^ (-(streamValuation ((Nat.digits p 360).map (fun d => (d : ℤ))) : ℤ))

end FdrsFormal.Modes.Adelic
