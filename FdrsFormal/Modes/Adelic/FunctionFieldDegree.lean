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

# Function-field complex FF0 — the degree keystone (`deg = ∑ v_P · deg P`)

The first stone of the function-field instance of `AdelicLaw` — the empty,
correctly-typed slot `AdelicInterface.lean` §4 leaves open. On `ℚ` the product formula
bottoms out in unique factorization of integers (`Nat.factorization_prod_pow_eq_self`,
the M4a core). On a function field `K(t)` the conservation law `∏_v |x|_v = 1`
(with `|x|_P = q^{−v_P(x)·deg P}` and `|x|_∞ = q^{intDegree x}`) bottoms out in the
**degree identity** for polynomials:

> for `h ∈ K[X]`, `h ≠ 0`:  `deg h = ∑_P v_P(h) · deg P`,

the sum over the (monic) irreducible factors of `h`. This file proves exactly that —
the polynomial `factorization_prod_pow_eq_self`, in additive (degree) form.

Design choices (recorded in `docs/function-field/00-prep.md`):

* **Additive form first.** The conservation law in degree form is `q`-free; the
  exponential `q^{±deg}` bookkeeping enters only when the absolute values are defined
  (FF1). Keeping the keystone additive keeps it generic over *any* field `K`.
* **Valuation = factor multiplicity.** `polyValuation P h = (normalizedFactors h).count P`
  — the count in the UFD factorization multiset, no `multiplicity`/`emultiplicity` API.
  The support is `(normalizedFactors h).toFinset`; over a field the normalized factors
  are monic irreducibles, so this *is* the classical place-set of the finite places.
* **Lightweight route.** Pure `normalizedFactors` + `natDegree_multiset_prod` +
  `Finset.sum_multiset_map_count` — no `HeightOneSpectrum`, no adele machinery,
  mirroring how M4a used `Nat.factorization` rather than `AdeleRing`.

**Honest scope.** This is the keystone only: no places, no absolute values, no
conservation statement yet (FF1–FF3, see the prep doc). It is classical bookkeeping —
the polynomial analogue of a Mathlib `Nat` lemma — *machine-checked assembly, not new
mathematics*. (As of the pinned Mathlib revision, the function-field product formula
is absent upstream: `Height.AdmissibleAbsValues` instances cover number fields only,
with function fields an explicit TODO — so FF0–FF3 fill a slot that is empty in
Mathlib too.) `normalizedFactors` is noncomputable; executable demos belong to the
engine layer (FF4), not the keystone. Leaf module. No `sorry`; axiom-clean.
-/
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.RingTheory.PrincipalIdealDomain

namespace FdrsFormal.Modes.Adelic

open Polynomial UniqueFactorizationMonoid

variable {K : Type*} [Field K] [DecidableEq K]

/-! ## 1. Finite-place valuation and support, as factorization data -/

/-- **The valuation of `h` at `P`**, read as a factor count: the multiplicity of the
(normalized = monic) irreducible `P` in the unique factorization of `h`. The
function-field analogue of `Nat.factorization n p`. -/
noncomputable def polyValuation (P h : K[X]) : ℕ := (normalizedFactors h).count P

/-- **The finite support of `h`**: its distinct monic irreducible factors. The
function-field analogue of `Nat.factorization.support`. -/
noncomputable def polySupport (h : K[X]) : Finset K[X] := (normalizedFactors h).toFinset

/-! ## 2. Normalization does not move the degree -/

/-- `normalize` rescales by the (unit) constant `C (normUnit leadingCoeff)`, so the
degree is untouched. -/
theorem natDegree_normalize_eq (h : K[X]) : (normalize h).natDegree = h.natDegree := by
  rcases eq_or_ne h 0 with rfl | hh
  · simp
  · rw [normalize_apply, Polynomial.coe_normUnit, natDegree_mul_C (Units.ne_zero _)]

/-! ## 3. The keystone -/

/-- **FF0 — THE DEGREE KEYSTONE.** For a nonzero polynomial over a field,
`deg h = ∑_{P ∈ polySupport h} v_P(h) · deg P`: the degree is exactly the
multiplicity-weighted sum of the degrees of its monic irreducible factors. This is
the function-field `Nat.factorization_prod_pow_eq_self` — the unique-factorization
fact the `K(t)` product formula (FF2) will bottom out in, in additive (degree) form,
generic over the coefficient field. -/
theorem natDegree_eq_sum_polyValuation (h : K[X]) (hh : h ≠ 0) :
    h.natDegree = ∑ P ∈ polySupport h, polyValuation P h * P.natDegree := by
  have h0 : (0 : K[X]) ∉ normalizedFactors h := fun hmem =>
    not_irreducible_zero (irreducible_of_normalized_factor 0 hmem)
  calc h.natDegree
      = (normalize h).natDegree := (natDegree_normalize_eq h).symm
    _ = ((normalizedFactors h).prod).natDegree := by
        rw [prod_normalizedFactors_eq hh]
    _ = ((normalizedFactors h).map natDegree).sum :=
        natDegree_multiset_prod _ h0
    _ = ∑ P ∈ (normalizedFactors h).toFinset,
          (normalizedFactors h).count P • P.natDegree :=
        Finset.sum_multiset_map_count _ _
    _ = ∑ P ∈ polySupport h, polyValuation P h * P.natDegree := by
        simp [polySupport, polyValuation, smul_eq_mul]

end FdrsFormal.Modes.Adelic
