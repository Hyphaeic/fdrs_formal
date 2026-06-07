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
-/
import FdrsFormal.NumberTheory.Valuations
import FdrsFormal.NumberTheory.FactorizationLens.Definition
import Mathlib.MeasureTheory.MeasurableSpace.Basic

/-!
# Valuation Sigma-Algebra

The multiplicative σ-algebra `M_E` at exponent-depth vector `E ∈ ℕ^P`, the
multiplicative leg of the factorization-lens dual filtration.

## Main definitions

* `truncatedValuationVector P hP E n` — pointwise `min(v_p(n), E p)` over `p ∈ P`.
* `truncatedLens P hP E n` — the pair `(u_P(n), v_P^{≤E}(n))`.
* `multiplicativeSigmaAlgebra P hP E` — the σ-algebra `M_E` on `ℕ`, realised as
  the pullback `comap (truncatedLens …) ⊤`.

## Main results

* `valuationFiltration_monotone` — `M_E ≤ M_{E'}` when `E ≤ E'` componentwise.

## References

* `docs/fdrs.md` lines 2280–2295, **Definition 44** (multiplicative σ-algebra
  at depth `E`). The earlier `Unit`-based stub referenced "Definition 40" —
  stale monotonic numbering from a previous spec revision.
-/

open FdrsFormal FdrsFormal.NumberTheory.FactorizationLens

namespace FdrsFormal.NumberTheory

/--
Truncated valuation vector `v_P^{≤E}(n) := (min(v_p(n), E p))_{p ∈ P}`.

The multiplicative analogue of "prefix at depth L": for each prime `p ∈ P`
it records the `p`-adic valuation of `n` capped at `E p`.
-/
def truncatedValuationVector (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (E : P → ℕ) (n : ℕ) : P → ℕ :=
  fun p => min (valuationVector P hP n p) (E p)

/--
Truncated factorization lens at depth vector `E`:
`n ↦ (u_P(n), v_P^{≤E}(n))`.
-/
def truncatedLens (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (E : P → ℕ) (n : ℕ) : ℕ × (P → ℕ) :=
  (freePart P hP n, truncatedValuationVector P hP E n)

/--
The multiplicative σ-algebra `M_E` at exponent-depth vector `E`.

**fdrs.md** Definition 44 (lines 2280–2295). Realised as the comap of the
discrete σ-algebra `⊤` on the codomain along `truncatedLens`. A function
`f : ℕ → α` is `M_E`-measurable iff it factors through `truncatedLens P hP E`,
i.e. `f(n) = f(m)` whenever `u_P(n) = u_P(m)` and `v_P^{≤E}(n) = v_P^{≤E}(m)`.
-/
def multiplicativeSigmaAlgebra (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (E : P → ℕ) : MeasurableSpace ℕ :=
  MeasurableSpace.comap (truncatedLens P hP E) ⊤

/--
The valuation filtration is monotone: `M_E ≤ M_{E'}` when `E p ≤ E' p` for
every prime `p ∈ P`.

Larger depth `E'` truncates *less* of each `p`-adic valuation, so the
truncated lens at `E` factors deterministically through the truncated lens
at `E'` via the post-processor `(u, v) ↦ (u, fun p => min (v p) (E p))`.
The σ-algebra inclusion then follows from `MeasurableSpace.comap_comp`
and `comap_mono` applied to `⊤.comap ψ ≤ ⊤`.
-/
theorem valuationFiltration_monotone (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    {E E' : P → ℕ} (h : ∀ p, E p ≤ E' p) :
    multiplicativeSigmaAlgebra P hP E ≤ multiplicativeSigmaAlgebra P hP E' := by
  have h_factor :
      truncatedLens P hP E =
        (fun q : ℕ × (P → ℕ) => (q.1, fun p => min (q.2 p) (E p))) ∘
          truncatedLens P hP E' := by
    funext n
    show (freePart P hP n, truncatedValuationVector P hP E n) =
         (freePart P hP n,
          fun p => min (truncatedValuationVector P hP E' n p) (E p))
    refine Prod.ext rfl ?_
    funext p
    show min (valuationVector P hP n p) (E p) =
         min (min (valuationVector P hP n p) (E' p)) (E p)
    rw [min_assoc, min_eq_right (h p)]
  unfold multiplicativeSigmaAlgebra
  rw [h_factor, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono le_top

end FdrsFormal.NumberTheory
