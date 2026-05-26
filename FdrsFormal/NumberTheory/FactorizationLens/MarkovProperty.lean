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

# Markov Property on Factorization Lens

This file proves Dirichlet transforms are Markov/local on factorization lens coordinates.

## Mathematical Content (fdrs.md lines 2412-2423)

**Proposition 53 (Dirichlet transforms are local/Markov on Λ_P)**:

For P-smooth kernel a, dependence graph is contained in:
  (u, e) ← (u, e - r) for r ∈ supp(ã), 0 ≤ r ≤ e

i.e., transitions only move **downward** in valuation lattice and never change u.

**Proof**: This is exactly Corollary 10 (fiber decomposition).

**Interpretation**: With state indexed by (u,e), T_a is structured Markov update
with finite dependency neighborhood determined by supp(a).

## Main Results

* `markov_on_lens` — the Dirichlet transform at n depends only on values of f
  on the freePart fiber {u_P(n) · k | k | s_P(n)}.
* `finite_dependency_neighborhood` — the set of positions that can influence
  (T_a f)(n) is a finite set of size ≤ |divisors(s_P(n))|.

## References

- fdrs.md, Phase 3, Fragment 4, Section 5 (lines 2412-2423)
-/

import FdrsFormal.NumberTheory.FactorizationLens.FiberDecomposition

open FdrsFormal.NumberTheory
open scoped BigOperators

namespace FdrsFormal.NumberTheory.FactorizationLens

/-!
## Markov Locality
-/

/--
Factorization lens state.

**fdrs.md Definition 45 (lines 2402-2409)**: Λ_P(n) = (u_P(n), v_P(n)).
-/
structure FactorizationLensState (P : Set ℕ) where
  /-- P-free part -/
  u_part : ℕ
  /-- Valuation vector -/
  v_part : ℕ  -- Should be ℕ^P (simplified)

/--
Dirichlet transforms with P-smooth kernels are local/Markov on the factorization
lens: the output at n depends only on values of f at points sharing the same
P-free part u_P(n).

**fdrs.md Proposition 53 (lines 2413-2420)**: Downward-only, u-preserving.

Concretely: if f₁ and f₂ agree on all points of the form u_P(n) · k for k | s_P(n),
then (T_a f₁)(n) = (T_a f₂)(n). The P-free part is an invariant of the dynamics,
and only the smooth part (exponent vector) participates in transitions.

**Proof**: Immediate from `factorizationFiberDecomp` (Theorem 23).
-/
theorem markov_on_lens (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (a f₁ f₂ : ℕ → ℂ) (n : ℕ) (hn : 0 < n)
    (ha_smooth : ∀ d, a d ≠ 0 → ∀ p, Nat.Prime p → p ∣ d → p ∈ P)
    (h_agree : ∀ d ∈ (smoothPart P hP n).divisors,
      f₁ (freePart P hP n * (smoothPart P hP n / d)) =
      f₂ (freePart P hP n * (smoothPart P hP n / d))) :
    ∑ d ∈ n.divisors, a d * f₁ (n / d) =
    ∑ d ∈ n.divisors, a d * f₂ (n / d) := by
  rw [factorizationFiberDecomp P hP a f₁ n hn ha_smooth,
      factorizationFiberDecomp P hP a f₂ n hn ha_smooth]
  apply Finset.sum_congr rfl
  intro d hd
  rw [h_agree d hd]

/--
The dependency neighborhood of the Dirichlet transform at n is contained in
divisors of the smooth part s_P(n), which is a finite set.

**fdrs.md line 2422**: Neighborhood determined by supp(a).

Concretely: there exists a finite set S such that (T_a f₁)(n) = (T_a f₂)(n)
whenever f₁ and f₂ agree on S.
-/
theorem finite_dependency_neighborhood (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (a : ℕ → ℂ) (n : ℕ) (hn : 0 < n)
    (ha_smooth : ∀ d, a d ≠ 0 → ∀ p, Nat.Prime p → p ∣ d → p ∈ P) :
    ∃ S : Finset ℕ, ∀ f₁ f₂ : ℕ → ℂ,
      (∀ m ∈ S, f₁ m = f₂ m) →
      ∑ d ∈ n.divisors, a d * f₁ (n / d) =
      ∑ d ∈ n.divisors, a d * f₂ (n / d) := by
  use (smoothPart P hP n).divisors.image
    (fun d => freePart P hP n * (smoothPart P hP n / d))
  intro f₁ f₂ h_agree
  apply markov_on_lens P hP a f₁ f₂ n hn ha_smooth
  intro d hd
  exact h_agree _ (Finset.mem_image_of_mem _ hd)

end FdrsFormal.NumberTheory.FactorizationLens
