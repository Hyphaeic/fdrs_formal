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

# p-adic Valuations

p-adic valuations, divisibility projectors, and exact valuation projectors.

## Mathematical Content (fdrs.md lines 2044-2098)

**Definition**: For prime p and n ∈ ℕ≥1, the p-adic valuation v_p(n) is the
largest exponent e such that p^e | n.

**Definition 40** (divisibility projector):
  Π_{p^e} f(n) = 𝟙_{p^e | n} · f(n)

**Definition 41** (exact valuation projector):
  Π_{p,=e} f(n) = 𝟙_{v_p(n) = e} · f(n)
                 = (𝟙_{p^e | n} - 𝟙_{p^{e+1} | n}) · f(n)

**Proposition 48** (orthogonal idempotents):
All Π_{p,=e} are idempotent, pairwise orthogonal, and partition unity:
  ∑_{e≥0} Π_{p,=e} = I

## References

- fdrs.md, Phase 3 Fragment 3 (lines 2044-2098)
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Defs
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace FdrsFormal.NumberTheory.Valuations

/-!
## Valuation Functions
-/

/--
The p-adic valuation v_p(n): largest e such that p^e | n.

**Definition**: v_p(n) = max{e ∈ ℕ : p^e | n}

**Implementation**: We use mathlib's `padicValNat`.
-/
noncomputable def padicValuation (p : ℕ) [Fact p.Prime] (n : ℕ) : ℕ :=
  padicValNat p n

notation "v_" p => padicValuation p

/--
**Theorem**: v_p(1) = 0 for any prime p

**Proof**: Direct from mathlib's `padicValNat.one`.
-/
theorem padicValuation_one (p : ℕ) [Fact p.Prime] : padicValuation p 1 = 0 := by
  unfold padicValuation
  exact padicValNat.one

/--
**Theorem**: v_p(p) = 1

**Proof**: Uses mathlib's `padicValNat.self`, which requires `1 < p`.
We derive this from `Fact p.Prime`.
-/
theorem padicValuation_self (p : ℕ) [Fact p.Prime] : padicValuation p p = 1 := by
  unfold padicValuation
  exact padicValNat.self (Nat.Prime.one_lt (Fact.out (p := Nat.Prime p)))

/-!
## Divisibility Projectors
-/

/--
**Definition 40**: Divisibility projector Π_{p^e}.

(Π_{p^e} f)(n) = 𝟙_{p^e | n} · f(n)

This is a diagonal idempotent operator selecting elements divisible by p^e.
-/
noncomputable def divisibilityProjector (p e : ℕ) [Fact p.Prime] (f : {n : ℕ // 0 < n} → ℂ) :
    {n : ℕ // 0 < n} → ℂ :=
  fun n => if p ^ e ∣ n.val then f n else 0

/--
**Definition 41**: Exact valuation projector Π_{p,=e}.

(Π_{p,=e} f)(n) = 𝟙_{v_p(n) = e} · f(n)

Selects elements with exactly valuation e at prime p.
-/
noncomputable def exactValuationProjector (p e : ℕ) [Fact p.Prime] (f : {n : ℕ // 0 < n} → ℂ) :
    {n : ℕ // 0 < n} → ℂ :=
  fun n => if padicValuation p n.val = e then f n else 0

/-!
## Projector Properties
-/

/--
**Proposition 48(a)**: Π_{p,=e} are idempotent.

**Proof** (fdrs.md lines 2065-2072): Π_{p,=e}² = Π_{p,=e} pointwise
since the indicator is 0/1-valued.
-/
theorem exactValuationProjector_idempotent (p e : ℕ) [Fact p.Prime] (f : {n : ℕ // 0 < n} → ℂ) :
    exactValuationProjector p e (exactValuationProjector p e f) =
    exactValuationProjector p e f := by
  funext n
  simp only [exactValuationProjector]
  split_ifs with h
  · -- v_p(n) = e: inner gives f n, outer gives f n
    rfl
  · -- v_p(n) ≠ e: outer gives 0
    rfl

/--
**Proposition 48(b)**: Π_{p,=e} are pairwise orthogonal.

**Proof**: For e ≠ e', the indicators 𝟙_{v_p(n)=e} and 𝟙_{v_p(n)=e'} are disjoint,
so Π_{p,=e} ∘ Π_{p,=e'} = 0.
-/
theorem exactValuationProjector_orthogonal (p e e' : ℕ) [Fact p.Prime]
    (hne : e ≠ e') (f : {n : ℕ // 0 < n} → ℂ) :
    exactValuationProjector p e (exactValuationProjector p e' f) = 0 := by
  funext n
  simp only [exactValuationProjector]
  split_ifs with h h'
  · -- v_p(n) = e and v_p(n) = e' contradicts e ≠ e'
    exfalso; exact hne (h.symm.trans h')
  · -- v_p(n) = e but v_p(n) ≠ e', inner is 0
    rfl
  · -- v_p(n) ≠ e, outer is 0
    rfl

/--
**Proposition 48(c)**: Π_{p,=e} partition unity.

**Statement**: ∑_{e=0}^∞ Π_{p,=e} = I

(Finite sum effectively, since v_p(n) ≤ log_p(n) for any fixed n.)

**Proof**: Every n has a unique p-adic valuation, so exactly one Π_{p,=e}
is active for each n.
-/
theorem exactValuationProjector_partition (p : ℕ) [Fact p.Prime] (f : {n : ℕ // 0 < n} → ℂ) (N : ℕ) :
    ∀ (n : {n : ℕ // 0 < n}), padicValuation p n.val ≤ N →
    (∑ e ∈ Finset.range (N + 1), exactValuationProjector p e f) n = f n := by
  intro n hn
  simp only [Finset.sum_apply, exactValuationProjector]
  rw [Finset.sum_eq_single (padicValuation p n.val)]
  · simp
  · intro e _ hne
    simp [show ¬(padicValuation p n.val = e) from fun h => hne h.symm]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

end FdrsFormal.NumberTheory.Valuations
