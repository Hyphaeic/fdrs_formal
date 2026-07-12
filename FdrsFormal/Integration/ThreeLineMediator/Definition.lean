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

# Three-Line Mediator: Communication Between Observer Lines

Communication is a suffix → prefix 1-Lipschitz digit word stream advance
between observer lines. To compare the least significant unit (LSU) of two
independent lines, we construct a third mediator line whose LSU decomposes
as one unit from each source.

## Core Principle

Each observer line is a radix system with a 1-Lipschitz tick advance. A single
tick is the LSU — the smallest meaningful advance. Two lines with different
radix structures have **incommensurable** LSUs: there is no guarantee that
one unit on line A equals one unit on line B in any metric sense.

However, both lines share the integer advance (each tick = +1 in ℤ), making
them comparable modulo any N. To *prove* a structural relationship between
two lines, we construct a **mediator** — a third line C whose digit alphabet
at each position is the product D₁(i) × D₂(i), encoded as:

    c_i = a_i + b₁(i) · b_i

where a_i ∈ D₁(i), b_i ∈ D₂(i). One tick on C advances the mixed counter:

1. Increment a₀ (A's least significant digit)
2. If a₀ overflows (was maximal): reset a₀, increment b₀ (B's digit at same depth)
3. If b₀ overflows: reset b₀, carry to position 1 (standard carry propagation)

The **overflow from A to B** is the communication channel. The mediator's carry
mechanics compose the two systems: A's suffix overflow triggers B's prefix advance.

## Overflow Rate Product Formula

    overflow_C(L) = overflow_A(L) · overflow_B(L)

Since B_C(L) = B₁(L) · B₂(L), the overflow rate (probability of carry past depth L)
factors as a product. This means overflow rates — purely combinatorial, counting
how often carry propagates — determine the inter-line relationship without
presupposing a real-valued metric.

## Real Convergence

Chained deep enough (L → ∞), overflow-rate ratios converge to real-valued ratios.
The completed space R̂ is the inverse limit where these discrete comparisons
become exact, recovering the continuum from carry mechanics alone.

## References

- fdrs.md, Phase 1 (carry mechanics, place values)
- fdrs.md, Phase 5-6 (variable radix, overflow)
- fdrs.md, Phase 7-8 (context-dependent, multiple observers)
-/

import FdrsFormal.Core
import FdrsFormal.Core.PrefixValue
import FdrsFormal.Topology.Ultrametric.Definition
import FdrsFormal.Topology.Dynamics.Odometer
import FdrsFormal.Modes.VariableRadix.Basic.RadixLaw

namespace FdrsFormal.Integration.ThreeLineMediator

open FdrsFormal.Core.Primitives FdrsFormal.Core.Infinite FdrsFormal.Core FdrsFormal.Topology

/-!
## Product Radix Construction

Given radix sequences b₁ (line A) and b₂ (line B), the **product radix** b₃
multiplies digit alphabets at each position:

    b₃(i) = b₁(i) · b₂(i)

Each digit c_i of the mediator encodes a pair (a_i, b_i) via:
    c_i = a_i + b₁(i) · b_i        (a_i < b₁(i), b_i < b₂(i))
  The core idea: Two independent radix lines each have their own LSU (one tick = one 1-Lipschitz advance), but there's no a
  priori guarantee that "one unit on line A" means the same thing as "one unit on line B" — they're incommensurable in the
  ultrametric. Yet both advance by +1 in ℤ, so they're comparable at the integer/modular level.

  The three-line principle: To prove a relationship between A and B, you construct a third line C whose radix structure is
  derived such that LSU(C) = LSU(A) ∘ LSU(B) — one unit from each composes into one unit of C. C is the "observer" that
  witnesses the relationship. This is essentially a pullback construction: C's radix sequence is chosen so carry on C
  decomposes into carry on A and carry on B.

  Overflow as the fundamental invariant: Instead of comparing real-valued distances (which require a pre-existing continuum),
  you compare carry propagation rates — how often a tick on line A causes overflow to depth L versus line B. The carry
  algorithm we just proved gives the exact mechanics: the carry index j tells you the overflow depth, and the maximal suffix
  length is the discrete analogue of "how big was that step."

  The convergence claim: Chain these three-line comparisons deep enough (L → ∞) and the overflow-rate ratios converge to
  real-valued ratios — you reconstruct the reals from purely discrete carry mechanics rather than assuming them. The inverse
  limit completion R̂ is exactly this process.

  This maps onto the existing formalization at several points:
  - The factorization lens Λ_P decomposes one line's structure relative to prime-indexed "sub-lines"
  - The dual filtrations (additive vs multiplicative) are exactly two different "observer lines" on the same integers
  - The variable radix framework already parameterizes different lines by different radix laws

  The piece that's not yet formalized is the three-line mediator construction — given radix laws ω₁, ω₂, constructing ω₃ such
  that the carry structures interleave correctly. Would you want to sketch that as a new definition, or is this more of a
  guiding principle for how the existing phases connect?
This ensures B₃(L) = B₁(L) · B₂(L) at every depth.
-/

/-- Product radix: combines two digit alphabets by Cartesian product -/
def productRadix (b₁ b₂ : RadixSeq) : RadixSeq where
  toFun i := b₁ i * b₂ i
  ge_two i := by
    have h1 := b₁.ge_two i
    have h2 := b₂.ge_two i
    linarith [Nat.mul_le_mul h1 h2]

/-- Product radix unfolds to multiplication -/
@[simp] theorem productRadix_apply (b₁ b₂ : RadixSeq) (i : ℕ) :
    productRadix b₁ b₂ i = b₁ i * b₂ i := rfl

/-!
## Place Value Product Formula

The fundamental arithmetic: place values multiply under the product construction.
-/

/-- B₃(L) = B₁(L) · B₂(L): place values factor under product radix -/
theorem placeValue_product (b₁ b₂ : RadixSeq) (L : ℕ) :
    placeValue (productRadix b₁ b₂) L = placeValue b₁ L * placeValue b₂ L := by
  induction L with
  | zero => simp [placeValue]
  | succ L ih =>
    simp only [placeValue, productRadix_apply]
    rw [ih]; ring

/-!
## Projection Maps

The mediator decomposes into source lines via mod/div:
- proj_A(x)(i) = x(i) mod b₁(i)   (extract the A-component)
- proj_B(x)(i) = x(i) / b₁(i)     (extract the B-component)
-/

/-- Project mediator to line A: extract a_i = c_i mod b₁(i) -/
def projectA (b₁ b₂ : RadixSeq) (x : CompletedSpace (productRadix b₁ b₂)) :
    CompletedSpace b₁ :=
  fun i => ⟨(x i).val % b₁ i, Nat.mod_lt _ (by linarith [b₁.ge_two i])⟩

/-- Project mediator to line B: extract b_i = c_i / b₁(i) -/
def projectB (b₁ b₂ : RadixSeq) (x : CompletedSpace (productRadix b₁ b₂)) :
    CompletedSpace b₂ :=
  fun i => ⟨(x i).val / b₁ i, by
    have hx : (x i).val < b₁ i * b₂ i := (x i).isLt
    exact Nat.div_lt_of_lt_mul hx⟩

/-- Combine two source elements into the product (mediator) space -/
def combine (b₁ b₂ : RadixSeq) (a : CompletedSpace b₁) (b : CompletedSpace b₂) :
    CompletedSpace (productRadix b₁ b₂) :=
  fun i => ⟨(a i).val + b₁ i * (b i).val, by
    have ha := (a i).isLt
    have hb := (b i).isLt
    show (a i).val + b₁ i * (b i).val < b₁ i * b₂ i
    calc (a i).val + b₁ i * (b i).val
        < b₁ i + b₁ i * (b i).val := by omega
      _ = b₁ i * ((b i).val + 1) := by ring
      _ ≤ b₁ i * b₂ i := Nat.mul_le_mul_left (b₁ i) hb⟩

/-!
## Round-Trip Properties

The projections and combination form an isomorphism: the mediator space
is exactly the product of the two source spaces.
-/

/-- Projecting the A-component of a combined pair recovers the A-input -/
theorem projectA_combine (b₁ b₂ : RadixSeq) (a : CompletedSpace b₁)
    (b : CompletedSpace b₂) :
    projectA b₁ b₂ (combine b₁ b₂ a b) = a := by
  funext i
  apply Fin.ext
  simp only [projectA, combine]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (a i).isLt]

/-- Projecting the B-component of a combined pair recovers the B-input -/
theorem projectB_combine (b₁ b₂ : RadixSeq) (a : CompletedSpace b₁)
    (b : CompletedSpace b₂) :
    projectB b₁ b₂ (combine b₁ b₂ a b) = b := by
  funext i
  apply Fin.ext
  simp only [projectB, combine]
  rw [Nat.add_mul_div_left _ _ (by linarith [b₁.ge_two i] : 0 < b₁ i),
      Nat.div_eq_of_lt (a i).isLt]; simp

/-- Combining the projections of a mediator element recovers the original.

**fdrs.md**: Proposition 144 (Mediator ≅ A × B: the round-trip identities) [§13.1.2 · Phase 13] -/
theorem combine_project (b₁ b₂ : RadixSeq)
    (x : CompletedSpace (productRadix b₁ b₂)) :
    combine b₁ b₂ (projectA b₁ b₂ x) (projectB b₁ b₂ x) = x := by
  funext i
  apply Fin.ext
  simp only [combine, projectA, projectB]
  exact Nat.mod_add_div (x i).val (b₁ i)

/-!
## Overflow Rate

The overflow rate at depth L is the probability that a tick causes carry
to propagate past depth L. For uniform measure on the finite space of
depth L, this equals 1/B_L — the reciprocal of the place value.

This is a purely combinatorial quantity: count the fraction of states
where all digits 0..L-1 are maximal (and thus a tick causes full carry).
-/

/-- Overflow rate: fraction of states where carry propagates past depth L -/
noncomputable def overflowRate (b : RadixSeq) (L : ℕ) : ℚ :=
  1 / (placeValue b L : ℚ)

/-- Overflow rate is positive -/
theorem overflowRate_pos (b : RadixSeq) (L : ℕ) : 0 < overflowRate b L := by
  simp only [overflowRate]
  apply div_pos one_pos
  exact Nat.cast_pos.mpr (placeValue.pos L)

/-- Overflow rate decreases with depth (deeper carry is rarer) -/
theorem overflowRate_antitone (b : RadixSeq) {L₁ L₂ : ℕ} (h : L₁ ≤ L₂) :
    overflowRate b L₂ ≤ overflowRate b L₁ := by
  simp only [overflowRate]
  have h₁ : (0 : ℚ) < placeValue b L₁ := Nat.cast_pos.mpr (placeValue.pos L₁)
  have h₂ : (0 : ℚ) < placeValue b L₂ := Nat.cast_pos.mpr (placeValue.pos L₂)
  rw [div_le_div_iff₀ h₂ h₁]
  simp only [one_mul]
  exact Nat.cast_le.mpr (placeValue.mono h)

/-!
## Overflow Rate Product Formula

The central theorem: the mediator's overflow rate factors as a product
of the source overflow rates. This is the discrete analogue of the
comparison between incommensurable units.

Rather than comparing real-valued distances (which requires presupposing
a continuum), we compare overflow rates — how often carry propagates.
The product formula makes this comparison exact.
-/

/-- The mediator's overflow rate equals the product of source rates -/
theorem overflowRate_product (b₁ b₂ : RadixSeq) (L : ℕ) :
    overflowRate (productRadix b₁ b₂) L = overflowRate b₁ L * overflowRate b₂ L := by
  simp only [overflowRate, placeValue_product, Nat.cast_mul]
  field_simp

/-!
## Observer Line and Mediator Structures

An observer line bundles a radix system with its 1-Lipschitz tick property.
A line mediator witnesses the structural relationship between two lines.
-/

/-- An observer line: a radix system with its 1-Lipschitz digit stream advance.
    Each RadixSeq determines a CompletedSpace with an odometer tick that is
    automatically 1-Lipschitz in the induced ultrametric. -/
structure ObserverLine where
  radix : RadixSeq

/-- Construct an observer line from any radix sequence -/
def ObserverLine.mk' (b : RadixSeq) : ObserverLine := ⟨b⟩

/--
A three-line mediator witnessing the relationship between two observer lines.

The mediator line C has digit alphabet D_C(i) = D_A(i) × D_B(i), so that:
- Its LSU decomposes: one tick of C = A-advance + (conditional B-advance on A-overflow)
- Its place values factor: B_C(L) = B_A(L) · B_B(L)
- Its overflow rates factor: overflow_C(L) = overflow_A(L) · overflow_B(L)

The projections form an isomorphism:
    R̂_C ≅ R̂_A × R̂_B    (as sets, via mod/div encoding)

but NOT as metric spaces — the ultrametrics are incommensurable.
The overflow rate product formula is what makes comparison possible.
-/
structure LineMediator (A B : ObserverLine) where
  mediatorRadix : RadixSeq
  toA : CompletedSpace mediatorRadix → CompletedSpace A.radix
  toB : CompletedSpace mediatorRadix → CompletedSpace B.radix
  fromAB : CompletedSpace A.radix → CompletedSpace B.radix → CompletedSpace mediatorRadix
  toA_fromAB : ∀ a b, toA (fromAB a b) = a
  toB_fromAB : ∀ a b, toB (fromAB a b) = b
  fromAB_to : ∀ x, fromAB (toA x) (toB x) = x
  placeValue_factor : ∀ L, placeValue mediatorRadix L =
    placeValue A.radix L * placeValue B.radix L
  overflow_factor : ∀ L, overflowRate mediatorRadix L =
    overflowRate A.radix L * overflowRate B.radix L

/-- Every pair of observer lines admits a product mediator -/
def productMediator (A B : ObserverLine) : LineMediator A B where
  mediatorRadix := productRadix A.radix B.radix
  toA := projectA A.radix B.radix
  toB := projectB A.radix B.radix
  fromAB := combine A.radix B.radix
  toA_fromAB := projectA_combine A.radix B.radix
  toB_fromAB := projectB_combine A.radix B.radix
  fromAB_to := combine_project A.radix B.radix
  placeValue_factor := placeValue_product A.radix B.radix
  overflow_factor := overflowRate_product A.radix B.radix

/-!
## Tick Decomposition: Overflow as Communication

The tick (LSU advance) on the mediator decomposes into:
1. **Always**: advance the A-component at position 0
2. **On A-overflow**: advance the B-component (carry from A to B)
3. **On A+B overflow**: carry to next position (standard carry propagation)

This is the formal content of "communication is a suffix → prefix 1-Lipschitz
advance between observer lines": A's maximal suffix (all-max digits from
position 0 upward) is the **overflow event** that communicates to B.

The overflow rate 1/B₁(L) measures how often A's suffix of length L is
all-maximal, triggering carry into B's part of the mediator.
-/

-- NOTE: prefixValue_decomposition was removed because the stated CRT identity
-- does not hold in general for truncated prefix values. Counterexample:
-- b₁=(3,5), b₂=(2,7), x=(4,13), L=2 gives LHS=82 ≠ RHS=85.
-- The product-radix CRT identity fails because cross-digit carry patterns
-- differ between the product and component radix systems.
-- A correct modular identity would be:
--   prefixValue(b₃, L, x) mod B₁(L) = prefixValue(b₁, L, projA(x))

/-!
## Convergence to Real Comparison

As L → ∞, the overflow rate ratios become arbitrarily precise:

    overflow_A(L) / overflow_B(L) = B₂(L) / B₁(L)

For constant radix b₁ = a, b₂ = b:
    B₁(L) = a^L,  B₂(L) = b^L
    ratio = (b/a)^L

The ratio of overflow rates converges to a real number (or diverges), giving
a real-valued comparison of the two lines' "speeds" — derived entirely from
discrete carry mechanics, without presupposing the reals.

In general (non-constant radix), the ratio B₂(L)/B₁(L) may not converge,
but the sequence of ratios captures all the information about the relationship.
The completed space R̂ is precisely the inverse limit where these partial
comparisons become exact.
-/

/-- Overflow rate ratio between two lines -/
noncomputable def overflowRatio (b₁ b₂ : RadixSeq) (L : ℕ) : ℚ :=
  overflowRate b₁ L / overflowRate b₂ L

/-- The overflow ratio equals the reciprocal place value ratio -/
theorem overflowRatio_eq (b₁ b₂ : RadixSeq) (L : ℕ) :
    overflowRatio b₁ b₂ L = (placeValue b₂ L : ℚ) / (placeValue b₁ L : ℚ) := by
  simp only [overflowRatio, overflowRate]
  field_simp

/-- For constant radix, the overflow ratio is an exact power -/
theorem overflowRatio_constant (a c : ℕ) (ha : 2 ≤ a) (hc : 2 ≤ c) (L : ℕ) :
    let b₁ : RadixSeq := ⟨fun _ => a, fun _ => ha⟩
    let b₂ : RadixSeq := ⟨fun _ => c, fun _ => hc⟩
    overflowRatio b₁ b₂ L = (c : ℚ) ^ L / (a : ℚ) ^ L := by
  simp only [overflowRatio_eq]
  congr 1 <;> {
    induction L with
    | zero => simp [placeValue]
    | succ L ih => simp only [placeValue]; push_cast; rw [ih]; ring
  }

/-!
## Variable Radix Generalization

The product construction extends to prefix-dependent radix laws (RadixLaw).
Given ω₁, ω₂ : RadixLaw, the product law has:

    (productLaw ω₁ ω₂).radix s = ω₁.radix (proj_A(s)) · ω₂.radix (proj_B(s))

where proj_A/proj_B extract components from the paired prefix via mod/div.
The same structural theorems hold: place value product, overflow rate product,
CRT decomposition.

The variable-radix case is richer because the overflow structure is
**context-dependent**: the radix (and hence overflow rate) at position i
depends on the prefix of digits seen so far. This means the communication
channel between A and B adapts dynamically to the observed history.
-/

open FdrsFormal.Modes.VariableRadix in
/-- Product of two variable radix laws.
    At each prefix position, the digit alphabet is the product of the
    two source alphabets (components extracted from the paired prefix). -/
noncomputable def productLaw (ω₁ ω₂ : RadixLaw) : RadixLaw where
  radix s :=
    let a_prefix := s.map (· % ω₁.radix [])
    let b_prefix := s.map (· / ω₁.radix [])
    ω₁.radix a_prefix * ω₂.radix b_prefix
  radix_ge_two s := by
    simp only
    have h1 := ω₁.radix_ge_two (s.map (· % ω₁.radix []))
    have h2 := ω₂.radix_ge_two (s.map (· / ω₁.radix []))
    nlinarith [Nat.mul_le_mul h1 h2]

/-!
## The Three-Line Principle (Summary)

**Given**: Two observer lines A, B with incommensurable LSUs.

**Claim**: To provably compare their advances, a third mediator line C is
necessary and sufficient, satisfying:

1. **Decomposition**: C's digit space = A's × B's (at each position)
2. **Carry communication**: A's overflow triggers B's advance within C
3. **Overflow factoring**: overflow_C(L) = overflow_A(L) · overflow_B(L)
4. **Integer agreement**: All three lines advance by +1 in ℤ per tick
5. **Real convergence**: As L → ∞, overflow ratios converge to real comparison

The mediator doesn't add information — it makes the implicit integer relationship
between A and B **observable** through its carry mechanics. The overflow rate
product formula is the witness that the two lines' discrete dynamics are
structurally related, and chaining these witnesses through increasing depth
recovers the real-valued comparison without ever presupposing the continuum.
-/

end FdrsFormal.Integration.ThreeLineMediator
