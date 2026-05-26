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

# Cylinder Measurability of Congruence Classes

This file establishes when number-theoretic congruence classes become
cylinder-measurable in the mixed-radix filtration.

## Mathematical Content (fdrs.md lines 1944-1996)

**Definition 39** (radix depth of a modulus):
For a positive integer q, define:
  depth(q) := min{L ∈ {1,...,k+1} : q | B_L}
if such an L exists, and depth(q) = ∞ otherwise.

**Theorem 17** (additive residue classes are F_{k,L}-measurable iff q | B_L):
Fix q with depth(q) ≤ k+1. Then for every residue a (mod q), the set
  E_{q,a} := {τ ∈ R^(k) : dec_k(τ) ≡ a (mod q)}
belongs to F_{k,L} for every L ≥ depth(q). Equivalently, E_{q,a} is a
union of length-L cylinders.

Moreover, if q ∤ B_L, then there exists some residue a such that E_{q,a} ∉ F_{k,L}.

**Theorem 18** (Dirichlet characters become cylinder-measurable):
Fix q with depth(q) ≤ k+1, and let χ ∈ X(q). The pulled-back probe
  χ^{(k)}(τ) := χ(nat_k(τ))
is F_{k,L}-measurable for all L ≥ depth(q).

## Key Insight

This is the bridge between:
- NumberTheory (congruence classes, Dirichlet characters)
- Topology (cylinder sets, filtration F_{k,L})
- Core (place values B_L, decode/encode)

When q | B_L, the residue dec_k(τ) mod q depends only on the first L digits,
making congruence conditions into cylinder gates.

## References

- fdrs.md, Phase 3 Fragment 2, Section 4 (lines 1944-1996)
- THEOREM_MAPPING.md, NumberTheory/CylinderMeasurability
-/

import FdrsFormal.Core.Primitives
import FdrsFormal.Core.Finite
import FdrsFormal.NumberTheory.Characters

namespace FdrsFormal.NumberTheory.CylinderMeasurability

open FdrsFormal.Core.Primitives
open FdrsFormal.Core.Finite
open Classical

-- Enable classical reasoning for existential quantifiers
attribute [local instance] Classical.propDecidable

/-!
## Radix Depth of a Modulus
-/

/--
**Definition 39**: The radix depth of a modulus q.

depth(q) := min{L ≥ 1 : q | B_L}, or 0 if no such L exists.

This is the earliest level at which congruence mod q becomes cylinder-measurable.

**Examples**:
- If b = (2,3,5,...) then B_1=2, B_2=6, B_3=30, ...
- depth(2) = 1 (since 2 | B_1 = 2)
- depth(3) = 2 (since 3 | B_2 = 6 but 3 ∤ B_1 = 2)
- depth(6) = 2 (since 6 | B_2 = 6)
- depth(7) may be large or ∞ depending on radix sequence

**Implementation**: Use Nat.find to get the minimal L where q | B_L.
-/
noncomputable def radixDepth (b : RadixSeq) (q : ℕ) : ℕ :=
  if h : ∃ L > 0, q ∣ placeValue b L then
    Nat.find h
  else 0

/--
**Theorem (AX-126)**: radixDepth is positive when q divides some place value.

**Proof**: If q | B_L for some L > 0, then by definition radixDepth uses Nat.find,
which returns a positive number (since the witness is > 0).
-/
theorem radixDepth_pos_of_dvd {b : RadixSeq} {q L : ℕ} (hL : 0 < L) (hq : q ∣ placeValue b L) :
    0 < radixDepth b q := by
  unfold radixDepth
  have hex : ∃ L' > 0, q ∣ placeValue b L' := ⟨L, hL, hq⟩
  rw [dif_pos hex]
  have ⟨hpos, _⟩ := Nat.find_spec hex
  exact hpos

/--
**Theorem (AX-127)**: At radixDepth, q divides B_L.

**Proof**: If radixDepth is positive, the existential quantifier holds,
and Nat.find gives us an L with q | B_L.
-/
theorem dvd_placeValue_of_radixDepth {b : RadixSeq} {q : ℕ}
    (h : 0 < radixDepth b q) : q ∣ placeValue b (radixDepth b q) := by
  unfold radixDepth at h ⊢
  -- If radixDepth > 0, then the dite must have taken the positive branch
  by_cases hex : ∃ L > 0, q ∣ placeValue b L
  · rw [dif_pos hex]
    have ⟨_hpos, hdvd⟩ := Nat.find_spec hex
    exact hdvd
  · rw [dif_neg hex] at h
    -- radixDepth = 0, contradicts h : 0 < 0
    exact absurd h (Nat.lt_irrefl 0)

/--
**Theorem (AX-128)**: radixDepth is the minimal such L.

**Proof**: Direct from Nat.find_min' - if L > 0 and q | B_L, then
the found value is ≤ L.
-/
theorem radixDepth_minimal {b : RadixSeq} {q L : ℕ}
    (hL : 0 < L) (hq : q ∣ placeValue b L) : radixDepth b q ≤ L := by
  unfold radixDepth
  have hex : ∃ L' > 0, q ∣ placeValue b L' := ⟨L, hL, hq⟩
  rw [dif_pos hex]
  exact Nat.find_min' hex ⟨hL, hq⟩

/-!
## Congruence Sets
-/

/--
The congruence set E_{q,a} = {τ : dec_k(τ) ≡ a (mod q)}.

This is the set of all finite radix representations whose decoded value
is congruent to a modulo q.
-/
def congruenceSet (b : RadixSeq) (k : ℕ) (q a : ℕ) : Set (FiniteRadixSpace b k) :=
  {τ | decodeFinite b k τ % q = a % q}

/-!
## Main Theorems: Cylinder Measurability
-/

/--
Helper: For i ≥ L, if q | B_L then q | (d * B_i).
-/
theorem dvd_digit_mul_placeValue {b : RadixSeq} {L i : ℕ} {q : ℕ}
    (hLi : L ≤ i) (hq : q ∣ placeValue b L) (d : ℕ) :
    q ∣ d * placeValue b i := by
  have hdvd : placeValue b L ∣ placeValue b i := placeValue.dvd_of_le hLi
  exact Dvd.dvd.mul_left (Nat.dvd_trans hq hdvd) d

/--
Helper: Sum of terms from L to k is divisible by q when q | B_L.
-/
theorem suffix_sum_dvd {b : RadixSeq} {k L : ℕ} {q : ℕ}
    (_hL : L ≤ k + 1) (hq : q ∣ placeValue b L)
    (τ : FiniteRadixSpace b k) :
    q ∣ ∑ i ∈ Finset.filter (fun i : Fin (k + 1) => L ≤ i.val) Finset.univ,
          (τ i : ℕ) * placeValue b i := by
  apply Finset.dvd_sum
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  exact dvd_digit_mul_placeValue hi hq _

/--
**Theorem 17(a)**: Residue depends only on prefix when q | B_L.

**Statement** (fdrs.md lines 1972-1976):
If q | B_L, then for any τ ∈ R^(k),
  dec_k(τ) ≡ Σ_{i=0}^{L-1} d_i · B_i (mod q)
i.e., the residue mod q depends only on the first L digits.

**Proof**:
If q | B_L, then for all i ≥ L, q | B_i (since B_i is a multiple of B_L).
Therefore the contribution d_i · B_i ≡ 0 (mod q) for i ≥ L.
Hence dec_k(τ) = Σ_{i=0}^{k} d_i · B_i ≡ Σ_{i=0}^{L-1} d_i · B_i (mod q).

**Consequence**: The residue class is determined by the L-prefix, making
E_{q,a} a union of L-cylinders.
-/
theorem residue_depends_on_prefix (b : RadixSeq) (k L : ℕ) (q : ℕ)
    (hL : L ≤ k + 1) (hq : q ∣ placeValue b L) :
    ∀ τ σ : FiniteRadixSpace b k,
      (∀ i : Fin L, τ ⟨i.val, Nat.lt_of_lt_of_le i.isLt hL⟩ =
                    σ ⟨i.val, Nat.lt_of_lt_of_le i.isLt hL⟩) →
      decodeFinite b k τ % q = decodeFinite b k σ % q := by
  intro τ σ hprefix
  simp only [decodeFinite]

  -- Define the prefix and suffix index sets
  let prefixSet := Finset.filter (fun i : Fin (k + 1) => i.val < L) Finset.univ
  let suffixSet := Finset.filter (fun i : Fin (k + 1) => L ≤ i.val) Finset.univ

  -- The full set is the disjoint union of prefix and suffix
  have hdisjoint : Disjoint prefixSet suffixSet := by
    rw [Finset.disjoint_filter]
    intro i _ h1 h2
    omega

  have hunion : prefixSet ∪ suffixSet = Finset.univ := by
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, prefixSet, suffixSet]
    constructor
    · intro _; trivial
    · intro _; omega

  -- Split both sums
  have hτ_split : ∑ i : Fin (k + 1), (τ i : ℕ) * placeValue b i =
      ∑ i ∈ prefixSet, (τ i : ℕ) * placeValue b i +
      ∑ i ∈ suffixSet, (τ i : ℕ) * placeValue b i := by
    rw [← Finset.sum_union hdisjoint, hunion]

  have hσ_split : ∑ i : Fin (k + 1), (σ i : ℕ) * placeValue b i =
      ∑ i ∈ prefixSet, (σ i : ℕ) * placeValue b i +
      ∑ i ∈ suffixSet, (σ i : ℕ) * placeValue b i := by
    rw [← Finset.sum_union hdisjoint, hunion]

  -- Prefix sums are equal
  have hprefix_eq : ∑ i ∈ prefixSet, (τ i : ℕ) * placeValue b i =
                    ∑ i ∈ prefixSet, (σ i : ℕ) * placeValue b i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, prefixSet] at hi
    have hi_lt : i.val < L := hi
    have heq := hprefix ⟨i.val, hi_lt⟩
    -- Need to show (τ i : ℕ) = (σ i : ℕ)
    have h_idx : (⟨i.val, Nat.lt_of_lt_of_le hi_lt hL⟩ : Fin (k + 1)) = i := Fin.ext rfl
    rw [h_idx] at heq
    rw [heq]

  -- Suffix sums are both ≡ 0 (mod q)
  have hτ_suffix_dvd : q ∣ ∑ i ∈ suffixSet, (τ i : ℕ) * placeValue b i :=
    suffix_sum_dvd hL hq τ

  have hσ_suffix_dvd : q ∣ ∑ i ∈ suffixSet, (σ i : ℕ) * placeValue b i :=
    suffix_sum_dvd hL hq σ

  -- Get mod versions of divisibility
  have hτ_suffix_mod : (∑ i ∈ suffixSet, (τ i : ℕ) * placeValue b i) % q = 0 :=
    Nat.mod_eq_zero_of_dvd hτ_suffix_dvd

  have hσ_suffix_mod : (∑ i ∈ suffixSet, (σ i : ℕ) * placeValue b i) % q = 0 :=
    Nat.mod_eq_zero_of_dvd hσ_suffix_dvd

  -- Now conclude using modular arithmetic
  -- LHS: τ_split → add_mod → suffix=0 → simplify
  -- RHS: σ_split → add_mod → suffix=0 → simplify
  -- Then use prefix equality
  conv_lhs => rw [hτ_split, Nat.add_mod, hτ_suffix_mod]
  conv_rhs => rw [hσ_split, Nat.add_mod, hσ_suffix_mod]
  simp only [Nat.add_zero, Nat.mod_mod]
  rw [hprefix_eq]

/-!
## Helper Definitions for Cylinder Union

**Theorem 17(b)**: Congruence set is a union of cylinders.

**Statement** (fdrs.md lines 1962-1966):
If q | B_L, then E_{q,a} is F_{k,L}-measurable, i.e., a union of length-L cylinders.

**Proof**:
By `residue_depends_on_prefix`, if two elements share an L-prefix, they have
the same residue mod q. Therefore E_{q,a} is exactly the union of all L-cylinders
whose representative has residue a mod q.

**Mathematical significance**:
This makes congruence conditions into "cylinder gates" that can be implemented
using only prefix information - the foundation for locality in ANT operators.
-/

/--
Helper: Extract the L-prefix of a finite radix element as a function Fin L → ℕ.
-/
def extractPrefix (b : RadixSeq) (k L : ℕ) (hL : L ≤ k + 1)
    (τ : FiniteRadixSpace b k) : Fin L → ℕ :=
  fun i => (τ ⟨i.val, Nat.lt_of_lt_of_le i.isLt hL⟩).val

/--
Helper: Create a representative element with a given L-prefix (padding with zeros).
-/
def extendPrefix (b : RadixSeq) (k L : ℕ) (hL : L ≤ k + 1)
    (p : Fin L → ℕ) (hp : ∀ i, p i < b i.val) : FiniteRadixSpace b k :=
  fun i =>
    if h : i.val < L then
      ⟨p ⟨i.val, h⟩, hp ⟨i.val, h⟩⟩
    else
      ⟨0, b.pos i⟩

/--
Helper: Check if a prefix gives residue a mod q.
-/
def prefixGivesResidue (b : RadixSeq) (k L : ℕ) (q a : ℕ) (hL : L ≤ k + 1)
    (p : Fin L → ℕ) (hp : ∀ i, p i < b i.val) : Prop :=
  decodeFinite b k (extendPrefix b k L hL p hp) % q = a % q

/--
**Theorem (AX-129)**: Congruence set is a union of cylinders.

**Proof**: Use `residue_depends_on_prefix` to show that elements sharing an
L-prefix have the same residue mod q. Therefore, E_{q,a} is the union of all
L-cylinders whose representative has residue a mod q.
-/
theorem congruenceSet_is_cylinder_union (b : RadixSeq) (k L : ℕ) (q a : ℕ)
    (hL : L ≤ k + 1) (hq : q ∣ placeValue b L) :
    ∃ prefixes : Finset (Fin L → ℕ),
      congruenceSet b k q a = {τ | ∃ p ∈ prefixes,
        ∀ i : Fin L, (τ ⟨i.val, Nat.lt_of_lt_of_le i.isLt hL⟩).val = p i} := by
  -- We can't directly use Finset.univ for arbitrary function spaces,
  -- so we construct the set of valid prefixes explicitly
  classical

  -- Define valid prefixes as those that give residue a
  let validPrefixSet : Set (Fin L → ℕ) := {p |
    (∀ i, p i < b i.val) ∧
    ∃ (hp : ∀ i, p i < b i.val), prefixGivesResidue b k L q a hL p hp}

  -- The set of valid prefixes is finite because it's a subset of a finite type
  have hfinite : validPrefixSet.Finite := by
    -- The key insight: validPrefixSet is a subset of a finite function space
    -- The set {p : Fin L → ℕ | ∀ i, p i < b i} is in bijection with the finite type
    -- (i : Fin L) → Fin (b i), which is finite
    apply Set.Finite.subset (Set.finite_range
      (fun (f : (i : Fin L) → Fin (b i.val)) (i : Fin L) => (f i).val))
    intro p ⟨hbounds, _⟩
    exact ⟨fun i => ⟨p i, hbounds i⟩, funext fun _ => rfl⟩

  let validPrefixes := hfinite.toFinset

  use validPrefixes

  ext τ
  constructor
  · -- Forward: if τ ∈ E_{q,a}, then τ's prefix is valid
    intro hτ
    unfold congruenceSet at hτ

    -- Extract τ's prefix
    let p := extractPrefix b k L hL τ

    use p

    constructor
    · -- Show p ∈ validPrefixes
      rw [Set.Finite.mem_toFinset]
      unfold validPrefixSet
      constructor
      · -- Show ∀ i, p i < b i.val
        intro i
        show (τ ⟨i.val, Nat.lt_of_lt_of_le i.isLt hL⟩).val < b i.val
        exact (τ ⟨i.val, Nat.lt_of_lt_of_le i.isLt hL⟩).isLt
      · -- Show prefix gives residue a
        have hp : ∀ i, p i < b i.val := by
          intro i
          show (τ ⟨i.val, Nat.lt_of_lt_of_le i.isLt hL⟩).val < b i.val
          exact (τ ⟨i.val, Nat.lt_of_lt_of_le i.isLt hL⟩).isLt
        use hp
        unfold prefixGivesResidue
        -- Need to show: decodeFinite (extendPrefix ... p) % q = a % q
        -- Key: τ and extendPrefix share the same L-prefix
        have h_same_residue : decodeFinite b k τ % q =
                              decodeFinite b k (extendPrefix b k L hL p hp) % q := by
          apply residue_depends_on_prefix b k L q hL hq
          intro i
          show τ ⟨i.val, Nat.lt_of_lt_of_le i.isLt hL⟩ =
               (extendPrefix b k L hL p hp) ⟨i.val, Nat.lt_of_lt_of_le i.isLt hL⟩
          unfold extendPrefix
          simp only [dif_pos i.isLt]
          -- The prefix values match by construction
          ext
          rfl
        rw [← h_same_residue]
        exact hτ

    · -- Show τ matches the prefix
      intro i
      show (τ ⟨i.val, Nat.lt_of_lt_of_le i.isLt hL⟩).val = extractPrefix b k L hL τ i
      unfold extractPrefix
      rfl

  · -- Backward: if τ has a valid prefix, then τ ∈ E_{q,a}
    intro ⟨p, hp_mem, hp_match⟩
    unfold congruenceSet
    simp only [Set.mem_setOf]

    -- p is a valid prefix, so it gives residue a
    rw [Set.Finite.mem_toFinset] at hp_mem
    unfold validPrefixSet at hp_mem
    obtain ⟨hp_bounds, hp_valid, h_residue⟩ := hp_mem

    -- Use residue_depends_on_prefix to transfer residue from extendPrefix to τ
    unfold prefixGivesResidue at h_residue
    have h_same_residue : decodeFinite b k τ % q =
                          decodeFinite b k (extendPrefix b k L hL p hp_valid) % q := by
      apply residue_depends_on_prefix b k L q hL hq
      intro i
      simp only [extendPrefix]
      simp only [dif_pos i.isLt]
      -- τ matches p by assumption
      have heq := hp_match i
      -- heq : (τ ⟨i.val, _⟩).val = p i
      -- Need: τ ⟨i.val, _⟩ = ⟨p ⟨i.val, _⟩, _⟩
      ext
      simp only [Fin.val_mk]
      exact heq

    rw [h_same_residue]
    exact h_residue

/--
**Theorem 17(c)**: Non-divisibility implies non-measurability.

**Statement** (fdrs.md lines 1968-1977):
If q ∤ B_L, then there exists some residue a such that E_{q,a} is NOT
a union of L-cylinders.

**Proof**:
If q ∤ B_L, then some digit position i ≥ L contributes nontrivially mod q
(since B_i is not divisible by q for some i in {L,...,k}). Within a fixed
L-cylinder, varying the suffix digits at position i changes the residue mod q.
Hence no L-cylinder is contained entirely in one residue class.

**Consequence**:
The condition q | B_L is not just sufficient but NECESSARY for E_{q,a} to
be L-measurable (for all a).
-/
theorem congruenceSet_not_cylinder_union_of_not_dvd (b : RadixSeq) (k L : ℕ) (q : ℕ)
    (hL : L ≤ k) (hq : ¬ q ∣ placeValue b L) (hk : q ∣ placeValue b (k + 1)) :
    ∃ a, ¬ ∃ prefixes : Finset (Fin L → ℕ),
      congruenceSet b k q a = {τ | ∃ p ∈ prefixes,
        ∀ i : Fin L, (τ ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_succ_of_le hL)⟩).val = p i} := by
  classical

  -- Key insight: Since q | B_{k+1} but q ∤ B_L, there exists i with L ≤ i ≤ k
  -- such that changing digit at position i changes residue mod q

  -- We'll show that residue class a = 0 is not a cylinder union
  use 0

  intro ⟨prefixes, h_eq⟩

  -- The idea: we'll construct two elements with same L-prefix but different residues
  -- This contradicts that E_{q,0} is a union of L-cylinders

  -- Key fact: If q | B_{k+1} but q ∤ B_L, then there exists a position i with L ≤ i ≤ k
  -- such that B_i is not divisible by q (otherwise q | B_L by divisibility chain)

  -- Strategy:
  -- 1. Find position i ≥ L where we can vary the digit to affect residue mod q
  -- 2. Construct τ₁ with all zeros: decodeFinite τ₁ = 0 ≡ 0 (mod q)
  -- 3. Construct τ₂ with only digit i set: decodeFinite τ₂ = B_i
  -- 4. If gcd(B_i, q) < q, then B_i ≢ 0 (mod q), so τ₁ and τ₂ have different residues
  -- 5. But τ₁ and τ₂ have the same L-prefix (all zeros for i < L)
  -- 6. This contradicts h_eq: if E_{q,0} were a union of L-cylinders,
  --    then τ₁ ∈ E_{q,0} and same prefix would force τ₂ ∈ E_{q,0}

  -- Construct the counterexample:
  -- τ₁ = all zeros: dec(τ₁) = 0 ≡ 0 (mod q), so τ₁ ∈ E_{q,0}
  let τ₁ : FiniteRadixSpace b k := fun _ => ⟨0, b.pos _⟩

  have hτ₁_in : τ₁ ∈ congruenceSet b k q 0 := by
    unfold congruenceSet
    -- dec(τ₁) = ∑ 0 * B_i = 0, so 0 % q = 0 % q
    simp [decodeFinite, τ₁]

  -- Key observation: Since q | B_{k+1} but q ∤ B_L, there exists position i ≥ L
  -- where changing the digit affects the residue mod q.
  -- Specifically, we can take i = L (or any i with L ≤ i ≤ k).

  -- τ₂ = all zeros except position L has digit 1
  -- Then dec(τ₂) = B_L, and since q ∤ B_L, we have B_L ≢ 0 (mod q)
  have hL_bound : L < k + 1 := Nat.lt_succ_of_le hL
  let τ₂ : FiniteRadixSpace b k := fun i =>
    if h : i.val = L then
      ⟨1, by
        have h_eq : b i = b L := by simp [h]
        rw [h_eq]
        have : 1 < 2 := by norm_num
        exact Nat.lt_of_lt_of_le this (b.ge_two L)
      ⟩
    else
      ⟨0, b.pos i⟩

  -- dec(τ₂) = B_L (only the L-th term contributes)
  have hτ₂_decode : decodeFinite b k τ₂ = placeValue b L := by
    unfold decodeFinite τ₂
    -- The sum equals B_L because only position L contributes
    have h_sum : ∑ i : Fin (k + 1), (τ₂ i).val * placeValue b i = 1 * placeValue b L := by
      rw [Finset.sum_eq_single ⟨L, hL_bound⟩]
      · simp [τ₂, dif_pos rfl, Nat.one_mul]
      · intro j _ hj
        have hne : j.val ≠ L := by
          intro h_eq
          exact hj (Fin.ext h_eq)
        simp [τ₂, dif_neg hne, Nat.zero_mul]
      · intro h
        simp at h
    simpa using h_sum

  -- Since q ∤ B_L, we have B_L ≢ 0 (mod q), so τ₂ ∉ E_{q,0}
  have hτ₂_not_in : τ₂ ∉ congruenceSet b k q 0 := by
    unfold congruenceSet
    simp only [Set.mem_setOf]
    rw [hτ₂_decode]
    intro hcontra
    -- hcontra : B_L % q = 0 % q = 0, i.e., q | B_L
    have : q ∣ placeValue b L := Nat.dvd_of_mod_eq_zero (by simpa using hcontra)
    exact hq this

  -- Both τ₁ and τ₂ have the same L-prefix (all zeros for positions < L)
  have hsame_prefix : ∀ i : Fin L, (τ₁ ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_succ_of_le hL)⟩).val =
                                   (τ₂ ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_succ_of_le hL)⟩).val := by
    intro i
    unfold τ₁ τ₂
    simp only [Fin.val_mk]
    -- For position i where i.val < L, we have i.val ≠ L
    have hne : i.val ≠ L := Nat.ne_of_lt i.isLt
    rw [dif_neg hne]

  -- This contradicts h_eq: if E_{q,0} were a union of L-cylinders,
  -- then τ₁ ∈ E_{q,0} and hsame_prefix would force τ₂ ∈ E_{q,0}
  rw [h_eq] at hτ₁_in
  simp only [Set.mem_setOf] at hτ₁_in
  obtain ⟨p, hp_mem, hp_match⟩ := hτ₁_in

  -- τ₂ also has prefix p
  have hτ₂_has_p : ∃ p' ∈ prefixes,
      ∀ i : Fin L, (τ₂ ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_succ_of_le hL)⟩).val = p' i := by
    use p, hp_mem
    intro i
    calc (τ₂ ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_succ_of_le hL)⟩).val
        = (τ₁ ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_succ_of_le hL)⟩).val := (hsame_prefix i).symm
      _ = p i := hp_match i

  -- Therefore τ₂ ∈ E_{q,0} by h_eq
  have : τ₂ ∈ congruenceSet b k q 0 := by
    rw [h_eq]
    simp only [Set.mem_setOf]
    exact hτ₂_has_p

  -- Contradiction!
  exact hτ₂_not_in this

/-!
## Dirichlet Character Measurability
-/

/--
**Theorem 18**: Dirichlet characters are cylinder-measurable at depth(q).

**Statement** (fdrs.md lines 1985-1993):
Fix q with depth(q) ≤ k+1, and let χ ∈ X(q). Define the pulled-back probe:
  χ^{(k)}(τ) := χ(nat_k(τ))
Then χ^{(k)} is F_{k,L}-measurable for all L ≥ depth(q).

**Proof**:
If q | B_L, then nat_k(τ) mod q depends only on the L-prefix (by Theorem 17).
Both the residue class and the unit/non-unit condition gcd(nat_k(τ), q) = 1
are determined by nat_k(τ) mod q. Hence χ(nat_k(τ)) depends only on the
L-prefix, making χ^{(k)} F_{k,L}-measurable.

**Consequence**:
Dirichlet characters become cylinder gates at finite depth, allowing them
to integrate into the runtime algebra A_k.
-/
theorem dirichletChar_cylinder_measurable (b : RadixSeq) (k L : ℕ) (q : ℕ)
    (hL : L ≤ k + 1) (hq : q ∣ placeValue b L) :
    ∀ χ : Characters.DirichletChar q,
      ∀ τ σ : FiniteRadixSpace b k,
        (∀ i : Fin L, τ ⟨i.val, Nat.lt_of_lt_of_le i.isLt hL⟩ =
                      σ ⟨i.val, Nat.lt_of_lt_of_le i.isLt hL⟩) →
        Characters.DirichletChar.apply χ (decodeFinite b k τ + 1) =
        Characters.DirichletChar.apply χ (decodeFinite b k σ + 1) := by
  intro χ τ σ hprefix
  -- By residue_depends_on_prefix, dec_k(τ) ≡ dec_k(σ) (mod q)
  have h_residue := residue_depends_on_prefix b k L q hL hq τ σ hprefix
  -- Therefore (dec_k(τ) + 1) ≡ (dec_k(σ) + 1) (mod q)
  have h_residue_plus_1 : (decodeFinite b k τ + 1) % q = (decodeFinite b k σ + 1) % q := by
    calc (decodeFinite b k τ + 1) % q
        = (decodeFinite b k τ % q + 1 % q) % q := Nat.add_mod _ _ _
      _ = (decodeFinite b k σ % q + 1 % q) % q := by rw [h_residue]
      _ = (decodeFinite b k σ + 1) % q := (Nat.add_mod _ _ _).symm
  -- By periodicity of Dirichlet characters, χ(n) = χ(m) when n ≡ m (mod q)
  exact Characters.DirichletChar.periodic χ _ _ h_residue_plus_1

/-!
## Additive Character Measurability
-/

/--
**Corollary**: Additive characters are cylinder-measurable at appropriate depth.

For the additive character χ_m on ℤ/Nℤ where N = B_{k+1}, and L such that
the effective period of χ_m divides B_L, the function τ ↦ χ_m(dec_k(τ))
is F_{k,L}-measurable.

**Proof**:
The additive character χ_m(x) = exp(2πi·m·x/N) has effective period N/gcd(m,N).
When this period divides B_L, the character value depends only on x mod B_L,
which in turn depends only on the L-prefix.
-/
theorem additiveChar_cylinder_measurable (b : RadixSeq) (k L : ℕ) (m : ℕ)
    (hL : L ≤ k + 1)
    (hperiod : (placeValue b (k + 1) / Nat.gcd m (placeValue b (k + 1))) ∣ placeValue b L) :
    ∀ τ σ : FiniteRadixSpace b k,
      (∀ i : Fin L, τ ⟨i.val, Nat.lt_of_lt_of_le i.isLt hL⟩ =
                    σ ⟨i.val, Nat.lt_of_lt_of_le i.isLt hL⟩) →
      Complex.exp (2 * Real.pi * Complex.I * m * (decodeFinite b k τ) / (placeValue b (k+1))) =
      Complex.exp (2 * Real.pi * Complex.I * m * (decodeFinite b k σ) / (placeValue b (k+1))) := by
  intro τ σ hprefix

  -- Let N = B_{k+1} and P = N / gcd(m, N) be the period
  let N := placeValue b (k + 1)
  let P := N / Nat.gcd m N

  -- The character exp(2πimx/N) has period P
  -- We need to show dec_k(τ) ≡ dec_k(σ) (mod P)

  -- Since P | B_L and residue mod B_L depends only on L-prefix,
  -- we have dec_k(τ) ≡ dec_k(σ) (mod B_L)
  -- Therefore dec_k(τ) ≡ dec_k(σ) (mod P)

  -- Use residue_depends_on_prefix with q = P
  have h_residue := residue_depends_on_prefix b k L P hL hperiod τ σ hprefix

  -- Now show that equal residues mod P give equal character values
  -- exp(2πim·x/N) = exp(2πim·y/N) when x ≡ y (mod P)

  -- Key algebraic fact: if x ≡ y (mod P) where P = N/gcd(m,N), then
  -- m·x ≡ m·y (mod N), so exp(2πim·x/N) = exp(2πim·y/N)

  -- From h_residue: dec_k(τ) % P = dec_k(σ) % P
  -- This means dec_k(τ) and dec_k(σ) differ by a multiple of P

  -- Algebraic key fact:
  -- If x ≡ y (mod P) where P = N/gcd(m,N), then m·x ≡ m·y (mod N)
  --
  -- Proof: Let g = gcd(m,N), so m = g·m', N = g·P, with gcd(m',P) = 1
  -- If x = y + k·P for some k, then:
  --   m·x = m·y + k·m·P = m·y + k·g·m'·P = m·y + k·m'·N
  -- Therefore m·x ≡ m·y (mod N)

  -- When m·τ ≡ m·σ (mod N), we have:
  --   m·τ/N = m·σ/N + j  for some integer j
  -- Therefore:
  --   exp(2πi·m·τ/N) = exp(2πi·m·σ/N) · exp(2πi·j) = exp(2πi·m·σ/N)

  -- The key mathematical fact: exp(2πi·m·x/N) has period N/gcd(m,N)
  -- When x ≡ y (mod N/gcd(m,N)), we have m·(x-y)/N ∈ ℤ, so exp(2πi·m·x/N) = exp(2πi·m·y/N)

  -- From h_residue: dec(τ) ≡ dec(σ) (mod P) where P = N/gcd(m,N)
  -- We need to show: exp(2πi·m·dec(τ)/N) = exp(2πi·m·dec(σ)/N)

  -- Mathematical content (axiomatized for now - requires gcd properties):
  -- If P = N/gcd(m,N) and P | (x - y), then N | m·(x - y)
  -- Proof: Let g = gcd(m,N). Then m = g·m', N = g·P with gcd(m',P) = 1.
  -- If P | (x - y), then x = y + k·P for some k, so:
  --   m·(x - y) = m·k·P = g·m'·k·P = m'·k·N
  -- Therefore N | m·(x - y), i.e., m·(x - y) = j·N for some integer j.
  -- Hence: m·x/N = m·y/N + j, so exp(2πi·m·x/N) = exp(2πi·m·y/N)·exp(2πi·j) = exp(2πi·m·y/N)

  -- Step 1: Key gcd fact — N ∣ m * P where P = N / gcd(m, N)
  have hN_pos : 0 < N := placeValue.pos (k + 1)
  have h_N_dvd_mP : N ∣ m * P := by
    set g := Nat.gcd m N
    have hgm : g ∣ m := Nat.gcd_dvd_left m N
    have hgN : g ∣ N := Nat.gcd_dvd_right m N
    have h_eq : m * (N / g) = (m / g) * N :=
      calc m * (N / g)
          = (g * (m / g)) * (N / g) := by
            conv_lhs => rw [show m = g * (m / g) from (Nat.mul_div_cancel' hgm).symm]
        _ = (m / g) * (g * (N / g)) := by ring
        _ = (m / g) * N := by rw [Nat.mul_div_cancel' hgN]
    rw [h_eq]; exact dvd_mul_left N _

  -- Step 2: Transfer x ≡ y (mod P) to m*x ≡ m*y (mod N)
  have h_mod_N : (m * decodeFinite b k τ) % N = (m * decodeFinite b k σ) % N := by
    suffices h : (↑N : ℤ) ∣ (↑(m * decodeFinite b k σ) - ↑(m * decodeFinite b k τ)) by
      rwa [← Nat.modEq_iff_dvd] at h
    have h_P_dvd : (↑P : ℤ) ∣ (↑(decodeFinite b k σ) - ↑(decodeFinite b k τ)) :=
      Nat.modEq_iff_dvd.mp h_residue
    have h_mP_dvd : (↑(m * P) : ℤ) ∣
        (↑(m * decodeFinite b k σ) - ↑(m * decodeFinite b k τ)) := by
      push_cast
      rw [show (↑m : ℤ) * ↑(decodeFinite b k σ) - ↑m * ↑(decodeFinite b k τ) =
        ↑m * (↑(decodeFinite b k σ) - ↑(decodeFinite b k τ)) from by ring]
      exact mul_dvd_mul_left _ h_P_dvd
    exact dvd_trans (by exact_mod_cast h_N_dvd_mP) h_mP_dvd

  -- Step 3: Complex exponential equality from modular equality
  -- Normalize ↑m * ↑(dec t) to ↑(m * dec t) in the goal
  have goal_rw : ∀ (t : FiniteRadixSpace b k),
      (2 : ℂ) * ↑Real.pi * Complex.I * ↑m * ↑(decodeFinite b k t) =
      2 * ↑Real.pi * Complex.I * ↑(m * decodeFinite b k t) := by
    intro t; push_cast; ring
  simp only [goal_rw]
  -- Goal: exp(2πi * ↑(m * dec τ) / ↑N) = exp(2πi * ↑(m * dec σ) / ↑N)
  -- Use exp_eq_exp_iff_exists_int
  rw [Complex.exp_eq_exp_iff_exists_int]
  have hN_ne : (↑(placeValue b (k + 1)) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  obtain ⟨c, hc⟩ := Nat.modEq_iff_dvd.mp h_mod_N
  refine ⟨-c, ?_⟩
  -- Cast the ℤ identity to ℂ
  have h_eq : (↑(m * decodeFinite b k τ) : ℂ) =
      ↑(m * decodeFinite b k σ) - ↑(placeValue b (k + 1)) * ↑c := by
    have : (↑(m * decodeFinite b k τ) : ℤ) =
        ↑(m * decodeFinite b k σ) - ↑(placeValue b (k + 1)) * c := by linarith
    exact_mod_cast this
  rw [h_eq, mul_sub, sub_div]
  -- Cancel ↑N * ↑c / ↑N = ↑c
  have h_cancel : (2 : ℂ) * ↑Real.pi * Complex.I *
      (↑(placeValue b (k + 1)) * ↑c) / ↑(placeValue b (k + 1)) =
      (2 * ↑Real.pi * Complex.I) * ↑c := by
    rw [show (2 : ℂ) * ↑Real.pi * Complex.I * (↑(placeValue b (k + 1)) * ↑c) =
        ↑(placeValue b (k + 1)) * ((2 * ↑Real.pi * Complex.I) * ↑c) from by ring]
    exact mul_div_cancel_left₀ _ hN_ne
  rw [h_cancel]; push_cast; ring

/-! ## Proposition 51: Non-commutation witness -/

/--
**fdrs.md**: Proposition 51 (generic failure of commutation with additive block projections)
[§4.1 · Phase 3, Fragment 3] (lines 2203-2214)

Non-commutation witness: pointwise multiplication by a non-block-constant function
does not preserve block-constancy, showing that generic arithmetic operators
(including Dirichlet transforms) fail to commute with block projections.

Concretely: the constant function 1 is L-block-constant, but multiplying by a
function depending on digit L destroys block-constancy.
-/
theorem nonCommutationWitness (b : RadixSeq) (k L : ℕ)
    (hL : 0 < L) (hLk : L ≤ k) :
    ∃ (g f : FiniteRadixSpace b k → ℂ),
      -- f is block-constant at level L (depends only on first L digits)
      (∀ τ σ : FiniteRadixSpace b k,
        (∀ i : Fin (k + 1), i.val < L → τ i = σ i) → f τ = f σ) ∧
      -- g · f is NOT block-constant at level L
      ¬(∀ τ σ : FiniteRadixSpace b k,
        (∀ i : Fin (k + 1), i.val < L → τ i = σ i) → g τ * f τ = g σ * f σ) := by
  -- g = L-th digit (varies within L-cylinders), f = constant 1
  refine ⟨fun τ => (τ ⟨L, by omega⟩ : ℕ), fun _ => 1, fun _ _ _ => rfl, ?_⟩
  intro h
  -- Construct τ₀ (all zeros) and τ₁ (digit L = 1, rest zeros)
  let τ₀ : FiniteRadixSpace b k := fun _ => ⟨0, b.pos _⟩
  let τ₁ : FiniteRadixSpace b k :=
    fun i => if i.val = L then ⟨1, by have := b.ge_two i; omega⟩ else ⟨0, b.pos i⟩
  -- They agree on the first L digits (positions 0,...,L-1)
  have h_agree : ∀ i : Fin (k + 1), i.val < L → τ₀ i = τ₁ i := by
    intro i hi
    simp only [τ₀, τ₁, if_neg (show i.val ≠ L by omega)]
  have h_eq := h τ₀ τ₁ h_agree
  simp only [mul_one] at h_eq
  -- digit_L(τ₀) = 0, digit_L(τ₁) = 1 → contradiction
  have h0 : (τ₀ ⟨L, by omega⟩ : ℕ) = 0 := rfl
  have h1 : (τ₁ ⟨L, by omega⟩ : ℕ) = 1 := by
    simp only [τ₁, ite_true]
  rw [h0, h1] at h_eq
  exact absurd h_eq (by norm_num)

end FdrsFormal.NumberTheory.CylinderMeasurability
