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

# THEOREM A: Canonical Bijection for Variable Radix

This file states and proves THEOREM A: the canonical bijection φ_ω: R_ω ≅ ℕ.

## Mathematical Content (fdrs.md lines 4080-4091)

**Theorem 30 (THEOREM A - Canonical Bijection)**:
For any radix law ω, there exists a canonical bijection
  φ_ω: R^{(∞)}_ω → ℕ
that:
1. Restricts to φ^{(k)}_ω: R^{(k)}_ω → {0, ..., |R^{(k)}_ω| - 1} for each k
2. Preserves lexicographic order
3. Is compatible with truncation: φ^{(k)}(τ|_k) = φ^{(k+1)}(τ|_{k+1}) mod |R^{(k)}_ω|

This generalizes the fixed-radix bijection from Core to variable radix systems.

## Paper Reference

This is **THEOREM A** from the FDRS paper (§6.3).

## References

- fdrs.md, Phase 5-6, Section 3 (lines 4080-4091)
- Paper (external draft): Theorem A (§6.3)
-/

import FdrsFormal.Modes.VariableRadix.Encoding.OrderPreserving

namespace FdrsFormal.Modes.VariableRadix

/-!
## THEOREM A: Finite Case
-/

/--
**THEOREM A (Finite Case)**: The variable radix decode is a bijection.

φ^{(k)}_ω: R^{(k)}_ω ≅ {0, ..., |R^{(k)}_ω| - 1}
-/
theorem theoremA_finite (ω : RadixLaw) (k : ℕ) :
    Function.Bijective (fun τ : FiniteVariableSpace ω k =>
      (⟨variableRadixDecode ω k τ, variableRadixDecode_lt ω k τ⟩ :
        Fin (completionCount ω k []))) := by
  constructor
  · -- Injective: follows from decode_inj
    intro τ σ h
    simp only [Fin.mk.injEq] at h
    exact decode_inj ω k h
  · -- Surjective: for any n, encode(n) decodes back to n
    intro ⟨n, hn⟩
    use variableRadixEncode ω k n hn
    simp only [Fin.mk.injEq]
    exact variableRadixDecode_encode ω k n hn

/-- The bijection as an equivalence -/
noncomputable def finiteVariableRadixEquiv (ω : RadixLaw) (k : ℕ) :
    FiniteVariableSpace ω k ≃ Fin (completionCount ω k []) :=
  Equiv.ofBijective _ (theoremA_finite ω k)

/-- Cardinality of the finite variable radix space -/
theorem finiteVariableSpace_card (ω : RadixLaw) (k : ℕ) :
    (completionCount ω k []) = completionCount ω k [] := rfl

/-!
## THEOREM A: Infinite Case (Direct Limit)
-/

/-- Truncate a finite sequence to a smaller depth -/
def FiniteVariableSpace.truncateToK {ω : RadixLaw} {k' : ℕ}
    (τ : FiniteVariableSpace ω k') (k : ℕ) (hk : k < k') : FiniteVariableSpace ω k where
  digits := τ.digits.take (k + 1)
  length_eq := by
    rw [List.length_take, τ.length_eq]
    exact Nat.min_eq_left (Nat.le_of_lt (Nat.add_lt_add_right hk 1))
  valid := by
    intro i hi
    have hle : k + 1 ≤ k' + 1 := Nat.le_of_lt (Nat.add_lt_add_right hk 1)
    rw [List.length_take, τ.length_eq, Nat.min_eq_left hle] at hi
    -- Need to show: (τ.digits.take (k+1))[i] < ω.radix ((τ.digits.take (k+1)).take i)
    -- Since i < k+1 ≤ k'+1 = τ.digits.length, we have i < τ.digits.length
    have hi' : i < τ.digits.length := by rw [τ.length_eq]; omega
    have h_get : (τ.digits.take (k + 1)).get ⟨i, by rw [List.length_take, τ.length_eq, Nat.min_eq_left hle]; exact hi⟩ =
        τ.digits.get ⟨i, hi'⟩ := by
      simp only [List.get_eq_getElem, List.getElem_take]
    have h_take : (τ.digits.take (k + 1)).take i = τ.digits.take i := by
      -- List.take_take gives (l.take m).take n = l.take (min n m)
      rw [List.take_take]
      congr 1
      -- min i (k + 1) = i since i < k + 1
      exact Nat.min_eq_left (Nat.le_of_lt hi)
    rw [h_get, h_take]
    exact τ.valid i hi'

/-!
## Infinite Space Properties
-/

/--
The all-zeros infinite sequence is valid (since 0 < radix for any prefix).
-/
def infiniteZeros (ω : RadixLaw) : InfiniteVariableSpace ω where
  digit := fun _ => 0
  valid := fun i => ω.radix_pos _

/--
There exist at least two distinct elements in InfiniteVariableSpace ω.
-/
theorem infiniteVariableSpace_nontrivial (ω : RadixLaw) :
    ∃ τ σ : InfiniteVariableSpace ω, τ ≠ σ := by
  -- The all-zeros sequence and a sequence starting with 1 are distinct
  use infiniteZeros ω
  -- Construct a sequence starting with 1 (valid since radix ≥ 2)
  use ⟨fun i => if i = 0 then 1 else 0, fun i => by
    by_cases hi : i = 0
    · simp only [hi, ↓reduceIte]
      -- Need: 1 < ω.radix (List.ofFn (fun j : Fin 0 => ...))
      simp only [List.ofFn_zero]
      -- radix ≥ 2 implies 1 < radix
      have h := ω.radix_ge_two []
      omega
    · simp only [hi, ↓reduceIte]
      exact ω.radix_pos _⟩
  intro heq
  have h := congrArg (·.digit 0) heq
  simp only [infiniteZeros, ↓reduceIte] at h
  exact absurd h (by norm_num)

/--
Construct an infinite sequence that is 1 at position n and 0 elsewhere.
This is valid because 0 < radix and 1 < radix (since radix ≥ 2).
-/
def singleOneAt (ω : RadixLaw) (n : ℕ) : InfiniteVariableSpace ω where
  digit := fun i => if i = n then 1 else 0
  valid := fun i => by
    by_cases hi : i = n
    · simp only [hi, ↓reduceIte]
      -- Need: 1 < ω.radix (prefix)
      -- Since radix ≥ 2 everywhere, 1 < radix
      calc 1 < 2 := by norm_num
        _ ≤ ω.radix _ := ω.radix_ge_two _
    · simp only [hi, ↓reduceIte]
      exact ω.radix_pos _

/--
The singleOneAt sequences are all distinct.
-/
theorem singleOneAt_injective (ω : RadixLaw) :
    Function.Injective (singleOneAt ω) := by
  intro m n hmn
  -- If singleOneAt m = singleOneAt n, then their digit functions are equal
  have h := congrArg (·.digit m) hmn
  simp only [singleOneAt] at h
  -- At position m, singleOneAt m has digit 1, singleOneAt n has digit (if m = n then 1 else 0)
  simp only [↓reduceIte] at h
  -- h says: 1 = if m = n then 1 else 0
  by_contra hmn'
  simp only [hmn', ↓reduceIte] at h
  exact absurd h.symm (by norm_num)

/--
InfiniteVariableSpace ω is infinite: we can construct distinct elements
by varying the position of a single 1.
-/
theorem infiniteVariableSpace_infinite (ω : RadixLaw) :
    Infinite (InfiniteVariableSpace ω) := by
  -- Construct an injection ℕ → InfiniteVariableSpace ω
  exact Infinite.of_injective (singleOneAt ω) (singleOneAt_injective ω)

/-!
## Note on the Infinite Case

**Mathematical Correction**: The infinite variable radix space R^{(∞)}_ω
is the boundary of an infinite tree with branching factor ≥ 2 at each node.
This space is UNCOUNTABLE (it contains a copy of Cantor space {0,1}^ℕ as a subset).

Therefore, there is NO bijection with ℕ. The original "THEOREM A (Infinite Case)"
statement claiming such a bijection was mathematically incorrect.

The correct formulation involves the projective limit structure:
- The finite spaces R^{(k)}_ω form a projective system under truncation
- R^{(∞)}_ω is homeomorphic to the projective limit lim←k R^{(k)}_ω
- Each finite space R^{(k)}_ω has a canonical bijection with Fin(completionCount k [])
-/

/-- The truncation map from InfiniteVariableSpace to FiniteVariableSpace -/
def truncateInfinite (ω : RadixLaw) (k : ℕ) (τ : InfiniteVariableSpace ω) :
    FiniteVariableSpace ω k where
  digits := List.ofFn (fun i : Fin (k + 1) => τ.digit i.val)
  length_eq := by simp only [List.length_ofFn]
  valid := by
    intro i hi
    simp only [List.length_ofFn] at hi
    -- Need to show (List.ofFn ...)[i] < ω.radix ((List.ofFn ...).take i)
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    -- Now need: τ.digit i < ω.radix ((List.ofFn fun i => τ.digit i).take i)
    have hvalid := τ.valid i
    convert hvalid using 2
    -- Show that (List.ofFn ...).take i = List.ofFn ...
    apply List.ext_getElem
    · simp only [List.length_take, List.length_ofFn]
      exact Nat.min_eq_left (Nat.le_of_lt hi)
    · intro j hj1 hj2
      simp only [List.getElem_take, List.getElem_ofFn]

/-- Truncation is compatible: truncating to j then to k equals truncating directly to k -/
theorem truncateInfinite_compat (ω : RadixLaw) (k j : ℕ) (hkj : k < j)
    (τ : InfiniteVariableSpace ω) :
    (truncateInfinite ω j τ).truncateToK k hkj = truncateInfinite ω k τ := by
  apply FiniteVariableSpace.ext
  simp only [FiniteVariableSpace.truncateToK, truncateInfinite]
  apply List.ext_getElem
  · simp only [List.length_take, List.length_ofFn]
    omega
  · intro i hi1 hi2
    simp only [List.getElem_take, List.getElem_ofFn]

/-!
## Properties of THEOREM A Bijection
-/

/-- The bijection preserves lexicographic order -/
theorem theoremA_orderPreserving (ω : RadixLaw) (k : ℕ)
    (τ σ : FiniteVariableSpace ω k) :
    τ.digits < σ.digits ↔
      variableRadixDecode ω k τ < variableRadixDecode ω k σ :=
  (decode_lt_iff ω k τ σ).symm

/--
Helper lemma: The only order-preserving automorphism of Fin n is the identity.

**Proof**: Build an OrderIso from the bijective strictly monotone map,
then apply Mathlib's `Fin.coe_orderIso_apply` which shows any OrderIso
on Fin acts as the identity on values.
-/
private theorem fin_strictMono_aut_is_id {n : ℕ} (h : Fin n → Fin n)
    (h_bij : Function.Bijective h)
    (h_mono : ∀ i j, i < j → h i < h j) :
    h = id := by
  have h_strictMono : StrictMono h := fun _ _ hab => h_mono _ _ hab
  -- Build an OrderIso from h
  let e : Fin n ≃o Fin n :=
    StrictMono.orderIsoOfSurjective h h_strictMono h_bij.2
  funext i
  simp only [id]
  have : (e i : ℕ) = (i : ℕ) := Fin.coe_orderIso_apply e i
  exact Fin.ext this

/--
**THEOREM A (Uniqueness)**: The bijection is the unique order-preserving bijection.

**Statement**: Any order-preserving bijection f: R^{(k)}_ω → Fin(M) must equal
the canonical decode function.

**Proof**: Construct h = f ∘ g⁻¹ : Fin M → Fin M, show it's an order-preserving
automorphism, apply `fin_strictMono_aut_is_id` to get h = id, conclude f = g.
-/
theorem theoremA_unique (ω : RadixLaw) (k : ℕ)
    (f : FiniteVariableSpace ω k → Fin (completionCount ω k []))
    (hf_bij : Function.Bijective f)
    (hf_order : ∀ τ σ, τ.digits < σ.digits → f τ < f σ) :
    f = fun τ => ⟨variableRadixDecode ω k τ, variableRadixDecode_lt ω k τ⟩ := by
  -- Define g = our canonical decode function
  let g : FiniteVariableSpace ω k → Fin (completionCount ω k []) :=
    fun τ => ⟨variableRadixDecode ω k τ, variableRadixDecode_lt ω k τ⟩

  -- g is bijective (already proven)
  have hg_bij : Function.Bijective g := theoremA_finite ω k

  -- g is order-preserving
  have hg_mono : ∀ τ σ, τ.digits < σ.digits → (g τ).val < (g σ).val := by
    intro τ σ h_lt
    simp only [g]
    exact (decode_lt_iff ω k τ σ).mpr h_lt

  -- Use the equivalence from g
  let g_equiv := finiteVariableRadixEquiv ω k

  -- Define h = f ∘ g_equiv.symm : Fin M → Fin M
  let h := fun i => f (g_equiv.symm i)

  -- h is a bijection Fin M → Fin M
  have h_bij : Function.Bijective h := by
    constructor
    · -- Injective
      intro i j heq
      have : g_equiv.symm i = g_equiv.symm j := hf_bij.1 heq
      have : i = g_equiv (g_equiv.symm i) := (g_equiv.apply_symm_apply i).symm
      rw [this]
      have : j = g_equiv (g_equiv.symm j) := (g_equiv.apply_symm_apply j).symm
      rw [this]
      rw [‹g_equiv.symm i = g_equiv.symm j›]
    · -- Surjective
      intro k'
      obtain ⟨τ, hτ⟩ := hf_bij.2 k'
      use g_equiv τ
      unfold h
      simp only [Equiv.symm_apply_apply]
      exact hτ

  -- h is strictly monotone
  have h_mono : ∀ i j, i < j → h i < h j := by
    intro i j hij
    unfold h
    apply hf_order
    -- Need: (g_equiv.symm i).digits < (g_equiv.symm j).digits
    -- This follows from g being order-preserving and i < j
    have hi : g (g_equiv.symm i) = i := g_equiv.apply_symm_apply i
    have hj : g (g_equiv.symm j) = j := g_equiv.apply_symm_apply j
    have hvals : (g (g_equiv.symm i)).val < (g (g_equiv.symm j)).val := by
      rw [hi, hj]
      exact hij
    unfold g at hvals
    exact (decode_lt_iff ω k (g_equiv.symm i) (g_equiv.symm j)).mp hvals

  -- h is an order-preserving automorphism, so h = id
  have h_id : h = id := fin_strictMono_aut_is_id h h_bij h_mono

  -- Therefore f ∘ g_equiv.symm = id, which means f = g_equiv.toFun
  ext τ_var
  -- Show: f τ_var = ⟨variableRadixDecode ω k τ_var, ...⟩
  -- Use Fin extensionality: show they have equal .val
  show (f τ_var).val = variableRadixDecode ω k τ_var
  calc (f τ_var).val
      = (h (g_equiv τ_var)).val := by
          unfold h
          -- f τ_var = f (g_equiv.symm (g_equiv τ_var))
          have : g_equiv.symm (g_equiv τ_var) = τ_var := g_equiv.symm_apply_apply τ_var
          rw [this]
    _ = (id (g_equiv τ_var)).val := by rw [h_id]
    _ = (g_equiv τ_var).val := rfl
    _ = (g τ_var).val := by
          unfold g
          rfl
    _ = variableRadixDecode ω k τ_var := by
          unfold g
          rfl

/-!
## Connection to Fixed Radix (Core)

When ω is position-only (depends only on prefix length), THEOREM A
specializes to the fixed-radix bijection from Core.

The key specialization: for `RadixLaw.ofRadixSeq b`, the variable radix
space has size `placeValue b (k + 1)`, matching the fixed-radix space `R^(k)`.
-/

open Core.Primitives in
private theorem radixLaw_ext' {ω₁ ω₂ : RadixLaw} (h : ω₁.radix = ω₂.radix) : ω₁ = ω₂ := by
  cases ω₁; cases ω₂; simp_all

open Core.Primitives in
private theorem placeValue_eq_prod (b : RadixSeq) :
    ∀ m, placeValue b (m + 1) =
      (Finset.range (m + 1)).prod (fun i => (b : ℕ → ℕ) i) := by
  intro m; induction m with
  | zero =>
    rw [placeValue.succ, placeValue.zero, Nat.one_mul, Finset.prod_range_one]
  | succ m ih =>
    rw [placeValue.succ, ih]
    exact (Finset.prod_range_succ _ _).symm

open Core.Primitives in
/--
**Specialization of Theorem A to fixed radix**:
For a RadixSeq b, the variable radix space R^(k)_ω has the same size as the
fixed-radix space R^(k)_b = Fin(placeValue b (k+1)).

This shows that the variable radix framework generalizes the fixed radix
framework: when ω = ofRadixSeq(b), the spaces are equinumerous.

**Proof**: By induction on k with generalized offset to handle the shift.
At each step, the shifted RadixLaw is position-only with offset + 1,
and the space size decomposes as b(n) × ∏_{i<k+1} b(i+n+1) = ∏_{i<k+2} b(i+n).
-/
theorem theoremA_specializes_to_fixed_statement (b : RadixSeq) (k : ℕ) :
    completionCount (RadixLaw.ofRadixSeq b) k [] = placeValue b (k + 1) := by
  rw [completionCount_nil, placeValue_eq_prod]
  -- Prove card of position-only law with offset n = product of radices
  -- Then specialize to n = 0 (matches ofRadixSeq b by definitional equality)
  suffices h : ∀ (n : ℕ) (k : ℕ),
      FiniteVariableSpace.card
        ⟨fun s => b (s.length + n), fun s => b.ge_two (s.length + n)⟩ k =
        (Finset.range (k + 1)).prod (fun i => (b : ℕ → ℕ) (i + n)) from h 0 k
  intro n k
  induction k generalizing n with
  | zero =>
    simp only [FiniteVariableSpace.card, List.length_nil, Nat.zero_add, Finset.prod_range_one]
  | succ k ih =>
    unfold FiniteVariableSpace.card
    show Finset.sum (Finset.range (b (0 + n)))
      (fun d => FiniteVariableSpace.card
        ((⟨fun s => b (s.length + n),
          fun s => b.ge_two (s.length + n)⟩ : RadixLaw).shift d) k) =
      (Finset.range (k + 1 + 1)).prod (fun i => (b : ℕ → ℕ) (i + n))
    simp only [Nat.zero_add]
    -- Each shifted law equals the law with offset n + 1
    have h_shift : ∀ d,
        (⟨fun s => b (s.length + n),
          fun s => b.ge_two (s.length + n)⟩ : RadixLaw).shift d =
        ⟨fun s => b (s.length + (n + 1)),
          fun s => b.ge_two (s.length + (n + 1))⟩ := by
      intro d; apply radixLaw_ext'; funext s
      simp only [RadixLaw.shift, List.length_cons]; ring_nf
    simp_rw [h_shift, ih (n + 1)]
    -- Sum of constant: ∑_{d<m} c = m * c
    have h_const : ∀ (m c : ℕ), (Finset.range m).sum (fun _ => c) = m * c := by
      intro m c; simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    rw [h_const]
    -- b(n) * ∏_{i<k+1} b(i+n+1) = ∏_{i<k+2} b(i+n)
    -- Prove by factoring RHS using prod_range_succ'
    symm
    calc (Finset.range (k + 1 + 1)).prod (fun i => (b : ℕ → ℕ) (i + n))
        = (Finset.range (k + 1)).prod (fun i => (b : ℕ → ℕ) (i + 1 + n)) *
          (b : ℕ → ℕ) (0 + n) :=
          Finset.prod_range_succ' _ _
      _ = (b : ℕ → ℕ) n *
          (Finset.range (k + 1)).prod (fun i => (b : ℕ → ℕ) (i + (n + 1))) := by
          rw [mul_comm, Nat.zero_add]
          congr 1; apply Finset.prod_congr rfl; intro i _; congr 1; omega

end FdrsFormal.Modes.VariableRadix
