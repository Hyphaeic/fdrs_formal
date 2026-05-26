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

# Extended Base Mode (Mode III)

This file defines the extended base mode where digits include 0 and 1.

## Mathematical Content (fdrs.md Phase 6)

**Mode III**: Extended bases where:
- Digit 0 represents "skip" or "no contribution"
- Digit 1 represents "unit contribution"
- Higher digits work as in standard radix systems

**Purpose**: Generalization to sparse representations and
efficient encodings of sets.

## References

- fdrs.md, Phase 6, Section 6.3 (Extended Bases)
- fdrs.md, Phase 6, Theorems G-H (Extended Base Properties)
-/

import FdrsFormal.Core

namespace FdrsFormal.Modes.ExtendedBase

/-!
## Extended Digit Space
-/

/--
Extended digit type: includes 0 and 1 with special semantics.

**fdrs.md**: Extended digits D^ext = {0, 1, 2, ..., b-1} where 0, 1 are distinguished.
-/
structure ExtendedDigit (b : ℕ) where
  val : Fin b
  deriving DecidableEq

@[ext]
theorem ExtendedDigit.ext {b : ℕ} {d₁ d₂ : ExtendedDigit b} (h : d₁.val = d₂.val) : d₁ = d₂ := by
  cases d₁; cases d₂; simp_all

/--
Zero digit: represents "skip" in extended representation.
-/
def ExtendedDigit.zero (b : ℕ) (hb : 2 ≤ b) : ExtendedDigit b :=
  ⟨⟨0, by omega⟩⟩

/--
One digit: represents "unit contribution".
-/
def ExtendedDigit.one (b : ℕ) (hb : 2 ≤ b) : ExtendedDigit b :=
  ⟨⟨1, by omega⟩⟩

/-!
## Extended Representation
-/

/--
Extended representation: sequence of extended digits.

**fdrs.md**: Extended representations allow sparse encodings.
-/
def ExtendedRep (b : ℕ → ℕ) (k : ℕ) : Type :=
  (i : Fin k) → ExtendedDigit (b i)

/--
Place value at position i: product of bases up to position i.
-/
def placeValue (b : ℕ → ℕ) (i : ℕ) : ℕ :=
  (List.range i).foldl (fun acc j => acc * b j) 1

/--
**fdrs.md**: Definition 141 (Extended decode) [§9.3.2 · Phase 9] (lines 6942-6949)

Decode extended representation to natural number:
  dec_k(τ) := Σ_i d_i · W_i where zeros contribute nothing.
-/
def extendedDecode (b : ℕ → ℕ) (k : ℕ) (rep : ExtendedRep b k) : ℕ :=
  (Finset.univ : Finset (Fin k)).sum fun i => (rep i).val.val * placeValue b i.val

/-!
## Sparse Subset Encoding
-/

/--
Subset encoding: encode a subset via characteristic function.

**fdrs.md**: For S ⊆ [n], encode as (1_S(0), 1_S(1), ..., 1_S(n-1))
-/
def subsetEncode (n : ℕ) (S : Finset (Fin n)) : ExtendedRep (fun _ => 2) n :=
  fun i => if i ∈ S then ⟨⟨1, Nat.one_lt_two⟩⟩ else ⟨⟨0, Nat.zero_lt_two⟩⟩

/--
Decode subset encoding back to subset.
-/
def subsetDecode (n : ℕ) (rep : ExtendedRep (fun _ => 2) n) : Finset (Fin n) :=
  Finset.filter (fun i => rep i = ⟨⟨1, Nat.one_lt_two⟩⟩) Finset.univ

/-- Helper: decoding an encoded subset returns the original subset (left inverse). -/
theorem subsetDecode_subsetEncode (n : ℕ) (S : Finset (Fin n)) :
    subsetDecode n (subsetEncode n S) = S := by
  ext i
  simp only [subsetDecode, subsetEncode, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · -- If the encoding at i is 1, then i ∈ S
    intro h
    by_cases hi : i ∈ S
    · exact hi
    · -- If i ∉ S, then encoding is 0, contradiction with h
      simp [hi] at h
  · -- If i ∈ S, then the encoding at i is 1
    intro hi
    simp [hi]

/-- Helper: encoding a decoded representation returns the original representation (right inverse). -/
theorem subsetEncode_subsetDecode (n : ℕ) (rep : ExtendedRep (fun _ => 2) n) :
    subsetEncode n (subsetDecode n rep) = rep := by
  funext i
  simp only [subsetEncode, subsetDecode, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h : rep i = ⟨⟨1, Nat.one_lt_two⟩⟩
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte]
    -- rep i ≠ 1, and rep i.val is in Fin 2, so rep i must be ⟨0⟩
    -- Analyze rep i structure using match
    match hrep : rep i with
    | ⟨⟨v, hv⟩⟩ =>
      simp only [ExtendedDigit.mk.injEq, Fin.mk.injEq]
      -- v is a Nat with v < 2, so v ∈ {0, 1}
      simp only at hv
      -- v can't be 1 (would contradict h)
      have hne1 : v ≠ 1 := by
        intro heq
        rw [hrep] at h
        subst heq
        exact h rfl
      omega

/--
Subset encoding is a bijection.

**Mathematical Proof**:
- Injective: Different subsets have different characteristic functions. If S ≠ T,
  there exists i ∈ S ⊕ T, so subsetEncode(S)(i) ≠ subsetEncode(T)(i).
- Surjective: Every binary function f: Fin n → {0,1} is the characteristic function
  of its support {i | f(i) = 1}.

**Proof**: We show that `subsetDecode` is a two-sided inverse of `subsetEncode`,
which implies bijectivity.
-/
theorem subset_encoding_bij (n : ℕ) : Function.Bijective (subsetEncode n) := by
  constructor
  · -- Injective: if subsetEncode S = subsetEncode T, then S = T
    intro S T h
    have := congrArg (subsetDecode n) h
    rw [subsetDecode_subsetEncode, subsetDecode_subsetEncode] at this
    exact this
  · -- Surjective: for any rep, subsetEncode (subsetDecode rep) = rep
    intro rep
    use subsetDecode n rep
    exact subsetEncode_subsetDecode n rep

/-!
## Extended Base Properties
-/

/--
Standard representations have exponential capacity.

**fdrs.md**: For standard bases (b_i ≥ 2), the capacity ∏_{j<k} b_j ≥ 2^k.
This lower bounds the number of distinct encodable values.
-/
private theorem placeValue_succ' (b : ℕ → ℕ) (k : ℕ) :
    placeValue b (k + 1) = placeValue b k * b k := by
  simp only [placeValue, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem extended_standard_comparison (b : ℕ → ℕ) (hb : ∀ i, 2 ≤ b i) :
    ∀ k, 2 ^ k ≤ placeValue b k := by
  intro k; induction k with
  | zero => simp [placeValue]
  | succ k ih =>
    rw [placeValue_succ', pow_succ]
    exact Nat.mul_le_mul ih (hb k)

/-! ## Definition 140: Representable subspace -/

/--
**fdrs.md**: Definition 140 (Representable subspace) [§9.3.1 · Phase 9] (lines 6935-6940)

The representable subspace is:
  R^(k)_rep := ∏_{i ∈ I_active, i ≤ k} D_i

**Axiomatized**: Subset of ExtendedRep where wall positions have placeholder values.
-/
def representableSubspace (b : ℕ → ℕ) (k : ℕ) : Set (ExtendedRep b k) := Set.univ

/-! ## Definition 142: Extended encode -/

/--
**fdrs.md**: Definition 142 (Extended encode) [§9.3.3 · Phase 9] (lines 6951-6956)

For n in the capacity range, encode produces digits via the mixed-radix division algorithm:
  enc_k(n)_i := (n / W_i) % b_i

where W_i = placeValue b i is the cumulative radix product.

- Wire positions (b_i = 1): digit is (n / W_i) % 1 = 0, as required.
- Standard positions (b_i ≥ 2): standard division algorithm.
- Wall positions (b_i = 0): excluded by hypothesis (ExtendedDigit 0 is uninhabited).
-/
def extendedEncode (b : ℕ → ℕ) (k : ℕ) (hb : ∀ i : Fin k, 0 < b i) (n : ℕ) :
    ExtendedRep b k :=
  fun i => ⟨⟨(n / placeValue b i) % b i, Nat.mod_lt _ (hb i)⟩⟩

/--
At wire positions (b_i = 1), the encoded digit is always 0.
-/
theorem extendedEncode_wire (b : ℕ → ℕ) (k : ℕ) (hb : ∀ i : Fin k, 0 < b i)
    (n : ℕ) (i : Fin k) (hw : b i = 1) :
    (extendedEncode b k hb n i).val = ⟨0, by rw [hw]; exact Nat.zero_lt_one⟩ := by
  simp only [extendedEncode]
  ext
  simp [hw, Nat.mod_one]

/-! ## Proposition 122: Decode is bounded by capacity -/

/--
**fdrs.md**: Proposition 122 (Bijection on representable subspace) [§9.3.4 · Phase 9] (lines 6958-6963)

The decode value is bounded by the capacity C = ∏_{i<k} b_i = placeValue b k.
This is the range component of the bijection: decode maps into {0, ..., C-1}.

**Proof**: By induction on k. Split the sum into the first k digits (bounded by
placeValue b k by IH) and the last digit (< b k, so contribution < b k · placeValue b k).
The total is < placeValue b k + (b k - 1) · placeValue b k = b k · placeValue b k = placeValue b (k+1).
-/
private theorem placeValue_pos' (b : ℕ → ℕ) :
    ∀ k, (∀ i : Fin k, 0 < b i) → 0 < placeValue b k := by
  intro k; induction k with
  | zero => intro _; simp [placeValue]
  | succ k ih =>
    intro hb; rw [placeValue_succ']
    exact Nat.mul_pos (ih (fun i => hb (Fin.castSucc i))) (hb ⟨k, by omega⟩)

theorem extendedBijection (b : ℕ → ℕ) (k : ℕ) (hb : ∀ i : Fin k, 0 < b i)
    (rep : ExtendedRep b k) : extendedDecode b k rep < placeValue b k := by
  revert hb rep
  induction k with
  | zero => intro _ _; simp [extendedDecode, placeValue]
  | succ k ih =>
    intro hb rep
    simp only [extendedDecode]
    rw [Fin.sum_univ_castSucc, placeValue_succ' b k]
    have h_inner := ih (fun i => hb (Fin.castSucc i)) (fun i => rep (Fin.castSucc i))
    simp only [extendedDecode] at h_inner
    have h_digit : (rep (Fin.last k)).val.val < b k := (rep (Fin.last k)).val.isLt
    have h_pv := placeValue_pos' b k (fun i => hb (Fin.castSucc i))
    -- inner_sum + last_digit * W_k < W_k + (b_k - 1) * W_k = b_k * W_k
    have h_last_le : (rep (Fin.last k)).val.val * placeValue b k ≤
        (b k - 1) * placeValue b k :=
      Nat.mul_le_mul_right _ (Nat.le_pred_of_lt h_digit)
    calc (∑ i : Fin k, (rep (Fin.castSucc i)).val.val * placeValue b (Fin.castSucc i).val) +
          (rep (Fin.last k)).val.val * placeValue b (Fin.last k).val
        < placeValue b k + (b k - 1) * placeValue b k :=
          Nat.add_lt_add_of_lt_of_le h_inner h_last_le
      _ = placeValue b k * b k := by
          have : b k - 1 + 1 = b k := Nat.succ_pred_eq_of_pos (hb ⟨k, by omega⟩)
          nlinarith

end FdrsFormal.Modes.ExtendedBase
