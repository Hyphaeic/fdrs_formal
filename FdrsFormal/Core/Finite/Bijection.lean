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
Authors: [Billy The Inorganic]

# Finite Mixed-Radix Spaces

This file defines finite mixed-radix spaces and proves the fundamental bijection
between digit sequences and natural numbers (Proposition 1).

## References

- fdrs.md, Phase 1 Fragment 1, Definitions 2.1-2.2, Proposition 1
-/

import FdrsFormal.Core.Primitives

namespace FdrsFormal.Core.Finite

open FdrsFormal.Core.Primitives

variable {b : RadixSeq}

/-! ## Definition 1: Finite horizon space -/

/-- The finite mixed-radix space R^(k) is the product of digit alphabets D_0 × ... × D_k. -/
def FiniteRadixSpace (b : RadixSeq) (k : ℕ) := (i : Fin (k + 1)) → Fin (b i)

namespace FiniteRadixSpace

variable {k : ℕ}

def zero (b : RadixSeq) (k : ℕ) : FiniteRadixSpace b k := fun i => ⟨0, b.pos i⟩
def max (b : RadixSeq) (k : ℕ) : FiniteRadixSpace b k := fun i => ⟨b i - 1, Nat.sub_lt (b.pos i) Nat.one_pos⟩

instance : Inhabited (FiniteRadixSpace b k) := ⟨zero b k⟩

/-- FiniteRadixSpace is a finite type (product of finite types). -/
instance : Fintype (FiniteRadixSpace b k) := by
  unfold FiniteRadixSpace
  infer_instance

/-- Discrete measurable space on finite radix spaces (for measure theory). -/
instance : MeasurableSpace (FiniteRadixSpace b k) :=
  ⊤

/-- Singletons are measurable in the discrete topology. -/
instance : MeasurableSingletonClass (FiniteRadixSpace b k) where
  measurableSet_singleton _ := trivial

/-- Extensionality for FiniteRadixSpace: two elements are equal iff they agree at all indices. -/
@[ext]
theorem ext {τ σ : FiniteRadixSpace b k} (h : ∀ i : Fin (k + 1), τ i = σ i) : τ = σ :=
  funext h

end FiniteRadixSpace

/-! ## Definition 2: Finite decoding and encoding -/

/-- The decode map dec_k : R^(k) → ℕ -/
def decodeFinite (b : RadixSeq) (k : ℕ) (τ : FiniteRadixSpace b k) : ℕ :=
  ∑ i : Fin (k + 1), (τ i : ℕ) * placeValue b i

/-- dec_k(τ) < B_{k+1} -/
theorem decodeFinite_lt (k : ℕ) (τ : FiniteRadixSpace b k) :
    decodeFinite b k τ < placeValue b (k + 1) :=
  placeValue.sum_digits_lt k τ

/-- The encode map enc_k : Fin B_{k+1} → R^(k) -/
def encodeFinite (b : RadixSeq) (k : ℕ) (n : Fin (placeValue b (k + 1))) : FiniteRadixSpace b k :=
  fun i => ⟨(n / placeValue b i) % b i, Nat.mod_lt _ (b.pos i)⟩

/-! ## Helper Lemmas for Proposition 1 -/

/-- **Key Reconstruction Lemma**: n = ∑_i ((n / B_i) % b_i) * B_i

    This proves that extracting digits via division/mod and summing them back
    correctly reconstructs the original number.

    **Proof shape**: induction on `k`. Base case: a single digit below `b 0`.
    Inductive step: split `n = B_{k+1} * (n / B_{k+1}) + (n % B_{k+1})` via
    `Nat.div_add_mod`; digit extraction below position `k+1` factors through
    `n % B_{k+1}` (locality, via `placeValue.dvd_of_le`); apply the IH to
    `n % B_{k+1}`; account the top digit `(n / B_{k+1}) % b (k+1)`. -/
theorem sum_div_mod_placeValue (k : ℕ) (n : ℕ) (hn : n < placeValue b (k + 1)) :
    n = ∑ i : Fin (k + 1), ((n / placeValue b i) % b i) * placeValue b i := by
  induction k generalizing n with
  | zero =>
    rw [Fin.sum_univ_one]
    simp only [Fin.val_zero, placeValue.zero, Nat.div_one, Nat.mul_one]
    have h_lt : n < b 0 := by
      calc n < placeValue b 1 := hn
        _ = b 0 := by rw [placeValue.succ, placeValue.zero, Nat.one_mul]
    exact (Nat.mod_eq_of_lt h_lt).symm
  | succ k ih =>
    -- INDUCTIVE STEP
    -- Split the sum into digits 0..k and the final digit k+1
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]

    -- Use division algorithm: n = q * B_{k+1} + r
    set q := n / placeValue b (k + 1)
    set r := n % placeValue b (k + 1)

    -- Show q < b(k+1) from the bound hn
    have hq_lt : q < b (k + 1) := by
      rw [placeValue.succ, Nat.mul_comm] at hn
      exact Nat.div_lt_iff_lt_mul (placeValue.pos (k + 1)) |>.mpr hn

    -- KEY LEMMA: Digit extraction is local - for i ≤ k, digits come from r, not from the quotient q
    have digit_locality : ∀ i : Fin (k + 1),
        (n / placeValue b i) % b i = (r / placeValue b i) % b i := by
      intro i
      have hdvd : placeValue b i ∣ placeValue b (k + 1) :=
        placeValue.dvd_of_le (Nat.le_of_lt i.isLt)
      obtain ⟨c, hc⟩ := hdvd

      -- Show that b_i divides c
      -- Since B_{k+1} = B_i * c and B_{i+1} = B_i * b_i, and B_{i+1} | B_{k+1}, we get b_i | c
      have b_dvd_c : b i ∣ c := by
        have h_succ : placeValue b (i + 1) = placeValue b i * b i := placeValue.succ i
        have hdvd2 : placeValue b (i + 1) ∣ placeValue b (k + 1) :=
          placeValue.dvd_of_le (Nat.succ_le_of_lt i.isLt)
        rw [hc, h_succ] at hdvd2
        -- hdvd2 : B_i * b_i ∣ B_i * c
        have hpos : 0 < placeValue b i := placeValue.pos i
        exact Nat.dvd_of_mul_dvd_mul_left hpos hdvd2

      -- Key property: (q * c) % b_i = 0 since b_i | c
      have qc_mod : (q * c) % b i = 0 := by
        rw [Nat.mul_mod]; simp [Nat.mod_eq_zero_of_dvd b_dvd_c]

      -- Show digit extraction is local using the division property
      calc (n / placeValue b i) % b i
        _ = ((placeValue b (k + 1) * q + r) / placeValue b i) % b i := by
            rw [← Nat.div_add_mod n (placeValue b (k + 1))]
        _ = ((q * placeValue b (k + 1) + r) / placeValue b i) % b i := by ring_nf
        _ = ((q * (placeValue b i * c) + r) / placeValue b i) % b i := by rw [hc]
        _ = (q * c + r / placeValue b i) % b i := by
            have step1 : q * (placeValue b i * c) = placeValue b i * (q * c) := by ring
            rw [step1]
            -- Apply division lemma: (B_i * a + r) / B_i = a + r / B_i
            congr 1
            calc (placeValue b i * (q * c) + r) / placeValue b i
              _ = (r + placeValue b i * (q * c)) / placeValue b i := by ring_nf
              _ = r / placeValue b i + q * c := Nat.add_mul_div_left r (q * c) (placeValue.pos i)
              _ = q * c + r / placeValue b i := by ring
        _ = ((q * c) % b i + (r / placeValue b i) % b i) % b i := Nat.add_mod _ _ _
        _ = (r / placeValue b i) % b i := by rw [qc_mod]; simp

    -- Apply IH to r to get its representation
    have hr_lt : r < placeValue b (k + 1) := Nat.mod_lt n (placeValue.pos (k + 1))
    have r_eq_sum := ih r hr_lt

    -- The digit sum for n equals the digit sum for r (by digit locality)
    have sum_eq : ∑ i : Fin (k + 1), ((n / placeValue b i) % b i) * placeValue b i =
                  ∑ i : Fin (k + 1), ((r / placeValue b i) % b i) * placeValue b i :=
      Finset.sum_congr rfl fun i _ => by
        congr 1
        exact digit_locality i

    -- Combine everything
    calc n
      _ = placeValue b (k + 1) * q + r := (Nat.div_add_mod n (placeValue b (k + 1))).symm
      _ = (q % b (k + 1)) * placeValue b (k + 1) + r := by rw [Nat.mod_eq_of_lt hq_lt]; ring
      _ = (n / placeValue b (k + 1)) % b (k + 1) * placeValue b (k + 1) + r := rfl
      _ = (n / placeValue b (k + 1)) % b (k + 1) * placeValue b (k + 1) +
          ∑ i : Fin (k + 1), ((r / placeValue b i) % b i) * placeValue b i := by rw [← r_eq_sum]
      _ = (n / placeValue b (k + 1)) % b (k + 1) * placeValue b (k + 1) +
          ∑ i : Fin (k + 1), ((n / placeValue b i) % b i) * placeValue b i := by rw [sum_eq]
      _ = ∑ i : Fin (k + 1), ((n / placeValue b i) % b i) * placeValue b i +
          (n / placeValue b (k + 1)) % b (k + 1) * placeValue b (k + 1) := by ring

/-- **Uniqueness Lemma**: If two digit sequences decode to the same value, they are equal.

    This proves that the mixed-radix representation is unique (injectivity of decode).

    **Proof shape**: functional extensionality, then per-position digit
    extraction by modular arithmetic — take the sum mod `B_{i+1}`, divide by
    `B_i`, reduce mod `b i`; higher terms vanish by `placeValue.dvd_of_le`. -/
theorem digits_unique {k : ℕ} (d e : (i : Fin (k + 1)) → Fin (b i))
    (h : ∑ i : Fin (k + 1), (d i : ℕ) * placeValue b i =
         ∑ i : Fin (k + 1), (e i : ℕ) * placeValue b i) :
    d = e := by
  -- Proof by induction on k (size of the digit sequence)
  induction k with
  | zero =>
    -- For k=0, we have a single digit
    funext i
    -- For Fin 1, there's only one element: i must equal 0
    apply Fin.ext
    -- Since i : Fin 1, we have i = 0
    have hi : i = 0 := by ext; simp
    rw [hi]
    -- The sum has only one term (at index 0)
    have hd_sum : ∑ j : Fin 1, (d j : ℕ) * placeValue b j = (d 0 : ℕ) * placeValue b 0 := Fin.sum_univ_one _
    have he_sum : ∑ j : Fin 1, (e j : ℕ) * placeValue b j = (e 0 : ℕ) * placeValue b 0 := Fin.sum_univ_one _
    rw [hd_sum, he_sum] at h
    simp only [placeValue.zero, Nat.mul_one] at h
    -- Now h : (d 0) = (e 0) as natural numbers
    exact h

  | succ k ih =>
    -- Inductive step: use modular arithmetic to extract each digit
    -- Classical proof: take mod b_0, show d_0 = e_0, subtract and repeat

    funext i

    -- We'll use the fact that d_i = (sum / B_i) % b_i
    -- Since the sums are equal, the extracted digits are equal

    apply Fin.ext

    -- Extract digit i from both sums
    -- Key lemma: extracting digit i from the sum gives us f_i
    -- Proof strategy (fdrs.md lines 52-56): Modular extraction
    --
    -- Mathematical idea:
    -- S = ∑ f_j * B_j can be split as:
    -- - Terms j < i: sum < B_i (by sum_max_digits), contribute 0 to (S / B_i)
    -- - Term j = i: contributes f_i to (S / B_i)
    -- - Terms j > i: each B_j divisible by B_{i+1} = B_i * b_i, so contribute multiples of b_i to (S / B_i)
    -- Therefore: (S / B_i) % b_i = f_i
    have extract_from_sum : ∀ (f : (j : Fin (k + 2)) → Fin (b j)),
        (∑ j : Fin (k + 2), (f j : ℕ) * placeValue b j) / placeValue b i % b i = (f i : ℕ) := by
      intro f
      -- **Mathematical Strategy** (fdrs.md lines 52-56):
      -- For S = ∑_j f_j * B_j, we extract digit i via: (S / B_i) % b_i = f_i
      -- This works because:
      --   - Low terms (j < i): total < B_i, so contribute 0 to S / B_i
      --   - Middle term (j = i): contributes exactly f_i to S / B_i
      --   - High terms (j > i): each B_j divisible by B_{i+1} = B_i * b_i,
      --                         so contribute multiples of b_i to S / B_i

      set S := ∑ j : Fin (k + 2), (f j : ℕ) * placeValue b j
      have hf_lt : (f i : ℕ) < b i := (f i).isLt
      have hB_pos : 0 < placeValue b i := placeValue.pos i

      -- Strategy: Split sum into low (j < i), middle (j = i), high (j > i) parts
      -- S = L + f_i * B_i + H where L < B_i
      -- So S / B_i = f_i + (L + H) / B_i where L contributes 0
      -- And (S / B_i) % b_i = f_i since high terms are divisible by b_i

      -- Split the sum into low (< i), middle (= i), high (> i) parts
      set low := ∑ j ∈ Finset.filter (fun j : Fin (k + 2) => j.val < i.val) Finset.univ,
                    (f j : ℕ) * placeValue b j with hlow
      set mid := (f i : ℕ) * placeValue b i with hmid
      set high := ∑ j ∈ Finset.filter (fun j : Fin (k + 2) => j.val > i.val) Finset.univ,
                    (f j : ℕ) * placeValue b j with hhigh

      have sum_split : S = low + mid + high := by
        -- Split the full sum at i
        have h1 : S = (∑ j ∈ Finset.filter (fun j : Fin (k + 2) => j.val < i.val) Finset.univ,
                        (f j : ℕ) * placeValue b j) +
                      (∑ j ∈ Finset.filter (fun j : Fin (k + 2) => ¬ j.val < i.val) Finset.univ,
                        (f j : ℕ) * placeValue b j) := by
          simp only [S]
          exact (Finset.sum_filter_add_sum_filter_not Finset.univ _ _).symm

        -- Split the "not less than i" part into "equal to i" and "greater than i"
        have h2 : (∑ j ∈ Finset.filter (fun j : Fin (k + 2) => ¬ j.val < i.val) Finset.univ,
                    (f j : ℕ) * placeValue b j) =
                  (∑ j ∈ Finset.filter (fun j : Fin (k + 2) => j.val = i.val)
                      (Finset.filter (fun j => ¬ j.val < i.val) Finset.univ),
                    (f j : ℕ) * placeValue b j) +
                  (∑ j ∈ Finset.filter (fun j : Fin (k + 2) => ¬ j.val = i.val)
                      (Finset.filter (fun j => ¬ j.val < i.val) Finset.univ),
                    (f j : ℕ) * placeValue b j) := by
          exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

        -- The middle filter is just {i}
        have hmid_filter : Finset.filter (fun j : Fin (k + 2) => j.val = i.val)
            (Finset.filter (fun j => ¬ j.val < i.val) Finset.univ) = {i} := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt, Finset.mem_singleton]
          constructor
          · intro ⟨hle, heq⟩; exact Fin.ext heq
          · intro hj; rw [hj]; exact ⟨Nat.le_refl _, rfl⟩

        -- The high filter is {j | j > i}
        have hhigh_filter : Finset.filter (fun j : Fin (k + 2) => ¬ j.val = i.val)
            (Finset.filter (fun j => ¬ j.val < i.val) Finset.univ) =
            Finset.filter (fun j : Fin (k + 2) => j.val > i.val) Finset.univ := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
          constructor
          · intro ⟨hle, hne⟩; exact Nat.lt_of_le_of_ne hle (Ne.symm hne)
          · intro hgt; exact ⟨Nat.le_of_lt hgt, Nat.ne_of_gt hgt⟩

        rw [h1, h2, hmid_filter, Finset.sum_singleton, hhigh_filter]
        simp only [← hlow, ← hmid, ← hhigh]
        ring

      -- Low terms sum to < B_i
      have low_lt : low < placeValue b i := by
        -- Case split on i
        cases i with
        | mk ival iisLt =>
          cases ival with
          | zero =>
            -- i = 0: no terms with j < 0, so low = 0 < B_0 = 1
            simp only [hlow, Nat.not_lt_zero, Finset.filter_false, Finset.sum_empty,
                       placeValue.zero]
            exact Nat.one_pos
          | succ n =>
            -- i = n + 1: low ≤ sum of max digits < B_{n+1}
            have h1 : low ≤ ∑ j ∈ Finset.filter (fun j : Fin (k + 2) => j.val < n + 1) Finset.univ,
                (b j - 1) * placeValue b j := by
              simp only [hlow]
              apply Finset.sum_le_sum
              intro j _
              apply Nat.mul_le_mul_right
              exact Nat.le_sub_one_of_lt (f j).isLt
            -- The max digit sum equals B_{n+1} - 1
            have h2 : ∑ j ∈ Finset.filter (fun j : Fin (k + 2) => j.val < n + 1) Finset.univ,
                (b j - 1) * placeValue b j = placeValue b (n + 1) - 1 := by
              -- Reindex to a sum over Fin (n + 1)
              have hreindex : ∑ j ∈ Finset.filter (fun j : Fin (k + 2) => j.val < n + 1) Finset.univ,
                  (b j - 1) * placeValue b j =
                  ∑ j : Fin (n + 1), (b j - 1) * placeValue b j := by
                refine Finset.sum_bij' (fun (j : Fin (k + 2)) _ => ⟨j.val, by
                      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
                      assumption⟩)
                    (fun (j : Fin (n + 1)) _ => ⟨j.val, Nat.lt_trans j.isLt iisLt⟩)
                    ?_ ?_ ?_ ?_ ?_
                · intro j hj; simp
                · intro j _; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact j.isLt
                · intro j _; rfl
                · intro j _; rfl
                · intro j _; rfl
              rw [hreindex]
              exact placeValue.sum_max_digits n
            calc low ≤ ∑ j ∈ Finset.filter (fun j : Fin (k + 2) => j.val < n + 1) Finset.univ,
                          (b j - 1) * placeValue b j := h1
              _ = placeValue b (n + 1) - 1 := h2
              _ < placeValue b (n + 1) := Nat.sub_lt (placeValue.pos (n + 1)) Nat.one_pos

      -- High terms are divisible by B_i * b_i = B_{i+1}
      have high_div : placeValue b (i + 1) ∣ high := by
        apply Finset.dvd_sum
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        have hdvd : placeValue b (i + 1) ∣ placeValue b j := placeValue.dvd_of_le hj
        exact Dvd.dvd.mul_left hdvd _

      -- Compute S / B_i
      -- Since low < B_i, we have (low + mid + high) / B_i = f_i + high / B_i
      have div_eq : S / placeValue b i = (f i : ℕ) + high / placeValue b i := by
        rw [sum_split]
        -- Rewrite: low + mid + high = low + f_i * B_i + high
        simp only [hmid]
        -- high is divisible by B_i (since B_{i+1} = B_i * b_i divides high)
        have hBi_dvd_high : placeValue b i ∣ high := by
          have h1 : placeValue b i ∣ placeValue b (i + 1) := Dvd.intro (b i) (placeValue.succ i)
          exact dvd_trans h1 high_div
        obtain ⟨q, hq⟩ := hBi_dvd_high
        -- hq: high = placeValue b i * q
        -- Show high / B_i = q
        have hq2 : high / placeValue b i = q := by
          rw [hq, Nat.mul_div_cancel_left _ hB_pos]
        -- Compute the division
        calc (low + (f i : ℕ) * placeValue b i + high) / placeValue b i
          _ = (low + (f i : ℕ) * placeValue b i + placeValue b i * q) / placeValue b i := by rw [hq]
          _ = (low + placeValue b i * ((f i : ℕ) + q)) / placeValue b i := by ring_nf
          _ = low / placeValue b i + ((f i : ℕ) + q) := by
              rw [Nat.add_mul_div_left _ _ hB_pos]
          _ = 0 + ((f i : ℕ) + q) := by rw [Nat.div_eq_of_lt low_lt]
          _ = (f i : ℕ) + q := by ring
          _ = (f i : ℕ) + high / placeValue b i := by rw [hq2]

      -- high / B_i is divisible by b_i (since high is divisible by B_{i+1} = B_i * b_i)
      have h_div_mod : (high / placeValue b i) % b i = 0 := by
        have h1 : placeValue b (i + 1) = placeValue b i * b i := placeValue.succ i
        obtain ⟨c, hc⟩ := high_div
        -- high = B_{i+1} * c = B_i * b_i * c
        rw [h1] at hc
        -- high / B_i = b_i * c
        have hdiv : high / placeValue b i = b i * c := by
          rw [hc]
          rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ hB_pos]
        rw [hdiv, Nat.mul_mod_right]

      -- Finally: (S / B_i) % b_i = f_i
      calc S / placeValue b i % b i
        _ = ((f i : ℕ) + high / placeValue b i) % b i := by rw [div_eq]
        _ = ((f i : ℕ) % b i + (high / placeValue b i) % b i) % b i := Nat.add_mod _ _ _
        _ = ((f i : ℕ) % b i + 0) % b i := by rw [h_div_mod]
        _ = (f i : ℕ) % b i := by simp
        _ = (f i : ℕ) := Nat.mod_eq_of_lt hf_lt

    -- Use extract_from_sum to show d i = e i
    have di_eq_ei : (d i : ℕ) = (e i : ℕ) := by
      calc (d i : ℕ)
        _ = (∑ j : Fin (k + 2), (d j : ℕ) * placeValue b j) / placeValue b i % b i := by
            exact (extract_from_sum d).symm
        _ = (∑ j : Fin (k + 2), (e j : ℕ) * placeValue b j) / placeValue b i % b i := by
            rw [h]
        _ = (e i : ℕ) := by
            exact extract_from_sum e

    exact di_eq_ei
/-! ## Proposition 1: Representation Theorem -/

theorem encodeFinite_digit (k : ℕ) (n : Fin (placeValue b (k + 1))) (i : Fin (k + 1)) :
    (encodeFinite b k n i : ℕ) = (n / placeValue b i) % b i := rfl

/-- dec_k ∘ enc_k = id -/
theorem decodeFinite_encodeFinite (k : ℕ) (n : Fin (placeValue b (k + 1))) :
    decodeFinite b k (encodeFinite b k n) = n := by
  unfold decodeFinite encodeFinite
  exact (sum_div_mod_placeValue k (n : ℕ) n.isLt).symm

/-- enc_k ∘ dec_k = id -/
theorem encodeFinite_decodeFinite (k : ℕ) (τ : FiniteRadixSpace b k) :
    encodeFinite b k ⟨decodeFinite b k τ, decodeFinite_lt k τ⟩ = τ := by
  apply digits_unique
  simp only [decodeFinite]
  have := decodeFinite_encodeFinite k ⟨decodeFinite b k τ, decodeFinite_lt k τ⟩
  simp only [decodeFinite] at this
  exact this

theorem decodeFinite_injective (k : ℕ) : Function.Injective (decodeFinite b k) := by
  intro τ σ h
  have hτ := encodeFinite_decodeFinite k τ
  have hσ := encodeFinite_decodeFinite k σ
  rw [← hτ, ← hσ]
  congr 1
  exact Fin.ext h

theorem decodeFinite_surjective (k : ℕ) :
    ∀ n : Fin (placeValue b (k + 1)), ∃ τ : FiniteRadixSpace b k, decodeFinite b k τ = n := by
  intro n
  exact ⟨encodeFinite b k n, decodeFinite_encodeFinite k n⟩

/-- **Proposition 1**: R^(k) ≃ Fin B_{k+1} -/
def finiteRadixEquiv (b : RadixSeq) (k : ℕ) : FiniteRadixSpace b k ≃ Fin (placeValue b (k + 1)) where
  toFun := fun τ => ⟨decodeFinite b k τ, decodeFinite_lt k τ⟩
  invFun := encodeFinite b k
  left_inv := encodeFinite_decodeFinite k
  right_inv := fun n => Fin.ext (decodeFinite_encodeFinite k n)

/-! ## Properties -/

@[simp]
theorem decodeFinite_zero (k : ℕ) : decodeFinite b k (FiniteRadixSpace.zero b k) = 0 := by
  simp [decodeFinite, FiniteRadixSpace.zero]

theorem encodeFinite_zero (k : ℕ) (h : 0 < placeValue b (k + 1)) :
    encodeFinite b k ⟨0, h⟩ = FiniteRadixSpace.zero b k := by
  funext i
  simp [encodeFinite, FiniteRadixSpace.zero]

end FdrsFormal.Core.Finite
