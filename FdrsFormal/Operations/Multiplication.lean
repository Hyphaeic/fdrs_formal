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

# Multiplication as digit convolution (Phase 1 addendum, §3.5)

Integer multiplication reduces to convolution of digit lists followed by carry
propagation — the first step of every fast multiplication algorithm (OpenAI family
109 starts here). On a mixed-radix schedule this reduction is not automatic: it
needs the place values to be multiplicative. This file proves exactly when it holds.

- **Proposition 162** (`placeValue_mul_iff`, `placeValue_mul_iff_local`):
  `B_i · B_j = B_{i+j}` for all `i, j` iff the schedule is constant; for `i, j ≤ k`
  iff `b_l = b_0` for every `l < 2k`.
- **Definition 218** (`digitConv`, `digitVal`, `carryStep`, `carrySweep`,
  `digitsOf`): digit convolution, the value of an unbounded digit list, and the
  carry sweep for an arbitrary schedule.
- **Theorem 131** (`digitVal_conv`, `mul_eq_carrySweep`): on a constant schedule the
  digit convolution has value `dec x · dec y`, and its carry sweep is the canonical
  digit vector of the product.
- **Corollary 39** (`conv_correct_iff`): on `𝓡^{(k)}`, digit convolution computes
  the product for all inputs iff `b_l = b_0` for every `l < 2k` — the boundary of the
  reduction on a variable schedule.

**Honest scope.** Classical (positional multiplication; Kronecker substitution).
The corpus contributes the statement on mixed-radix schedules and its sharp
boundary. Nothing about the cost of multiplication is claimed here.
-/

import FdrsFormal.Core.Finite

namespace FdrsFormal.Operations.Multiplication

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite

variable {b : RadixSeq}

/-! ## Proposition 162: multiplicative place values -/

theorem placeValue_eq_pow_of_const {n : ℕ} (h : ∀ l < n, b l = b 0) :
    ∀ m ≤ n, placeValue b m = b 0 ^ m := by
  intro m hm
  induction m with
  | zero => simp
  | succ m ih => rw [placeValue.succ, ih (by omega), h m (by omega), pow_succ]

theorem placeValue_mul_of_const {n : ℕ} (h : ∀ l < n, b l = b 0) {i j : ℕ}
    (hij : i + j ≤ n) : placeValue b i * placeValue b j = placeValue b (i + j) := by
  rw [placeValue_eq_pow_of_const h i (by omega), placeValue_eq_pow_of_const h j (by omega),
    placeValue_eq_pow_of_const h (i + j) hij, pow_add]

/-- **Proposition 162 (local form).** The place values of the first `k + 1` digits
multiply like powers, `B_i B_j = B_{i+j}` for `i, j ≤ k`, iff the radices below `2k`
all equal `b_0`.

**fdrs.md**: Proposition 162 (multiplicative place values). -/
theorem placeValue_mul_iff_local (k : ℕ) :
    (∀ i j, i ≤ k → j ≤ k → placeValue b i * placeValue b j = placeValue b (i + j)) ↔
      ∀ l < 2 * k, b l = b 0 := by
  constructor
  · intro hB
    have hlow : ∀ l, l < k → b l = b 0 := by
      intro l hl
      have h1 := hB 1 l (by omega) hl.le
      rw [show 1 + l = l + 1 by ring, placeValue.succ l, placeValue.succ 0, placeValue.zero,
        one_mul] at h1
      have h2 : placeValue b l * b l = placeValue b l * b 0 := by rw [← h1]; ring
      exact Nat.eq_of_mul_eq_mul_left (placeValue.pos l) h2
    intro l hl
    by_cases hlk : l < k
    · exact hlow l hlk
    · have hj : l - k < k := by omega
      have hA := hB k (l - k + 1) le_rfl (by omega)
      have hA' := hB k (l - k) le_rfl (by omega)
      have e1 : k + (l - k + 1) = (k + (l - k)) + 1 := by omega
      have e2 : k + (l - k) = l := by omega
      rw [e1, placeValue.succ (l - k), placeValue.succ (k + (l - k)), e2, hlow _ hj] at hA
      rw [e2] at hA'
      have h2 : placeValue b l * b l = placeValue b l * b 0 := by
        rw [← hA, ← hA']; ring
      exact Nat.eq_of_mul_eq_mul_left (placeValue.pos l) h2
  · intro h i j hi hj
    exact placeValue_mul_of_const h (by omega)

/-- **Proposition 162 (multiplicative place values).** `B_i · B_j = B_{i+j}` for all
`i, j` iff the schedule is constant.

**fdrs.md**: Proposition 162 (multiplicative place values). -/
theorem placeValue_mul_iff :
    (∀ i j, placeValue b i * placeValue b j = placeValue b (i + j)) ↔ ∀ i, b i = b 0 :=
  ⟨fun h l => (placeValue_mul_iff_local (l + 1)).mp (fun i j _ _ => h i j) l (by omega),
    fun h i j => placeValue_mul_of_const (n := i + j) (fun l _ => h l) le_rfl⟩

/-! ## Definition 218: digit convolution, value, carries -/

/-- Digit convolution `(x ⋆ y)_m = Σ_{i ≤ m} x_i y_{m−i}`.

**fdrs.md**: Definition 218 (digit convolution and the carry sweep). -/
def digitConv (x y : ℕ → ℕ) (m : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (m + 1), x i * y (m - i)

/-- The value of the first `n` entries of a digit list, digits unrestricted:
`Σ_{i<n} d_i B_i`. -/
def digitVal (b : RadixSeq) (d : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, d i * placeValue b i

/-- One carry at position `i`: keep `d_i mod b_i`, pass `⌊d_i / b_i⌋` to `i + 1`. -/
def carryStep (b : RadixSeq) (d : ℕ → ℕ) (i : ℕ) : ℕ → ℕ := fun j =>
  if j = i then d i % b i
  else if j = i + 1 then d (i + 1) + d i / b i
  else d j

/-- The carry sweep over positions `0, …, n − 1`. -/
def carrySweep (b : RadixSeq) (d : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0 => d
  | n + 1 => carryStep b (carrySweep b d n) n

/-- A digit vector of `𝓡^{(k)}`, extended by zeros. -/
def digitsOf {k : ℕ} (x : FiniteRadixSpace b k) : ℕ → ℕ := fun n =>
  if h : n < k + 1 then (x ⟨n, h⟩ : ℕ) else 0

theorem digitsOf_eq_zero {k : ℕ} (x : FiniteRadixSpace b k) {n : ℕ} (hn : k < n) :
    digitsOf x n = 0 := by
  simp [digitsOf, show ¬ n < k + 1 by omega]

theorem digitVal_digitsOf {k : ℕ} (x : FiniteRadixSpace b k) :
    digitVal b (digitsOf x) (k + 1) = decodeFinite b k x := by
  rw [digitVal, decodeFinite,
    ← Fin.sum_univ_eq_sum_range (fun i => digitsOf x i * placeValue b i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [digitsOf, i.isLt]

/-! ## Carries preserve value -/

theorem carryStep_val (d : ℕ → ℕ) {i N : ℕ} (h : i + 1 < N) :
    digitVal b (carryStep b d i) N = digitVal b d N := by
  obtain ⟨r, rfl⟩ : ∃ r, N = i + 2 + r := ⟨N - (i + 2), by omega⟩
  have split : ∀ f : ℕ → ℕ, ∑ x ∈ Finset.range (i + 2 + r), f x =
      ∑ x ∈ Finset.range i, f x + f i + f (i + 1) + ∑ x ∈ Finset.range r, f (i + 2 + x) := by
    intro f
    rw [Finset.sum_range_add, show i + 2 = i + 1 + 1 from rfl, Finset.sum_range_succ,
      Finset.sum_range_succ]
  simp only [digitVal]
  rw [split, split]
  have hlow : ∑ x ∈ Finset.range i, carryStep b d i x * placeValue b x =
      ∑ x ∈ Finset.range i, d x * placeValue b x :=
    Finset.sum_congr rfl fun x hx => by
      have : x < i := Finset.mem_range.mp hx
      simp [carryStep, show x ≠ i by omega, show x ≠ i + 1 by omega]
  have hhigh : ∑ x ∈ Finset.range r, carryStep b d i (i + 2 + x) * placeValue b (i + 2 + x) =
      ∑ x ∈ Finset.range r, d (i + 2 + x) * placeValue b (i + 2 + x) :=
    Finset.sum_congr rfl fun x _ => by
      simp [carryStep, show i + 2 + x ≠ i by omega, show i + 2 + x ≠ i + 1 by omega]
  have hi : carryStep b d i i = d i % b i := by simp [carryStep]
  have hi1 : carryStep b d i (i + 1) = d (i + 1) + d i / b i := by simp [carryStep]
  rw [hlow, hhigh, hi, hi1, placeValue.succ i]
  have hmid : d i % b i * placeValue b i + (d (i + 1) + d i / b i) * (placeValue b i * b i) =
      d i * placeValue b i + d (i + 1) * (placeValue b i * b i) := by
    calc d i % b i * placeValue b i + (d (i + 1) + d i / b i) * (placeValue b i * b i)
        = (b i * (d i / b i) + d i % b i) * placeValue b i +
            d (i + 1) * (placeValue b i * b i) := by ring
      _ = _ := by rw [Nat.div_add_mod]
  omega

theorem carrySweep_spec (d : ℕ → ℕ) : ∀ n,
    (∀ j, n < j → carrySweep b d n j = d j) ∧
    (∀ j < n, carrySweep b d n j < b j) ∧
    (∀ N, n < N → digitVal b (carrySweep b d n) N = digitVal b d N)
  | 0 => ⟨fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl⟩
  | n + 1 => by
    obtain ⟨h1, h2, h3⟩ := carrySweep_spec d n
    refine ⟨fun j hj => ?_, fun j hj => ?_, fun N hN => ?_⟩
    · simp only [carrySweep, carryStep, show j ≠ n by omega, show j ≠ n + 1 by omega,
        if_false]
      exact h1 j (by omega)
    · simp only [carrySweep, carryStep]
      by_cases hjn : j = n
      · subst hjn; simp [Nat.mod_lt _ (b.pos j)]
      · simp only [hjn, show j ≠ n + 1 by omega, if_false]
        exact h2 j (by omega)
    · simp only [carrySweep]
      rw [carryStep_val _ hN, h3 N (by omega)]

/-! ## Theorem 131: convolution plus carries is the product -/

/-- The value identity behind Theorem 131, under the local hypothesis of
Proposition 162. -/
theorem digitVal_conv_of_mul {k : ℕ}
    (hB : ∀ i j, i ≤ k → j ≤ k → placeValue b i * placeValue b j = placeValue b (i + j))
    (x y : ℕ → ℕ) (hx : ∀ i, k < i → x i = 0) (hy : ∀ i, k < i → y i = 0) :
    digitVal b (digitConv x y) (2 * k + 1) = digitVal b x (k + 1) * digitVal b y (k + 1) := by
  set F : ℕ → ℕ → ℕ := fun i j => x i * y j * placeValue b (i + j)
  -- the right side as a double sum of `F`
  have hR : digitVal b x (k + 1) * digitVal b y (k + 1) =
      ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1), F i j := by
    rw [digitVal, digitVal, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    have hi' : i ≤ k := by simp at hi; omega
    have hj' : j ≤ k := by simp at hj; omega
    simp only [F, ← hB i j hi' hj']; ring
  -- the left side, re-indexed by `(i, j = m − i)`
  have hL : digitVal b (digitConv x y) (2 * k + 1) =
      ∑ i ∈ Finset.range (2 * k + 1), ∑ j ∈ Finset.range (2 * k + 1 - i), F i j := by
    have step1 : digitVal b (digitConv x y) (2 * k + 1) =
        ∑ m ∈ Finset.range (2 * k + 1), ∑ i ∈ Finset.range (m + 1), F i (m - i) := by
      rw [digitVal]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [digitConv, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      have : i + (m - i) = m := by simp at hi; omega
      simp only [F, this]
    rw [step1, Finset.sum_comm' (t' := Finset.range (2 * k + 1))
      (s' := fun i => Finset.Ico i (2 * k + 1))]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Nat.add_sub_cancel_left]
    · intro m i
      simp only [Finset.mem_range, Finset.mem_Ico]
      omega
  rw [hL, hR]
  symm
  calc ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1), F i j
      = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (2 * k + 1 - i), F i j := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi' : i ≤ k := by simp at hi; omega
        apply Finset.sum_subset (Finset.range_mono (by omega))
        intro j _ hjk
        have : k < j := by simp at hjk; omega
        simp [F, hy j this]
    _ = _ := by
        apply Finset.sum_subset (Finset.range_mono (by omega))
        intro i _ hik
        have : k < i := by simp at hik; omega
        exact Finset.sum_eq_zero fun j _ => by simp [F, hx i this]

theorem digitConv_eq_zero {k : ℕ} (x y : ℕ → ℕ) (hx : ∀ i, k < i → x i = 0)
    (hy : ∀ i, k < i → y i = 0) {m : ℕ} (hm : 2 * k < m) : digitConv x y m = 0 := by
  refine Finset.sum_eq_zero fun i hi => ?_
  by_cases hik : i ≤ k
  · rw [hy (m - i) (by simp at hi; omega), mul_zero]
  · rw [hx i (by omega), zero_mul]

/-- **Theorem 131 (value).** On a constant schedule, the digit convolution of
`x, y ∈ 𝓡^{(k)}` has value `dec x · dec y`.

**fdrs.md**: Theorem 131 (multiplication is digit convolution plus carries). -/
theorem digitVal_conv {k : ℕ} (hb : ∀ i, b i = b 0) (x y : FiniteRadixSpace b k) :
    digitVal b (digitConv (digitsOf x) (digitsOf y)) (2 * k + 1) =
      decodeFinite b k x * decodeFinite b k y := by
  rw [← digitVal_digitsOf x, ← digitVal_digitsOf y]
  exact digitVal_conv_of_mul ((placeValue_mul_iff_local k).mpr fun l _ => hb l) _ _
    (fun _ h => digitsOf_eq_zero x h) (fun _ h => digitsOf_eq_zero y h)

/-- **Theorem 131 (multiplication is digit convolution plus carries).** On a constant
schedule, sweeping the carries of the digit convolution of `x, y ∈ 𝓡^{(k)}` over
positions `0, …, 2k` yields exactly the digits of `dec x · dec y` in `𝓡^{(2k+1)}`.

**fdrs.md**: Theorem 131 (multiplication is digit convolution plus carries). -/
theorem mul_eq_carrySweep {k : ℕ} (hb : ∀ i, b i = b 0) (x y : FiniteRadixSpace b k) :
    ∃ hlt : decodeFinite b k x * decodeFinite b k y < placeValue b (2 * k + 2),
      ∀ i : Fin (2 * k + 2),
        carrySweep b (digitConv (digitsOf x) (digitsOf y)) (2 * k + 1) i =
          (encodeFinite b (2 * k + 1) ⟨_, hlt⟩ i : ℕ) := by
  set d := digitConv (digitsOf x) (digitsOf y)
  set s := carrySweep b d (2 * k + 1)
  obtain ⟨_, hcan, hval⟩ := carrySweep_spec (b := b) d (2 * k + 1)
  have hd0 : d (2 * k + 1) = 0 := digitConv_eq_zero (k := k) _ _
    (fun _ h => digitsOf_eq_zero x h) (fun _ h => digitsOf_eq_zero y h) (by omega)
  have hprod : digitVal b s (2 * k + 2) = decodeFinite b k x * decodeFinite b k y := by
    rw [hval _ (by omega), show 2 * k + 2 = 2 * k + 1 + 1 by ring, digitVal,
      Finset.sum_range_succ, hd0, zero_mul, add_zero, ← digitVal, digitVal_conv hb]
  have hlt : decodeFinite b k x * decodeFinite b k y < placeValue b (2 * k + 2) := by
    have hsq : placeValue b (k + 1) * placeValue b (k + 1) = placeValue b (2 * k + 2) := by
      rw [placeValue_mul_of_const (n := 2 * k + 2) (fun l _ => hb l) (by omega)]
      ring_nf
    rw [← hsq]
    exact Nat.mul_lt_mul'' (decodeFinite_lt k x) (decodeFinite_lt k y)
  -- the top digit is canonical too
  have htop : s (2 * k + 1) < b (2 * k + 1) := by
    have hle : s (2 * k + 1) * placeValue b (2 * k + 1) ≤ digitVal b s (2 * k + 2) := by
      rw [show 2 * k + 2 = 2 * k + 1 + 1 by ring, digitVal, Finset.sum_range_succ]
      exact Nat.le_add_left _ _
    have : placeValue b (2 * k + 1) * s (2 * k + 1) <
        placeValue b (2 * k + 1) * b (2 * k + 1) := by
      rw [mul_comm, ← placeValue.succ]
      calc _ ≤ _ := hle
        _ = _ := hprod
        _ < _ := hlt
    exact Nat.lt_of_mul_lt_mul_left this
  have hdig : ∀ i : Fin (2 * k + 2), s i < b i := fun i => by
    rcases Nat.lt_or_ge (i : ℕ) (2 * k + 1) with h | h
    · exact hcan i h
    · have : (i : ℕ) = 2 * k + 1 := by omega
      rw [this]; exact htop
  set τ : FiniteRadixSpace b (2 * k + 1) := fun i => ⟨s i, hdig i⟩
  have hdec : decodeFinite b (2 * k + 1) τ = decodeFinite b k x * decodeFinite b k y := by
    rw [← hprod, decodeFinite, digitVal,
      ← Fin.sum_univ_eq_sum_range (fun i => s i * placeValue b i)]
  refine ⟨hlt, fun i => ?_⟩
  have hτ : encodeFinite b (2 * k + 1) ⟨_, hlt⟩ = τ := by
    rw [← encodeFinite_decodeFinite (2 * k + 1) τ]
    congr 1
    exact Fin.ext hdec.symm
  rw [hτ]

/-! ## Corollary 39: the variable-radix boundary -/

/-- The unit digit vector at position `i`. -/
def unitDigit (k i : ℕ) : FiniteRadixSpace b k := fun l =>
  if (l : ℕ) = i then ⟨1, lt_of_lt_of_le one_lt_two (b.ge_two l)⟩ else ⟨0, b.pos l⟩

theorem digitsOf_unitDigit {k i : ℕ} (hi : i ≤ k) :
    digitsOf (unitDigit (b := b) k i) = fun n => if n = i then 1 else 0 := by
  funext n
  unfold digitsOf unitDigit
  split_ifs with h1 h2 h3 <;> simp_all

theorem digitVal_indicator {i n : ℕ} (hi : i < n) :
    digitVal b (fun m => if m = i then 1 else 0) n = placeValue b i := by
  simp [digitVal, ite_mul, Finset.sum_ite_eq', hi]

theorem digitConv_indicator (i j : ℕ) :
    digitConv (fun n => if n = i then 1 else 0) (fun n => if n = j then 1 else 0) =
      fun m => if m = i + j then 1 else 0 := by
  funext m
  unfold digitConv
  by_cases hm : i ≤ m
  · rw [Finset.sum_eq_single i (fun a _ ha => by simp [ha])
      (fun h => absurd (Finset.mem_range.mpr (by omega)) h)]
    by_cases h : m = i + j
    · simp [h]
    · simp [h, show m - i ≠ j by omega]
  · rw [Finset.sum_eq_zero fun a ha => by
      have : a ≠ i := by simp at ha; omega
      simp [this]]
    simp [show m ≠ i + j by omega]

/-- **Corollary 39 (the variable-radix boundary).** On `𝓡^{(k)}`, digit convolution
computes the product for every pair of inputs iff `b_l = b_0` for every `l < 2k`.
Unit vectors reduce the converse to Proposition 162; e.g. `b = (2, 3, …)` already
fails at `k = 1`, since `B_1 B_1 = 4 ≠ 6 = B_2`.

**fdrs.md**: Corollary 39 (the variable-radix boundary). -/
theorem conv_correct_iff (k : ℕ) :
    (∀ x y : FiniteRadixSpace b k,
      digitVal b (digitConv (digitsOf x) (digitsOf y)) (2 * k + 1) =
        decodeFinite b k x * decodeFinite b k y) ↔
      ∀ l < 2 * k, b l = b 0 := by
  constructor
  · intro h
    refine (placeValue_mul_iff_local k).mp fun i j hi hj => ?_
    have hij := h (unitDigit k i) (unitDigit k j)
    rw [← digitVal_digitsOf, ← digitVal_digitsOf, digitsOf_unitDigit hi,
      digitsOf_unitDigit hj, digitConv_indicator, digitVal_indicator (by omega),
      digitVal_indicator (by omega), digitVal_indicator (by omega)] at hij
    exact hij.symm
  · intro h x y
    rw [← digitVal_digitsOf x, ← digitVal_digitsOf y]
    exact digitVal_conv_of_mul ((placeValue_mul_iff_local k).mpr h) _ _
      (fun _ h => digitsOf_eq_zero x h) (fun _ h => digitsOf_eq_zero y h)

/-- The schedule `(2, 3, 3, …)`. -/
def twoThree : RadixSeq :=
  ⟨fun i => if i = 0 then 2 else 3, fun i => by dsimp only; split_ifs <;> norm_num⟩

/-- The smallest failure: on `(2, 3, 3, …)`, `B_1 · B_1 = 4 ≠ 6 = B_2`. -/
example : placeValue twoThree 1 * placeValue twoThree 1 ≠ placeValue twoThree 2 := by
  decide

end FdrsFormal.Operations.Multiplication
