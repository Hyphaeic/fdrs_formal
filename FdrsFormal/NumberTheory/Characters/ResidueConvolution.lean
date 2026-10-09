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

# The residue chart carries convolution (Phase 3 addendum, §1.13)

Corollary 33 says the residue chart turns the DFT of length `B_{k+1}` into the
Vilenkin transform of `∏ ℤ/b_i`. This file proves the convolution twin, and chains
it with §3.5: an integer product on a constant schedule is a Vilenkin convolution
read through the residue chart of any pairwise-coprime schedule long enough to hold
it — the first two reductions of OpenAI family 109.

- **Definition 219** (`vAdd`, `vSub`, `vConv`, `cycConv`): carry-free digitwise
  addition and subtraction on `𝓡^{(k)}`, Vilenkin convolution, and cyclic
  convolution of length `N`, over any commutative semiring.
- **Proposition 163** (`crtChart_add`, `crtChart_cycSub`): on every schedule, the
  residue chart sends `+` and cyclic `−` to digitwise `+` and `−`.
- **Theorem 132** (`cycConv_eq_vConv`): for pairwise-coprime radices, cyclic
  convolution of length `B_{k+1}` is Vilenkin convolution read through the residue
  chart.
- **Corollary 40** (`digitConv_eq_cycConv`): digit lists of length `k + 1`, padded to
  `N ≥ 2k + 1`, have digit convolution equal to cyclic convolution (no wrap).
- **Corollary 41** (`mul_eq_vConv`): the chain — `dec x · dec y` is the value of the
  Vilenkin convolution of the padded digit lists, read through the residue chart.

**Honest scope.** Classical (Agarwal–Cooley 1977, the CRT reduction of cyclic
convolution to multidimensional convolution; Kronecker substitution). The corpus
contributes the statements on its charts and the chain to Theorem 131. No cost is
claimed.
-/

import FdrsFormal.NumberTheory.Characters.GoodThomas
import FdrsFormal.Operations.Multiplication

namespace FdrsFormal.NumberTheory.Characters.MixedRadixFFT

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite
open FdrsFormal.Operations.Multiplication

variable {b : RadixSeq}

/-! ## Definition 219: carry-free arithmetic and the two convolutions -/

/-- Digitwise addition, `(τ + σ)_i = τ_i + σ_i mod b_i` — no carries.

**fdrs.md**: Definition 219 (Vilenkin and cyclic convolution). -/
def vAdd {k : ℕ} (τ σ : FiniteRadixSpace b k) : FiniteRadixSpace b k :=
  fun i => ⟨((τ i : ℕ) + σ i) % b i, Nat.mod_lt _ (b.pos i)⟩

/-- Digitwise subtraction, `(τ − σ)_i = τ_i − σ_i mod b_i`. -/
def vSub {k : ℕ} (τ σ : FiniteRadixSpace b k) : FiniteRadixSpace b k :=
  fun i => ⟨((τ i : ℕ) + b i - σ i) % b i, Nat.mod_lt _ (b.pos i)⟩

/-- Convolution on the carry-free group `∏ ℤ/b_i`:
`(F ∗ G)(τ) = Σ_σ F(σ) G(τ − σ)`.

**fdrs.md**: Definition 219 (Vilenkin and cyclic convolution). -/
def vConv {R : Type*} [CommSemiring R] {k : ℕ} (F G : FiniteRadixSpace b k → R)
    (τ : FiniteRadixSpace b k) : R :=
  ∑ σ : FiniteRadixSpace b k, F σ * G (vSub τ σ)

/-- Cyclic convolution of length `N` on `ℕ`-indexed sequences:
`Σ_{m<N} f_m g_{(n − m) mod N}`. -/
def cycConv {R : Type*} [CommSemiring R] (N : ℕ) (f g : ℕ → R) (n : ℕ) : R :=
  ∑ m ∈ Finset.range N, f m * g ((n + N - m) % N)

/-! ## Proposition 163: the residue chart is additive -/

/-- **Proposition 163 (the residue chart is additive).** On every schedule,
`(n + m) mod b_i = (n mod b_i + m mod b_i) mod b_i`.

**fdrs.md**: Proposition 163 (the residue chart is additive). -/
theorem crtChart_add (k n m : ℕ) :
    crtChart b k (n + m) = vAdd (crtChart b k n) (crtChart b k m) := by
  funext i
  exact Fin.ext (by simp [crtChart, vAdd, Nat.add_mod])

/-- **Proposition 163 (cyclic subtraction).** With `N = B_{k+1}` and `m ≤ n + N`, the
residues of `(n − m) mod N` are the digitwise differences of the residues.

**fdrs.md**: Proposition 163 (the residue chart is additive). -/
theorem crtChart_cycSub (k n m : ℕ) (hm : m ≤ n + placeValue b (k + 1)) :
    crtChart b k ((n + placeValue b (k + 1) - m) % placeValue b (k + 1)) =
      vSub (crtChart b k n) (crtChart b k m) := by
  funext i
  apply Fin.ext
  simp only [crtChart, vSub]
  have hdvd : b i ∣ placeValue b (k + 1) := ⟨coBlock b k i, (mul_coBlock k i).symm⟩
  rw [Nat.mod_mod_of_dvd _ hdvd]
  rw [← ZMod.natCast_eq_natCast_iff', Nat.cast_sub hm,
    Nat.cast_sub (show m % b i ≤ n % b i + b i by have := Nat.mod_lt m (b.pos i); omega)]
  push_cast [ZMod.natCast_mod]
  have h0 : ((placeValue b (k + 1) : ℕ) : ZMod (b i)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  rw [h0, ZMod.natCast_self]

/-! ## Theorem 132: cyclic convolution is Vilenkin convolution -/

/-- **Theorem 132 (the residue chart carries convolution).** For pairwise-coprime
radices and `N = B_{k+1}`, read inputs through the inverse residue chart
`e⁻¹ : ∏ ℤ/b_i → ℤ/N`. Then cyclic convolution of length `N` at `n` is Vilenkin
convolution at the residues of `n`:
`Σ_{m<N} f_m g_{(n−m) mod N} = Σ_σ f(e⁻¹σ) g(e⁻¹(ρ(n) − σ))`.

**fdrs.md**: Theorem 132 (the residue chart carries convolution). -/
theorem cycConv_eq_vConv {R : Type*} [CommSemiring R] (k : ℕ)
    (h : PairwiseCoprimeRadices b k) (f g : ℕ → R) (n : ℕ) :
    cycConv (placeValue b (k + 1)) f g n =
      vConv (fun σ => f ((Equiv.ofBijective _ ((crtChart_bijective_iff k).mpr h)).symm σ))
        (fun σ => g ((Equiv.ofBijective _ ((crtChart_bijective_iff k).mpr h)).symm σ))
        (crtChart b k n) := by
  set N := placeValue b (k + 1)
  set e := Equiv.ofBijective _ ((crtChart_bijective_iff (b := b) k).mpr h)
  rw [cycConv, Finset.sum_range (fun m => f m * g ((n + N - m) % N)), vConv]
  refine Fintype.sum_equiv e _ _ fun m => ?_
  have hsub : vSub (crtChart b k n) (e m) =
      e ⟨(n + N - m) % N, Nat.mod_lt _ (placeValue.pos _)⟩ := by
    show _ = crtChart b k ((n + N - m) % N)
    rw [crtChart_cycSub k n m (by have := m.isLt; omega)]
    rfl
  rw [Equiv.symm_apply_apply, hsub, Equiv.symm_apply_apply]

/-! ## Corollaries 40–41: the multiplication chain -/

/-- **Corollary 40 (padding removes the wrap).** Digit lists supported on
`0, …, k`, padded to length `N ≥ 2k + 1`: their digit convolution equals their cyclic
convolution of length `N` at every `m < N`.

**fdrs.md**: Corollary 40 (padding removes the wrap). -/
theorem digitConv_eq_cycConv {k N : ℕ} (hN : 2 * k + 1 ≤ N) (x y : ℕ → ℕ)
    (hx : ∀ i, k < i → x i = 0) (hy : ∀ i, k < i → y i = 0) {m : ℕ} (hm : m < N) :
    digitConv x y m = cycConv N x y m := by
  rw [digitConv, cycConv]
  symm
  rw [← Finset.sum_subset (Finset.range_mono (show m + 1 ≤ N by omega))]
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ m := by simp at hi; omega
    rw [show m + N - i = (m - i) + N by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · intro i hi him
    have hiN : i < N := by simpa using hi
    have hmi : m < i := by simp at him; omega
    by_cases hik : i ≤ k
    · rw [Nat.mod_eq_of_lt (by omega), hy _ (by omega), mul_zero]
    · rw [hx i (by omega), zero_mul]

/-- **Corollary 41 (the multiplication chain).** Let the digit schedule `b` be
constant and the residue schedule `c` pairwise coprime on `0, …, K` with
`C_{K+1} ≥ 2k + 1`. For `x, y ∈ 𝓡_b^{(k)}`, with `X = x̄ ∘ e⁻¹`, `Y = ȳ ∘ e⁻¹`
the padded digit lists read through the inverse residue chart of `c`:
`dec x · dec y = Σ_{m ≤ 2k} (X ∗ Y)(ρ_c(m)) · B_m`.

**fdrs.md**: Corollary 41 (the multiplication chain). -/
theorem mul_eq_vConv {c : RadixSeq} {k K : ℕ} (hb : ∀ i, b i = b 0)
    (hc : PairwiseCoprimeRadices c K) (hN : 2 * k + 1 ≤ placeValue c (K + 1))
    (x y : FiniteRadixSpace b k) :
    decodeFinite b k x * decodeFinite b k y =
      digitVal b (fun m =>
        vConv (fun σ => digitsOf x ((Equiv.ofBijective _ ((crtChart_bijective_iff K).mpr hc)).symm σ))
          (fun σ => digitsOf y ((Equiv.ofBijective _ ((crtChart_bijective_iff K).mpr hc)).symm σ))
          (crtChart c K m)) (2 * k + 1) := by
  rw [← digitVal_conv hb x y, digitVal, digitVal]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : m < placeValue c (K + 1) := by simp at hm; omega
  rw [digitConv_eq_cycConv hN _ _ (fun _ h => digitsOf_eq_zero x h)
    (fun _ h => digitsOf_eq_zero y h) hm', cycConv_eq_vConv K hc]

end FdrsFormal.NumberTheory.Characters.MixedRadixFFT
