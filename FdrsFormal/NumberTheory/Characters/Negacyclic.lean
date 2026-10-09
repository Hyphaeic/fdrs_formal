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

# The negacyclic twist (Phase 3 addendum, §1.14)

Negacyclic convolution — products modulo `y^r + 1`, where the wrap-around enters
with a sign — is cyclic convolution after a diagonal twist by any `w` with
`w^r = −1`. Family 109 uses this to turn the last cyclic axis into a polynomial
ring `ℂ[y]/(y^r + 1)` whose roots of unity are signed shifts.

- **Definition 220** (`negConv`): negacyclic convolution of length `r`.
- **Proposition 164** (`negConv_twist`): over any commutative ring, if `w^r = −1`
  then `w^n · (f ⊛⁻ g)_n = ((w^· f) ⊛ (w^· g))_n` for `n < r`.
- **Corollary 42** (`negConv_twist_zeta`): the complex instance `w = ζ_{2r}`.

**Honest scope.** Classical (the weighted / "right-angle" convolution; Nussbaumer
1980). The corpus contributes the statement next to Theorem 132. No cost is claimed.
-/

import FdrsFormal.NumberTheory.Characters.ResidueConvolution
import FdrsFormal.NumberTheory.Characters.CircuitCompose

namespace FdrsFormal.NumberTheory.Characters.MixedRadixFFT

open FdrsFormal.NumberTheory.Characters.FourierCircuit

/-- **Definition 220 (negacyclic convolution).** Length `r`: terms that wrap past
`r` enter with a minus sign, `(f ⊛⁻ g)_n = Σ_{m ≤ n} f_m g_{n−m} − Σ_{m > n} f_m g_{n+r−m}`.

**fdrs.md**: Definition 220 (negacyclic convolution). -/
def negConv {R : Type*} [CommRing R] (r : ℕ) (f g : ℕ → R) (n : ℕ) : R :=
  ∑ m ∈ Finset.range r, if m ≤ n then f m * g (n - m) else -(f m * g (n + r - m))

/-- **Proposition 164 (the negacyclic twist).** If `w^r = −1`, twisting both inputs
by `w^m` turns negacyclic convolution into cyclic convolution:
`w^n · (f ⊛⁻ g)_n = ((w^· f) ⊛_r (w^· g))_n` for every `n < r`.

**fdrs.md**: Proposition 164 (the negacyclic twist). -/
theorem negConv_twist {R : Type*} [CommRing R] (r : ℕ) (w : R) (hw : w ^ r = -1)
    (f g : ℕ → R) {n : ℕ} (hn : n < r) :
    w ^ n * negConv r f g n =
      cycConv r (fun m => w ^ m * f m) (fun m => w ^ m * g m) n := by
  rw [negConv, cycConv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : m < r := Finset.mem_range.mp hm
  split_ifs with hmn
  · rw [show n + r - m = (n - m) + r by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have : w ^ m * w ^ (n - m) = w ^ n := by rw [← pow_add]; congr 1; omega
    rw [← this]; ring
  · rw [Nat.mod_eq_of_lt (by omega)]
    have : w ^ m * w ^ (n + r - m) = -w ^ n := by
      rw [← pow_add, show m + (n + r - m) = n + r by omega, pow_add, hw]; ring
    rw [show w ^ m * f m * (w ^ (n + r - m) * g (n + r - m)) =
      (w ^ m * w ^ (n + r - m)) * (f m * g (n + r - m)) by ring, this]
    ring

/-- `ζ_{2r}^r = −1`. -/
theorem zeta_two_mul_pow (r : ℕ) (hr : r ≠ 0) : zeta (2 * r) ^ r = -1 := by
  have := zeta_mul_pow_mul 2 r 1 (by norm_num) hr
  rw [mul_one, pow_one, zeta_two'] at this
  exact this

/-- **Corollary 42 (the complex twist).** With `w = ζ_{2r}`, negacyclic convolution
of length `r` is a twisted cyclic convolution of length `r`.

**fdrs.md**: Corollary 42 (the complex twist). -/
theorem negConv_twist_zeta (r : ℕ) (hr : r ≠ 0) (f g : ℕ → ℂ) {n : ℕ} (hn : n < r) :
    zeta (2 * r) ^ n * negConv r f g n =
      cycConv r (fun m => zeta (2 * r) ^ m * f m) (fun m => zeta (2 * r) ^ m * g m) n :=
  negConv_twist r _ (zeta_two_mul_pow r hr) f g hn

end FdrsFormal.NumberTheory.Characters.MixedRadixFFT
