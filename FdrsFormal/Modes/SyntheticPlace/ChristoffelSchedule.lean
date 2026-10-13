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

# Product defects of limb schedules, and why radix 2^25.5 (Phase 1 addendum, §3.23)

A power-of-two limb schedule for arithmetic modulo `2^q − c` with `N` limbs is a sequence of
bit positions `W_0 = 0 < W_1 < … ` with `W_{k+N} = W_k + q` (the lap). The product of limbs
`m` and `j` has weight `2^{W_m + W_j}`, which lands at place `m + j` with product coefficient
`κ(m, j) = 2^{d(m, j)}`, where the **defect** is `d(m, j) = W_m + W_j − W_{m+j}` (§3.13). The
schedule is product-closed iff every defect is `≥ 0`.

- **Defect bounds** (Theorem 174): if every defect lies in `[0, δ]`, then
  `q·a ≤ N·W_a ≤ q·a + (N − 1)·δ` for every `a`. In particular every product-closed schedule
  lies above the ceiling schedule: `W_a ≥ ⌈q a / N⌉`.
- **Christoffel optimality** (Theorem 175): the schedules whose product coefficients are all
  `1` or `2` (defects in `{0, 1}`) are exactly one: the **ceiling schedule**
  `W_a = ⌈q a / N⌉`. Its limb widths are the balanced (Christoffel) word of slope `q / N`.
- **Why radix 2^25.5** (Corollary 60): the 25519 schedule `W_k = ⌈25.5 k⌉` (widths
  `26, 25, 26, …`) is the ceiling schedule for `q = 255`, `N = 10`; hence it is the *unique*
  ten-limb schedule of `2^255` whose schoolbook products need at most a doubling — the
  familiar gains `2` and `38` are forced, not chosen.

The proof is three lines of arithmetic: periodicity pins `W_{N a} = q a`; non-negative
defects give `W_{N a} ≤ N W_a`; defects at most `δ` give `W_{N a} ≥ N W_a − (N − 1) δ`.
Bounds for indices below `N` extend to all indices by periodicity (`defect_mod`).

Reuses the 25519 weight ladder (`Field25519Carry.lean`) and its defect table
(`MixedRingProduct.lean`, `weightBits_add`).

- **Definition 245** (`IsSchedule`, `defect`, `ceilSched`): schedules and their defects.
- **Theorem 174** (`defect_mod`, `defect_bounds`, `above_ceiling`): the defect bounds.
- **Theorem 175** (`ceilSched_isSchedule`, `ceilSched_defect`, `christoffel_unique`): the
  ceiling schedule is the unique schedule with all product coefficients in `{1, 2}`.
- **Corollary 60** (`weightBits_period`, `weightBits_eq_ceil`, `radix_25_5_unique`): why
  radix `2^25.5`.

**Honest scope.** The ceiling schedule is classical (Crandall–Fagin 1994; Bernstein 2006;
fiat-crypto); balanced/Christoffel words are classical (Morse–Hedlund; Berstel et al.). The
characterization of the ceiling schedule as the unique schedule with product coefficients at
most `2`, and the pointwise lower bound for all product-closed schedules, were not found in
the literature surveyed for this project (see `reports/Carry theory novelty survey.md`);
they are elementary.
-/

import FdrsFormal.Modes.SyntheticPlace.MixedRingProduct

namespace FdrsFormal.Modes.SyntheticPlace.ChristoffelSchedule

/-! ## Definition 245: schedules and defects -/

/-- A limb schedule of `2^q` with `N` limbs: bit positions with `W_0 = 0` and lap `q`.

**fdrs.md**: Definition 245 (limb schedules and their defects). -/
def IsSchedule (N q : ℕ) (W : ℕ → ℤ) : Prop := W 0 = 0 ∧ ∀ k, W (k + N) = W k + q

/-- The defect of a product of limbs `a` and `b`: `κ(a, b) = 2^{defect}`.

**fdrs.md**: Definition 245 (limb schedules and their defects). -/
def defect (W : ℕ → ℤ) (a b : ℕ) : ℤ := W a + W b - W (a + b)

/-- The ceiling schedule `W_a = ⌈q a / N⌉`.

**fdrs.md**: Definition 245 (limb schedules and their defects). -/
noncomputable def ceilSched (N q : ℕ) (a : ℕ) : ℤ := ⌈((q * a : ℕ) : ℚ) / N⌉

section Bounds

variable {N q : ℕ} {W : ℕ → ℤ}

theorem period_mul (hW : IsSchedule N q W) : ∀ a, W (N * a) = q * a
  | 0 => by simpa using hW.1
  | a + 1 => by
    rw [show N * (a + 1) = N * a + N by ring, hW.2, period_mul hW a]; push_cast; ring

theorem period_decomp (hW : IsSchedule N q W) (r : ℕ) : ∀ t, W (r + N * t) = W r + q * t
  | 0 => by simp
  | t + 1 => by
    rw [show r + N * (t + 1) = (r + N * t) + N by ring, hW.2, period_decomp hW r t]
    push_cast; ring

/-- **Theorem 174 (defects are periodic).** Defects depend only on the indices modulo `N`, so
bounds checked on `a, b < N` hold everywhere.

**fdrs.md**: Theorem 174 (defect bounds). -/
theorem defect_mod (hW : IsSchedule N q W) (a b : ℕ) :
    defect W a b = defect W (a % N) (b % N) := by
  have ha := period_decomp hW (a % N) (a / N)
  have hb := period_decomp hW (b % N) (b / N)
  have hab := period_decomp hW (a % N + b % N) (a / N + b / N)
  rw [Nat.mod_add_div] at ha hb
  rw [show a % N + b % N + N * (a / N + b / N) = a + b by
    have h1 := Nat.mod_add_div a N; have h2 := Nat.mod_add_div b N; linarith] at hab
  simp only [defect]
  rw [ha, hb, hab]; push_cast; ring

theorem iter_upper (hlo : ∀ a b, 0 ≤ defect W a b) (h0 : W 0 = 0) (a : ℕ) :
    ∀ n : ℕ, W (n * a) ≤ n * W a
  | 0 => by simp [h0]
  | n + 1 => by
    have h := hlo (n * a) a
    have ih := iter_upper hlo h0 a n
    simp only [defect] at h
    rw [show (n + 1) * a = n * a + a by ring]; push_cast; linarith

theorem iter_lower {δ : ℤ} (hhi : ∀ a b, defect W a b ≤ δ) (a : ℕ) :
    ∀ n : ℕ, (n + 1) * W a - n * δ ≤ W ((n + 1) * a)
  | 0 => by simp
  | n + 1 => by
    have h := hhi ((n + 1) * a) a
    have ih := iter_lower hhi a n
    simp only [defect] at h
    rw [show (n + 1 + 1) * a = (n + 1) * a + a by ring]; push_cast at ih ⊢; linarith

/-- Non-negative defects: `q a ≤ N W_a`. -/
theorem lower_bound (hW : IsSchedule N q W) (hlo : ∀ a b, 0 ≤ defect W a b) (a : ℕ) :
    (q : ℤ) * a ≤ N * W a := by
  have hp := period_mul hW a
  have h := iter_upper hlo hW.1 a N
  rw [hp] at h
  exact h

/-- Defects at most `δ`: `N W_a ≤ q a + (N − 1) δ`. -/
theorem upper_bound (hN : 0 < N) (hW : IsSchedule N q W) {δ : ℤ}
    (hhi : ∀ a b, defect W a b ≤ δ) (a : ℕ) : (N : ℤ) * W a ≤ q * a + (N - 1) * δ := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hp := period_mul hW a
  have h := iter_lower hhi a M
  rw [hp] at h
  push_cast at h ⊢
  linarith

/-- **Theorem 174 (the defect bounds).** If every defect lies in `[0, δ]`, then
`q a ≤ N W_a ≤ q a + (N − 1) δ`.

**fdrs.md**: Theorem 174 (defect bounds). -/
theorem defect_bounds (hN : 0 < N) (hW : IsSchedule N q W) {δ : ℤ}
    (hlo : ∀ a b, 0 ≤ defect W a b) (hhi : ∀ a b, defect W a b ≤ δ) (a : ℕ) :
    (q : ℤ) * a ≤ N * W a ∧ (N : ℤ) * W a ≤ q * a + (N - 1) * δ :=
  ⟨lower_bound hW hlo a, upper_bound hN hW hhi a⟩

/-- **Theorem 174 (every product-closed schedule lies above the ceiling schedule).**

**fdrs.md**: Theorem 174 (defect bounds). -/
theorem above_ceiling (hN : 0 < N) (hW : IsSchedule N q W) (hlo : ∀ a b, 0 ≤ defect W a b)
    (a : ℕ) : ceilSched N q a ≤ W a := by
  have h := lower_bound hW hlo a
  rw [ceilSched, Int.ceil_le, div_le_iff₀ (by exact_mod_cast hN)]
  have : ((q * a : ℕ) : ℤ) ≤ W a * N := by push_cast; linarith
  exact_mod_cast this

end Bounds

/-! ## Theorem 175: Christoffel optimality -/

section Christoffel

variable {N q : ℕ}

/-- The ceiling schedule is a schedule. -/
theorem ceilSched_isSchedule (hN : 0 < N) : IsSchedule N q (ceilSched N q) := by
  refine ⟨by simp [ceilSched], fun k => ?_⟩
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [ceilSched, ceilSched, show ((q * (k + N) : ℕ) : ℚ) / N = ((q * k : ℕ) : ℚ) / N + (q : ℤ) by
    push_cast; field_simp, Int.ceil_add_intCast]

/-- The ceiling schedule's defects are `0` or `1`. -/
theorem ceilSched_defect (a b : ℕ) :
    0 ≤ defect (ceilSched N q) a b ∧ defect (ceilSched N q) a b ≤ 1 := by
  have hsplit : ((q * (a + b) : ℕ) : ℚ) / N = ((q * a : ℕ) : ℚ) / N + ((q * b : ℕ) : ℚ) / N := by
    push_cast; ring
  simp only [defect, ceilSched, hsplit]
  exact ⟨by linarith [Int.ceil_add_le (((q * a : ℕ) : ℚ) / N) (((q * b : ℕ) : ℚ) / N)],
    by linarith [Int.ceil_add_ceil_le (((q * a : ℕ) : ℚ) / N) (((q * b : ℕ) : ℚ) / N)]⟩

/-- **Theorem 175 (Christoffel optimality).** A schedule all of whose product coefficients are
`1` or `2` (defects in `{0, 1}`) is the ceiling schedule; and the ceiling schedule has this
property.

**fdrs.md**: Theorem 175 (Christoffel optimality). -/
theorem christoffel_unique (hN : 0 < N) {W : ℕ → ℤ} (hW : IsSchedule N q W)
    (hlo : ∀ a b, 0 ≤ defect W a b) (hhi : ∀ a b, defect W a b ≤ 1) : W = ceilSched N q := by
  funext a
  obtain ⟨h1, h2⟩ := defect_bounds hN hW hlo hhi a
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  symm
  rw [ceilSched, Int.ceil_eq_iff]
  constructor
  · rw [lt_div_iff₀ hNq]
    have : ((W a - 1) : ℤ) * N < ((q * a : ℕ) : ℤ) := by push_cast; nlinarith
    exact_mod_cast this
  · rw [div_le_iff₀ hNq]
    have : ((q * a : ℕ) : ℤ) ≤ W a * N := by push_cast; linarith
    exact_mod_cast this

end Christoffel

/-! ## Corollary 60: why radix 2^25.5 -/

section Field25519

open FdrsFormal.Applications.Field25519 FdrsFormal.Modes.SyntheticPlace.MixedRingProduct

/-- The 25519 weight ladder as a schedule (bit positions). -/
def W25519 (k : ℕ) : ℤ := weightBits k

theorem radixBits_period (k : ℕ) : radixBits (k + 10) = radixBits k := by
  simp only [radixBits]
  rw [show (k + 10) % 2 = k % 2 by omega]

theorem weightBits_period : ∀ k, weightBits (k + 10) = weightBits k + 255
  | 0 => by decide
  | k + 1 => by
    have h1 : weightBits ((k + 10) + 1) = weightBits (k + 10) + radixBits (k + 10) := rfl
    have h2 : weightBits (k + 1) = weightBits k + radixBits k := rfl
    rw [show k + 1 + 10 = (k + 10) + 1 by ring, h1, h2, weightBits_period k, radixBits_period]
    ring

theorem W25519_isSchedule : IsSchedule 10 255 W25519 :=
  ⟨rfl, fun k => by simp only [W25519, weightBits_period]; push_cast; ring⟩

theorem W25519_defect (a b : ℕ) : 0 ≤ defect W25519 a b ∧ defect W25519 a b ≤ 1 := by
  rw [defect_mod W25519_isSchedule]
  have h := weightBits_add (a % 10) (Nat.mod_lt _ (by norm_num)) (b % 10) (Nat.mod_lt _ (by norm_num))
  simp only [defect, W25519]
  constructor <;> split_ifs at h <;> omega

/-- **Corollary 60 (the 25519 ladder is the ceiling schedule).** `W_k = ⌈255 k / 10⌉`.

**fdrs.md**: Corollary 60 (why radix 2^25.5). -/
theorem weightBits_eq_ceil : W25519 = ceilSched 10 255 :=
  christoffel_unique (by norm_num) W25519_isSchedule (fun a b => (W25519_defect a b).1)
    (fun a b => (W25519_defect a b).2)

/-- **Corollary 60 (why radix 2^25.5).** Any ten-limb schedule of `2^255` whose schoolbook
product coefficients are all `1` or `2` is the 25519 ladder `26, 25, 26, …`.

**fdrs.md**: Corollary 60 (why radix 2^25.5). -/
theorem radix_25_5_unique {W : ℕ → ℤ} (hW : IsSchedule 10 255 W)
    (hlo : ∀ a b, 0 ≤ defect W a b) (hhi : ∀ a b, defect W a b ≤ 1) : W = W25519 := by
  rw [christoffel_unique (by norm_num) hW hlo hhi, weightBits_eq_ceil]

end Field25519


end FdrsFormal.Modes.SyntheticPlace.ChristoffelSchedule
