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

# Carry frequency on the generated timeline — the `overflowRate` ⇄ engine bridge

The corpus `ThreeLineMediator.overflowRate b L = 1 / placeValue b L = 1/B_L` is the
carry frequency of a *fixed*-radix odometer: the fraction of states whose tick carries
past depth `L`. This file extends that exact, rational, discrete accounting to the
**generated / continued-fraction timeline** — the timeline the density-free engine
emits onto.

The bridge is the gauge. For a fixed radix the place value is `B_L = ∏ radix`; for a
continued fraction it is the convergent denominator `qₗ` (= the admissible-config count
the engine routes through, `SubshiftMetric.gaugeAt`). So the generated-timeline carry
frequency is `cfOverflowRate x L = 1/qₗ`, and it satisfies the same laws as the corpus
`overflowRate` — positive, antitone in depth — *and* it vanishes (carries get
arbitrarily rare), which is exactly the refinement the integration engine relies on.

Honest caveat: the corpus `overflowRate_product` (`B_C = B_A · B_B`) does **not** carry
over to the bihomographic engine — continued-fraction combination is not a radix
product, so the mediator's output place value is not the product of the inputs'. The
bridge is at the level of the *carry-frequency law* (reciprocal place value), not the
product structure.
-/
import FdrsFormal.Modes.VariableRadix.SubshiftMetric

namespace FdrsFormal.Modes.VariableRadix.Subshift

/-- **Carry frequency of a generated (continued-fraction) timeline**: the reciprocal of
the gauge `qₗ`. The CF analogue of the corpus `overflowRate b L = 1/B_L`, with the
gauge `qₗ` (admissible-config count / CF place value) in place of the fixed place value
`B_L`. Rational and exact — no measure, no density. -/
noncomputable def cfOverflowRate (x : ℕ → ℕ) (L : ℕ) : ℚ := 1 / (gaugeAt x L : ℚ)

/-- Carry frequency is positive (mirrors `overflowRate_pos`). -/
theorem cfOverflowRate_pos {x : ℕ → ℕ} (hx : Admissible x) (L : ℕ) :
    0 < cfOverflowRate x L := by
  simp only [cfOverflowRate]
  exact div_pos one_pos (by exact_mod_cast gaugeAt_pos hx L)

/-- Carry frequency decreases with depth — deeper carry is rarer (mirrors
`overflowRate_antitone`); here via gauge monotonicity rather than place-value monotonicity. -/
theorem cfOverflowRate_antitone {x : ℕ → ℕ} (hx : Admissible x) {L₁ L₂ : ℕ} (h : L₁ ≤ L₂) :
    cfOverflowRate x L₂ ≤ cfOverflowRate x L₁ := by
  simp only [cfOverflowRate]
  have h₁ : (0 : ℚ) < (gaugeAt x L₁ : ℚ) := by exact_mod_cast gaugeAt_pos hx L₁
  have h₂ : (0 : ℚ) < (gaugeAt x L₂ : ℚ) := by exact_mod_cast gaugeAt_pos hx L₂
  rw [div_le_div_iff₀ h₂ h₁]
  simp only [one_mul]
  exact_mod_cast gaugeAt_monotone hx h

/-- **Carries vanish.** Beyond some depth the carry frequency drops below any `ε > 0` —
the generated-timeline refinement (`1/qₗ → 0`) that the integration engine relies on.
This is the strict-positivity payoff of the gauge growth, which the *fixed*-radix
`overflowRate` only attains when `B_L → ∞`; here it holds even for `φ`. -/
theorem cfOverflowRate_vanishes {x : ℕ → ℕ} (hx : Admissible x) {ε : ℚ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ L, N ≤ L → cfOverflowRate x L < ε := by
  obtain ⟨N, hN⟩ := gaugeAt_inv_lt hx (ε : ℝ) (by exact_mod_cast hε)
  refine ⟨N, fun L hL => ?_⟩
  have hℝ : ((cfOverflowRate x L : ℝ)) < (ε : ℝ) := by
    have : (cfOverflowRate x L : ℝ) = ((gaugeAt x L : ℝ))⁻¹ := by
      simp only [cfOverflowRate, one_div]; push_cast; ring
    rw [this]; exact hN L hL
  exact_mod_cast hℝ

end FdrsFormal.Modes.VariableRadix.Subshift
