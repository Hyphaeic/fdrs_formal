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

# Residual as Metric Discrepancy

This file characterizes residual payload as metric discrepancy.

## Mathematical Content (fdrs.md lines 5369-5380)

**Theorem 42 (Residual as metric discrepancy)**:

The residual payload at step n can be characterized as:
  payload(n) = log(δ_{ω_I}(τ_n, τ_{n+1}) / π_B^*δ_{ω_B}(τ_n, τ_{n+1}))

**Interpretation**: Payload measures how much "distance information" is lost
when projecting from composite metric to B's metric.

**Proof sketch**: Ratio compares intrinsic I-distance to projected B-distance.
Logarithm converts multiplicative discrepancy to additive payload.

## References

- fdrs.md, Phase 6, Section 6.5 (lines 5369-5380)
-/

import FdrsFormal.Modes.VariableRadix.MultiMetric.ObserverComplex
import FdrsFormal.Modes.VariableRadix.MultiMetric.Projection
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace FdrsFormal.Modes.VariableRadix.MultiMetric

/-!
## Residual Payload Characterization
-/

/--
The residual payload at step `n`: the logarithm of the metric discrepancy ratio
between the intrinsic composite `I`-distance and the pullback of `B`'s distance
via the projection `π_B`. Captures Theorem 42's right-hand side as a concrete
(noncomputable) real number.
-/
noncomputable def residualPayload {α β : Type*}
    (τ : ℕ → α) (πB : α → β) (δI : α → α → ℝ) (δB : β → β → ℝ) (n : ℕ) : ℝ :=
  Real.log (δI (τ n) (τ (n + 1)) / δB (πB (τ n)) (πB (τ (n + 1))))

/--
**fdrs.md**: Theorem 42 (Residual as metric discrepancy) [§6.5.3 · Phase 6] (lines 5369-5378)

For an interpreter state evolution `τ : ℕ → ℛ_I`, a timeline projection
`π_B : ℛ_I → ℛ_B` (Definition 83), and the intrinsic and projected metrics
`δ_{ω_I}` and `δ_{ω_B}`, there is a residual payload at step `n` given by

  `payload(n) = log(δ_{ω_I}(τ_n, τ_{n+1}) / π_B^* δ_{ω_B}(τ_n, τ_{n+1}))`,

where the pullback is `π_B^* δ_{ω_B}(x, y) = δ_{ω_B}(π_B(x), π_B(y))`.

This quantifies the "distance information" lost when projecting from the
composite metric to `B`'s metric — when the intrinsic distance exceeds the
pullback, the payload is positive; when they agree, it is zero
(`residualPayload_eq_zero_of_eq`).
-/
theorem residualAsMetricDiscrepancy {α β : Type*}
    (τ : ℕ → α) (πB : α → β) (δI : α → α → ℝ) (δB : β → β → ℝ) (n : ℕ) :
    ∃ payload : ℝ,
      payload = Real.log (δI (τ n) (τ (n + 1)) / δB (πB (τ n)) (πB (τ (n + 1)))) :=
  ⟨residualPayload τ πB δI δB n, rfl⟩

/-- Companion to Theorem 42: the residual payload vanishes whenever the
intrinsic distance equals the pullback distance — no information is lost when
the two metrics agree on the step `(τ_n, τ_{n+1})`. -/
theorem residualPayload_eq_zero_of_eq {α β : Type*}
    (τ : ℕ → α) (πB : α → β) (δI : α → α → ℝ) (δB : β → β → ℝ) (n : ℕ)
    (h : δI (τ n) (τ (n + 1)) = δB (πB (τ n)) (πB (τ (n + 1)))) :
    residualPayload τ πB δI δB n = 0 := by
  unfold residualPayload
  rw [h]
  by_cases hx : δB (πB (τ n)) (πB (τ (n + 1))) = 0
  · rw [hx, zero_div, Real.log_zero]
  · rw [div_self hx, Real.log_one]

/--
Payload measures information loss under projection.

**fdrs.md line 5377**: Payload = distance info lost in B's projection.
-/
def payload_measures_information_loss (obs : MultiMetricObserver) : Prop :=
  pullback_ne_intrinsic obs → timelines_independent_metrics obs

end FdrsFormal.Modes.VariableRadix.MultiMetric
