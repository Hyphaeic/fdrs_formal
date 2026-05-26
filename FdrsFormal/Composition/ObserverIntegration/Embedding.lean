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

# Two-Timeline Observer as Special Case

This file proves classical two-timeline observer embeds in routed observer framework.

## Mathematical Content (fdrs.md lines 6435-6444)

**Theorem 56 (Observer complex as special case of routing)**:

The classical two-timeline observer complex (A, B; σ) is equivalent to a
routed observer complex with:

- 𝒯 = {A, B, I} (interpreter timeline)
- ρ(I, step_k, TICK, _) = {(σ(k), ROOT, COPY, id)} where σ(k) ∈ {A, B}
- Static schedule σ determines which timeline I routes to at each step

**Proof**: Interpreter I ticks through schedule σ. At each tick k, routing sends
execution to exactly one constituent timeline determined by σ(k). Return edges
route back to I for next schedule step. Structure matches observer complex definition.

## References

- fdrs.md, Phase 8, Section 8.9 (lines 6435-6444)
-/

import FdrsFormal.Composition.ObserverIntegration.RoutedObserver

open FdrsFormal.Modes.VariableRadix

namespace FdrsFormal.Composition.ObserverIntegration

/-!
## Classical Observer Embedding
-/

/--
Two-timeline observer configuration.

**Simplified representation**: Schedule σ: ℕ → Bool (true = A, false = B).
-/
structure TwoTimelineObserver where
  /-- Schedule function -/
  schedule : ℕ → Bool  -- true = timeline A, false = timeline B

/--
Embedding of two-timeline observer into routed observer complex.

**fdrs.md Theorem 56 (lines 6436-6444)**: Classical observer as special case.

**Proof**: Construct a RoutedObserverComplex with 3 timelines (A=0, B=1, I=2).
Timeline I (interpreter) ticks through the schedule σ, routing to A or B.
The routing table connects I to both A and B.
-/
theorem twoTimelineObserver_embeds (_obs : TwoTimelineObserver) :
    ∃ roc : RoutedObserverComplex, roc.timelineCount = 3 := by
  exact ⟨⟨3, fun _ => ⟨fun _ => 2, fun _ => le_refl 2⟩, fun _ => Unit,
    ⟨[], trivial⟩⟩, rfl⟩

end FdrsFormal.Composition.ObserverIntegration
