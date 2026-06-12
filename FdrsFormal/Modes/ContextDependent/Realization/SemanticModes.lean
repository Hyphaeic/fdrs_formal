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

# Operational Semantic Modes

Defines the three computational modes for context-dependent systems.

## Mathematical Content (fdrs.md lines 5601-5609)

**Definition 91**: Operational semantic modes (RandomAccess, Streaming, Sequential)

## References

- fdrs.md, Phase 7, Section 7.3 (lines 5601-5609)
-/

import FdrsFormal.Modes.ContextDependent.Realization.Strategies

namespace FdrsFormal.Modes.ContextDependent.Realization

/-! ## Definition 91: Operational semantic modes -/

/--
**fdrs.md**: Definition 91 (Operational semantic modes) [§7.3.1 · Phase 7] (lines 5601-5609)

A context-dependent system can operate in different semantic modes
corresponding to different computational models:

1. **RandomAccess**: State at any time t can reference state at any time t'
   (full directed graph)
2. **Streaming**: State at time t depends only on finite window t-k,...,t
   (bounded causal)
3. **Sequential**: State at time t depends only on t-1 (Markov property)

The mode is a constraint on the computation graph, not on the algebraic structure.
-/
inductive SemanticMode where
  /-- Full random access: state at t can reference any t' -/
  | RandomAccess : SemanticMode
  /-- Streaming: bounded causal window of size k -/
  | Streaming (windowSize : ℕ) : SemanticMode
  /-- Purely sequential: Markov property, depends only on t-1 -/
  | Sequential : SemanticMode
  deriving DecidableEq, Repr

end FdrsFormal.Modes.ContextDependent.Realization
