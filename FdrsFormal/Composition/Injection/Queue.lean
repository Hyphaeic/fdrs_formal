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

# Injection Queue

This file defines injection queues for asynchronous timeline coupling.

## Mathematical Content (fdrs.md lines 6084-6095)

**Definition 118 (Injection queue for asynchrony)**:

Each timeline T maintains an **injection queue:**
  Q_T: Queue(Σ* × Payload)

**Protocol:**
- **Enqueue** when routed: Q_T.push(s_B, p)
- **Process** on timeline tick: (s, p) ← Q_T.pop(); Inject(T, s, p)

**Bounded queues**: System is well-behaved if |Q_T| ≤ Q_max for all T.

## References

- fdrs.md, Phase 8, Section 8.3 (lines 6084-6095)
-/

import FdrsFormal.Composition.Injection.Definition

namespace FdrsFormal.Composition.Injection

/-!
## Injection Queue Structure
-/

/--
Injection queue entry: (cylinder prefix, payload) pair.

**fdrs.md line 6088**: Queue stores pending injections.
-/
structure InjectionQueueEntry where
  /-- Target cylinder prefix for injection -/
  cylinderPrefix : ℕ
  /-- Payload to inject -/
  payload : ℕ

/--
Injection queue for a timeline.

**fdrs.md Definition 118 (lines 6086-6088)**: FIFO queue of pending injections.

**Axiomatized**: Uses List as queue implementation (simplified).
-/
structure InjectionQueue where
  /-- Queue entries (FIFO order) -/
  entries : List InjectionQueueEntry

/--
Enqueue operation.

**fdrs.md line 6092**: Q_T.push(s_B, p) when routing triggers.

**Axiomatized**: FIFO enqueue semantics.
-/
def enqueue (q : InjectionQueue) (entry : InjectionQueueEntry) : InjectionQueue :=
  { entries := q.entries ++ [entry] }

/--
Dequeue operation.

**fdrs.md line 6093**: (s, p) ← Q_T.pop() on timeline tick.

**Axiomatized**: FIFO dequeue with Option for empty queue.
-/
def dequeue (q : InjectionQueue) : Option (InjectionQueueEntry × InjectionQueue) :=
  match q.entries with
  | [] => none
  | e :: es => some (e, { entries := es })

/--
Bounded queue property.

**fdrs.md line 6095**: System well-behaved if |Q_T| ≤ Q_max.

**Axiomatized**: Queue size bound predicate.
-/
def isBounded (q : InjectionQueue) (Q_max : ℕ) : Prop :=
  q.entries.length ≤ Q_max

/--
Queue size.

**fdrs.md line 6095**: |Q_T| for bounding.
-/
def queueSize (q : InjectionQueue) : ℕ := q.entries.length

end FdrsFormal.Composition.Injection
