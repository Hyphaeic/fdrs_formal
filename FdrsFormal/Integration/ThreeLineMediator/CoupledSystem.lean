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

# Coupled Observer System with Independent Radix

Formalizes the general three-line mediator where:
- The coupling ratio (latency) defines the mediator's LSU
- The mediator's radix is independent of the coupling
- Two instantiation modes: pre-initialized and manifest-on-overflow

## Core Principle

**Coupling** defines what "1" means — the LSU content: how many A-ticks
constitute one B-emission.

**Radix** defines overflow behavior — how high the mediator counts before
carrying to the next position.

These are independent. Changing the radix does not change what "1" means.
Changing the coupling does not change when overflow occurs.

## Instantiation Modes

**Pre-initialized**: All digit positions exist from the start, filled with 0.
The completed space R̂ — every slot occupied from the beginning.

**Manifest-on-overflow**: Digit positions are null (∅) until carry first
reaches them. The first carry writes 0 — the additive identity — bringing
the position into existence. Zero is not the default state; it is the
first act of creation. The transition ∅ → 0 is manifestation, not counting.

## References

- fdrs.md, Phase 1 (carry mechanics, place values)
- fdrs.md, Phase 5-6 (variable radix, overflow)
- ThreeLineMediator/Definition.lean (product construction as special case)
-/

import FdrsFormal.Core
import FdrsFormal.Integration.ThreeLineMediator.Definition

namespace FdrsFormal.Integration.ThreeLineMediator

open FdrsFormal.Core.Primitives FdrsFormal.Core.Infinite

/-!
## Instantiation Modes
-/

/-- Two modes of bringing digit positions into existence -/
inductive InstantiationMode where
  /-- All positions exist from the start, initialized to 0.
      Corresponds to CompletedSpace (the inverse limit R̂). -/
  | preInitialized
  /-- Positions are null (∅) until carry first reaches them.
      The first carry writes 0, manifesting the additive identity.
      Corresponds to the direct limit R^(∞)_fin. -/
  | manifestOnOverflow
  deriving DecidableEq, Repr

/-!
## Manifest Space

In manifest-on-overflow mode, each digit position is either:
- `none`: null slot (∅), not yet reached by carry, truly absent
- `some d`: manifested, currently at digit value d

The additive identity (0) appears as `some 0`, not as the default.
The default is `none` — genuine absence, not zero.
-/

/-- The manifest space: digits that come into existence on first carry.
    `none` = null slot (∅), `some d` = manifested digit at value d. -/
def ManifestSpace (b : RadixSeq) := (i : ℕ) → Option (Fin (b i))

namespace ManifestSpace

variable {b : RadixSeq}

/-- The fully null state: nothing has been created yet -/
def null : ManifestSpace b := fun _ => none

/-- Whether position i has been manifested (is not null) -/
def isManifested (x : ManifestSpace b) (i : ℕ) : Prop := x i ≠ none

/-- A manifest state is well-formed if manifested positions form a contiguous
    prefix: if position i exists, all positions below it also exist.
    This is the natural invariant maintained by carry propagation. -/
def WellFormed (x : ManifestSpace b) : Prop :=
  ∀ i, isManifested x i → ∀ j, j < i → isManifested x j

/-- The null state is vacuously well-formed -/
theorem null_wellFormed : WellFormed (null : ManifestSpace b) := by
  intro i hi; exact absurd rfl hi

/-- Embed a completed-space element (pre-initialized: all positions manifested) -/
def ofCompleted (x : CompletedSpace b) : ManifestSpace b :=
  fun i => some (x i)

/-- A completed-space element is everywhere manifested -/
theorem ofCompleted_manifested (x : CompletedSpace b) (i : ℕ) :
    isManifested (ofCompleted x) i := by
  simp [ofCompleted, isManifested]

/-- Project to completed space (null positions become 0) -/
def toCompleted (x : ManifestSpace b) : CompletedSpace b :=
  fun i => (x i).getD ⟨0, b.pos i⟩

/-- Round-trip: completed → manifest → completed is identity -/
theorem toCompleted_ofCompleted (x : CompletedSpace b) :
    (ofCompleted x).toCompleted = x := by
  funext i; simp [toCompleted, ofCompleted]

/-!
### Manifest Tick Semantics

Single-position tick with manifest semantics. The key insight:

**Manifestation absorbs carry.** When carry reaches a null slot, it does
not propagate further — it creates the position by writing 0.

- `none → (some 0, false)`: manifestation absorbs carry, position created
- `some v → (some (v+1), false)`: normal increment, no carry
- `some (b_i - 1) → (some 0, true)`: overflow, carry propagates upward
-/

/-- Single-position manifest tick. Returns (new digit value, carry out). -/
def tickDigit (b : RadixSeq) (i : ℕ) (d : Option (Fin (b i))) :
    Option (Fin (b i)) × Bool :=
  match d with
  | none => (some ⟨0, b.pos i⟩, false)
  | some ⟨v, _⟩ =>
    if h : v + 1 < b i then (some ⟨v + 1, h⟩, false)
    else (some ⟨0, b.pos i⟩, true)

/-- Manifestation absorbs carry: ticking a null slot produces 0 with no carry out -/
theorem tickDigit_none (i : ℕ) :
    tickDigit b i none = (some ⟨0, b.pos i⟩, false) := rfl

/-- After manifestation, the position is manifested -/
theorem tickDigit_manifested (i : ℕ) (d : Option (Fin (b i))) :
    (tickDigit b i d).1 ≠ none := by
  simp only [tickDigit]
  split
  · simp
  · split <;> simp

end ManifestSpace

/-!
## Coupling: The Observed Latency

A coupling between two observer lines records the integer count of
A-ticks that elapse before B emits. This count — the **latency** —
defines the mediator's LSU.

The coupling does NOT determine the mediator's radix. It only defines
what "one unit" means on the mediator line.

The mediator's single "1" is composite: it contains `latency` A-ticks
and exactly 1 B-emission. C's digit doesn't just count — each count
*holds* the A/B relationship as its internal structure.
-/

/-- A coupling between two observer lines: the tick ratio that defines
    the mediator's LSU. `latency` = number of A-ticks per B-emission. -/
structure Coupling (A B : ObserverLine) where
  /-- Number of A-ticks before B emits once -/
  latency : ℕ
  /-- At least one A-tick per B-emission -/
  latency_pos : 0 < latency

namespace Coupling

variable {A B : ObserverLine}

/-- The LSU weight: how many A-ticks one mediator unit is worth -/
def lsuWeight (c : Coupling A B) : ℕ := c.latency

/-- Lockstep coupling: lines advance together (1 A-tick per B-emission) -/
def isLockstep (c : Coupling A B) : Prop := c.latency = 1

/-- The composite unit: one mediator tick decomposes into
    `latency` A-ticks and 1 B-emission -/
structure CompositeUnit where
  aTicks : ℕ
  bEmission : Bool

/-- The standard unit for this coupling -/
def unit (c : Coupling A B) : CompositeUnit where
  aTicks := c.latency
  bEmission := true

end Coupling

/-!
## Coupled Observer System

A coupled system bundles:
1. Two observer lines A (finer) and B (coarser)
2. A coupling that defines the mediator's LSU
3. The mediator line C with its own **independent** radix
4. An instantiation mode

The separation of concerns:
- `coupling.latency = 3` means "one C-tick = 3 A-ticks + 1 B-emission"
- `mediatorRadix 0 = 5` means "C counts 5 of those units before overflowing"
- These are independent choices. The same coupling works with any radix.
-/

/-- A coupled observer system with three lines -/
structure CoupledSystem where
  /-- The finer line (faster tick rate, smaller LSU) -/
  lineA : ObserverLine
  /-- The coarser line (slower tick rate, larger LSU) -/
  lineB : ObserverLine
  /-- The coupling: defines the mediator's LSU -/
  coupling : Coupling lineA lineB
  /-- The mediator's radix sequence (independent of coupling) -/
  mediatorRadix : RadixSeq
  /-- How digit positions come into existence -/
  mode : InstantiationMode

namespace CoupledSystem

/-- The mediator as an observer line -/
def mediator (sys : CoupledSystem) : ObserverLine := ⟨sys.mediatorRadix⟩

/-!
### Tick Correspondence

The fundamental invariant: one mediator tick = `latency` A-ticks = 1 B-emission.
This is an exact integer relationship at every count, at every depth.
-/

/-- A-ticks corresponding to n mediator units -/
def aTicksFor (sys : CoupledSystem) (n : ℕ) : ℕ :=
  n * sys.coupling.latency

/-- B-emissions corresponding to n mediator units -/
def bEmissionsFor (_sys : CoupledSystem) (n : ℕ) : ℕ := n

/-- The A:B ratio is exactly the latency at every count -/
theorem tick_ratio (sys : CoupledSystem) (n : ℕ) :
    sys.aTicksFor n = sys.coupling.latency * sys.bEmissionsFor n := by
  simp [aTicksFor, bEmissionsFor, mul_comm]

/-- Zero mediator ticks = zero A-ticks -/
theorem aTicksFor_zero (sys : CoupledSystem) : sys.aTicksFor 0 = 0 := by
  simp [aTicksFor]

/-- A-ticks scale linearly with mediator ticks -/
theorem aTicksFor_add (sys : CoupledSystem) (m n : ℕ) :
    sys.aTicksFor (m + n) = sys.aTicksFor m + sys.aTicksFor n := by
  simp [aTicksFor, Nat.add_mul]

/-!
### Capacity (determined by radix alone)

The mediator's capacity at each depth is determined entirely by the radix —
the coupling has no effect on when overflow occurs.
-/

/-- Mediator capacity at depth L: number of composite units before overflow -/
def capacityAtDepth (sys : CoupledSystem) (L : ℕ) : ℕ :=
  placeValue sys.mediatorRadix L

/-- Total A-tick capacity at depth L = capacity × latency -/
def aCapacityAtDepth (sys : CoupledSystem) (L : ℕ) : ℕ :=
  placeValue sys.mediatorRadix L * sys.coupling.latency

/-- A-capacity factors as mediator-capacity × latency -/
theorem aCapacity_eq (sys : CoupledSystem) (L : ℕ) :
    sys.aCapacityAtDepth L = sys.capacityAtDepth L * sys.coupling.latency := rfl

/-!
### Independence Theorems

The two structural parameters — coupling and radix — are orthogonal:
- Same coupling + different radix → same LSU, different overflow
- Different coupling + same radix → different LSU, same overflow
-/

/-- **LSU Independence**: changing the radix doesn't change what "1" means -/
theorem lsu_independent_of_radix (sys₁ sys₂ : CoupledSystem)
    (h : sys₁.coupling.latency = sys₂.coupling.latency) (n : ℕ) :
    sys₁.aTicksFor n = sys₂.aTicksFor n := by
  simp [aTicksFor, h]

/-- **Radix Independence**: changing the coupling doesn't change overflow -/
theorem radix_independent_of_coupling (sys₁ sys₂ : CoupledSystem)
    (h : sys₁.mediatorRadix = sys₂.mediatorRadix) (L : ℕ) :
    sys₁.capacityAtDepth L = sys₂.capacityAtDepth L := by
  simp [capacityAtDepth, h]

end CoupledSystem

/-!
## The Product Construction as Special Case

The product radix mediator from `Definition.lean` is recovered when:
- `coupling.latency = A.radix 0` (B emits after A's full cycle at position 0)
- `mediatorRadix = productRadix A.radix B.radix` (radix forced to product)

This is the unique case where coupling and radix coincide: the LSU content
and the overflow structure are both determined by the component radices.
In general, they are independent structural choices.
-/

/-- Product coupling: B emits when A completes a full cycle at position 0 -/
def productCoupling (A B : ObserverLine) : Coupling A B where
  latency := A.radix 0
  latency_pos := A.radix.pos 0

/-- The product construction forces coupling and radix simultaneously -/
def productCoupledSystem (A B : ObserverLine) : CoupledSystem where
  lineA := A
  lineB := B
  coupling := productCoupling A B
  mediatorRadix := productRadix A.radix B.radix
  mode := .preInitialized

/-- General construction: choose coupling and radix independently -/
def mkCoupledSystem (A B : ObserverLine) (latency : ℕ) (h : 0 < latency)
    (mRadix : RadixSeq) (mode : InstantiationMode := .preInitialized) :
    CoupledSystem where
  lineA := A
  lineB := B
  coupling := ⟨latency, h⟩
  mediatorRadix := mRadix
  mode := mode

/-!
## Example: Three A-ticks per B-emission

If line A counts {0,1,2,3,4} (radix 5 at position 0) and the coupling
has latency 3, then:
- B emits after 3 A-ticks (not waiting for A's full cycle of 5)
- C's "1" = (3 A-ticks, 1 B-emission)
- C's radix is independently chosen — say radix 4 at position 0
- C counts {0,1,2,3} of these composite units before overflowing
- One C-overflow = 4 × 3 = 12 A-ticks = 4 B-emissions

The latency (3) and the radix (4) are independent parameters.
A's own radix (5) plays no role in the coupling.
-/

end FdrsFormal.Integration.ThreeLineMediator
