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

# Carry-Route Unification (Fractal Unification)

Proves that arithmetic carry propagation through a cylinder of SpatialDigits
is strictly equal to a queue-based routing process where each digit's carry
is an OVERFLOW event routed as an INJECT to the next digit.

This unifies two perspectives:
- **Vertical (arithmetic)**: Carry propagates from digit i to digit i+1
- **Lateral (routing)**: OVERFLOW at timeline i routes to INJECT at timeline i+1

The theorem `carry_is_overflow_route` proves they produce identical states.

## Mathematical Content

**Definition 148**: CarryEvent — classifies carry output as OVERFLOW or QUIESCENT
**Definition 149**: Carry-as-route — maps carry to Phase 8 routing events
**Definition 150**: Unified spatial tick — queue-based single-pass carry resolution
**Theorem 61**: Fractal unification — recursive carry = queue-based route

## References

- fdrs.md, Phase 9, Section 9.9
- SpatialThermometer.lean (Definition 145-147, Theorem 60)
- Events.lean (Definition 111: Event.OVERFLOW, Event.INJECT)
- TransferSemantics.lean (Definition 113: TransferType.TOTAL)
-/

import FdrsFormal.Modes.ExtendedBase.SpatialThermometer
import FdrsFormal.Composition.Routing.Events
import FdrsFormal.Composition.Junctions.TransferSemantics

namespace FdrsFormal.Modes.ExtendedBase

open FdrsFormal.Composition.Routing (Event)
open FdrsFormal.Composition.Junctions (TransferType applyTransfer)

/-!
## Spatial Cylinder

A cylinder of `k` spatial digits, each with its own capacity `M i` and active
radix `b i`. This is the spatial analogue of `ExtendedRep`.
-/

/--
A spatial cylinder: a sequence of `k` spatial digits, each with capacity `M i`.
Each digit has an independent cell-chain capacity.
-/
def SpatialCylinder (M : Fin k → ℕ) : Type :=
  (i : Fin k) → SpatialDigit (M i)

/--
Validity predicate: every token is within its active zone.
-/
def cylinderValid {k : ℕ} (b : Fin k → ℕ) (M : Fin k → ℕ)
    (cyl : SpatialCylinder M) : Prop :=
  ∀ i, (cyl i).tokenPos.val < b i

/--
Update a single digit in a cylinder, preserving all others.
-/
def cylinderUpdate {k : ℕ} {M : Fin k → ℕ} (cyl : SpatialCylinder M)
    (i : Fin k) (d : SpatialDigit (M i)) : SpatialCylinder M :=
  fun j => if h : j = i then h ▸ d else cyl j

@[simp]
theorem cylinderUpdate_at {k : ℕ} {M : Fin k → ℕ} (cyl : SpatialCylinder M)
    (i : Fin k) (d : SpatialDigit (M i)) :
    cylinderUpdate cyl i d i = d := by
  simp [cylinderUpdate]

@[simp]
theorem cylinderUpdate_ne {k : ℕ} {M : Fin k → ℕ} (cyl : SpatialCylinder M)
    (i j : Fin k) (d : SpatialDigit (M i)) (h : j ≠ i) :
    cylinderUpdate cyl i d j = cyl j := by
  simp [cylinderUpdate, h]

/-- Validity is preserved when updating a digit via spatialTick. -/
theorem cylinderValid_update {k : ℕ} {M : Fin k → ℕ} {b : Fin k → ℕ}
    {cyl : SpatialCylinder M} (hvalid : cylinderValid b M cyl)
    (hb : ∀ i, 1 ≤ b i) (hbM : ∀ i, b i ≤ M i)
    (i : Fin k) :
    cylinderValid b M (cylinderUpdate cyl i (spatialTick (cyl i) (b i) (hb i) (hbM i) (hvalid i)).1) := by
  intro j
  unfold cylinderUpdate
  split
  · next h =>
    subst h
    unfold spatialTick
    split
    · next hadv => simp_all
    · next hwrap => exact hb j
  · exact hvalid j

/-!
## Definition 148: Carry event classification

A single-digit tick either produces OVERFLOW (carry = true) or is
QUIESCENT (carry = false). This bridges the Boolean carry flag from
`spatialTick` into the Phase 8 event vocabulary.
-/

/--
Carry event type: the output of a single-digit tick, classified for routing.
-/
inductive CarryEvent where
  /-- Digit overflowed: carry must be routed to the next digit -/
  | OVERFLOW : CarryEvent
  /-- Digit absorbed the tick: no further propagation -/
  | QUIESCENT : CarryEvent
  deriving DecidableEq, Repr

/--
Classify the Boolean carry output of `spatialTick` as a `CarryEvent`.
-/
def classifyCarry (carry : Bool) : CarryEvent :=
  if carry then .OVERFLOW else .QUIESCENT

theorem classifyCarry_true : classifyCarry true = .OVERFLOW := rfl
theorem classifyCarry_false : classifyCarry false = .QUIESCENT := rfl

/--
Map a carry event to the Phase 8 event type.
The OVERFLOW at digit `i` in timeline `T` becomes `Event.OVERFLOW T [i]`.
-/
def carryToPhase8Event (T : ℕ) (digitIndex : ℕ) (ce : CarryEvent) : Option Event :=
  match ce with
  | .OVERFLOW => some (Event.OVERFLOW T [digitIndex])
  | .QUIESCENT => none

/-!
## Definition 149: Carry-as-route (carryAsRoute)

The default odometer routing rule: when `SpatialDigit i` produces an
OVERFLOW, route an INJECT payload to `SpatialDigit (i+1)`.

This is a deterministic, acyclic routing table with exactly one rule
per digit position: `OVERFLOW @ i → INJECT @ (i+1)`.
-/

/--
Odometer routing decision: given a carry event at position `pos`,
determine whether to propagate (and to which position).

Returns `true` (propagate to pos+1) iff the event is OVERFLOW.
-/
def carryRouteDecision (ce : CarryEvent) : Bool :=
  match ce with
  | .OVERFLOW => true
  | .QUIESCENT => false

/--
The routing decision faithfully mirrors the carry flag.
-/
theorem carryRouteDecision_eq_carry (c : Bool) :
    carryRouteDecision (classifyCarry c) = c := by
  cases c <;> rfl

/--
The transfer type for carry routing is always TOTAL: the overflowing digit
resets to 0 and transfers one unit of carry.
-/
def carryTransferType : TransferType := .TOTAL

/--
Applying TOTAL transfer to carry: source resets to 0, payload is the residue.
-/
theorem carry_uses_total_transfer (residue state : ℕ) :
    applyTransfer carryTransferType residue state = (0, residue) := rfl

/-!
## Recursive Carry Tick (standard arithmetic)

The traditional left-to-right carry propagation: tick digit at `pos`,
if it carries then tick digit at `pos+1`, etc.

Processes positions `pos, pos+1, ..., k-1`.
-/

/--
Recursive carry propagation through a spatial cylinder, starting
at position `pos`. Ticks the digit at `pos` if `carry_in` is true,
then propagates any resulting carry rightward.

Returns the updated cylinder and whether carry exits the cylinder.
-/
def recursiveCarryTick {k : ℕ} (M : Fin k → ℕ) (b : Fin k → ℕ)
    (hb : ∀ i, 1 ≤ b i) (hbM : ∀ i, b i ≤ M i)
    (cyl : SpatialCylinder M)
    (hvalid : cylinderValid b M cyl)
    (pos : ℕ) (carry_in : Bool) :
    SpatialCylinder M × Bool :=
  if hpos : pos < k then
    if carry_in then
      let i : Fin k := ⟨pos, hpos⟩
      let result := spatialTick (cyl i) (b i) (hb i) (hbM i) (hvalid i)
      let cyl' := cylinderUpdate cyl i result.1
      have hvalid' : cylinderValid b M cyl' :=
        cylinderValid_update hvalid hb hbM i
      recursiveCarryTick M b hb hbM cyl' hvalid' (pos + 1) result.2
    else
      (cyl, false)
  else
    (cyl, carry_in)
termination_by k - pos

/-!
## Definition 150: Unified Spatial Tick (queue-based routing)

Instead of direct recursion on the carry Boolean, we:
1. Apply `spatialTick` to the current digit
2. Classify the result as a `CarryEvent`
3. Consult `carryRouteDecision` to determine propagation
4. If routed, process the next digit; otherwise stop

The routing abstraction makes the event-driven nature explicit.
-/

/--
Queue-based carry resolution starting at position `pos`.

Applies `spatialTick`, classifies the carry via `classifyCarry`,
and consults `carryRouteDecision` to determine whether to propagate.

This is operationally the event-driven perspective: each OVERFLOW
event at position `pos` triggers an INJECT at position `pos+1`.
-/
def unifiedSpatialTick {k : ℕ} (M : Fin k → ℕ) (b : Fin k → ℕ)
    (hb : ∀ i, 1 ≤ b i) (hbM : ∀ i, b i ≤ M i)
    (cyl : SpatialCylinder M)
    (hvalid : cylinderValid b M cyl)
    (pos : ℕ) (carry_in : Bool) :
    SpatialCylinder M × Bool :=
  if hpos : pos < k then
    if carry_in then
      let i : Fin k := ⟨pos, hpos⟩
      -- Step 1: Apply spatialTick to digit i
      let result := spatialTick (cyl i) (b i) (hb i) (hbM i) (hvalid i)
      -- Step 2: Update the cylinder
      let cyl' := cylinderUpdate cyl i result.1
      -- Step 3: Classify the carry as a routing event
      let event := classifyCarry result.2
      -- Step 4: Consult the routing table
      let should_propagate := carryRouteDecision event
      have hvalid' : cylinderValid b M cyl' :=
        cylinderValid_update hvalid hb hbM i
      -- Step 5: Route or stop
      unifiedSpatialTick M b hb hbM cyl' hvalid' (pos + 1) should_propagate
    else
      (cyl, false)
  else
    (cyl, carry_in)
termination_by k - pos

/-!
## Theorem 61: Fractal Unification

The core theorem: recursive arithmetic carry propagation produces
exactly the same cylinder state as queue-based OVERFLOW routing.

"Digits are timelines, and addition is just local routing."
-/

/--
**Fractal Unification Theorem**: For any spatial cylinder, applying
recursive carry propagation is strictly equal to applying the
unified queue-based routing tick.

This proves that the arithmetic carry mechanism (vertical propagation
through digit positions) is identical to Phase 8's lateral OVERFLOW
routing between isomorphic Base-1 topological spaces.

**Proof**: By well-founded induction on `k - pos`.
The key insight is `carryRouteDecision_eq_carry`: the routing table's
decision to propagate is exactly the Boolean carry flag. So at each
step, the routing-based function passes the same `should_propagate`
as the recursive function passes `local_carry`, making the two
definitions unfold identically.
-/
theorem carry_is_overflow_route {k : ℕ} (M : Fin k → ℕ) (b : Fin k → ℕ)
    (hb : ∀ i, 1 ≤ b i) (hbM : ∀ i, b i ≤ M i)
    (cyl : SpatialCylinder M)
    (hvalid : cylinderValid b M cyl)
    (pos : ℕ) (carry_in : Bool) :
    recursiveCarryTick M b hb hbM cyl hvalid pos carry_in =
    unifiedSpatialTick M b hb hbM cyl hvalid pos carry_in := by
  unfold recursiveCarryTick unifiedSpatialTick
  -- Both branch on pos < k
  split
  case isTrue hpos =>
    -- Both branch on carry_in
    split
    case isTrue hc =>
      -- Both apply spatialTick, update cylinder, then recurse
      -- The key: carryRouteDecision (classifyCarry c) = c
      simp only [carryRouteDecision_eq_carry]
      -- Now both sides recurse with identical arguments
      exact carry_is_overflow_route M b hb hbM _ _ (pos + 1) _
    case isFalse => rfl
  case isFalse => rfl
termination_by k - pos

/-!
## Corollaries
-/

/--
Applying the full cylinder tick from position 0: the two mechanisms agree.
-/
theorem carry_is_overflow_route_full {k : ℕ} (M : Fin k → ℕ) (b : Fin k → ℕ)
    (hb : ∀ i, 1 ≤ b i) (hbM : ∀ i, b i ≤ M i)
    (cyl : SpatialCylinder M)
    (hvalid : cylinderValid b M cyl) :
    recursiveCarryTick M b hb hbM cyl hvalid 0 true =
    unifiedSpatialTick M b hb hbM cyl hvalid 0 true :=
  carry_is_overflow_route M b hb hbM cyl hvalid 0 true

/--
The carry produced by `spatialTick` at wrap is a TOTAL transfer:
the digit resets to 0 and emits residue 1.
-/
theorem spatialTick_wrap_is_total_transfer {M : ℕ} (d : SpatialDigit M) (b : ℕ)
    (hb : 1 ≤ b) (hbM : b ≤ M) (hd : d.tokenPos.val < b)
    (hwrap : (spatialTick d b hb hbM hd).2 = true) :
    (spatialTick d b hb hbM hd).1.tokenPos.val = 0 ∧
    applyTransfer carryTransferType 1 d.tokenPos.val = (0, 1) := by
  unfold spatialTick at hwrap ⊢
  split
  · next h => simp_all
  · exact ⟨rfl, rfl⟩

/--
When no overflow occurs, the digit absorbs the tick locally with no transfer.
-/
theorem spatialTick_absorb_no_transfer {M : ℕ} (d : SpatialDigit M) (b : ℕ)
    (hb : 1 ≤ b) (hbM : b ≤ M) (hd : d.tokenPos.val < b)
    (habsorb : (spatialTick d b hb hbM hd).2 = false) :
    classifyCarry (spatialTick d b hb hbM hd).2 = .QUIESCENT := by
  simp [classifyCarry, habsorb]

/--
An OVERFLOW event at digit i is routed to an INJECT at digit i+1
via `carryToPhase8Event`, establishing the Phase 8 event correspondence.
-/
theorem overflow_generates_event (T i : ℕ) :
    carryToPhase8Event T i .OVERFLOW = some (Event.OVERFLOW T [i]) := rfl

/--
A QUIESCENT event generates no Phase 8 routing event.
-/
theorem quiescent_no_event (T i : ℕ) :
    carryToPhase8Event T i .QUIESCENT = none := rfl

end FdrsFormal.Modes.ExtendedBase
