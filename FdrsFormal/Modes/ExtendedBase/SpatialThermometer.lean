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

# Spatial Thermometer Encoding

Physicalizes a mixed-radix digit as a one-hot token on a chain of cells
with a movable radix wall.

## Mathematical Content (fdrs.md lines 7082-7124)

**Definition 145**: Spatial digit capacity — one-hot token on M cells
**Definition 146**: Spatial tick — advance or wrap within active zone [0, b)
**Definition 147**: Spatial radix wall — wall position determines base type
**Theorem 60**: Spatial-algebraic isomorphism — commutative diagram

## References

- fdrs.md, Phase 9, Section 9.8 (lines 7082-7124)
- DEPENDENCY_BASED_STRUCTURE.md, Tier 21
-/

import FdrsFormal.Modes.ExtendedBase.Definition

namespace FdrsFormal.Modes.ExtendedBase

/-! ## Definition 145: Spatial digit capacity -/

/--
**fdrs.md**: Definition 145 (Spatial digit capacity) [§9.8.1 · Phase 9] (lines 7086-7092)

A spatial digit with capacity M is a one-hot token on a chain of M cells.
Isomorphic to `Fin M` and, when restricted to the active zone `[0, b)`,
to `ExtendedDigit b`.
-/
structure SpatialDigit (M : ℕ) where
  tokenPos : Fin M

@[ext]
theorem SpatialDigit.ext {M : ℕ} {d₁ d₂ : SpatialDigit M}
    (h : d₁.tokenPos = d₂.tokenPos) : d₁ = d₂ := by
  cases d₁; cases d₂; simp_all

/-! ## Definition 146: Spatial tick -/

/--
**fdrs.md**: Definition 146 (Spatial tick) [§9.8.2 · Phase 9] (lines 7094-7100)

Given a spatial digit with token at position p in the active zone [0, b):
- No carry: If p + 1 < b, advance to p + 1. carry = false.
- Carry (wrap): If p + 1 ≥ b, wrap to 0. carry = true.

Requires 1 ≤ b ≤ M and p < b (token is in active zone).
-/
def spatialTick {M : ℕ} (d : SpatialDigit M) (b : ℕ) (hb : 1 ≤ b)
    (hbM : b ≤ M) (hd : d.tokenPos.val < b) : SpatialDigit M × Bool :=
  if h : d.tokenPos.val + 1 < b then
    (⟨⟨d.tokenPos.val + 1, by omega⟩⟩, false)
  else
    (⟨⟨0, by omega⟩⟩, true)

/-! ## Definition 147: Spatial radix wall -/

/--
**fdrs.md**: Definition 147 (Spatial radix wall) [§9.8.3 · Phase 9] (lines 7102-7110)

A radix wall at position b ≤ M restricts the active zone to [0, b):
- b = 0 → Wall (Base-0): no active cells
- b = 1 → Wire (Base-1): one cell, token fixed at 0
- b ≥ 2 → Standard: full digit with b states

The wall position IS the radix. Moving the wall implements instantiation.
-/
def spatialRadixWall (_M b : ℕ) : ℕ := b

/-! ## Algebraic single-digit tick -/

/--
Single-digit algebraic tick on `ExtendedDigit b`: increment or wrap with carry.
This is the algebraic counterpart of `spatialTick`, operating on the abstract
digit type rather than the spatial chain.
-/
def algebraicTick {b : ℕ} (d : ExtendedDigit b) (hb : 1 ≤ b) :
    ExtendedDigit b × Bool :=
  if h : d.val.val + 1 < b then
    (⟨⟨d.val.val + 1, h⟩⟩, false)
  else
    (⟨⟨0, by omega⟩⟩, true)

/-! ## Projection maps -/

/--
Project a spatial digit into the algebraic digit space by restricting
the token position from `Fin M` to `Fin b`.
Requires the token to be in the active zone: `tokenPos < b`.
-/
def spatialToAlgebraic {M : ℕ} (d : SpatialDigit M) (b : ℕ)
    (hd : d.tokenPos.val < b) : ExtendedDigit b :=
  ⟨⟨d.tokenPos.val, hd⟩⟩

/--
Embed an algebraic digit into the spatial chain.
Requires `b ≤ M` so that `Fin b` embeds into `Fin M`.
-/
def algebraicToSpatial {M : ℕ} (d : ExtendedDigit b)
    (hbM : b ≤ M) : SpatialDigit M :=
  ⟨⟨d.val.val, by omega⟩⟩

/-! ## Theorem 60: Spatial-algebraic isomorphism -/

/--
**fdrs.md**: Theorem 60 (Spatial-algebraic isomorphism) [§9.8.4 · Phase 9] (lines 7112-7124)

The following diagram commutes:
```
SpatialDigit(M) --spatialTick--> SpatialDigit(M) × Bool
      |                                |
    proj                          proj × id
      |                                |
      v                                v
ExtendedDigit(b) --algebraicTick--> ExtendedDigit(b) × Bool
```

Proof: Case split on wrap vs no-wrap. Both branches project identically.
-/
theorem spatialAlgebraicIsomorphism {M : ℕ} (d : SpatialDigit M) (b : ℕ)
    (hb : 1 ≤ b) (hbM : b ≤ M) (hd : d.tokenPos.val < b) :
    ((spatialTick d b hb hbM hd).1.tokenPos.val,
     (spatialTick d b hb hbM hd).2) =
    ((algebraicTick (spatialToAlgebraic d b hd) hb).1.val.val,
     (algebraicTick (spatialToAlgebraic d b hd) hb).2) := by
  simp only [spatialTick, algebraicTick, spatialToAlgebraic]
  split <;> simp_all

/-! ## Round-trip theorems -/

/-- Projecting an embedded algebraic digit recovers the original. -/
theorem spatialToAlgebraic_algebraicToSpatial {M b : ℕ} (d : ExtendedDigit b)
    (hbM : b ≤ M) :
    spatialToAlgebraic (algebraicToSpatial d hbM) b
      (by simp [algebraicToSpatial]) = d := by
  simp [spatialToAlgebraic, algebraicToSpatial]

/-- Embedding a projected spatial digit recovers the original (when token is in active zone). -/
theorem algebraicToSpatial_spatialToAlgebraic {M : ℕ} (d : SpatialDigit M) (b : ℕ)
    (hbM : b ≤ M) (hd : d.tokenPos.val < b) :
    algebraicToSpatial (spatialToAlgebraic d b hd) hbM = d := by
  simp [spatialToAlgebraic, algebraicToSpatial]

end FdrsFormal.Modes.ExtendedBase
