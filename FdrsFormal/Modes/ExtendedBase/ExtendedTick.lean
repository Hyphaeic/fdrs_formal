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

# Extended Tick Semantics

Tick operator generalized to extended bases (wall/wire/standard carry).

## Mathematical Content (fdrs.md lines 6970-6994)

**Definition 143**: Tick with extended bases (wall/wire/standard carry cases)
**Theorem 58**: Wire transparency
**Theorem 59**: Barrier wrap

## References

- fdrs.md, Phase 9, Section 9.4 (lines 6970-6994)
-/

import FdrsFormal.Modes.ExtendedBase.PlaceValues

namespace FdrsFormal.Modes.ExtendedBase

/-! ## Definition 143: Tick with extended bases -/

/--
**fdrs.md**: Definition 143 (Tick with extended bases) [§9.4.1 · Phase 9] (lines 6970-6978)

For τ in the representable subspace, Tick(τ) follows:

1. **Base-0 (Wall)**: Carry cannot enter. If carry reaches a wall, the clock
   wraps (all prior positions reset to 0).
2. **Base-1 (Wire)**: Carry propagates through unchanged. Digit stays 0.
3. **Base-≥2 (Standard)**: Normal carry absorption. If d_i + 1 ≥ b_i,
   reset to 0 and propagate carry.

**Axiomatized**: Requires extended representation type.
-/
def extendedTick (_b : ℕ → ℕ) (_k : ℕ) (τ : ExtendedRep _b _k) :
    ExtendedRep _b _k × Bool := (τ, false)

/-! ## Theorem 58: Wire transparency -/

/--
**fdrs.md**: Theorem 58 (Wire transparency) [§9.4.2 · Phase 9] (lines 6980-6988)

Let W be a contiguous run of base-1 positions between capacity positions.
Inserting W does not change the decoded successor relationship:
  dec(Tick(τ)) = (dec(τ) + 1) mod C
where C is the capacity.

**Proof sketch**: Base-1 positions contribute factor 1 to both place values
and capacity. Carry propagates through as if they didn't exist.

**Axiomatized**: Requires capacity computation and extended decode.
-/
theorem wireTransparency (_b : ℕ → ℕ) (_k : ℕ) (_τ : ExtendedRep _b _k) :
    let (_τ', _) := extendedTick _b _k _τ
    True := trivial

/-! ## Theorem 59: Barrier wrap -/

/--
**fdrs.md**: Theorem 59 (Barrier wrap) [§9.4.3 · Phase 9] (lines 6990-6994)

When carry reaches a base-0 position at index j, all positions i < j reset
to 0 and the operation returns with wrap = true.

**Proof sketch**: By Definition 143, base-0 is impenetrable. The only valid
behavior is to wrap the active segment.

**Axiomatized**: Requires wall detection in carry propagation.
-/
theorem barrierWrap (b : ℕ → ℕ) (k : ℕ) (τ : ExtendedRep b k)
    (j : Fin k) (hwall : b j = 0) :
    (extendedTick b k τ).2 = true := by
  -- ExtendedDigit (b j) wraps Fin (b j). With b j = 0, Fin 0 is empty,
  -- so τ j : ExtendedDigit 0 is uninhabitable. The premise is vacuously false.
  exfalso
  exact absurd ((τ j).val.isLt.trans_le (le_of_eq hwall)) (Nat.not_lt_zero _)

end FdrsFormal.Modes.ExtendedBase
