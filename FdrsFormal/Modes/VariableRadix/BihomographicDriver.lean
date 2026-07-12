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

# Bihomographic driver — the two-stream scheduler (liveness)

The scheduler that turns the verified `BihTensor` primitives into a running engine: it
reads partial quotients from the two input streams (A and B) and emits the output
stream (C). The decision is exactly Gosper's: **emit** when `emitReady` fires (the
output digit is forced — certified by `emit_traps`), otherwise **absorb** the next
quotient, alternating between A and B.

The emission *correctness* is the proven `emit_traps` (the 4-corner bound); the
*scheduling* (when to read vs write, alternation, fuel) is engineering. The two are
cleanly separable precisely because `emit_traps` seals the primitive — the driver can
interleave reads and writes in any order (the commutations) and emit only when forced.
-/
import FdrsFormal.Modes.VariableRadix.BihomographicSound

namespace FdrsFormal.Modes.VariableRadix.BihTensor

/-- Run the two-stream mediator: given input partial-quotient lists `xs` (Timeline A)
and `ys` (Timeline B), an alternation `turn`, and a `fuel` bound, produce the output
quotient stream (Timeline C). Emits when `emitReady`; otherwise absorbs the next
quotient, alternating A/B and falling back to whichever stream is non-empty.

**fdrs.md**: Definition 190 (The two-stream driver) [§13.6.6 · Phase 13] -/
def run (T : BihTensor) (xs ys : List ℤ) (turn : Bool) : ℕ → List ℤ
  | 0 => []
  | fuel + 1 =>
    if emitReady T then
      emitDigit T :: run (emit (emitDigit T) T) xs ys turn fuel
    else if turn then
      match xs with
      | x :: xs' => run (absorbX x T) xs' ys false fuel
      | [] =>
        match ys with
        | y :: ys' => run (absorbY y T) [] ys' true fuel
        | [] => []
    else
      match ys with
      | y :: ys' => run (absorbY y T) xs ys' true fuel
      | [] =>
        match xs with
        | x :: xs' => run (absorbX x T) xs' [] false fuel
        | [] => []

/-- `z = x + y` mediator: numerator `x + y`, denominator `1`. -/
def addTensor : BihTensor := ⟨0, 1, 1, 0, 0, 0, 0, 1⟩

/-- `z = x · y` mediator: numerator `xy`, denominator `1`. -/
def mulTensor : BihTensor := ⟨1, 0, 0, 0, 0, 0, 0, 1⟩

/-! ## Demonstrations — exact two-stream irrational arithmetic, density-free

`φ = [1;1,1,…]`, `√2 = [1;2,2,…]`. The engine computes the operation exactly in `ℤ`. -/

-- φ + φ = 2φ = 1+√5 = [3;4,4,…]
#eval run addTensor (List.replicate 25 1) (List.replicate 25 1) true 40   -- [3, 4, 4, 4, 4]
-- φ · φ = φ+1 = (3+√5)/2 = [2;1,1,…]
#eval run mulTensor (List.replicate 25 1) (List.replicate 25 1) true 40   -- [2, 1, 1, 1, …]
-- √2 + √2 = 2√2 = [2;1,4,1,4,…]
#eval run addTensor (1 :: List.replicate 25 2) (1 :: List.replicate 25 2) true 40  -- [2, 1, 4, 1, 4, …]
-- √2 · √2 = 2, EXACTLY on the floor-1/floor-2 boundary: undecidable from finite input,
-- so the engine SAFELY refuses to emit (this is `emit_traps` preventing a hallucinated digit).
#eval run mulTensor (1 :: List.replicate 25 2) (1 :: List.replicate 25 2) true 60  -- []

end FdrsFormal.Modes.VariableRadix.BihTensor
