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
Authors: [Your Name]

# Tick Operator (Mixed-Radix Increment)

This file defines the Tick operator (mixed-radix increment with carry) and proves
that it corresponds to +1 in decoded coordinates (Theorem 2).

## References

- fdrs.md, Phase 1 Fragment 1, Definitions 4.1-4.3, Proposition 2, Theorem 2
-/

import FdrsFormal.Core.Infinite

namespace FdrsFormal.Operations.Tick

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite FdrsFormal.Core.Infinite

variable {b : RadixSeq}

/-! ## Definition 6: Tick on the direct-limit space -/

/-- The Tick operator T : R^(∞)_fin → R^(∞)_fin defined as T(τ) := enc(dec(τ) + 1) -/
noncomputable def tick (b : RadixSeq) (τ : DirectLimitSpace b) : DirectLimitSpace b :=
  encode b (decode b τ + 1)

/-! ## Theorem 2: Tick matches successor -/

/-- **Theorem 2**: dec(T(τ)) = dec(τ) + 1 -/
theorem tick_decode (τ : DirectLimitSpace b) :
    decode b (tick b τ) = decode b τ + 1 := by
  simp only [tick]
  exact decode_encode (decode b τ + 1)

theorem tick_zero : tick b (0 : DirectLimitSpace b) = encode b 1 := by
  simp only [tick, decode_zero, Nat.zero_add]

theorem tick_injective : Function.Injective (tick b) := by
  intro τ σ h
  apply decode_injective
  have h1 : decode b (tick b τ) = decode b τ + 1 := tick_decode τ
  have h2 : decode b (tick b σ) = decode b σ + 1 := tick_decode σ
  have h3 : decode b (tick b τ) = decode b (tick b σ) := by rw [h]
  rw [h1, h2] at h3
  exact Nat.succ_injective h3

theorem tick_lt (τ : DirectLimitSpace b) : τ < tick b τ := by
  show decode b τ < decode b (tick b τ)
  rw [tick_decode]
  exact Nat.lt_succ_self _

end FdrsFormal.Operations.Tick
