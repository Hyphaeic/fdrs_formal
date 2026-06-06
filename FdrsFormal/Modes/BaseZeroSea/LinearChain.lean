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

# Base-Zero Sea: Linear-Chain Operational Semantics (strengthened Theorem 64)

This file wires the abstract coupled-digit layer (`CoupledDigitNetwork`,
Definition 163) to the *proven* Phase 9 spatial-tick infrastructure, turning
Theorem 64 from the vacuous statement in `Modules.lean`
(`classicalMixedRadixLine`, whose conclusion is `… → True` plus a restated
hypothesis) into a genuine projection-equivalence — the exact analogue, one
layer up, of how Theorem 63 (`phase9_specialCase`) reduces to Theorem 61.

## Why a new state type is needed

`CoupledDigitNetwork` / `LinearChainConstraints` describe a *static* network
(module rules + couplings + disjointness); they carry no dynamic digit state,
so there is nothing for a `CoupledDigitNetwork → CoupledDigitNetwork` step to
"increment". We therefore bundle the chain constraints with the missing data —
per-module active radix `b i`, capacity `M i`, and a digit-vector state — into
a `LinearChain` machine. The step is then `LinearChain → LinearChain`, mirroring
how `SeaState` carries the occupancy that `seaTick` advances.

## Contents

1. `LinearChain` + `chainIncrement` + `linearChainStep` — the evaluator
   (deterministic mixed-radix increment-or-overflow, nearest-right carry).
2. `chainToCylinder` (Π_chain) — projection of each module's digit to a Phase 9
   spatial token position, mirroring `windowToDigitProjection`.
3. `chainIncrement_lt_b` / `linearChainStep_valid` — the validity lemma (the
   analogue of `cylinderValid_update`), used to *derive* output validity.
4. `linearChain_projectsTo_odometer` — the strengthened Theorem 64, fully
   proven (0 sorries) by induction reducing to the Phase 9 spatial tick.

## References

- fdrs.md, Phase 10, §10.9.1 (Theorem 64); §10.4.3 (Theorem 63, the template)
- Modules.lean (`CoupledDigitNetwork`, `LinearChainConstraints`, `classicalMixedRadixLine`)
- CarryRouteUnification.lean (`SpatialCylinder`, `unifiedSpatialTick`, `carry_is_overflow_route`)
- SpatialThermometer.lean (`SpatialDigit`, `spatialTick`, Theorem 60)
-/

import FdrsFormal.Modes.BaseZeroSea.Modules
import FdrsFormal.Modes.ExtendedBase.CarryRouteUnification

namespace FdrsFormal.Modes.BaseZeroSea

open FdrsFormal.Modes.ExtendedBase

/-! ## 1. The evaluator: a linear chain as a stateful machine -/

/--
A **linear chain machine**: a chain-constrained coupled-digit network
(`LinearChainConstraints`, Definition 163 restricted to a single ordered
lineage) bundled with the data the abstract layer lacks — active radix `b i`,
cell-chain capacity `M i`, and the dynamic digit state `digits i`.
-/
structure LinearChain (n : ℕ) extends LinearChainConstraints n where
  /-- Active radix (wall position) of each module. -/
  b : Fin n → ℕ
  /-- Cell-chain capacity of each module's spatial digit. -/
  M : Fin n → ℕ
  /-- Each active radix is at least 1 (arithmetic digit, not a base-0 wall). -/
  hb : ∀ i, 1 ≤ b i
  /-- Each active radix fits within its capacity. -/
  hbM : ∀ i, b i ≤ M i
  /-- Current digit value (sustained occupancy depth) of each module. -/
  digits : Fin n → ℕ

/--
Abstract mixed-radix **increment-or-overflow** with nearest-right carry,
starting at position `pos` with incoming carry `carry_in`. The digit-vector
counterpart of `unifiedSpatialTick`: advance the active digit if it is below its
wall, otherwise wrap it to `0` and propagate the carry one step right.
-/
def chainIncrement {n : ℕ} (b : Fin n → ℕ) (d : Fin n → ℕ)
    (pos : ℕ) (carry_in : Bool) : Fin n → ℕ :=
  if hpos : pos < n then
    if carry_in then
      let i : Fin n := ⟨pos, hpos⟩
      if d i + 1 < b i then
        fun j => if j = i then d i + 1 else d j
      else
        chainIncrement b (fun j => if j = i then 0 else d j) (pos + 1) true
    else
      d
  else
    d
termination_by n - pos

/-- One deterministic step of the chain: a single mixed-radix `+1`. -/
def linearChainStep {n : ℕ} (lc : LinearChain n) : LinearChain n :=
  { lc with digits := chainIncrement lc.b lc.digits 0 true }

/-! ## 2. The projection: Π_chain -/

/--
**Π_chain**: project the chain's digit vector into a Phase 9 spatial cylinder,
sending each module's digit value to a one-hot token position. Mirrors
`windowToDigitProjection` (the Theorem 63 bridge); faithful when every digit
lies within its capacity (`hv`).
-/
def chainToCylinder {n : ℕ} (lc : LinearChain n)
    (hv : ∀ i, lc.digits i < lc.M i) : SpatialCylinder lc.M :=
  fun i => ⟨⟨lc.digits i, hv i⟩⟩

@[simp]
theorem chainToCylinder_tokenPos {n : ℕ} (lc : LinearChain n)
    (hv : ∀ i, lc.digits i < lc.M i) (i : Fin n) :
    (chainToCylinder lc hv i).tokenPos.val = lc.digits i := rfl

/-! ## 3. The validity lemma (analogue of `cylinderValid_update`) -/

/-- `chainIncrement` preserves active-zone validity: if every input digit is
    below its wall, so is every output digit. -/
theorem chainIncrement_lt_b {n : ℕ} (b : Fin n → ℕ) (hb : ∀ i, 1 ≤ b i)
    (d : Fin n → ℕ) (hd : ∀ i, d i < b i) (pos : ℕ) (carry_in : Bool) (i : Fin n) :
    chainIncrement b d pos carry_in i < b i := by
  unfold chainIncrement
  by_cases hpos : pos < n
  · rw [dif_pos hpos]
    cases carry_in with
    | false => simp only [Bool.false_eq_true, if_false]; exact hd i
    | true =>
      simp only [if_true]
      set i₀ : Fin n := ⟨pos, hpos⟩ with hi₀
      by_cases hadv : d i₀ + 1 < b i₀
      · simp only [hadv, if_true]
        by_cases hii : i = i₀
        · rw [if_pos hii, hii]; exact hadv
        · rw [if_neg hii]; exact hd i
      · simp only [hadv, if_false]
        refine chainIncrement_lt_b b hb (fun j => if j = i₀ then 0 else d j) ?_ (pos + 1) true i
        intro k
        show (if k = i₀ then (0 : ℕ) else d k) < b k
        by_cases hkk : k = i₀
        · rw [if_pos hkk, hkk]; exact hb i₀
        · rw [if_neg hkk]; exact hd k
  · rw [dif_neg hpos]; exact hd i
termination_by n - pos

/-- `linearChainStep` preserves active-zone validity. -/
theorem linearChainStep_valid {n : ℕ} (lc : LinearChain n)
    (hvalid : ∀ i, lc.digits i < lc.b i) (i : Fin n) :
    (linearChainStep lc).digits i < lc.b i :=
  chainIncrement_lt_b lc.b lc.hb lc.digits hvalid 0 true i

/-! ## 4. Spatial-tick computation lemmas -/

/-- The token position produced by `spatialTick`. -/
theorem spatialTick_fst_tokenPos {M : ℕ} (d : SpatialDigit M) (b : ℕ)
    (hb : 1 ≤ b) (hbM : b ≤ M) (hd : d.tokenPos.val < b) :
    (spatialTick d b hb hbM hd).1.tokenPos.val
      = if d.tokenPos.val + 1 < b then d.tokenPos.val + 1 else 0 := by
  unfold spatialTick; split <;> simp_all

/-- The carry produced by `spatialTick`. -/
theorem spatialTick_snd {M : ℕ} (d : SpatialDigit M) (b : ℕ)
    (hb : 1 ≤ b) (hbM : b ≤ M) (hd : d.tokenPos.val < b) :
    (spatialTick d b hb hbM hd).2 = decide ¬(d.tokenPos.val + 1 < b) := by
  unfold spatialTick; split <;> simp_all

/-- A `unifiedSpatialTick` with no incoming carry is the identity on the
    cylinder (no digit changes). -/
theorem unifiedSpatialTick_false {n : ℕ} (M b : Fin n → ℕ)
    (hb : ∀ i, 1 ≤ b i) (hbM : ∀ i, b i ≤ M i)
    (cyl : SpatialCylinder M) (hvalid : cylinderValid b M cyl) (pos : ℕ) :
    unifiedSpatialTick M b hb hbM cyl hvalid pos false = (cyl, false) := by
  unfold unifiedSpatialTick
  split <;> simp

/-! ## 5. Core induction: chain step projects to the spatial tick -/

/-- **Core lemma.** When `cyl` projects digit vector `d` (token positions equal
    `d`), the token positions of `unifiedSpatialTick` agree with `chainIncrement`
    at every position and carry. Induction on `n - pos`, closed in the carry
    step by the route-decision identity `carryRouteDecision_eq_carry`. -/
theorem unifiedSpatialTick_tokenPos_eq {n : ℕ} (M b : Fin n → ℕ)
    (hb : ∀ i, 1 ≤ b i) (hbM : ∀ i, b i ≤ M i)
    (cyl : SpatialCylinder M) (hvalid : cylinderValid b M cyl)
    (d : Fin n → ℕ) (hcyl : ∀ j, (cyl j).tokenPos.val = d j)
    (pos : ℕ) (carry_in : Bool) (i : Fin n) :
    ((unifiedSpatialTick M b hb hbM cyl hvalid pos carry_in).1 i).tokenPos.val
      = chainIncrement b d pos carry_in i := by
  unfold unifiedSpatialTick chainIncrement
  by_cases hpos : pos < n
  · rw [dif_pos hpos, dif_pos hpos]
    cases carry_in with
    | false => simp only [if_false, Bool.false_eq_true]; exact hcyl i
    | true =>
      simp only [if_true]
      set i₀ : Fin n := ⟨pos, hpos⟩ with hi₀
      have hci₀ : (cyl i₀).tokenPos.val = d i₀ := hcyl i₀
      simp only [carryRouteDecision_eq_carry]
      rw [spatialTick_snd]
      by_cases hadv : d i₀ + 1 < b i₀
      · -- advance: carry stops; unified collapses via `unifiedSpatialTick_false`
        rw [hci₀]
        simp only [hadv, not_true_eq_false, decide_false]
        rw [unifiedSpatialTick_false]
        simp only [if_true]
        by_cases hii : i = i₀
        · subst hii
          rw [cylinderUpdate_at, spatialTick_fst_tokenPos, hci₀]
          simp only [hadv, if_pos]
        · rw [cylinderUpdate_ne _ _ _ _ hii, if_neg hii]
          exact hcyl i
      · -- wrap: carry propagates; recurse via the IH
        rw [hci₀]
        simp only [hadv, not_false_eq_true, decide_true]
        simp only [if_false]
        apply unifiedSpatialTick_tokenPos_eq
        intro j
        by_cases hjj : j = i₀
        · subst hjj
          rw [cylinderUpdate_at, spatialTick_fst_tokenPos, hci₀]
          simp only [hadv, if_false, if_pos]
        · rw [cylinderUpdate_ne _ _ _ _ hjj, if_neg hjj]
          exact hcyl j
  · rw [dif_neg hpos, dif_neg hpos]
    exact hcyl i
termination_by n - pos

/-! ## 6. Theorem 64 (strengthened): the chain step projects to the odometer -/

/--
**Theorem 64 (faithful form)** — fdrs.md §10.9.1.

The linear-chain step, projected to the Phase 9 spatial cylinder, equals the
Phase 9 unified spatial tick (`unifiedSpatialTick`, Definition 150). This is the
genuine "classical mixed-radix line as a single-lineage special case" statement
that `classicalMixedRadixLine` (Modules.lean) only asserts vacuously: the
abstract increment-or-overflow on the coupled-digit chain *commutes with the
projection* into the proven spatial-tick semantics — the exact analogue of
Theorem 63 (`phase9_specialCase`) one layer up.

The only hypothesis is input active-zone validity (`hvalid : ∀ i, digits i <
b i`); the output validity and the `cylinderValid` premise are *derived* via
`linearChainStep_valid`.
-/
theorem linearChain_projectsTo_odometer {n : ℕ} (lc : LinearChain n)
    (hvalid : ∀ i, lc.digits i < lc.b i) :
    chainToCylinder (linearChainStep lc)
        (fun i => lt_of_lt_of_le (linearChainStep_valid lc hvalid i) (lc.hbM i))
      = (unifiedSpatialTick lc.M lc.b lc.hb lc.hbM
          (chainToCylinder lc (fun i => lt_of_lt_of_le (hvalid i) (lc.hbM i)))
          hvalid 0 true).1 := by
  funext i
  apply SpatialDigit.ext
  apply Fin.ext
  rw [chainToCylinder_tokenPos]
  show chainIncrement lc.b lc.digits 0 true i = _
  exact (unifiedSpatialTick_tokenPos_eq lc.M lc.b lc.hb lc.hbM
    (chainToCylinder lc (fun i => lt_of_lt_of_le (hvalid i) (lc.hbM i)))
    hvalid lc.digits (fun _ => rfl) 0 true i).symm

end FdrsFormal.Modes.BaseZeroSea
