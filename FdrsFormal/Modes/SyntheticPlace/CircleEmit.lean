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

# Feasibility probe — floor-free certified emission on the circle

The keystone for a certified SE(2) pose engine: SE(2) = rotation (a *circle*, wrapping, no
global order) ⊕ translation (ordered ℝ², the Gosper `BihTensor` FLOOR-emission) ⊕ their
bilinear coupling. The open piece is the rotation half — a CERTIFIED emission with **no floor**
(the corpus's standing "what is *emit* with no floor?" gate; the §9.6 Base-0-Sea instantiation
trigger). This probe demonstrates that keystone is FEASIBLE, as the faithful wrap-analogue of
`BihomographicSound.emit_traps`.

THE CORRESPONDENCE:
| | `emit_traps` (Archimedean, built) | here (circle, floor-free) |
|---|---|---|
| value | bilinear `N/D` over tails `x,y≥1` | a position on the circle `ℤ/(M·cellWidth)` |
| cell | FLOOR interval `[k, k+1)` | cyclic SECTOR `k` (one of `M`) |
| digit | `k ∈ ℤ`, unbounded | `k ∈ [0,M)`, **WRAPS** (the base-0 wall) |
| certified by | both tail-corners agree on the floor | both arc-endpoints agree on the sector |
| needs | `IsStrictOrderedRing` (a floor) | NO order — cyclic cell-membership + a no-wall-crossing bound |
| trap | value `∈ [k,k+1)` ∀ tails | value `∈ sector k` ∀ values in the arc |

`emitSector_sound` is the wrap-analogue of `emit_traps`; `wall_wraps` is the base-0 wall. The
no-wall-crossing bound (`lo+w < circ`) substitutes for the floor's monotonicity: it is what
makes a finite endpoint check certify the whole *cyclic* arc, with no order in sight. At a
sector boundary or the wall the engine REFUSES (`none`) — the circle analogue of `√2·√2 → []`.

**Honest scope.** This is HALF an SE(2) pose digit (the rotation). Coupling it to the
translation `BihTensor` (the bilinear `c·t'`) and discharging the `⊆` over-approximation
obligations of `SE2Pose.TractablePose` is the NEXT step — NOT done here. The contribution is
that the floor-free-emission gate is *closable* on the circle, machine-checked, with a precise
floor↔wrap correspondence — not the engine, and no new theorem (the cyclic cell trap is
elementary). Leaf module. No `sorry`; axiom-clean.
-/
import Mathlib.Tactic.NormNum

namespace FdrsFormal.Modes.SyntheticPlace

namespace CircleEmit

/-- The circumference: `M` sectors of `cellWidth` each. -/
def circ (cellWidth M : ℕ) : ℕ := M * cellWidth

/-- The cyclic sector (cell) of a position — **floor-free**: the digit is a CYCLIC index in
`[0, M)`, the position WRAPS `mod circ` (the base-0 wall), and the cell is read by `/ cellWidth`.
There is no global order on the circle to take a floor against. -/
def sector (cellWidth M p : ℕ) : ℕ := (p % circ cellWidth M) / cellWidth

/-- **Certified floor-free emission.** From a belief arc `[lo, lo+w]` (the value, given the
unread tail, lies in this arc), emit sector `k` iff both endpoints agree on the sector AND the
arc stays within one period (`lo+w < circ` — it does not cross the base-0 wall). `none` =
REFUSE (the arc straddles a sector boundary or the wall). -/
def emitSector (cellWidth M lo w : ℕ) : Option ℕ :=
  if lo + w < circ cellWidth M ∧ sector cellWidth M lo = sector cellWidth M (lo + w)
  then some (sector cellWidth M lo) else none

/-- **THE KEYSTONE — the wrap-analogue of `emit_traps`.** If the emission certifies sector `k`,
then for EVERY value `v` in the belief arc `[lo, lo+w]`, the true sector is `k`: the value is
trapped in the sector. No floor — only the cyclic cell quotient and the no-wall-crossing bound
(which replaces the Archimedean floor's monotonicity in `emit_traps`). -/
theorem emitSector_sound (cellWidth M lo w k v : ℕ)
    (hemit : emitSector cellWidth M lo w = some k)
    (hlv : lo ≤ v) (hvw : v ≤ lo + w) : sector cellWidth M v = k := by
  unfold emitSector at hemit
  -- `split_ifs` keeps only the certified (`if`-true) branch; the `none = some k`
  -- branch is the engine REFUSING, discharged automatically as a contradiction.
  split_ifs at hemit with hcond
  obtain ⟨hlt, hsec⟩ := hcond
  injection hemit with hk
  have hvcirc : v < circ cellWidth M := by omega
  have hlocirc : lo < circ cellWidth M := by omega
  have e1 : sector cellWidth M lo = lo / cellWidth := by
    simp only [sector, Nat.mod_eq_of_lt hlocirc]
  have e2 : sector cellWidth M (lo + w) = (lo + w) / cellWidth := by
    simp only [sector, Nat.mod_eq_of_lt hlt]
  have e3 : sector cellWidth M v = v / cellWidth := by
    simp only [sector, Nat.mod_eq_of_lt hvcirc]
  rw [e1] at hk hsec
  rw [e2] at hsec
  rw [e3]
  have m1 : lo / cellWidth ≤ v / cellWidth := Nat.div_le_div_right hlv
  have m2 : v / cellWidth ≤ (lo + w) / cellWidth := Nat.div_le_div_right hvw
  omega

/- ===========================================================================
   The base-0 wall (the wrap) + emission demos, machine-checked
   =========================================================================== -/

-- `M = 4` sectors of width `cellWidth = 3` ⇒ `circ = 12`.
#eval sector 3 4 0    -- 0
#eval sector 3 4 11   -- 3   (the last sector)
#eval sector 3 4 12   -- 0   ← THE WRAP: position 12 ≡ 0 (the base-0 wall resets the sector)
#eval sector 3 4 13   -- 0

/-- **The base-0 wall, machine-checked.** Crossing the circumference wraps the sector to `0` —
the cyclic, floor-free behaviour a floor (`emit_traps`) cannot have. -/
theorem wall_wraps : sector 3 4 12 = sector 3 4 0 := by norm_num [sector, circ]

-- Emission: certify within a sector, refuse at a boundary.
#eval emitSector 3 4 0 2   -- some 0  (arc [0,2] ⊆ sector 0 ⇒ forced)
#eval emitSector 3 4 2 2   -- none    (arc [2,4] straddles sector 0|1 ⇒ REFUSE — the √2·√2 move)

/-- A certified emission, machine-checked: arc `[0,2]` forces sector `0`. -/
theorem emit_demo : emitSector 3 4 0 2 = some 0 := by norm_num [emitSector, sector, circ]

/-- A refusal, machine-checked: arc `[2,4]` straddles the `0|1` sector boundary ⇒ no digit. -/
theorem refuse_demo : emitSector 3 4 2 2 = none := by norm_num [emitSector, sector, circ]

end CircleEmit

end FdrsFormal.Modes.SyntheticPlace
