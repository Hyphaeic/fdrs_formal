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

# Synthetic place complex SU6c′ — the window boundary, CLOSED (alternating machine)

Closes the "window boundary beyond three points" row of
`docs/synthetic-place/03-digit-coupling.md` §7 — for the strict-alternation
machine, as a full characterization. The right invariant is not a window taxonomy
but a single uniformity condition:

* **`GrantUniform`** — the grant agrees across co-reachable contexts with the same
  source prefix: what A's books *must not depend on* is exactly the partner data
  that varies while A's own view stays fixed.
* **`issued_placeLocal_iff_grantUniform`** — **THE BOUNDARY THEOREM**: the carry
  charge is place-locally accountable **iff** the coupling is grant-uniform. The
  forward direction is two applications of the exactness equation (sharper than the
  rectangle argument of Theorem 90 — no factorization needed); the converse defines
  the transfer rule by choice over reachable contexts and discharges it by
  uniformity.
* The calibrated points fall out as corollaries: clock windows are uniform
  (`grantUniform_of_lengthWindow` — the shared clock means same-`sA` co-reachable
  contexts have same-length `sB`s), so SU6c's theorem is subsumed; the bilateral
  content window is NOT uniform (`jointFiber_not_grantUniform` — two co-reachable
  contexts, grants 2 vs 3, kernel-checked), recovering Theorem 90's no-go through
  the iff.

So on the alternating machine: **accountable ⟺ the grant cannot distinguish
co-reachable partner states** — and since alternation pins the partner's length
(`reachable_length`), the deducible data is exactly the clock; everything beyond it
breaks accounting. The clock-deducibility conjecture is RESOLVED for this
discipline.

**Honest scope.** The characterization is relative to the strict-alternation,
capacity-one machine: its reachable set determines which contexts "co-reachable"
ranges over. Under free scheduling the partner's clock is no longer deducible and
the boundary question reopens — that is the network arc's territory
(`04-network-config.md`). Leaf module over SU6c. No `sorry`; axiom-clean. -/
import FdrsFormal.Modes.SyntheticPlace.WindowAccountability

namespace FdrsFormal.Modes.SyntheticPlace

/-! ## 1. Grant uniformity -/

/-- **Grant uniformity**: across any two reachable, ready-to-issue configurations
with the SAME source prefix, the grant is the same — the coupling cannot read
whatever partner data varies while the source's own view is fixed. -/
def GrantUniform (C : CoupledFiber) : Prop :=
  ∀ cfg cfg' : CoupledConfig, Reachable C cfg → Reachable C cfg' →
    cfg.pending = none → cfg'.pending = none → cfg.sA = cfg'.sA →
    ∀ a, a < C.fiberA cfg.sA →
      C.fiberB cfg.sB (cfg.sA ++ [a]) = C.fiberB cfg'.sB (cfg'.sA ++ [a])

/-- Clock windows are grant-uniform: the shared clock (`reachable_length`) makes
same-`sA` co-reachable contexts carry same-length partner prefixes. -/
theorem grantUniform_of_lengthWindow (C : CoupledFiber) (h : LengthWindow C) :
    GrantUniform C := by
  obtain ⟨F, hF⟩ := h
  intro cfg cfg' hr hr' hp hp' hsa a _
  have l1 := (reachable_length hr).1 hp
  have l2 := (reachable_length hr').1 hp'
  rw [hF, hF, ← l1, ← l2, hsa]

/-! ## 2. The boundary theorem -/

/-- The canonical source-side transfer rule: the grant at any reachable context with
this source prefix (well-defined under uniformity; junk `0` off the reachable set). -/
noncomputable def canonicalTauA (C : CoupledFiber) (sA : List ℕ) (a : ℕ) : ℤ := by
  classical
  exact if h : ∃ cfg : CoupledConfig,
      Reachable C cfg ∧ cfg.pending = none ∧ cfg.sA = sA
    then (C.fiberB (Classical.choose h).sB (sA ++ [a]) : ℤ)
    else 0

/-- **SU6c′ — THE BOUNDARY THEOREM (alternating machine, closed).** The carry charge
admits a place-local transfer rule **iff** the coupling is grant-uniform. Reading
the partner's clock is free (alternation broadcasts it); reading anything that
varies across co-reachable same-source contexts is exactly what breaks one-sided
accounting. -/
theorem issued_placeLocal_iff_grantUniform (C : CoupledFiber) :
    (∃ τA τB, PlaceLocalExact C issuedCharge τA τB) ↔ GrantUniform C := by
  constructor
  · rintro ⟨τA, τB, hA, hB⟩ cfg cfg' hr hr' hp hp' hsa a ha
    have ha' : a < C.fiberA cfg'.sA := by rwa [hsa] at ha
    have e1 := hA cfg a hr ha hp
    have e2 := hA cfg' a hr' ha' hp'
    simp only [issuedCharge, applyA] at e1 e2
    push_cast at e1 e2
    have g1 : (C.fiberB cfg.sB (cfg.sA ++ [a]) : ℤ) = τA cfg.sA a := by linarith
    have g2 : (C.fiberB cfg'.sB (cfg'.sA ++ [a]) : ℤ) = τA cfg'.sA a := by linarith
    rw [hsa] at g1
    have hZ : (C.fiberB cfg.sB (cfg'.sA ++ [a]) : ℤ)
        = (C.fiberB cfg'.sB (cfg'.sA ++ [a]) : ℤ) := by
      rw [g1, g2]
    rw [hsa]
    exact_mod_cast hZ
  · intro hu
    refine ⟨canonicalTauA C, fun _ _ => 0, ?_, ?_⟩
    · intro cfg a hr ha hp
      have hex : ∃ c0 : CoupledConfig,
          Reachable C c0 ∧ c0.pending = none ∧ c0.sA = cfg.sA := ⟨cfg, hr, hp, rfl⟩
      simp only [issuedCharge, applyA, canonicalTauA]
      rw [dif_pos hex]
      obtain ⟨hr0, hp0, hsa0⟩ := Classical.choose_spec hex
      have huni := hu (Classical.choose hex) cfg hr0 hr hp0 hp hsa0 a
        (by rw [hsa0]; exact ha)
      rw [hsa0] at huni
      rw [huni]
      push_cast
      ring
    · intro cfg b g hr hp hb
      simp only [issuedCharge, applyB]
      ring

/-! ## 3. The calibrated points, recovered through the iff -/

/-- Clock windows are accountable — SU6c, subsumed (its explicit `τA` remains the
constructive version). -/
theorem issued_placeLocal_of_lengthWindow' (C : CoupledFiber) (h : LengthWindow C) :
    ∃ τA τB, PlaceLocalExact C issuedCharge τA τB :=
  (issued_placeLocal_iff_grantUniform C).mpr (grantUniform_of_lengthWindow C h)

/-- The bilateral content window is NOT grant-uniform: two co-reachable contexts
with the same source prefix `[0]` and partner prefixes `[0]` vs `[1]` carry grants
`2` vs `3` (kernel-checked) — through the iff, Theorem 90's no-go, recovered without
the rectangle. -/
theorem jointFiber_not_grantUniform : ¬ GrantUniform jointFiber := by
  intro h
  have c1 : Reachable jointFiber (applyB (applyA jointFiber initConfig 0) 0) :=
    Reachable.stepB (g := 3)
      (Reachable.stepA Reachable.init 0 (by decide) (by decide)) 0 (by decide) (by decide)
  have c2 : Reachable jointFiber (applyB (applyA jointFiber initConfig 0) 1) :=
    Reachable.stepB (g := 3)
      (Reachable.stepA Reachable.init 0 (by decide) (by decide)) 1 (by decide) (by decide)
  have h23 := h _ _ c1 c2 rfl rfl rfl 0 (by decide)
  exact absurd h23 (by decide)

end FdrsFormal.Modes.SyntheticPlace
