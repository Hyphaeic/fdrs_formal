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

# Synthetic place complex SU6c — window accountability (the lattice meets the boundary)

Third stone of the digit-coupling layer (`docs/synthetic-place/03-digit-coupling.md`
§windows). A coupling rule declares a **window** — what the grant may read of the
partner: nothing (blind), the partner's clock (length), or the partner's content
(digits). SU4c located the accountability boundary at two points: blind windows are
place-locally accountable (`issued_placeLocal_of_blind`), content windows are not
(`issued_not_placeLocal`). This file adds the intermediate point, and it lands on the
accountable side for a structural reason worth stating:

* **`reachable_length`** — the alternation discipline is a SHARED CLOCK: on every
  reachable configuration, `|s_A| = |s_B|` when the interface is empty and
  `|s_A| = |s_B| + 1` when a grant is pending.
* **`issued_placeLocal_of_lengthWindow`** — SU6c: if the grant reads only the
  partner's prefix LENGTH (`fiberB s_B t = F |s_B| t`), the carry charge is
  place-locally accountable — A can run the books alone, because the alternation
  makes the partner's clock deducible from A's own (`τ_A(s_A, a) = F |s_A| (s_A·a)`).

So the window lattice meets the rigidity boundary as: **blind ⊂ clock — accountable;
content — not.** Reading the partner's *time* costs nothing (synchrony already
shares it); reading the partner's *content* is exactly what place-local accounting
cannot absorb. The conjecture this calibrates (design doc): accountability holds
precisely for windows deducible from the shared schedule — the clock-deducible
boundary — open beyond these three points.

**Honest scope.** One machine (strict alternation, capacity-one interface); the
length window's accountability is a consequence of THIS scheduling discipline — under
free scheduling the partner's clock is no longer deducible and the question reopens
(noted, not resolved). Leaf module over SU4c. No `sorry`; axiom-clean.
-/
import FdrsFormal.Modes.SyntheticPlace.ConservationRigidity

namespace FdrsFormal.Modes.SyntheticPlace

/-! ## 1. The shared clock: alternation pins the partner's length -/

/-- **The shared clock.** On every reachable configuration of the coupled machine,
the two prefix lengths are locked to the interface state: equal when empty, A one
ahead when a grant is in flight. The alternation discipline is itself an information
channel — it broadcasts the partner's clock for free. -/
theorem reachable_length {C : CoupledFiber} {cfg : CoupledConfig}
    (h : Reachable C cfg) :
    (cfg.pending = none → cfg.sA.length = cfg.sB.length) ∧
    (∀ g, cfg.pending = some g → cfg.sA.length = cfg.sB.length + 1) := by
  induction h with
  | init =>
    constructor
    · intro _; rfl
    · intro g hg; simp [initConfig] at hg
  | stepA hr a ha hp ih =>
    constructor
    · intro hnone; simp [applyA] at hnone
    · intro g _
      have hlen := ih.1 hp
      simp [applyA, List.length_append, hlen]
  | stepB hr b hp hb ih =>
    constructor
    · intro _
      have hlen := ih.2 _ hp
      simp [applyB, List.length_append, hlen]
    · intro g hg; simp [applyB] at hg

/-! ## 2. SU6c — the length window is accountable -/

/-- **The length (clock) window**: the grant reads only the partner's prefix length,
never its digit content — one step up the window lattice from blind. -/
def LengthWindow (C : CoupledFiber) : Prop :=
  ∃ F : ℕ → List ℕ → ℕ, ∀ sB t, C.fiberB sB t = F sB.length t

/-- **SU6c — WINDOW-MONOTONE ACCOUNTABILITY (the intermediate point).** Length-window
couplings are place-locally accountable: the A-side transfer rule reads the partner's
clock off its OWN prefix (`|s_B| = |s_A|` at every A-step, by `reachable_length`), so
`τ_A(s_A, a) = F |s_A| (s_A·a)` accounts the whole carry ledger from one side.
Reading the partner's time is free under alternation; only reading its content
(Theorem 90's bilateral witness) breaks one-sided accounting. -/
theorem issued_placeLocal_of_lengthWindow (C : CoupledFiber) (h : LengthWindow C) :
    ∃ τA : List ℕ → ℕ → ℤ,
      PlaceLocalExact C issuedCharge τA (fun _ _ => 0) := by
  obtain ⟨F, hF⟩ := h
  refine ⟨fun sA a => (F sA.length (sA ++ [a]) : ℤ), ?_, ?_⟩
  · intro cfg a hr ha hp
    simp only [issuedCharge, applyA, hF]
    have hlen : cfg.sA.length = cfg.sB.length := (reachable_length hr).1 hp
    rw [← hlen]
    push_cast
    ring
  · intro cfg b g hr hp hb
    simp only [issuedCharge, applyB]
    ring

/-- The window lattice meets the boundary (the three calibrated points):
blind — accountable (Theorem 90 iii); clock — accountable (SU6c); content — NOT
(Theorem 90 ii). Phrased as data: `raggedFiber` is also a length-window coupling? It
is NOT (its grant reads A's content, which is fine — the window concerns the
PARTNER'S side `s_B`, which `raggedFiber` ignores entirely, making it blind). The
genuinely new point is any fiber of the form `F |s_B| t`. -/
theorem lengthWindow_of_blind (C : CoupledFiber)
    (hblind : ∀ sB sB' t, C.fiberB sB t = C.fiberB sB' t) : LengthWindow C :=
  ⟨fun _ t => C.fiberB [] t, fun sB t => hblind sB [] t⟩

end FdrsFormal.Modes.SyntheticPlace
