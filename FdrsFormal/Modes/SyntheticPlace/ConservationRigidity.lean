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

# Synthetic place complex SU4c — conservation rigidity (the no-go and the boundary)

Third piece of the conservation arc (`docs/synthetic-place/00-thesis.md` §3): the
rigidity move, mirroring how `Rigidity.lean` handled synthetic places — first prove
the boundary, then exhibit witnesses on both sides of it.

A transfer rule is **place-local** when each half-step's charge increment is computed
from that place's own data alone: `τA` reads `(sA, a)`, `τB` reads `(sB, b)` — neither
sees the other place or the interface.

* **`placeLocal_factors` — THE FACTORIZATION (classification) THEOREM.** Any charge
  that is exact with place-local transfers factors, on every reachable configuration,
  as `Φ = Φ(init) + f(sA) + g(sB)` with `f, g` the telescopes of `τA, τB`. A
  place-locally-accounted charge is additively separable: *it cannot measure the
  coupling.* (Corollary shape: such a Φ satisfies the rectangle identity
  `Φ₀₀ + Φ₁₁ = Φ₀₁ + Φ₁₀` across reachable corners.)
* **`issued_not_placeLocal` — THE NO-GO, machine-checked.** For the genuinely
  bilateral coupling `jointFiber` (B's grant reads BOTH opening digits), the carry
  charge `issued` admits NO place-local transfer rule: the four corner runs have
  issued-ledgers `5, 6, 6, 5`, breaking the rectangle (`5 + 5 ≠ 6 + 6`). The carry
  cannot be accounted from either side alone — conservation of the coupling charge
  *requires* the explicit interface register of SU4b. The conserved quantity lives ON
  the coupling, not in the places.
* **`issued_placeLocal_of_blind` — INSIDE THE BOUNDARY.** When the coupling is
  **B-blind** (the grant ignores B's own prefix), the carry charge IS place-locally
  exact — `τA` is the grant read off A alone, `τB = 0`. SU1's `raggedFiber` is
  B-blind (`issued_placeLocal_ragged`): a witness *inside* the boundary, with
  `jointFiber` the witness *outside*. The boundary is real and crossed.

**Honest scope.** The boundary is proven as two implications with explicit witnesses
(B-blind ⟹ accountable; one bilateral instance ⟹ not accountable). The full iff —
"place-locally accountable ⟺ grant satisfies the rectangle identity on reachables" —
is the open refinement; and none of this produces a cross-place *product* law
(thesis §3, ledger item 1). Leaf module over SU4b. No `sorry`; axiom-clean; kernel
`decide` only.
-/
import FdrsFormal.Modes.SyntheticPlace.InterfaceBalance

namespace FdrsFormal.Modes.SyntheticPlace

/-! ## 1. Telescopes and place-local exactness -/

/-- The telescope of a transfer rule along a prefix: the accumulated increments
`Σ_{i<|s|} τ (s.take i) (s.get i)` (defined by the shift trick, `prefixWeight`'s
recursion pattern). -/
def telescope (τ : List ℕ → ℕ → ℤ) : List ℕ → ℤ
  | [] => 0
  | d :: ds => τ [] d + telescope (fun s a => τ (d :: s) a) ds

/-- Telescoping law: one more digit adds exactly its own increment. -/
theorem telescope_append (τ : List ℕ → ℕ → ℤ) (s : List ℕ) (d : ℕ) :
    telescope τ (s ++ [d]) = telescope τ s + τ s d := by
  induction s generalizing τ with
  | nil => simp [telescope]
  | cons c cs ih =>
    simp only [List.cons_append, telescope, ih (fun s a => τ (c :: s) a)]
    ring

/-- **Place-local exactness**: the charge's increment at an A-half-step is computed
from `(sA, a)` alone, and at a B-half-step from `(sB, b)` alone — neither transfer
rule sees the other place or the interface. Required only along reachable, guarded
steps (the honest minimal demand). -/
def PlaceLocalExact (C : CoupledFiber) (Φ : CoupledConfig → ℤ)
    (τA τB : List ℕ → ℕ → ℤ) : Prop :=
  (∀ cfg (a : ℕ), Reachable C cfg → a < C.fiberA cfg.sA → cfg.pending = none →
      Φ (applyA C cfg a) = Φ cfg + τA cfg.sA a) ∧
  (∀ cfg (b g : ℕ), Reachable C cfg → cfg.pending = some g → b < g →
      Φ (applyB cfg b) = Φ cfg + τB cfg.sB b)

/-! ## 2. The factorization theorem -/

/-- **SU4c — THE FACTORIZATION THEOREM.** A place-locally exact charge is additively
separable on reachables: `Φ = Φ(init) + f(sA) + g(sB)`, `f`/`g` the telescopes of
`τA`/`τB`. Place-local accounting cannot measure the coupling — any cross-place
content of a charge must flow through an interface term. -/
theorem placeLocal_factors {C : CoupledFiber} {Φ : CoupledConfig → ℤ}
    {τA τB : List ℕ → ℕ → ℤ} (h : PlaceLocalExact C Φ τA τB) :
    ∀ {cfg : CoupledConfig}, Reachable C cfg →
      Φ cfg = Φ initConfig + telescope τA cfg.sA + telescope τB cfg.sB := by
  intro cfg hr
  induction hr with
  | init => simp [initConfig, telescope]
  | stepA hr a ha hp ih =>
    rw [h.1 _ a hr ha hp, ih]
    simp only [applyA, telescope_append]
    ring
  | stepB hr b hp hb ih =>
    rw [h.2 _ b _ hr hp hb, ih]
    simp only [applyB, telescope_append]
    ring

/-! ## 3. The carry charge, and the boundary from inside -/

/-- The carry charge: the cumulative issued grant, as an integer. -/
def issuedCharge (cfg : CoupledConfig) : ℤ := (cfg.issued : ℤ)

/-- **INSIDE THE BOUNDARY.** When the coupling is B-blind — the grant ignores B's own
prefix — the carry charge IS place-locally exact: A can account the whole ledger
alone (`τA` = the grant read off `sA`; `τB = 0`). -/
theorem issued_placeLocal_of_blind (C : CoupledFiber)
    (hblind : ∀ sB sB' t, C.fiberB sB t = C.fiberB sB' t) :
    PlaceLocalExact C issuedCharge
      (fun sA a => (C.fiberB [] (sA ++ [a]) : ℤ)) (fun _ _ => 0) := by
  constructor
  · intro cfg a _ _ _
    simp only [issuedCharge, applyA]
    rw [hblind cfg.sB [] (cfg.sA ++ [a])]
    push_cast
    ring
  · intro cfg b g _ _ _
    simp only [issuedCharge, applyB]
    ring

/-- SU1's ragged witness is B-blind, hence INSIDE the boundary: raggedness (no
odometer) does not by itself obstruct place-local accounting. The obstruction is
bilaterality, not raggedness. -/
theorem issued_placeLocal_ragged :
    PlaceLocalExact raggedFiber issuedCharge
      (fun sA a => (raggedFiber.fiberB [] (sA ++ [a]) : ℤ)) (fun _ _ => 0) :=
  issued_placeLocal_of_blind raggedFiber (fun _ _ _ => rfl)

/-! ## 4. The genuinely bilateral coupling, and the no-go -/

/-- A genuinely **bilateral** coupling: the grant compares the two chains' opening
digits — it reads BOTH prefixes irreducibly. -/
def jointFiber : CoupledFiber where
  fiberA _ := 2
  fiberB sB sA := if sB.head? = sA.head? then 2 else 3
  fiberA_ge_two _ := le_refl 2
  fiberB_ge_two s t := by by_cases h : s.head? = t.head? <;> norm_num [h]

/-- The four corner runs `(a₀, b₀, 0, 0)`: two full coupled steps. -/
def cornerCfg (a₀ b₀ : ℕ) : CoupledConfig :=
  applyB (applyA jointFiber (applyB (applyA jointFiber initConfig a₀) b₀) 0) 0

-- the broken rectangle, visible: issued ledgers 5, 6, 6, 5
#eval [(cornerCfg 0 0).issued, (cornerCfg 0 1).issued,
       (cornerCfg 1 0).issued, (cornerCfg 1 1).issued]   -- [5, 6, 6, 5]

theorem corner_reachable_00 : Reachable jointFiber (cornerCfg 0 0) :=
  Reachable.stepB (g := 2)
    (Reachable.stepA
      (Reachable.stepB (g := 3)
        (Reachable.stepA Reachable.init 0 (by decide) (by decide))
        0 (by decide) (by decide))
      0 (by decide) (by decide))
    0 (by decide) (by decide)

theorem corner_reachable_01 : Reachable jointFiber (cornerCfg 0 1) :=
  Reachable.stepB (g := 3)
    (Reachable.stepA
      (Reachable.stepB (g := 3)
        (Reachable.stepA Reachable.init 0 (by decide) (by decide))
        1 (by decide) (by decide))
      0 (by decide) (by decide))
    0 (by decide) (by decide)

theorem corner_reachable_10 : Reachable jointFiber (cornerCfg 1 0) :=
  Reachable.stepB (g := 3)
    (Reachable.stepA
      (Reachable.stepB (g := 3)
        (Reachable.stepA Reachable.init 1 (by decide) (by decide))
        0 (by decide) (by decide))
      0 (by decide) (by decide))
    0 (by decide) (by decide)

theorem corner_reachable_11 : Reachable jointFiber (cornerCfg 1 1) :=
  Reachable.stepB (g := 2)
    (Reachable.stepA
      (Reachable.stepB (g := 3)
        (Reachable.stepA Reachable.init 1 (by decide) (by decide))
        1 (by decide) (by decide))
      0 (by decide) (by decide))
    0 (by decide) (by decide)

/-- **SU4c — THE NO-GO (machine-checked).** For the bilateral coupling, the carry
charge admits NO place-local transfer rule: the factorization theorem forces the
rectangle identity on the four corner runs, but their issued-ledgers are `5, 6, 6, 5`
and `5 + 5 ≠ 6 + 6`. The carry crossing a genuine coupling cannot be accounted from
either place alone — the interface register of SU4b is *necessary*, not a
convenience: the conserved quantity lives on the coupling itself. -/
theorem issued_not_placeLocal :
    ¬ ∃ τA τB, PlaceLocalExact jointFiber issuedCharge τA τB := by
  rintro ⟨τA, τB, h⟩
  have h00 := placeLocal_factors h corner_reachable_00
  have h01 := placeLocal_factors h corner_reachable_01
  have h10 := placeLocal_factors h corner_reachable_10
  have h11 := placeLocal_factors h corner_reachable_11
  rw [show cornerCfg 0 0 = (⟨[0, 0], [0, 0], none, 5, 5⟩ : CoupledConfig) from by decide] at h00
  rw [show cornerCfg 0 1 = (⟨[0, 0], [1, 0], none, 6, 6⟩ : CoupledConfig) from by decide] at h01
  rw [show cornerCfg 1 0 = (⟨[1, 0], [0, 0], none, 6, 6⟩ : CoupledConfig) from by decide] at h10
  rw [show cornerCfg 1 1 = (⟨[1, 0], [1, 0], none, 5, 5⟩ : CoupledConfig) from by decide] at h11
  simp only [issuedCharge, initConfig] at h00 h01 h10 h11
  push_cast at h00 h01 h10 h11
  linarith

end FdrsFormal.Modes.SyntheticPlace
