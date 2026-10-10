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

# Carrying around a frustrated ring (Phase 1 addendum, §3.11)

A ring of `n + 1` places, each overflowing into the next at an integer ratio `ρ_i ≥ 2`,
is frustrated: the loop's holonomy `∏ ρ_i` is not `1`, so no weight is consistent on the
ring (Theorem 93) and carries cannot be conserved there. On the holonomy cover (§3.10)
they can: the forward lift of the loop is a **helix** that never meets itself, its
sheets are exactly the place values of the **periodic schedule** `b_i = ρ_{i mod (n+1)}`,
and each lap multiplies the place value by the holonomy. Carries around the ring, kept
on the cover, are carries on that schedule — so conservation, the cut law and the
carry streams of §3.8–3.9 apply verbatim.

Reuses `Grading.lean` (coupling graphs, walks, `gradable_holonomy`), `HolonomyCover.lean`
(the cover, lifting, the ℚˣ bridge), `CarryStreams.lean` (path networks, streams) and
`Field25519Carry.lean` (the 25519 digit ring and its wrap, Theorem 114).

- **Definition 229** (`ringGraph`, `ringSchedule`, `helix`): the ring complex, its
  periodic schedule, and the forward walk around it.
- **Theorem 146** (`helix_isWalk`, `helix_walkFactor`, `helix_lift`, `helix_injective`):
  the lifted helix from sheet `1` reaches place `K mod (n+1)` on sheet `B_K` of the
  periodic schedule, and never revisits a cell — the cover of a frustrated ring is a
  number line.
- **Proposition 174** (`placeValue_period`, `ring_not_gradable`): each lap multiplies the
  place value by the holonomy, `B_{i + (n+1)} = h · B_i` with `h = B_{n+1} ≥ 2`; the ring
  itself is not gradable.
- **Corollary 50** (`ring_counter_stream`): carries around the ring, kept on the cover,
  obey §3.9: counting to `T`, the `i`-th crossing carries `⌊T / B_{i+1}⌋`.
- **Proposition 175** (`field25519_unrolls`, `field25519_lap_holonomy`): the 25519 digit
  ring unrolls to its weight ladder `2^{W_i}`; after one lap the sheet is `2^255`, which
  is `19` modulo `p = 2^255 − 19` — the path back that exists only modulo `p`.

**Honest scope.** Elementary (a cyclic cover of a cycle is a path). The corpus
contributes the identification of carries around a frustrated digit ring with carries on
a periodic schedule, and the 25519 instance.
-/

import FdrsFormal.Modes.SyntheticPlace.HolonomyCover
import FdrsFormal.Operations.CarryStreams
import FdrsFormal.Applications.Field25519Carry

namespace FdrsFormal.Modes.SyntheticPlace.RingUnrolling

open FdrsFormal.Core.Primitives FdrsFormal.Operations.CarryNetwork

variable {n : ℕ} (ρ : Fin (n + 1) → ℕ) (hρ : ∀ i, 2 ≤ ρ i)

/-! ## Definition 229: the ring, its schedule, its helix -/

/-- The ring complex: place `i` overflows into place `i + 1 (mod n+1)` at ratio `ρ_i`.

**fdrs.md**: Definition 229 (the ring complex and its unrolling). -/
def ringGraph : CouplingGraph (Fin (n + 1)) where
  Edge := Fin (n + 1)
  src e := e
  tgt e := e + 1
  ratio e := (ρ e : ℚ)
  ratio_pos e := by have := hρ e; positivity

/-- The place of the `j`-th crossing. -/
def placeOf (j : ℕ) : Fin (n + 1) := ⟨j % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩

/-- The periodic schedule `b_j = ρ_{j mod (n+1)}`.

**fdrs.md**: Definition 229 (the ring complex and its unrolling). -/
def ringSchedule : RadixSeq := ⟨fun j => ρ (placeOf j), fun _ => hρ _⟩

/-- The forward walk around the ring: `K` crossings starting at place `0`. -/
def helix (K : ℕ) : List (ringGraph ρ hρ).Step :=
  (List.range K).map fun j => ((placeOf j, true) : (ringGraph ρ hρ).Step)

/-! ## Theorem 146: the helix -/

theorem placeOf_succ (j : ℕ) : placeOf (n := n) j + 1 = placeOf (j + 1) := by
  apply Fin.ext
  simp only [placeOf, Fin.val_add, Fin.val_one']
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  rcases n with _ | n
  · simp [Nat.mod_one]
  · rw [show (1 : ℕ) % (n + 1 + 1) = 1 by
      exact Nat.mod_eq_of_lt (by omega)]

theorem helix_succ (K : ℕ) : helix ρ hρ (K + 1) =
    helix ρ hρ K ++ ([((placeOf K : Fin (n + 1)), true)] : List (ringGraph ρ hρ).Step) := by
  simp [helix, List.range_succ]

theorem helix_isWalk : ∀ K, (ringGraph ρ hρ).IsWalk 0 (helix ρ hρ K) (placeOf K)
  | 0 => by
    show (0 : Fin (n + 1)) = placeOf 0
    exact Fin.ext (by simp [placeOf])
  | K + 1 => by
    rw [helix_succ]
    exact (ringGraph ρ hρ).isWalk_append (helix_isWalk K)
      ⟨rfl, show placeOf K + 1 = placeOf (K + 1) from placeOf_succ K⟩

theorem helix_walkFactor : ∀ K,
    (ringGraph ρ hρ).walkFactor (helix ρ hρ K) = (placeValue (ringSchedule ρ hρ) K : ℚ)
  | 0 => by simp [helix]
  | K + 1 => by
    rw [helix_succ, (ringGraph ρ hρ).walkFactor_append, helix_walkFactor K, placeValue.succ]
    simp [CouplingGraph.walkFactor, CouplingGraph.stepFactor, ringGraph, ringSchedule, mul_comm]

/-- The sheet `B_K` as a unit of `ℚ`. -/
def sheet (K : ℕ) : ℚˣ :=
  Units.mk0 (placeValue (ringSchedule ρ hρ) K : ℚ) (Nat.cast_ne_zero.mpr (placeValue.ne_zero K))

/-- **Theorem 146 (the helix).** The forward walk around the ring, lifted to the
holonomy cover from sheet `1`, reaches place `K mod (n+1)` on sheet `B_K` — the place
value of the periodic schedule.

**fdrs.md**: Theorem 146 (the cover of a frustrated ring is a number line). -/
theorem helix_lift (K : ℕ) :
    (ringGraph ρ hρ).toGroupGraph.cover.IsWalk ((0 : Fin (n + 1)), (1 : ℚˣ))
      ((ringGraph ρ hρ).toGroupGraph.liftWalk (helix ρ hρ K) 1) (placeOf K, sheet ρ hρ K) := by
  have h := (ringGraph ρ hρ).toGroupGraph.lift_isWalk
    ((CouplingGraph.toGroupGraph_isWalk _).mpr (helix_isWalk ρ hρ K)) 1
  have hs : (ringGraph ρ hρ).toGroupGraph.walkFactor (helix ρ hρ K) * 1 = sheet ρ hρ K := by
    apply Units.ext
    rw [mul_one, CouplingGraph.toGroupGraph_walkFactor, helix_walkFactor]
    rfl
  rwa [hs] at h

/-- **Theorem 146 (the helix never meets itself).** Distinct crossings land on distinct
cells of the cover: the cover of a frustrated ring is a path — a number line.

**fdrs.md**: Theorem 146 (the cover of a frustrated ring is a number line). -/
theorem helix_injective {i j : ℕ} (h : (placeOf (n := n) i, sheet ρ hρ i) = (placeOf j, sheet ρ hρ j)) :
    i = j := by
  have h2 := congrArg (fun x : Fin (n + 1) × ℚˣ => ((x.2 : ℚˣ) : ℚ)) h
  simp only [sheet, Units.val_mk0, Nat.cast_inj] at h2
  exact (placeValue.strictMono (b := ringSchedule ρ hρ)).injective h2

/-! ## Proposition 174: each lap multiplies by the holonomy -/

theorem placeOf_add_period (i : ℕ) : placeOf (n := n) (i + (n + 1)) = placeOf i :=
  Fin.ext (by simp [placeOf])

/-- **Proposition 174 (laps multiply by the holonomy).** With `h = B_{n+1} = ∏_i ρ_i`, the
loop's holonomy, `B_{i + (n+1)} = h · B_i`.

**fdrs.md**: Proposition 174 (each lap multiplies by the holonomy). -/
theorem placeValue_period : ∀ i, placeValue (ringSchedule ρ hρ) (i + (n + 1)) =
    placeValue (ringSchedule ρ hρ) (n + 1) * placeValue (ringSchedule ρ hρ) i
  | 0 => by simp
  | i + 1 => by
    rw [show i + 1 + (n + 1) = (i + (n + 1)) + 1 by omega, placeValue.succ (i + (n + 1)),
      placeValue_period i, placeValue.succ i]
    have : (ringSchedule ρ hρ) (i + (n + 1)) = (ringSchedule ρ hρ) i := by
      show ρ (placeOf (i + (n + 1))) = ρ (placeOf i)
      rw [placeOf_add_period]
    rw [this]; ring

/-- **Proposition 174 (the ring is frustrated).** The loop has holonomy `B_{n+1} ≥ 2`, so by
Theorem 93 the ring admits no consistent weight.

**fdrs.md**: Proposition 174 (each lap multiplies by the holonomy). -/
theorem ring_not_gradable : ¬ (ringGraph ρ hρ).Gradable := by
  intro hg
  have hloop : (ringGraph ρ hρ).IsWalk 0 (helix ρ hρ (n + 1)) 0 := by
    have := helix_isWalk ρ hρ (n + 1)
    rwa [show placeOf (n := n) (n + 1) = 0 from Fin.ext (by simp [placeOf])] at this
  have h1 := (ringGraph ρ hρ).gradable_holonomy hg hloop
  rw [helix_walkFactor] at h1
  have h2 : placeValue (ringSchedule ρ hρ) 0 < placeValue (ringSchedule ρ hρ) (n + 1) :=
    placeValue.strictMono (Nat.succ_pos n)
  rw [placeValue.zero] at h2
  have : (placeValue (ringSchedule ρ hρ) (n + 1) : ℚ) = 1 := h1
  norm_cast at this
  omega

/-! ## Corollary 50: carries around the ring are schedule carries -/

/-- **Corollary 50 (carries around a frustrated ring).** Kept on the cover, `T` units
entering place `0` and carried around the ring (`K` crossings, the sweep) send exactly
`⌊T / B_{i+1}⌋` across the `i`-th crossing — Corollary 47 on the periodic schedule.

**fdrs.md**: Corollary 50 (carries around a frustrated ring). -/
theorem ring_counter_stream (K i T : ℕ) (hi : i < K) :
    lineFlux K i (transfers (sweepTo (ringSchedule ρ hρ) K K) (single 0 T)) =
      T / placeValue (ringSchedule ρ hρ) (i + 1) :=
  counter_stream_sweep (ringSchedule ρ hρ) K i T hi

/-! ## Proposition 175: the 25519 ring -/

section Field25519

open FdrsFormal.Applications.Field25519

/-- The 25519 digit ring: ten places, radices `2^26, 2^25, …` (Definition 212). -/
def ring25519 : Fin 10 → ℕ := fun i => radix i

theorem ring25519_ge_two (i : Fin 10) : 2 ≤ ring25519 i := by
  simp only [ring25519, radix, radixBits]
  split_ifs <;> norm_num

theorem ring25519_schedule (j : ℕ) :
    ringSchedule ring25519 ring25519_ge_two j = radix j := by
  show radix (j % 10) = radix j
  simp only [radix, radixBits]
  rw [Nat.mod_mod_of_dvd j (by norm_num : 2 ∣ 10)]

/-- **Proposition 175 (the 25519 ring unrolls to its weight ladder).** The periodic
schedule of the 25519 ring has place values `2^{W_i}`, the weights of Definition 212.

**fdrs.md**: Proposition 175 (the 25519 ring unrolled). -/
theorem field25519_unrolls : ∀ i,
    placeValue (ringSchedule ring25519 ring25519_ge_two) i = 2 ^ weightBits i
  | 0 => rfl
  | i + 1 => by
    rw [placeValue.succ, field25519_unrolls i, ring25519_schedule, radix, weightBits, pow_add]

/-- **Proposition 175 (one lap of the 25519 ring).** The sheet after one lap is
`2^255`, and modulo `p = 2^255 − 19` it is `19` (Theorem 114): the cover never returns to
sheet `1` over the integers; modulo `p` the lap is identified with multiplication by `19`.

**fdrs.md**: Proposition 175 (the 25519 ring unrolled). -/
theorem field25519_lap_holonomy :
    placeValue (ringSchedule ring25519 ring25519_ge_two) 10 = 2 ^ 255 ∧
      placeValue (ringSchedule ring25519 ring25519_ge_two) 10 % p = holonomy := by
  rw [field25519_unrolls, weightBits_ten]
  exact ⟨rfl, by rw [← weightBits_ten]; exact wrap_holonomy⟩

end Field25519

end FdrsFormal.Modes.SyntheticPlace.RingUnrolling
