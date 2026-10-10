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

# The holonomy cover: where frustrated carries live (Phase 1 addendum, §3.10)

A frustrated complex (Theorem 93: a loop whose holonomy is not `1`) has no consistent
global weight: carries that go around the loop cannot be merged back into the ring.
Instead of forcing them, **expand**: give every place one copy per accumulated
holonomy. A carry that goes around the loop lands on a new **sheet** — a new branch that
holds it at its exact weight — and the history of the operations is recorded in the
sheet label. On this cover every frustration is resolved: it is gradable by
construction. A **path back** to an earlier sheet exists exactly when the history
between them has trivial holonomy; a single frustrated loop never provides one, but a
combination of loops through different parts of the complex can.

Built on `GroupGrading.lean` (group-valued complexes, walks, `walkFactor`, `Gradable`,
`potential_walk`, Theorem 93/99) and `Grading.lean` (the ℚ-valued complex and its
frustrated triangle), which are reused, not restated.

- **Definition 228** (`GroupGraph.cover`, `liftWalk`, `proj`): the holonomy cover and
  the lifting and projection of walks.
- **Theorem 143** (`cover_gradable`, `cover_holonomy`): the cover is gradable — its
  potential is the sheet label — so every closed walk upstairs has holonomy `1`.
- **Theorem 144** (`lift_isWalk`, `proj_isWalk`, `sheet_of_walk`): every walk lifts
  uniquely from any sheet, ending on the sheet multiplied by its holonomy.
- **Theorem 145** (`path_back_iff`, `forward_path_back_iff`): sheets `(u, g)` and
  `(v, g')` are joined — by carries only, in the forward version — iff some walk
  `u → v` has holonomy `g' g⁻¹`.
- **Corollary 49** (`lap_sheet`, `lap_returns_iff`): `m` laps of a loop of holonomy `h`
  move the sheet by `h^m`; the history returns iff `h^m = 1`.
- **Proposition 173** (witnesses): the ℚ frustrated triangle of `Grading.lean` grows a
  new sheet every lap and has no forward path back; the dihedral frustrated triangle of
  `GroupGrading.lean` returns after exactly two laps; a complex with a second loop of
  holonomy `1/8` through the same place opens a path back — a hop across parts.

**Honest scope.** Classical (the covering graph of a gain graph / the derived graph of a
voltage graph, Gross 1974; Zaslavsky's balance theory). The corpus contributes the reading
of frustrated carries as sheets of the cover, the path-back criterion with forward
(carry-only) walks, and the witnesses on its own complexes.
-/

import FdrsFormal.Modes.SyntheticPlace.GroupGrading
import FdrsFormal.Modes.SyntheticPlace.Grading
import Mathlib.Data.Fin.VecNotation

namespace FdrsFormal.Modes.SyntheticPlace

namespace GroupGraph

variable {V G : Type*} [Group G] (Γ : GroupGraph V G)

/-! ## Definition 228: the holonomy cover -/

/-- The holonomy cover: one copy of each place per group element (sheet); an edge
`u → v` of ratio `ρ` lifts from sheet `g` to `(u, g) → (v, ρ g)`.

**fdrs.md**: Definition 228 (the holonomy cover). -/
def cover : GroupGraph (V × G) G where
  Edge := Γ.Edge × G
  src e := (Γ.src e.1, e.2)
  tgt e := (Γ.tgt e.1, Γ.ratio e.1 * e.2)
  ratio e := Γ.ratio e.1

/-- Project a walk of the cover to the base. -/
def proj (S : List Γ.cover.Step) : List Γ.Step := S.map fun s => (s.1.1, s.2)

/-- Lift one base step to the cover, starting on sheet `h`. -/
def liftStep : Γ.Step → G → Γ.cover.Step
  | (e, true), h => ((e, h), true)
  | (e, false), h => ((e, (Γ.ratio e)⁻¹ * h), false)

/-- Lift a base walk to the cover, starting on sheet `h`.

**fdrs.md**: Definition 228 (the holonomy cover). -/
def liftWalk : List Γ.Step → G → List Γ.cover.Step
  | [], _ => []
  | s :: rest, h => Γ.liftStep s h :: liftWalk rest (Γ.stepFactor s * h)

/-! ## Theorem 143: the cover is gradable -/

/-- **Theorem 143 (the cover is gradable).** The sheet label is a global potential.

**fdrs.md**: Theorem 143 (the holonomy cover is gradable). -/
theorem cover_gradable : Γ.cover.Gradable := ⟨Prod.snd, fun _ => rfl⟩

/-- **Theorem 143 (every frustration resolves upstairs).** Every closed walk of the cover
has holonomy `1` (Theorem 93 applied to the cover).

**fdrs.md**: Theorem 143 (the holonomy cover is gradable). -/
theorem cover_holonomy {x : V × G} {S : List Γ.cover.Step} (h : Γ.cover.IsWalk x S x) :
    Γ.cover.walkFactor S = 1 :=
  Γ.cover.gradable_holonomy Γ.cover_gradable h

/-! ## Theorem 144: lifting and projecting walks -/

theorem cover_stepFactor (s : Γ.cover.Step) : Γ.cover.stepFactor s = Γ.stepFactor (s.1.1, s.2) := by
  rcases s with ⟨⟨e, g⟩, b⟩; cases b <;> rfl

theorem cover_walkFactor : ∀ S : List Γ.cover.Step, Γ.cover.walkFactor S = Γ.walkFactor (Γ.proj S)
  | [] => rfl
  | s :: S => by
    rw [walkFactor_cons, cover_walkFactor S, cover_stepFactor]
    rfl

theorem cover_stepSrc_fst (s : Γ.cover.Step) : (Γ.cover.stepSrc s).1 = Γ.stepSrc (s.1.1, s.2) := by
  rcases s with ⟨⟨e, g⟩, b⟩; cases b <;> rfl

theorem cover_stepTgt_fst (s : Γ.cover.Step) : (Γ.cover.stepTgt s).1 = Γ.stepTgt (s.1.1, s.2) := by
  rcases s with ⟨⟨e, g⟩, b⟩; cases b <;> rfl

/-- **Theorem 144 (projection).** A walk of the cover projects to a walk of the base. -/
theorem proj_isWalk : ∀ {x y : V × G} {S : List Γ.cover.Step},
    Γ.cover.IsWalk x S y → Γ.IsWalk x.1 (Γ.proj S) y.1
  | x, y, [], h => by have : x = y := h; subst this; rfl
  | x, y, s :: S, h => by
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, ?_⟩
    · rw [← cover_stepSrc_fst, h1]
    · rw [← cover_stepTgt_fst]; exact proj_isWalk h2

/-- **Theorem 144 (sheets record holonomy).** Along any walk of the cover the sheet is
multiplied by the holonomy of the projected walk. -/
theorem sheet_of_walk {x y : V × G} {S : List Γ.cover.Step} (h : Γ.cover.IsWalk x S y) :
    y.2 = Γ.walkFactor (Γ.proj S) * x.2 := by
  rw [← cover_walkFactor]
  exact Γ.cover.potential_walk (w := Prod.snd) (fun _ => rfl) S x y h

theorem liftStep_src (s : Γ.Step) (h : G) :
    Γ.cover.stepSrc (Γ.liftStep s h) = (Γ.stepSrc s, h) := by
  rcases s with ⟨e, b⟩
  cases b
  · show (Γ.tgt e, Γ.ratio e * ((Γ.ratio e)⁻¹ * h)) = _
    rw [mul_inv_cancel_left]; rfl
  · rfl

theorem liftStep_tgt (s : Γ.Step) (h : G) :
    Γ.cover.stepTgt (Γ.liftStep s h) = (Γ.stepTgt s, Γ.stepFactor s * h) := by
  rcases s with ⟨e, b⟩; cases b <;> rfl

theorem proj_liftWalk : ∀ (steps : List Γ.Step) (h : G), Γ.proj (Γ.liftWalk steps h) = steps
  | [], _ => rfl
  | (e, b) :: rest, h => by
    cases b <;> simp only [liftWalk, liftStep, proj, List.map_cons, List.cons.injEq,
      true_and] <;> exact proj_liftWalk rest _

/-- **Theorem 144 (lifting).** A base walk `u → v` lifts from any sheet `h` to a walk of
the cover ending on sheet `walkFactor · h`.

**fdrs.md**: Theorem 144 (walks lift; sheets record holonomy). -/
theorem lift_isWalk : ∀ {u v : V} {steps : List Γ.Step}, Γ.IsWalk u steps v →
    ∀ h, Γ.cover.IsWalk (u, h) (Γ.liftWalk steps h) (v, Γ.walkFactor steps * h)
  | u, v, [], hw, h => by have : u = v := hw; subst this; simp [liftWalk, IsWalk]
  | u, v, s :: rest, hw, h => by
    obtain ⟨h1, h2⟩ := hw
    refine ⟨by rw [liftStep_src, h1], ?_⟩
    rw [liftStep_tgt, walkFactor_cons, mul_assoc]
    exact lift_isWalk h2 _

/-! ## Theorem 145: paths back -/

/-- **Theorem 145 (paths back).** Sheets `(u, g)` and `(v, g')` of the cover are joined
iff some base walk `u → v` has holonomy `g' g⁻¹` — the history between them.

**fdrs.md**: Theorem 145 (paths back). -/
theorem path_back_iff (u v : V) (g g' : G) :
    (∃ S, Γ.cover.IsWalk (u, g) S (v, g')) ↔
      ∃ steps, Γ.IsWalk u steps v ∧ Γ.walkFactor steps * g = g' := by
  constructor
  · rintro ⟨S, hS⟩
    exact ⟨Γ.proj S, Γ.proj_isWalk hS, (Γ.sheet_of_walk hS).symm⟩
  · rintro ⟨steps, hw, rfl⟩
    exact ⟨_, Γ.lift_isWalk hw g⟩

/-- A walk that only carries: every step forward. -/
def Forward (steps : List Γ.Step) : Prop := ∀ s ∈ steps, s.2 = true

theorem forward_proj {S : List Γ.cover.Step} (h : Γ.cover.Forward S) : Γ.Forward (Γ.proj S) := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
  exact h t ht

theorem forward_liftWalk : ∀ {steps : List Γ.Step} (h : G), Γ.Forward steps →
    Γ.cover.Forward (Γ.liftWalk steps h)
  | [], _, _ => fun _ hs => by simp [liftWalk] at hs
  | (e, b) :: rest, h, hf => by
    have hb : b = true := hf (e, b) List.mem_cons_self
    subst hb
    intro s hs
    simp only [liftWalk, liftStep, List.mem_cons] at hs
    rcases hs with rfl | hs
    · rfl
    · exact forward_liftWalk _ (fun s hs => hf s (List.mem_cons_of_mem _ hs)) s hs

/-- **Theorem 145 (paths back by carries only).** A forward walk of the cover joins
`(u, g)` to `(v, g')` iff some forward base walk `u → v` has holonomy `g' g⁻¹`.

**fdrs.md**: Theorem 145 (paths back). -/
theorem forward_path_back_iff (u v : V) (g g' : G) :
    (∃ S, Γ.cover.Forward S ∧ Γ.cover.IsWalk (u, g) S (v, g')) ↔
      ∃ steps, Γ.Forward steps ∧ Γ.IsWalk u steps v ∧ Γ.walkFactor steps * g = g' := by
  constructor
  · rintro ⟨S, hf, hS⟩
    exact ⟨Γ.proj S, Γ.forward_proj hf, Γ.proj_isWalk hS, (Γ.sheet_of_walk hS).symm⟩
  · rintro ⟨steps, hf, hw, rfl⟩
    exact ⟨_, Γ.forward_liftWalk g hf, Γ.lift_isWalk hw g⟩

/-! ## Corollary 49: laps -/

/-- `m` consecutive laps of a walk. -/
def laps (L : List Γ.Step) : ℕ → List Γ.Step
  | 0 => []
  | m + 1 => laps L m ++ L

theorem laps_isWalk {u : V} {L : List Γ.Step} (hL : Γ.IsWalk u L u) :
    ∀ m, Γ.IsWalk u (Γ.laps L m) u
  | 0 => rfl
  | m + 1 => Γ.isWalk_append (laps_isWalk hL m) hL

theorem laps_walkFactor (L : List Γ.Step) : ∀ m, Γ.walkFactor (Γ.laps L m) = Γ.walkFactor L ^ m
  | 0 => by simp [laps]
  | m + 1 => by rw [laps, walkFactor_append, laps_walkFactor L m, pow_succ']

/-- **Corollary 49 (laps move the sheet by `h^m`).** Lifting `m` laps of a loop of
holonomy `h` from sheet `g` ends on sheet `h^m g`.

**fdrs.md**: Corollary 49 (laps). -/
theorem lap_sheet {u : V} {L : List Γ.Step} (hL : Γ.IsWalk u L u) (m : ℕ) (g : G) :
    Γ.cover.IsWalk (u, g) (Γ.liftWalk (Γ.laps L m) g) (u, Γ.walkFactor L ^ m * g) := by
  have := Γ.lift_isWalk (Γ.laps_isWalk hL m) g
  rwa [laps_walkFactor] at this

/-- **Corollary 49 (the history returns iff `h^m = 1`).**

**fdrs.md**: Corollary 49 (laps). -/
theorem lap_returns_iff (L : List Γ.Step) (m : ℕ) (g : G) :
    Γ.walkFactor L ^ m * g = g ↔ Γ.walkFactor L ^ m = 1 :=
  mul_eq_right

end GroupGraph

/-! ## The ℚ-valued complexes as group complexes -/

namespace CouplingGraph

variable {V : Type*} (C : CouplingGraph V)

/-- A ℚ-valued coupling graph (`Grading.lean`) as a group complex over `ℚˣ`. -/
def toGroupGraph : GroupGraph V ℚˣ where
  Edge := C.Edge
  src := C.src
  tgt := C.tgt
  ratio e := Units.mk0 (C.ratio e) (C.ratio_pos e).ne'

theorem toGroupGraph_isWalk : ∀ {u v : V} {steps : List C.Step},
    C.toGroupGraph.IsWalk u steps v ↔ C.IsWalk u steps v
  | u, v, [] => Iff.rfl
  | u, v, s :: rest => by
    show (_ ∧ _) ↔ (_ ∧ _)
    rcases s with ⟨e, b⟩
    cases b <;> exact and_congr Iff.rfl toGroupGraph_isWalk

theorem toGroupGraph_walkFactor : ∀ steps : List C.Step,
    ((C.toGroupGraph.walkFactor steps : ℚˣ) : ℚ) = C.walkFactor steps
  | [] => by simp [GroupGraph.walkFactor, CouplingGraph.walkFactor]
  | (e, b) :: rest => by
    rw [GroupGraph.walkFactor_cons, Units.val_mul, toGroupGraph_walkFactor rest,
      CouplingGraph.walkFactor_cons, mul_comm]
    cases b <;> simp [GroupGraph.stepFactor, CouplingGraph.stepFactor, toGroupGraph]

end CouplingGraph

/-! ## Proposition 173: witnesses -/

namespace HolonomyCover

open GroupGraph

/-- The loop around the frustrated triangle of `Grading.lean`. -/
def triLoop : List frustratedTriangle.Step :=
  [((0 : Fin 3), true), ((1 : Fin 3), true), ((2 : Fin 3), true)]

/-- **Proposition 173 (frustration grows sheets).** Every lap around the ℚ frustrated
triangle (holonomy `8`) lands on a new sheet `8^m`: the history never returns along the
loop.

**fdrs.md**: Proposition 173 (witnesses). -/
theorem triangle_laps_never_return (m : ℕ) (hm : 0 < m) :
    frustratedTriangle.toGroupGraph.walkFactor triLoop ^ m ≠ 1 := by
  intro h
  have h8 : ((frustratedTriangle.toGroupGraph.walkFactor triLoop : ℚˣ) : ℚ) = 8 := by
    rw [CouplingGraph.toGroupGraph_walkFactor]; exact frustrated_loop_factor
  have := congrArg (fun x : ℚˣ => (x : ℚ)) h
  simp only [Units.val_pow_eq_pow_val, h8, Units.val_one] at this
  exact absurd this (ne_of_gt (one_lt_pow₀ (by norm_num) hm.ne'))

/-- Every forward step of the ℚ triangle has factor `2`, so a forward walk of length `n`
has holonomy `2^n ≥ 1`. -/
theorem triangle_forward_factor : ∀ steps : List frustratedTriangle.Step,
    (∀ s ∈ steps, s.2 = true) → frustratedTriangle.walkFactor steps = 2 ^ steps.length
  | [], _ => by simp
  | (e, b) :: rest, h => by
    have hb : b = true := h (e, b) List.mem_cons_self
    subst hb
    rw [CouplingGraph.walkFactor_cons, triangle_forward_factor rest
      (fun s hs => h s (List.mem_cons_of_mem _ hs))]
    simp [CouplingGraph.stepFactor, frustratedTriangle, pow_succ, mul_comm]

/-- The sheet `8` of `ℚˣ`. -/
def eight : ℚˣ := Units.mk0 8 (by norm_num)

/-- **Proposition 173 (no path back by carries).** In the cover of the ℚ frustrated
triangle there is no forward walk from sheet `8` back to sheet `1` at any place: every
forward history has holonomy `2^n ≥ 1`, never `1/8`.

**fdrs.md**: Proposition 173 (witnesses). -/
theorem triangle_no_forward_path_back (u : Fin 3) :
    ¬ ∃ S, frustratedTriangle.toGroupGraph.cover.Forward S ∧
      frustratedTriangle.toGroupGraph.cover.IsWalk (u, eight) S (u, 1) := by
  rw [forward_path_back_iff]
  rintro ⟨steps, hf, _, hfac⟩
  have hval := congrArg (fun x : ℚˣ => (x : ℚ)) hfac
  simp only [Units.val_mul, Units.val_one, CouplingGraph.toGroupGraph_walkFactor] at hval
  rw [triangle_forward_factor steps hf] at hval
  have h8 : ((eight : ℚˣ) : ℚ) = 8 := rfl
  rw [h8] at hval
  have : (1 : ℚ) ≤ 2 ^ steps.length := one_le_pow₀ (by norm_num)
  linarith

/-- The dihedral loop of `GroupGrading.lean`. -/
def diLoop : List GroupGrading.frustratedTriangle.Step :=
  [((0 : Fin 3), true), ((1 : Fin 3), true), ((2 : Fin 3), true)]

/-- **Proposition 173 (a path back after enough history).** The dihedral frustrated
triangle does not close after one lap but does after two: the history returns to its
starting sheet exactly when the accumulated holonomy `(sr 0)^m` is trivial.

**fdrs.md**: Proposition 173 (witnesses). -/
theorem dihedral_returns_after_two :
    GroupGrading.frustratedTriangle.walkFactor diLoop ^ 1 ≠ 1 ∧
      GroupGrading.frustratedTriangle.walkFactor diLoop ^ 2 = 1 := by
  refine ⟨?_, ?_⟩ <;> decide

theorem dihedral_two_laps_close (g : DihedralGroup 3) :
    GroupGrading.frustratedTriangle.cover.IsWalk ((0 : Fin 3), g)
      (GroupGrading.frustratedTriangle.liftWalk
        (GroupGrading.frustratedTriangle.laps diLoop 2) g) ((0 : Fin 3), g) := by
  have := GroupGrading.frustratedTriangle.lap_sheet (L := diLoop)
    GroupGrading.frustrated_loop_isWalk 2 g
  rwa [dihedral_returns_after_two.2, one_mul] at this

/-- Two loops through place `0`: `0 → 1 → 2 → 0` at ratio `2` (holonomy `8`) and
`0 → 3 → 4 → 0` at ratio `1/2` (holonomy `1/8`). -/
def twoLoops : CouplingGraph (Fin 5) where
  Edge := Fin 6
  src e := ![0, 1, 2, 0, 3, 4] e
  tgt e := ![1, 2, 0, 3, 4, 0] e
  ratio e := if (e : ℕ) < 3 then 2 else 1 / 2
  ratio_pos e := by split_ifs <;> norm_num

/-- The return loop through the second part. -/
def returnLoop : List twoLoops.Step := [((3 : Fin 6), true), ((4 : Fin 6), true), ((5 : Fin 6), true)]

theorem returnLoop_isWalk : twoLoops.IsWalk 0 returnLoop 0 := by
  simp only [returnLoop, CouplingGraph.IsWalk, CouplingGraph.stepSrc, CouplingGraph.stepTgt,
    twoLoops, if_true]
  decide

theorem returnLoop_factor : twoLoops.walkFactor returnLoop = 1 / 8 := by
  simp only [returnLoop, CouplingGraph.walkFactor, CouplingGraph.stepFactor, twoLoops,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, if_true]
  norm_num

/-- **Proposition 173 (a hop across parts opens the path back).** In the two-loop
complex, carries alone lead from sheet `8` at place `0` back to sheet `1` — through the
second loop, which the first loop by itself never provides.

**fdrs.md**: Proposition 173 (witnesses). -/
theorem twoLoops_forward_path_back :
    ∃ S, twoLoops.toGroupGraph.cover.Forward S ∧
      twoLoops.toGroupGraph.cover.IsWalk ((0 : Fin 5), eight) S ((0 : Fin 5), 1) := by
  rw [forward_path_back_iff]
  refine ⟨returnLoop, ?_, (CouplingGraph.toGroupGraph_isWalk _).mpr returnLoop_isWalk, ?_⟩
  · intro s hs; simp [returnLoop] at hs; rcases hs with rfl | rfl | rfl <;> rfl
  · apply Units.ext
    rw [Units.val_mul, CouplingGraph.toGroupGraph_walkFactor, returnLoop_factor]
    show 1 / 8 * (8 : ℚ) = 1
    norm_num

end HolonomyCover

end FdrsFormal.Modes.SyntheticPlace
