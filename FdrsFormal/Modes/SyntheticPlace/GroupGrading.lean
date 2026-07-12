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

# Synthetic place complex — non-abelian grading: holonomy over a general group

Generalizes `Grading.lean` from the abelian/scalar coupling ratio (`ratio : Edge → ℚ`,
a *magnitude* cocycle) to a **general-group** ratio (`ratio : Edge → G`, `[Group G]`) — the
SE(2)/pose case, where the "ratio" is a relative transform that does NOT commute.

The scalar reading — a global *magnitude* `w : V → ℚ`, positive — does not survive: a general
group has no magnitude, only a **G-valued potential** `w : V → G`, and gradability becomes a
**consistency** statement, not a sizing. What survives is the dichotomy itself:

> **`group_gradable_iff_trivial_holonomy`** — on a connected complex, a global G-valued
> potential (`w (tgt e) = ratio e · w (src e)`) exists IFF every closed walk has holonomy
> (ordered product of edge transforms) equal to `1`.

**Pose dictionary** (the intended instance, `G = SE(2)`): edge ratio = relative pose; loop
holonomy = loop-closure residual; gradable = a consistent global pose assignment exists; the
converse = "all loops close ⇒ a global pose exists."

**HONEST SCOPE — this is the verification of a classical theorem, NOT new mathematics.** The
result is **gain-graph balance** (Zaslavsky 1989, generalizing Harary's 1953 signed-graph
balance from `{±1}` to an arbitrary group) = a flat connection with trivial holonomy on a
graph (Gao–Brodzki–Mukherjee 2021); the proof is the standard spanning-tree / cycle-space
argument. The contribution is the *machine-checked artifact* and its placement as the
non-abelian completion of the grading axis — never the theorem. Two things this module does
NOT do, by design: (i) the noisy loop-*closing* optimization (pose-graph SLAM / SE(d)
synchronization — Lu–Milios 1997, SE-Sync, GTSAM — a separate, classical layer); (ii) the
genuinely-frontier object, a *sound set-membership pose region on the SE(2) manifold*
(propagation through non-commutative composition with a curvature/BCH bound) — an open
research problem, deliberately out of scope. `SE(2) = ℂ ⋊ Circle` as a concrete `[Group]`
instance is the immediate next step; the witness below uses `DihedralGroup 3`, the finite
rigid-motion group, which is `decide`-checkable.

The one place non-commutativity bites (vs the abelian template): `walkFactor` folds the **new
step on the right** (`walkFactor (s :: rest) = walkFactor rest * stepFactor s`), giving the
anti-homomorphism `walkFactor (a ++ b) = walkFactor b * walkFactor a`. The abelian file's
closing `ring` relied on commutativity to reconcile fold-order with the left-action potential
law — which is *false* in a general `G`; the convention here is what makes the port go through.

Leaf module. No `sorry`; axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.GroupTheory.SpecificGroups.Dihedral

namespace FdrsFormal.Modes.SyntheticPlace

/-! ## 1. Group-valued coupling graphs and traversals -/

/-- A **group-valued coupling graph**: digit/place nodes joined by directed edges, each
carrying a group element `ratio` — the transform (e.g. relative pose) one increment of the
target is worth in source terms. The non-abelian generalization of `CouplingGraph`. -/
structure GroupGraph (V G : Type*) [Group G] where
  Edge : Type*
  src : Edge → V
  tgt : Edge → V
  ratio : Edge → G

namespace GroupGraph

variable {V G : Type*} [Group G] (Γ : GroupGraph V G)

/-- A traversal step: an edge crossed forward (`true`) or backward (`false`). -/
def Step := Γ.Edge × Bool

def stepSrc (s : Γ.Step) : V := if s.2 then Γ.src s.1 else Γ.tgt s.1

def stepTgt (s : Γ.Step) : V := if s.2 then Γ.tgt s.1 else Γ.src s.1

/-- The transform of a step: the ratio forward, its inverse backward. -/
def stepFactor (s : Γ.Step) : G := if s.2 then Γ.ratio s.1 else (Γ.ratio s.1)⁻¹

/-- `IsWalk u steps v`: the steps chain from `u` to `v`. -/
def IsWalk : V → List Γ.Step → V → Prop
  | u, [], v => u = v
  | u, s :: rest, v => Γ.stepSrc s = u ∧ IsWalk (Γ.stepTgt s) rest v

/-- **Holonomy** of a walk: the ordered product of step transforms, with the **new step on
the right** so the left-action potential law composes without commutativity. -/
def walkFactor : List Γ.Step → G
  | [] => 1
  | s :: rest => walkFactor rest * Γ.stepFactor s

@[simp] theorem walkFactor_nil : Γ.walkFactor [] = 1 := rfl

theorem walkFactor_cons (s : Γ.Step) (rest : List Γ.Step) :
    Γ.walkFactor (s :: rest) = Γ.walkFactor rest * Γ.stepFactor s := rfl

/-! ## 2. Gradability and the holonomy theorem -/

/-- **Gradable**: a global G-valued potential whose edge law is the coupling transform. No
positivity (a group has no magnitude); just the consistency `w (tgt e) = ratio e · w (src e)`. -/
def Gradable : Prop :=
  ∃ w : V → G, ∀ e, w (Γ.tgt e) = Γ.ratio e * w (Γ.src e)

theorem potential_step {w : V → G}
    (hw : ∀ e, w (Γ.tgt e) = Γ.ratio e * w (Γ.src e)) (s : Γ.Step) :
    w (Γ.stepTgt s) = Γ.stepFactor s * w (Γ.stepSrc s) := by
  rcases s with ⟨e, b⟩
  cases b
  · simp only [stepSrc, stepTgt, stepFactor, Bool.false_eq_true, if_false]
    rw [hw e, inv_mul_cancel_left]
  · simp only [stepSrc, stepTgt, stepFactor, if_true]
    exact hw e

theorem potential_walk {w : V → G}
    (hw : ∀ e, w (Γ.tgt e) = Γ.ratio e * w (Γ.src e)) :
    ∀ (steps : List Γ.Step) (u v : V), Γ.IsWalk u steps v →
      w v = Γ.walkFactor steps * w u := by
  intro steps
  induction steps with
  | nil => intro u v h; have huv : u = v := h; subst huv; simp
  | cons s rest ih =>
    intro u v h
    obtain ⟨hsrc, hrest⟩ := h
    have h2 := Γ.potential_step hw s
    rw [hsrc] at h2
    have h1 := ih (Γ.stepTgt s) v hrest
    rw [h1, h2, walkFactor_cons, mul_assoc]

/-- **THE HOLONOMY THEOREM** (port of `gradable_holonomy`). A gradable complex has trivial
holonomy: every closed walk's transform is `1`. (Group cancellation replaces the field's
nonzero-cancellation; no positivity needed.) -/
theorem gradable_holonomy (hΓ : Γ.Gradable) {u : V} {steps : List Γ.Step}
    (h : Γ.IsWalk u steps u) : Γ.walkFactor steps = 1 := by
  obtain ⟨w, hw⟩ := hΓ
  have h1 := Γ.potential_walk hw steps u u h
  have h2 : Γ.walkFactor steps * w u = 1 * w u := by rw [one_mul]; exact h1.symm
  exact mul_right_cancel h2

/-! ## 2b. The converse: trivial holonomy suffices -/

def revStep (s : Γ.Step) : Γ.Step := (s.1, !s.2)

@[simp] theorem stepSrc_revStep (s : Γ.Step) : Γ.stepSrc (Γ.revStep s) = Γ.stepTgt s := by
  rcases s with ⟨e, b⟩; cases b <;> simp [revStep, stepSrc, stepTgt]

@[simp] theorem stepTgt_revStep (s : Γ.Step) : Γ.stepTgt (Γ.revStep s) = Γ.stepSrc s := by
  rcases s with ⟨e, b⟩; cases b <;> simp [revStep, stepSrc, stepTgt]

theorem stepFactor_revStep (s : Γ.Step) :
    Γ.stepFactor (Γ.revStep s) = (Γ.stepFactor s)⁻¹ := by
  rcases s with ⟨e, b⟩; cases b <;> simp [revStep, stepFactor]

/-- Reverse a walk: reverse the steps and flip each. -/
def revWalk (steps : List Γ.Step) : List Γ.Step := (steps.reverse).map Γ.revStep

theorem isWalk_append {u v x : V} {s t : List Γ.Step}
    (hs : Γ.IsWalk u s v) (ht : Γ.IsWalk v t x) : Γ.IsWalk u (s ++ t) x := by
  induction s generalizing u with
  | nil => have huv : u = v := hs; subst huv; simpa using ht
  | cons a rest ih => obtain ⟨ha, hrest⟩ := hs; exact ⟨ha, ih hrest⟩

theorem isWalk_revWalk {u v : V} {s : List Γ.Step} (h : Γ.IsWalk u s v) :
    Γ.IsWalk v (Γ.revWalk s) u := by
  induction s generalizing u with
  | nil => have huv : u = v := h; subst huv; simp [revWalk, IsWalk]
  | cons a rest ih =>
    obtain ⟨ha, hrest⟩ := h
    have hrev : Γ.revWalk (a :: rest) = Γ.revWalk rest ++ [Γ.revStep a] := by
      simp [revWalk, List.reverse_cons]
    rw [hrev]
    exact Γ.isWalk_append (ih hrest)
      ⟨Γ.stepSrc_revStep a, by rw [Γ.stepTgt_revStep]; exact ha⟩

/-- Holonomy is an anti-homomorphism (the reverse convention): the factor of a concatenation
multiplies in reverse order. -/
theorem walkFactor_append (s t : List Γ.Step) :
    Γ.walkFactor (s ++ t) = Γ.walkFactor t * Γ.walkFactor s := by
  induction s with
  | nil => simp
  | cons a ss ih =>
    rw [List.cons_append, walkFactor_cons, ih, walkFactor_cons, mul_assoc]

theorem walkFactor_revWalk (s : List Γ.Step) :
    Γ.walkFactor (Γ.revWalk s) = (Γ.walkFactor s)⁻¹ := by
  induction s with
  | nil => simp [revWalk]
  | cons a rest ih =>
    have hrev : Γ.revWalk (a :: rest) = Γ.revWalk rest ++ [Γ.revStep a] := by
      simp [revWalk, List.reverse_cons]
    rw [hrev, walkFactor_append, ih, walkFactor_cons, walkFactor_nil, one_mul,
        stepFactor_revStep, walkFactor_cons, mul_inv_rev]

/-- **THE HOLONOMY CONVERSE** (port of `gradable_of_trivial_holonomy`). On a connected complex,
trivial holonomy SUFFICES: weight each node by the transform of any walk from a base; closing
the triangle over an edge yields the edge law. The classical spanning-tree trivialization, in
a general group. -/
theorem gradable_of_trivial_holonomy (base : V)
    (hconn : ∀ v : V, ∃ steps : List Γ.Step, Γ.IsWalk base steps v)
    (hhol : ∀ (u : V) (steps : List Γ.Step), Γ.IsWalk u steps u →
      Γ.walkFactor steps = 1) :
    Γ.Gradable := by
  classical
  choose path hpath using hconn
  refine ⟨fun v => Γ.walkFactor (path v), ?_⟩
  intro e
  have hstep : Γ.IsWalk (Γ.src e) ([(e, true)] : List Γ.Step) (Γ.tgt e) := ⟨rfl, rfl⟩
  have hloop : Γ.IsWalk base
      (path (Γ.src e) ++ (([(e, true)] : List Γ.Step) ++ Γ.revWalk (path (Γ.tgt e)))) base := by
    refine Γ.isWalk_append (hpath (Γ.src e)) ?_
    exact Γ.isWalk_append hstep (Γ.isWalk_revWalk (hpath (Γ.tgt e)))
  have hone := hhol base _ hloop
  have hB : Γ.walkFactor ([(e, true)] : List Γ.Step) = Γ.ratio e := by
    simp [walkFactor_cons, walkFactor_nil, stepFactor]
  rw [walkFactor_append, walkFactor_append, walkFactor_revWalk, hB, mul_assoc] at hone
  exact inv_mul_eq_one.mp hone

/-- **THE FULL CHARACTERIZATION.** On a connected complex, a global G-valued potential exists
IFF every loop has trivial holonomy. (Gain-graph balance / flat connection — classical;
verified here for a general group.) -/
theorem group_gradable_iff_trivial_holonomy (base : V)
    (hconn : ∀ v : V, ∃ steps : List Γ.Step, Γ.IsWalk base steps v) :
    Γ.Gradable ↔
      ∀ (u : V) (steps : List Γ.Step), Γ.IsWalk u steps u → Γ.walkFactor steps = 1 :=
  ⟨fun hg _ _ h => Γ.gradable_holonomy hg h, Γ.gradable_of_trivial_holonomy base hconn⟩

end GroupGraph

/- The witness instances live in the `GroupGrading` sub-namespace: their base names
(`chainGraph`, `chainPotential`, `frustratedTriangle`, …) deliberately mirror the
ℚ-valued witnesses of `Grading.lean` (the group arc re-derives that axis), and the
two modules are imported together by the `Modes.SyntheticPlace` aggregator. -/
namespace GroupGrading

variable {G : Type*} [Group G]

/-! ## 3. The graded witness: a chain is gradable in any group -/

/-- A chain (path topology, no loops): each position transformed into the next by `r`. -/
def chainGraph (r : ℕ → G) : GroupGraph ℕ G where
  Edge := ℕ
  src e := e
  tgt e := e + 1
  ratio := r

/-- The chain's global potential: the accumulated transform. -/
def chainPotential (r : ℕ → G) : ℕ → G
  | 0 => 1
  | i + 1 => r i * chainPotential r i

/-- **The graded case**: a chain admits a global potential (no loops ⇒ holonomy vacuous),
for ANY group — the number-line analogue, non-abelian. -/
theorem chainGraph_gradable (r : ℕ → G) : (chainGraph r).Gradable :=
  ⟨chainPotential r, fun _ => rfl⟩

/-! ## 4. The frustrated witness: a rigid-motion loop that does not close -/

/-- Three places in a loop, each edge the reflection `sr 0` of the triangle (`DihedralGroup 3`
= the finite rigid-motion group). The loop composes three reflections into one — `sr 0³ = sr 0
≠ 1` — a non-identity holonomy, so no consistent global pose exists. The discrete
SE(2)-flavoured `frustratedTriangle`. -/
def frustratedTriangle : GroupGraph (Fin 3) (DihedralGroup 3) where
  Edge := Fin 3
  src e := e
  tgt e := e + 1
  ratio := fun _ => DihedralGroup.sr 0

theorem frustrated_loop_isWalk :
    frustratedTriangle.IsWalk 0
      [((0 : Fin 3), true), ((1 : Fin 3), true), ((2 : Fin 3), true)] 0 := by
  simp only [GroupGraph.IsWalk]
  decide

theorem frustrated_loop_factor_ne_one :
    frustratedTriangle.walkFactor
      [((0 : Fin 3), true), ((1 : Fin 3), true), ((2 : Fin 3), true)] ≠ 1 := by
  decide

/-- **THE FRUSTRATED WITNESS (machine-checked).** The rigid-motion loop has non-identity
holonomy, so by `gradable_holonomy` no global pose assignment exists — the loop provably does
not close. The non-abelian analogue of `frustratedTriangle_not_gradable`. -/
theorem frustratedTriangle_not_gradable : ¬ frustratedTriangle.Gradable := fun hg =>
  frustrated_loop_factor_ne_one (frustratedTriangle.gradable_holonomy hg frustrated_loop_isWalk)

end GroupGrading

end FdrsFormal.Modes.SyntheticPlace
