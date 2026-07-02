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

# SE(2) instantiation of the grading port + the certified-pose-region frontier

Two parts, both honest:

**§1 (a real rigid motion, not the finite shadow).** Assemble `SE(2)` — rotations (`Circle`,
the unit complex) ⋉ translations (`ℂ`) — as a concrete `Group`, instantiate `GroupGrading`
(`GroupGrading.lean`) at it, and exhibit a genuine SE(2) frustrated loop: three slides that
compose to a slide-by-3, a real rigid-motion cycle that does not close (`frustratedSE2`). This
replaces the `DihedralGroup 3` finite witness with the continuous pose group. Classical (the
existence theorem is gain-graph balance — see `GroupGrading.lean`'s banner).

**§2 (the frontier — scoped HONESTLY in Lean, NOT solved).** The TYPE-2 certified pose region.
The literature line (web-verified): TYPE-1 — a coordinate box on `(x, y, θ)` — is SOLVED
(Jaulin; Song et al. 2025, guaranteed 2D pose-graph SLAM); a sound TYPE-2 region on the SE(2)
*manifold* (propagation through non-commutative composition) is a 2024–26 frontier (InZSMF
2025 is *linearized*-only — it drops the 2nd-order BCH term; Harapanahalli–Coogan 2024 is
SO(3) reachability, neighbourhood-limited).

What this file proves SHARPENS that line into a precise statement:

> **Soundness through non-commutative composition is FREE.** The EXACT set-membership region
> (`PoseRegion := Set SE2`), predicted by the group's own set-product and updated by
> intersection, keeps the true moved pose for SE(2) *exactly, with no curvature bound*
> (`run_sound`, axiom-clean). The open problem is NOT soundness — it is **tractability**: a
> finite representation needs an OVER-APPROXIMATION whose soundness is the curvature/BCH
> bound. That obligation is isolated as the two hypothesis fields of `TractablePose`, and the
> tractable estimator is proven sound *given* them (`TractablePose.run_sound`). The exact
> representation discharges them trivially (`exactTractable`) — proving the framework is
> sound, not vacuous — but **no tractable instance is supplied: discharging those fields for a
> tangent-zonotope on SE(2) IS the open problem, and we do not claim to.**

No new theorem; the contribution is the verified artifact and the precise localization of the
frontier (soundness is free; tractability is the curvature bound). Leaf module. No `sorry`;
axiom-clean.
-/
import FdrsFormal.Modes.SyntheticPlace.GroupGrading
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

namespace FdrsFormal.Modes.SyntheticPlace

/-! ## 1. SE(2) = rotations ⋉ translations, as a concrete group -/

/-- A rigid motion of the plane: a rotation (`Circle`, the unit complex) and a translation
(`ℂ`). Acts on `z` by `z ↦ rot · z + trans`; composition is the semidirect-product law
`(c₁,t₁)·(c₂,t₂) = (c₁c₂, c₁·t₂ + t₁)`. -/
@[ext] structure SE2 where
  rot : Circle
  trans : ℂ

namespace SE2

noncomputable instance : Mul SE2 := ⟨fun a b => ⟨a.rot * b.rot, (a.rot : ℂ) * b.trans + a.trans⟩⟩
noncomputable instance : One SE2 := ⟨⟨1, 0⟩⟩
noncomputable instance : Inv SE2 := ⟨fun a => ⟨a.rot⁻¹, -((a.rot : ℂ)⁻¹ * a.trans)⟩⟩

@[simp] theorem mul_rot (a b : SE2) : (a * b).rot = a.rot * b.rot := rfl
@[simp] theorem mul_trans (a b : SE2) : (a * b).trans = (a.rot : ℂ) * b.trans + a.trans := rfl
@[simp] theorem one_rot : (1 : SE2).rot = 1 := rfl
@[simp] theorem one_trans : (1 : SE2).trans = 0 := rfl
@[simp] theorem inv_rot (a : SE2) : a⁻¹.rot = a.rot⁻¹ := rfl
@[simp] theorem inv_trans (a : SE2) : a⁻¹.trans = -((a.rot : ℂ)⁻¹ * a.trans) := rfl

noncomputable instance : Group SE2 where
  mul := (· * ·)
  one := 1
  inv := (·⁻¹)
  mul_assoc a b c := by
    ext
    · simp [mul_assoc]
    · simp only [mul_trans, mul_rot, Circle.coe_mul]; ring
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  inv_mul_cancel a := by
    ext
    · simp
    · simp only [mul_trans, inv_rot, inv_trans, one_trans, Circle.coe_inv]; ring

end SE2

/-- A genuine SE(2) frustrated loop: three edges, each the unit slide `⟨1, 1⟩` (translate by
`1`, no rotation). The loop's holonomy is the slide `⟨1, 3⟩ ≠ 1` — a real rigid-motion cycle
that does not close. (Replaces the finite `DihedralGroup` shadow with continuous SE(2).) -/
noncomputable def frustratedSE2 : GroupGraph (Fin 3) SE2 where
  Edge := Fin 3
  src e := e
  tgt e := e + 1
  ratio := fun _ => (⟨1, 1⟩ : SE2)

theorem frustratedSE2_loop_isWalk :
    frustratedSE2.IsWalk 0
      [((0 : Fin 3), true), ((1 : Fin 3), true), ((2 : Fin 3), true)] 0 := by
  simp only [GroupGraph.IsWalk]
  decide

/-- The loop's holonomy is the slide by `3` — computed in genuine SE(2). -/
theorem frustratedSE2_holonomy :
    frustratedSE2.walkFactor
      [((0 : Fin 3), true), ((1 : Fin 3), true), ((2 : Fin 3), true)]
      = (⟨1, 3⟩ : SE2) := by
  simp only [GroupGraph.walkFactor, GroupGraph.stepFactor, frustratedSE2, if_true]
  ext
  · simp
  · simp only [SE2.mul_trans, SE2.mul_rot, SE2.one_trans, SE2.one_rot, Circle.coe_one]
    norm_num

theorem frustratedSE2_holonomy_ne_one :
    frustratedSE2.walkFactor
      [((0 : Fin 3), true), ((1 : Fin 3), true), ((2 : Fin 3), true)] ≠ 1 := by
  rw [frustratedSE2_holonomy]
  intro h
  have h3 : (3 : ℂ) = 0 := by simpa using congrArg SE2.trans h
  norm_num at h3

/-- **THE SE(2) FRUSTRATED WITNESS.** A real rigid-motion loop has non-identity holonomy, so by
`gradable_holonomy` no consistent global pose assignment exists — the loop provably does not
close, on the genuine pose group. -/
theorem frustratedSE2_not_gradable : ¬ frustratedSE2.Gradable := fun hg =>
  frustratedSE2_holonomy_ne_one (frustratedSE2.gradable_holonomy hg frustratedSE2_loop_isWalk)

-- (SE(2) is genuinely non-abelian — the law's `c₁·t₂` term — and that non-commutativity is
-- already exercised end-to-end by the `DihedralGroup 3` witness in `GroupGrading.lean`; the
-- SE(2) loop above uses the translation subgroup, its job being "a real rigid motion".)

/-! ## 2. The TYPE-2 certified pose region — sound by composition, open by tractability -/

/-- A pose belief: the representation-free EXACT region (a set of candidate poses on SE(2)). -/
abbrev PoseRegion := Set SE2

/-- **Predict**: push the region through a motion (right-translate by `m`). -/
noncomputable def predict (S : PoseRegion) (m : SE2) : PoseRegion := (· * m) '' S

/-- **Update**: intersect with a measurement region. -/
def update (S M : PoseRegion) : PoseRegion := S ∩ M

theorem predict_sound {S : PoseRegion} {x m : SE2} (h : x ∈ S) : x * m ∈ predict S m :=
  ⟨x, h, rfl⟩

theorem update_sound {S M : PoseRegion} {x : SE2} (hS : x ∈ S) (hM : x ∈ M) :
    x ∈ update S M := ⟨hS, hM⟩

/-- The true pose after a sequence of motions (the SE(2) composition). -/
noncomputable def truePath : SE2 → List (SE2 × PoseRegion) → SE2
  | x, [] => x
  | x, (m, _) :: rest => truePath (x * m) rest

/-- Every measurement contains the moved truth (the soundness premise). -/
def MeasSound : SE2 → List (SE2 × PoseRegion) → Prop
  | _, [] => True
  | x, (m, M) :: rest => (x * m ∈ M) ∧ MeasSound (x * m) rest

/-- Run the exact estimator: fold predict→update over a stream of (motion, measurement). -/
noncomputable def run : PoseRegion → List (SE2 × PoseRegion) → PoseRegion
  | S, [] => S
  | S, (m, M) :: rest => run (update (predict S m) M) rest

/-- **SOUNDNESS THROUGH NON-COMMUTATIVE COMPOSITION IS FREE.** The exact set-membership region
keeps the true moved pose after every predict→update cycle — for SE(2), exactly, with NO
curvature/linearization bound — because the set operations respect the group composition. This
is what the literature's TYPE-2 problem is NOT about; the open part is tractability (below). -/
theorem run_sound : ∀ (steps : List (SE2 × PoseRegion)) (S : PoseRegion) (x : SE2),
    x ∈ S → MeasSound x steps → truePath x steps ∈ run S steps := by
  intro steps
  induction steps with
  | nil => intro S x hx _; exact hx
  | cons head rest ih =>
    intro S x hx hms
    obtain ⟨m, M⟩ := head
    obtain ⟨hM, hrest⟩ := hms
    exact ih (update (predict S m) M) (x * m) (update_sound (predict_sound hx) hM) hrest

/-- A **tractable** pose representation `R`: a finite encoding with a `concretize`, tractable
predict/update — sound IFF the concretization OVER-APPROXIMATES the exact operations. Those two
`⊆` fields are the SOUNDNESS OBLIGATION; for SE(2) they are exactly where the curvature/BCH
bound lives (a tangent-zonotope's exp-composition remainder). They are left as hypotheses. -/
structure TractablePose (R : Type*) where
  concretize : R → PoseRegion
  predictR : R → SE2 → R
  updateR : R → PoseRegion → R
  /-- THE OPEN OBLIGATION (predict): the representation contains the exact predicted set. -/
  predict_overapprox : ∀ (r : R) (m : SE2),
    predict (concretize r) m ⊆ concretize (predictR r m)
  /-- THE OPEN OBLIGATION (update): the representation contains the exact updated set. -/
  update_overapprox : ∀ (r : R) (M : PoseRegion),
    update (concretize r) M ⊆ concretize (updateR r M)

namespace TractablePose

variable {R : Type*}

def run (T : TractablePose R) : R → List (SE2 × PoseRegion) → R
  | r, [] => r
  | r, (m, M) :: rest => run T (T.updateR (T.predictR r m) M) rest

/-- **The tractable estimator is sound — GIVEN the over-approximation obligations.** Proven
modulo exactly the two `⊆` fields. Those fields, for a finite SE(2) representation, ARE the
open curvature/BCH bound (InZSMF discharges them only linearized); this file does not claim to
discharge them — it isolates them. -/
theorem run_sound (T : TractablePose R) :
    ∀ (steps : List (SE2 × PoseRegion)) (r : R) (x : SE2),
      x ∈ T.concretize r → MeasSound x steps →
        truePath x steps ∈ T.concretize (T.run r steps) := by
  intro steps
  induction steps with
  | nil => intro r x hx _; exact hx
  | cons head rest ih =>
    intro r x hx hms
    obtain ⟨m, M⟩ := head
    obtain ⟨hM, hrest⟩ := hms
    refine ih (T.updateR (T.predictR r m) M) (x * m) ?_ hrest
    exact T.update_overapprox _ _ ⟨T.predict_overapprox _ _ (predict_sound hx), hM⟩

end TractablePose

/-- The framework is **sound, not vacuous**: the EXACT representation (`R = PoseRegion`,
`concretize = id`) discharges the obligations trivially — soundness through composition is
free. The catch is that this representation is not finite/tractable; supplying a tractable `R`
that still discharges the `⊆` fields for SE(2) is the open problem, and is NOT done here. -/
noncomputable def exactTractable : TractablePose PoseRegion where
  concretize := id
  predictR := predict
  updateR := update
  predict_overapprox := fun _ _ => le_refl _
  update_overapprox := fun _ _ => le_refl _

/-! ### A non-vacuous tractable instance — the projection hull (decoupled product)

`exactTractable` discharges the obligations with `id` (no over-approximation at all). The honest
next question: is there a *genuinely coarser* representation that still discharges them — or do
the `⊆` fields secretly force exactness? They do not. The **projection hull** tracks a pose
region as a PRODUCT `(rotation-set) × (translation-set)`, deliberately FORGETTING the
rotation↔translation correlation. It over-approximates any region (a set lies in the product of
its projections), and `boxPredictR`'s translation component `{c·tm + t | c ∈ Cr, t ∈ Ct}` *does*
inflate with the rotation uncertainty `Cr` — that inflation is the rotation→translation
curvature bleed, captured in its coarsest (decoupled) form.

This discharges BOTH obligations with a real, non-trivial instance (strictly coarser than
`exactTractable`) — but it also SHARPENS the scope: the `⊆` fields demand only SOUNDNESS of the
over-approximation, which *any* hull (down to the trivial `Set.univ`) satisfies. So discharging
them is necessary, not sufficient, for TYPE-2; the open problem is a TIGHT, FINITE bound (a
tangent zonotope whose exp-composition remainder is controlled) that KEEPS the correlation this
hull throws away. The certified rotation-sector emission (`CircleEmit.emitSector_sound`) is the
floor-free machinery that would refine the rotation-set component toward that tight bound. -/

/-- Concretize a `(rotation-set, translation-set)` product into a pose region. -/
def boxConcretize (r : Set Circle × Set ℂ) : PoseRegion :=
  {p : SE2 | p.rot ∈ r.1 ∧ p.trans ∈ r.2}

/-- Tractable predict on the product: rotate the rotation-set, and form the translation-set
`{c·tm + t}` — which inflates with the rotation uncertainty `Cr` (the curvature bleed). -/
noncomputable def boxPredictR (r : Set Circle × Set ℂ) (m : SE2) : Set Circle × Set ℂ :=
  ( (· * m.rot) '' r.1,
    {z : ℂ | ∃ c ∈ r.1, ∃ t ∈ r.2, (c : ℂ) * m.trans + t = z} )

/-- Tractable update on the product: intersect, then re-project to a product (the hull). -/
noncomputable def boxUpdateR (r : Set Circle × Set ℂ) (M : PoseRegion) : Set Circle × Set ℂ :=
  ( SE2.rot '' (boxConcretize r ∩ M), SE2.trans '' (boxConcretize r ∩ M) )

/-- **A genuine non-vacuous tractable estimator.** The projection hull discharges BOTH
over-approximation obligations — strictly coarser than `exactTractable` (it decouples rotation
from translation) yet provably sound. The proofs are the projection-hull argument: a set lies in
the product of its projections. No curvature/BCH *tightness* is claimed — only soundness, which
is all the `⊆` fields ask. -/
noncomputable def boxTractable : TractablePose (Set Circle × Set ℂ) where
  concretize := boxConcretize
  predictR := boxPredictR
  updateR := boxUpdateR
  predict_overapprox := by
    rintro r m p ⟨q, hq, rfl⟩
    exact ⟨⟨q.rot, hq.1, rfl⟩, q.rot, hq.1, q.trans, hq.2, rfl⟩
  update_overapprox := by
    rintro r M p ⟨hp, hpM⟩
    exact ⟨⟨p, ⟨hp, hpM⟩, rfl⟩, p, ⟨hp, hpM⟩, rfl⟩

end FdrsFormal.Modes.SyntheticPlace
