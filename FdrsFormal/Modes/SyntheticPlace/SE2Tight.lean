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

# The wire: a TIGHT `TractablePose` over the real `Circle ⋉ ℂ` SE(2)

This closes the last seam. `SE2Pose.boxTractable` discharged the `⊆` obligations but COARSE
(decoupled projection hull). `SE2Engine` built the TIGHT four-corner trap but over abstract
`K × K` poses. This file IDENTIFIES the two: a `SE2Pose.TractablePose` instance over the genuine
`SE2 = Circle ⋉ ℂ` group whose `predict_overapprox` is discharged by `SE2Engine`'s tight
four-corner machinery (`bbox_sound`, `mul_trapped`) instantiated at `K = ℝ`.

THE IDENTIFICATION. Track a pose belief as a box on the rotation's COORDINATES `(c.re, c.im)`
and a box on the translation's coordinates `(t.re, t.im)`. Then under `x ↦ x · m`:
- the new rotation coords `(x.rot · m.rot)` are a **linear image** of `(x.rot)`'s coords (rotation
  by `m.rot`) — bounded by the tight `Aff.bbox` four-corner trap;
- the new translation `(x.rot)·m.trans + x.trans` is **affine** in the rotation AND translation
  coords (the bilinear coupling `c·t'`, here `t'` fixed) — bounded term-by-term by `mul_trapped`.

So `predict_overapprox` holds with the FULL coupling kept — the rotation uncertainty inflates the
translation box exactly as `mul_trapped` dictates. This is the curvature/BCH bound, discharged
TIGHTLY on the real pose group, axiom-clean. `update` keeps the box (sound on arbitrary
set-measurements; box-measurements tighten via the exact `Box.inter`, not needed for the
obligation). Leaf module. No `sorry`.
-/
import FdrsFormal.Modes.SyntheticPlace.SE2Pose
import FdrsFormal.Modes.SyntheticPlace.SE2Engine

namespace FdrsFormal.Modes.SyntheticPlace

open SE2Engine

/-- Rotation coordinates of a pose: the unit complex's `(re, im)`. -/
noncomputable def rc (p : SE2) : ℝ × ℝ := ((p.rot : ℂ).re, (p.rot : ℂ).im)

/-- Translation coordinates of a pose. -/
noncomputable def tc (p : SE2) : ℝ × ℝ := (p.trans.re, p.trans.im)

/-- The pose-box belief: a box on the rotation coords × a box on the translation coords. -/
abbrev PoseBox := Box ℝ × Box ℝ

/-- Concretize a pose-box to the set of SE(2) elements whose coords lie in the boxes. -/
def concretizeBox (r : PoseBox) : PoseRegion :=
  {p : SE2 | r.1.mem (rc p) ∧ r.2.mem (tc p)}

/-- The rotation `c ↦ c · m.rot` as a real linear map on rotation coordinates. -/
noncomputable def rotAff (m : SE2) : Aff ℝ :=
  ⟨(m.rot : ℂ).re, -(m.rot : ℂ).im, (m.rot : ℂ).im, (m.rot : ℂ).re, 0, 0⟩

/-- New rotation coords = the linear image of the old ones (rotation by `m.rot`). -/
theorem rc_mul (x m : SE2) : rc (x * m) = (rotAff m).apply (rc x) := by
  simp only [rc, rotAff, Aff.apply, SE2.mul_rot, Circle.coe_mul, Complex.mul_re, Complex.mul_im,
    Prod.mk.injEq]
  constructor <;> ring

/-- The translation predict box: each new translation coord is affine in the rotation AND
translation coords, so the box is the per-term `mul_trapped` extremes — the coupling kept. -/
noncomputable def transBox (r : PoseBox) (m : SE2) : Box ℝ where
  xlo := min (m.trans.re * r.1.xlo) (m.trans.re * r.1.xhi)
       + min (-m.trans.im * r.1.ylo) (-m.trans.im * r.1.yhi) + r.2.xlo
  xhi := max (m.trans.re * r.1.xlo) (m.trans.re * r.1.xhi)
       + max (-m.trans.im * r.1.ylo) (-m.trans.im * r.1.yhi) + r.2.xhi
  ylo := min (m.trans.im * r.1.xlo) (m.trans.im * r.1.xhi)
       + min (m.trans.re * r.1.ylo) (m.trans.re * r.1.yhi) + r.2.ylo
  yhi := max (m.trans.im * r.1.xlo) (m.trans.im * r.1.xhi)
       + max (m.trans.re * r.1.ylo) (m.trans.re * r.1.yhi) + r.2.yhi

/-- Tractable predict: rotation coords via the tight `bbox`, translation via `transBox`. -/
noncomputable def predictBox (r : PoseBox) (m : SE2) : PoseBox :=
  ((rotAff m).bbox r.1, transBox r m)

/-- New translation coords, expanded (the SE(2) coupling `c·t' + t` in coordinates). -/
theorem tc_mul (x m : SE2) :
    (tc (x * m)).1 = m.trans.re * (rc x).1 + (-m.trans.im) * (rc x).2 + (tc x).1 ∧
    (tc (x * m)).2 = m.trans.im * (rc x).1 + m.trans.re * (rc x).2 + (tc x).2 := by
  constructor <;>
    simp only [tc, rc, SE2.mul_trans, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im] <;> ring

/-- **THE TIGHT WIRE.** A `TractablePose` over the REAL `Circle ⋉ ℂ` SE(2): `predict_overapprox`
is discharged by the four-corner trap (`bbox_sound` for the rotation, `mul_trapped` term-by-term
for the translation), keeping the full rotation→translation coupling — the curvature/BCH bound,
tight, on the genuine pose group. (Coarse `boxTractable` decoupled; this does not.) -/
noncomputable def tightTractable : TractablePose PoseBox where
  concretize := concretizeBox
  predictR := predictBox
  updateR := fun r _ => r
  predict_overapprox := by
    rintro r m p ⟨x, hx, rfl⟩
    obtain ⟨hrot, htrans⟩ := hx
    refine ⟨?_, ?_⟩
    · -- rotation: rc (x*m) = (rotAff m).apply (rc x) ∈ tight bbox
      rw [rc_mul]
      exact (rotAff m).bbox_sound r.1 (rc x) hrot
    · -- translation: tc (x*m) ∈ transBox, by per-term mul_trapped
      obtain ⟨hx1, hx2, hy1, hy2⟩ := hrot
      obtain ⟨tx1, tx2, ty1, ty2⟩ := htrans
      obtain ⟨e1, e2⟩ := tc_mul x m
      obtain ⟨a1, a2⟩ := mul_trapped m.trans.re (rc x).1 r.1.xlo r.1.xhi hx1 hx2
      obtain ⟨b1, b2⟩ := mul_trapped (-m.trans.im) (rc x).2 r.1.ylo r.1.yhi hy1 hy2
      obtain ⟨c1, c2⟩ := mul_trapped m.trans.im (rc x).1 r.1.xlo r.1.xhi hx1 hx2
      obtain ⟨d1, d2⟩ := mul_trapped m.trans.re (rc x).2 r.1.ylo r.1.yhi hy1 hy2
      simp only [Box.mem, predictBox, transBox]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [e1]; linarith
      · rw [e1]; linarith
      · rw [e2]; linarith
      · rw [e2]; linarith
  update_overapprox := fun _ _ _ hp => hp.1

/-- Sanity: the framework's generic soundness theorem fires on this real-SE(2) tight instance. -/
theorem tightTractable_run_sound (steps : List (SE2 × PoseRegion)) (r : PoseBox) (x : SE2)
    (hx : x ∈ tightTractable.concretize r) (hms : MeasSound x steps) :
    truePath x steps ∈ tightTractable.concretize (tightTractable.run r steps) :=
  tightTractable.run_sound steps r x hx hms

end FdrsFormal.Modes.SyntheticPlace
