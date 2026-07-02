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

# A certified exact SE(2) pose engine over an ordered ring — the tight four-corner trap

The tight, executable realization of `SE2Pose`'s open obligations, now generic over ANY
`[CommRing K] [LinearOrder K] [IsStrictOrderedRing K]` — **exactly the typeclass of
`BihomographicSound.emit_traps`**. So the same four-corner certification covers:
- `K = ℤ` — the integer engine; the integer rotations are the 90° multiples (exact).
- `K = ℚ` — **genuine fine rotations**, exact and rational: the Pythagorean `(3,4,5)` rotation
  `cos = 3/5, sin = 4/5` (a det-1 rational rotation by `atan(4/3) ≈ 53°`), no floats.

WHAT IS HERE (all exact, generic, certified; `#eval`'d at `ℤ` and `ℚ`):
- `Aff` / `comp` / `comp_apply` — exact affine SE(2) motion; composition = the genuine
  NON-COMMUTATIVE group law, realized with no error (`(S∘T)(p) = S(T(p))`, by `ring`).
- `bbox` / `bbox_sound` — **THE TIGHT FOUR-CORNER TRAP**: every box point maps into the bbox of
  the *actual* slanted image (parallelogram). Tight, keeps the linear coupling (no decoupling).
- `bilinear_ge` / `bilinear_le` — **THE BIHOMOGRAPHIC COUPLING TRAP**: the bilinear form
  `α·x·y + β·x + γ·y + δ` (the Gosper `BihTensor` numerator) over a box is trapped by its FOUR
  CORNERS — the bounded-region analogue of `emit_traps` (whose region is the `[1,∞]` tails). With
  `α = 1` this certifies the SE(2) coupling `c·t'` itself: rotation × translation, four-corner,
  exact, over ordered ℚ. THIS is "couple it to the translation BihTensor", made literal.
- `bboxSet` / `bboxSet_sound` — predict under a ROTATION-UNCERTAINTY SECTOR (the `CircleEmit`
  sector lifted to member rotations): uncertain heading inflates the box, certified.
- `runPose` / `runPose_sound` — the engine: predict (tight) → update (exact ∩), sound through
  non-commutative composition, tight bound at every step.

HONEST SCOPE (the seam that stays open): the engine is over `K × K` Cartesian poses with the
rotation given as a (rational) matrix. Bridging to `SE2Pose.lean`'s `Circle ⋉ ℂ` SE(2) = these
boxes + the rational-rotation lift here + `CircleEmit`'s certified sector feeding the heading.
The certification machinery is now all in place and generic; that final identification is the
remaining wire. Leaf module. No `sorry`; axiom-clean.
-/
import Mathlib.Tactic
import Mathlib.Algebra.Order.Field.Rat

namespace FdrsFormal.Modes.SyntheticPlace

namespace SE2Engine

variable {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

/-- An axis-aligned box over `K` — an exact pose-translation belief. -/
structure Box (K : Type*) where
  xlo : K
  xhi : K
  ylo : K
  yhi : K
deriving Repr, DecidableEq

/-- The point lies in the box. -/
def Box.mem (B : Box K) (p : K × K) : Prop :=
  B.xlo ≤ p.1 ∧ p.1 ≤ B.xhi ∧ B.ylo ≤ p.2 ∧ p.2 ≤ B.yhi

/-- An exact affine SE(2) motion: linear part `[[a,b],[c,d]]`, translation `(e,f)`. -/
structure Aff (K : Type*) where
  a : K
  b : K
  c : K
  d : K
  e : K
  f : K
deriving Repr, DecidableEq

/-- Apply the motion to a point. -/
def Aff.apply (T : Aff K) (p : K × K) : K × K :=
  (T.a * p.1 + T.b * p.2 + T.e, T.c * p.1 + T.d * p.2 + T.f)

/-- Compose motions — the (non-commutative) SE(2)/affine group law. -/
def Aff.comp (S T : Aff K) : Aff K where
  a := S.a * T.a + S.b * T.c
  b := S.a * T.b + S.b * T.d
  c := S.c * T.a + S.d * T.c
  d := S.c * T.b + S.d * T.d
  e := S.a * T.e + S.b * T.f + S.e
  f := S.c * T.e + S.d * T.f + S.f

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- **Wiring is exact**: composing motions, then applying, equals applying in sequence. -/
theorem Aff.comp_apply (S T : Aff K) (p : K × K) :
    (S.comp T).apply p = S.apply (T.apply p) := by
  simp only [Aff.comp, Aff.apply, Prod.mk.injEq]
  constructor <;> ring

/-- A linear functional over an interval is trapped between its endpoint values (the `min`/`max`
absorbs the sign of the coefficient). -/
theorem mul_trapped (a p lo hi : K) (h1 : lo ≤ p) (h2 : p ≤ hi) :
    min (a * lo) (a * hi) ≤ a * p ∧ a * p ≤ max (a * lo) (a * hi) := by
  rcases le_total 0 a with ha | ha
  · exact ⟨le_trans (min_le_left _ _) (by nlinarith),
          le_trans (by nlinarith) (le_max_right _ _)⟩
  · exact ⟨le_trans (min_le_right _ _) (by nlinarith),
          le_trans (by nlinarith) (le_max_left _ _)⟩

/-- The **tight four-corner over-approximation**: the bbox of the image `T '' B`. The linear part
separates per axis, so the bbox is the per-axis endpoint extremes (the four corner products). -/
def Aff.bbox (T : Aff K) (B : Box K) : Box K where
  xlo := min (T.a * B.xlo) (T.a * B.xhi) + min (T.b * B.ylo) (T.b * B.yhi) + T.e
  xhi := max (T.a * B.xlo) (T.a * B.xhi) + max (T.b * B.ylo) (T.b * B.yhi) + T.e
  ylo := min (T.c * B.xlo) (T.c * B.xhi) + min (T.d * B.ylo) (T.d * B.yhi) + T.f
  yhi := max (T.c * B.xlo) (T.c * B.xhi) + max (T.d * B.ylo) (T.d * B.yhi) + T.f

/-- **THE FOUR-CORNER TRAP (tight, coupling-preserving).** Every box point maps into the bbox of
the image — the certified over-approximation. A non-grid `T` slants `B` into a parallelogram and
the bbox traps it via the four corner products: the curvature/BCH bound made exact. -/
theorem Aff.bbox_sound (T : Aff K) (B : Box K) (p : K × K) (hp : B.mem p) :
    (T.bbox B).mem (T.apply p) := by
  obtain ⟨hx1, hx2, hy1, hy2⟩ := hp
  obtain ⟨ax1, ax2⟩ := mul_trapped T.a p.1 B.xlo B.xhi hx1 hx2
  obtain ⟨bx1, bx2⟩ := mul_trapped T.b p.2 B.ylo B.yhi hy1 hy2
  obtain ⟨cx1, cx2⟩ := mul_trapped T.c p.1 B.xlo B.xhi hx1 hx2
  obtain ⟨dx1, dx2⟩ := mul_trapped T.d p.2 B.ylo B.yhi hy1 hy2
  simp only [Box.mem, Aff.apply, Aff.bbox]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/- =====================================================================
   The bihomographic coupling trap: the bilinear `c·t'`, four corners.
   ===================================================================== -/

/-- An affine functional `m·u + k` over `[lo,hi]`: if `k₀` bounds it below at both endpoints, it
bounds it below throughout (no sign assumption). -/
theorem lin_ge (m k₀ u lo hi c : K) (h1 : lo ≤ u) (h2 : u ≤ hi)
    (kl : k₀ ≤ m * lo + c) (kh : k₀ ≤ m * hi + c) : k₀ ≤ m * u + c := by
  rcases le_total 0 m with hm | hm
  · exact le_trans kl (by nlinarith)
  · exact le_trans kh (by nlinarith)

/-- Dual of `lin_ge`: an upper bound at both endpoints bounds the affine functional above. -/
theorem lin_le (m k₀ u lo hi c : K) (h1 : lo ≤ u) (h2 : u ≤ hi)
    (kl : m * lo + c ≤ k₀) (kh : m * hi + c ≤ k₀) : m * u + c ≤ k₀ := by
  rcases le_total 0 m with hm | hm
  · exact le_trans (by nlinarith) kh
  · exact le_trans (by nlinarith) kl

/-- **THE BIHOMOGRAPHIC COUPLING TRAP (lower).** The bilinear form `α·x·y + β·x + γ·y + δ` (the
Gosper `BihTensor` numerator) over a box `[xlo,xhi]×[ylo,yhi]` is bounded below by `k₀` whenever
its FOUR CORNERS are — the bounded-region twin of `emit_traps`. With `α = 1, β = γ = δ = 0` this
certifies the SE(2) coupling `c·t'` (rotation × translation) from the four sector×interval
corners. No order on the *circle* is used; the order is on the value `K`, just as `emit_traps`. -/
theorem bilinear_ge (α β γ δ xlo xhi ylo yhi x y k₀ : K)
    (hx1 : xlo ≤ x) (hx2 : x ≤ xhi) (hy1 : ylo ≤ y) (hy2 : y ≤ yhi)
    (c_ll : k₀ ≤ α * xlo * ylo + β * xlo + γ * ylo + δ)
    (c_hl : k₀ ≤ α * xhi * ylo + β * xhi + γ * ylo + δ)
    (c_lh : k₀ ≤ α * xlo * yhi + β * xlo + γ * yhi + δ)
    (c_hh : k₀ ≤ α * xhi * yhi + β * xhi + γ * yhi + δ) :
    k₀ ≤ α * x * y + β * x + γ * y + δ := by
  -- trap in `x` at `y = ylo` and `y = yhi` (affine in `x`), then trap in `y` (affine in `y`).
  have hlo : k₀ ≤ α * x * ylo + β * x + γ * ylo + δ := by
    have e : α * x * ylo + β * x + γ * ylo + δ = (α * ylo + β) * x + (γ * ylo + δ) := by ring
    rw [e]
    refine lin_ge (α * ylo + β) k₀ x xlo xhi (γ * ylo + δ) hx1 hx2 ?_ ?_
    · have : (α * ylo + β) * xlo + (γ * ylo + δ) = α * xlo * ylo + β * xlo + γ * ylo + δ := by ring
      rw [this]; exact c_ll
    · have : (α * ylo + β) * xhi + (γ * ylo + δ) = α * xhi * ylo + β * xhi + γ * ylo + δ := by ring
      rw [this]; exact c_hl
  have hhi : k₀ ≤ α * x * yhi + β * x + γ * yhi + δ := by
    have e : α * x * yhi + β * x + γ * yhi + δ = (α * yhi + β) * x + (γ * yhi + δ) := by ring
    rw [e]
    refine lin_ge (α * yhi + β) k₀ x xlo xhi (γ * yhi + δ) hx1 hx2 ?_ ?_
    · have : (α * yhi + β) * xlo + (γ * yhi + δ) = α * xlo * yhi + β * xlo + γ * yhi + δ := by ring
      rw [this]; exact c_lh
    · have : (α * yhi + β) * xhi + (γ * yhi + δ) = α * xhi * yhi + β * xhi + γ * yhi + δ := by ring
      rw [this]; exact c_hh
  have e : α * x * y + β * x + γ * y + δ = (α * x + γ) * y + (β * x + δ) := by ring
  rw [e]
  refine lin_ge (α * x + γ) k₀ y ylo yhi (β * x + δ) hy1 hy2 ?_ ?_
  · have : (α * x + γ) * ylo + (β * x + δ) = α * x * ylo + β * x + γ * ylo + δ := by ring
    rw [this]; exact hlo
  · have : (α * x + γ) * yhi + (β * x + δ) = α * x * yhi + β * x + γ * yhi + δ := by ring
    rw [this]; exact hhi

/-- **THE BIHOMOGRAPHIC COUPLING TRAP (upper).** Dual of `bilinear_ge`. -/
theorem bilinear_le (α β γ δ xlo xhi ylo yhi x y k₀ : K)
    (hx1 : xlo ≤ x) (hx2 : x ≤ xhi) (hy1 : ylo ≤ y) (hy2 : y ≤ yhi)
    (c_ll : α * xlo * ylo + β * xlo + γ * ylo + δ ≤ k₀)
    (c_hl : α * xhi * ylo + β * xhi + γ * ylo + δ ≤ k₀)
    (c_lh : α * xlo * yhi + β * xlo + γ * yhi + δ ≤ k₀)
    (c_hh : α * xhi * yhi + β * xhi + γ * yhi + δ ≤ k₀) :
    α * x * y + β * x + γ * y + δ ≤ k₀ := by
  have hlo : α * x * ylo + β * x + γ * ylo + δ ≤ k₀ := by
    have e : α * x * ylo + β * x + γ * ylo + δ = (α * ylo + β) * x + (γ * ylo + δ) := by ring
    rw [e]
    refine lin_le (α * ylo + β) k₀ x xlo xhi (γ * ylo + δ) hx1 hx2 ?_ ?_
    · have : (α * ylo + β) * xlo + (γ * ylo + δ) = α * xlo * ylo + β * xlo + γ * ylo + δ := by ring
      rw [this]; exact c_ll
    · have : (α * ylo + β) * xhi + (γ * ylo + δ) = α * xhi * ylo + β * xhi + γ * ylo + δ := by ring
      rw [this]; exact c_hl
  have hhi : α * x * yhi + β * x + γ * yhi + δ ≤ k₀ := by
    have e : α * x * yhi + β * x + γ * yhi + δ = (α * yhi + β) * x + (γ * yhi + δ) := by ring
    rw [e]
    refine lin_le (α * yhi + β) k₀ x xlo xhi (γ * yhi + δ) hx1 hx2 ?_ ?_
    · have : (α * yhi + β) * xlo + (γ * yhi + δ) = α * xlo * yhi + β * xlo + γ * yhi + δ := by ring
      rw [this]; exact c_lh
    · have : (α * yhi + β) * xhi + (γ * yhi + δ) = α * xhi * yhi + β * xhi + γ * yhi + δ := by ring
      rw [this]; exact c_hh
  have e : α * x * y + β * x + γ * y + δ = (α * x + γ) * y + (β * x + δ) := by ring
  rw [e]
  refine lin_le (α * x + γ) k₀ y ylo yhi (β * x + δ) hy1 hy2 ?_ ?_
  · have : (α * x + γ) * ylo + (β * x + δ) = α * x * ylo + β * x + γ * ylo + δ := by ring
    rw [this]; exact hlo
  · have : (α * x + γ) * yhi + (β * x + δ) = α * x * yhi + β * x + γ * yhi + δ := by ring
    rw [this]; exact hhi

/-- **The SE(2) coupling `c·t'` is trapped by its four corners** — the literal bilinear coupling
(`α=1, β=γ=δ=0` in `bilinear_ge`), certified from the rotation-sector × translation-interval
corners, in `emit_traps`' own shape: corner bounds as hypotheses ⟹ the value is trapped. This
is the rotation × translation coupling, four-corner, exact, over the ordered value ring. -/
theorem coupling_ge (clo chi tlo thi c t k₀ : K)
    (hc1 : clo ≤ c) (hc2 : c ≤ chi) (ht1 : tlo ≤ t) (ht2 : t ≤ thi)
    (c_ll : k₀ ≤ clo * tlo) (c_hl : k₀ ≤ chi * tlo)
    (c_lh : k₀ ≤ clo * thi) (c_hh : k₀ ≤ chi * thi) : k₀ ≤ c * t := by
  have h := bilinear_ge 1 0 0 0 clo chi tlo thi c t k₀ hc1 hc2 ht1 ht2
    (by simpa using c_ll) (by simpa using c_hl) (by simpa using c_lh) (by simpa using c_hh)
  simpa using h

/-- Dual coupling trap: corner upper bounds ⟹ `c·t'` bounded above. -/
theorem coupling_le (clo chi tlo thi c t k₀ : K)
    (hc1 : clo ≤ c) (hc2 : c ≤ chi) (ht1 : tlo ≤ t) (ht2 : t ≤ thi)
    (c_ll : clo * tlo ≤ k₀) (c_hl : chi * tlo ≤ k₀)
    (c_lh : clo * thi ≤ k₀) (c_hh : chi * thi ≤ k₀) : c * t ≤ k₀ := by
  have h := bilinear_le 1 0 0 0 clo chi tlo thi c t k₀ hc1 hc2 ht1 ht2
    (by simpa using c_ll) (by simpa using c_hl) (by simpa using c_lh) (by simpa using c_hh)
  simpa using h

/- =====================================================================
   Exact update + the engine (predict tight → update exact, folded).
   ===================================================================== -/

/-- Exact box intersection — the measurement update, no over-approximation. -/
def Box.inter (B M : Box K) : Box K where
  xlo := max B.xlo M.xlo
  xhi := min B.xhi M.xhi
  ylo := max B.ylo M.ylo
  yhi := min B.yhi M.yhi

omit [CommRing K] [IsStrictOrderedRing K] in
/-- Update is exact: a point in both boxes is in their intersection. -/
theorem Box.inter_sound (B M : Box K) (p : K × K) (hB : B.mem p) (hM : M.mem p) :
    (B.inter M).mem p := by
  obtain ⟨hx1, hx2, hy1, hy2⟩ := hB
  obtain ⟨gx1, gx2, gy1, gy2⟩ := hM
  exact ⟨max_le hx1 gx1, le_min hx2 gx2, max_le hy1 gy1, le_min hy2 gy2⟩

/-- The hull of two boxes (smallest axis-aligned box containing both). -/
def Box.hull (B C : Box K) : Box K where
  xlo := min B.xlo C.xlo
  xhi := max B.xhi C.xhi
  ylo := min B.ylo C.ylo
  yhi := max B.yhi C.yhi

omit [CommRing K] [IsStrictOrderedRing K] in
theorem Box.mem_hull_left {B C : Box K} {p : K × K} (h : B.mem p) : (B.hull C).mem p := by
  obtain ⟨hx1, hx2, hy1, hy2⟩ := h
  exact ⟨le_trans (min_le_left _ _) hx1, le_trans hx2 (le_max_left _ _),
         le_trans (min_le_left _ _) hy1, le_trans hy2 (le_max_left _ _)⟩

omit [CommRing K] [IsStrictOrderedRing K] in
theorem Box.mem_hull_right {B C : Box K} {p : K × K} (h : C.mem p) : (B.hull C).mem p := by
  obtain ⟨hx1, hx2, hy1, hy2⟩ := h
  exact ⟨le_trans (min_le_right _ _) hx1, le_trans hx2 (le_max_right _ _),
         le_trans (min_le_right _ _) hy1, le_trans hy2 (le_max_right _ _)⟩

omit [IsStrictOrderedRing K] in
/-- Hulling only grows a box, so membership survives the whole fold. -/
theorem foldl_hull_mono (B : Box K) (q : K × K) :
    ∀ (Ts : List (Aff K)) (acc : Box K), acc.mem q →
      (Ts.foldl (fun a S => Box.hull a (S.bbox B)) acc).mem q := by
  intro Ts
  induction Ts with
  | nil => intro acc h; exact h
  | cons U Us ih => intro acc h; exact ih _ (Box.mem_hull_left h)

/-- Any member's image is covered by the fold. -/
theorem foldl_hull_covers (B : Box K) (p : K × K) (hp : B.mem p) :
    ∀ (Ts : List (Aff K)) (acc : Box K) (T : Aff K), T ∈ Ts →
      (Ts.foldl (fun a S => Box.hull a (S.bbox B)) acc).mem (T.apply p) := by
  intro Ts
  induction Ts with
  | nil => intro acc T hT; simp at hT
  | cons U Us ih =>
    intro acc T hT
    rcases List.mem_cons.mp hT with h | h
    · subst h
      exact foldl_hull_mono B (T.apply p) Us _ (Box.mem_hull_right (T.bbox_sound B p hp))
    · exact ih (Box.hull acc (U.bbox B)) T h

/-- **Predict under a ROTATION-UNCERTAINTY SECTOR.** `Ts` is the certified floor-free sector
(`CircleEmit.emitSector`) lifted to its member rotation-motions; `bboxSet` over-approximates all
at once — the predicted box INFLATES with the rotation uncertainty (the rotation→translation
curvature bleed), certified and tight per member. Where the circle half meets the box half. -/
def Aff.bboxSet : List (Aff K) → Box K → Box K
  | [], _ => ⟨1, 0, 1, 0⟩
  | T :: Ts, B => Ts.foldl (fun acc S => Box.hull acc (S.bbox B)) (T.bbox B)

/-- **The sector predict is sound.** For ANY rotation in the sector and ANY box point, the moved
pose lands in the inflated box. -/
theorem Aff.bboxSet_sound (Ts : List (Aff K)) (B : Box K) (T : Aff K) (p : K × K)
    (hT : T ∈ Ts) (hp : B.mem p) : (Aff.bboxSet Ts B).mem (T.apply p) := by
  cases Ts with
  | nil => simp at hT
  | cons U Us =>
    simp only [Aff.bboxSet]
    rcases List.mem_cons.mp hT with h | h
    · subst h
      exact foldl_hull_mono B (T.apply p) Us (T.bbox B) (T.bbox_sound B p hp)
    · exact foldl_hull_covers B p hp Us (U.bbox B) T h

/-- One pose step: predict by the motion (tight bbox), then update by the measurement (exact ∩). -/
def stepPose (B : Box K) (mot : Aff K) (meas : Box K) : Box K := (mot.bbox B).inter meas

/-- Run the engine over a (motion, measurement) stream. -/
def runPose : Box K → List (Aff K × Box K) → Box K
  | B, [] => B
  | B, (mot, meas) :: rest => runPose (stepPose B mot meas) rest

/-- The true pose evolves by composing the motions. -/
def truePose : (K × K) → List (Aff K × Box K) → (K × K)
  | p, [] => p
  | p, (mot, _) :: rest => truePose (mot.apply p) rest

/-- Every measurement really does contain the moved truth (the soundness premise). -/
def measOK : (K × K) → List (Aff K × Box K) → Prop
  | _, [] => True
  | p, (mot, meas) :: rest => meas.mem (mot.apply p) ∧ measOK (mot.apply p) rest

/-- **THE ENGINE IS SOUND — with a TIGHT bound at every step.** Through non-commutative
composition, the true pose stays inside the box: the four-corner bbox (`bbox_sound`) not a
decoupled hull, the update exact (`inter_sound`). Certified, exact, generic over the value ring. -/
theorem runPose_sound : ∀ (steps : List (Aff K × Box K)) (B : Box K) (p : K × K),
    B.mem p → measOK p steps → (runPose B steps).mem (truePose p steps) := by
  intro steps
  induction steps with
  | nil => intro B p hp _; exact hp
  | cons head rest ih =>
    intro B p hp hms
    obtain ⟨mot, meas⟩ := head
    obtain ⟨hmeas, hrest⟩ := hms
    exact ih (stepPose B mot meas) (mot.apply p)
      (Box.inter_sound _ _ _ (mot.bbox_sound _ _ hp) hmeas) hrest

/- =====================================================================
   Demos (executable): ℤ grid rotation (exact) + ℚ fine rotation (rational).
   ===================================================================== -/

/-- An exact 90° rotation over `ℤ` (det-1, grid-preserving). -/
def rot90 : Aff ℤ := ⟨0, -1, 1, 0, 0, 0⟩

/-- The identity motion (`0°`) over `ℤ`. -/
def rot0 : Aff ℤ := ⟨1, 0, 0, 1, 0, 0⟩

/-- A det-1 shear over `ℤ` (non-grid) — slants a box into a parallelogram. -/
def shear : Aff ℤ := ⟨1, 1, 0, 1, 0, 0⟩

-- 90° of `[0,2]²` is EXACTLY `[-2,0]×[0,2]` (no slack); the shear over-approximates to `[0,4]×[0,2]`.
#eval rot90.bbox ⟨0, 2, 0, 2⟩            -- {-2, 0, 0, 2}
#eval shear.bbox ⟨0, 2, 0, 2⟩            -- {0, 4, 0, 2}
-- A rotation-uncertainty sector `{0°, 90°}` inflates `[0,2]²` to `[-2,2]×[0,2]`.
#eval Aff.bboxSet [rot0, rot90] ⟨0, 2, 0, 2⟩   -- {-2, 2, 0, 2}

/-- The grid rotation is exact (machine-checked). -/
theorem rot90_exact : rot90.bbox ⟨0, 2, 0, 2⟩ = ⟨-2, 0, 0, 2⟩ := by
  simp only [rot90, Aff.bbox]; norm_num

/-- A **genuine fine rotation over `ℚ`**: `cos = 3/5, sin = 4/5` — the Pythagorean `(3,4,5)`
rotation by `atan(4/3) ≈ 53°`, det 1, exact and rational (no float, no 90° restriction). -/
def pyth : Aff ℚ := ⟨3/5, -4/5, 4/5, 3/5, 0, 0⟩

-- `pyth` sends `[0,5]²` to a tilted square; its exact-rational bbox is `[-4,3]×[0,7]`.
#eval pyth.bbox ⟨0, 5, 0, 5⟩             -- {-4, 3, 0, 7}

/-- The fine rational rotation's bbox is exact-rational and machine-checked. -/
theorem pyth_bbox : pyth.bbox ⟨0, 5, 0, 5⟩ = ⟨-4, 3, 0, 7⟩ := by
  simp only [pyth, Aff.bbox]; norm_num

end SE2Engine

end FdrsFormal.Modes.SyntheticPlace
