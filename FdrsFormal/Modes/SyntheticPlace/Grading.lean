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

# Synthetic place complex SU6a — grading: when "bigger" exists (the holonomy dichotomy)

First stone of the digit-coupling layer (`docs/synthetic-place/03-digit-coupling.md`
§grading). On a single radix line, "size" looks like a property of digit positions —
but its two readings (composition: one increment of position `p` is worth `B_p`
units; activity: position `p` is touched once per `B_p` units) are reciprocal
currencies of the same EDGE datum: the coupling ratio. Size is not a node property;
it is **a multiplicative cocycle on the coupling graph**, composing along paths.
Left/right is not geometry — it is exactness:

* **`gradable_holonomy`** — in a gradable complex (one admitting a global positive
  magnitude with `w(tgt) = ratio · w(src)` on every edge), EVERY closed walk has
  ratio-product `1`. Global size exists only when the holonomy is trivial.
* **`chainGraph_gradable`** — the standard number line is the graded case: path
  topology has no loops, and the witness potential is exactly the place value
  (`chainPotential` = `B_i`). "Most significant digit" is well-defined *because*
  chains are trees.
* **`frustratedTriangle_not_gradable`** — THE FRUSTRATED WITNESS, machine-checked: a
  three-digit complex, each overflowing into the next at ratio `2` around a loop
  (loop factor `8 ≠ 1`). Dynamically perfectly well-defined; yet **no global notion
  of bigger/smaller exists** — a Penrose staircase of digits. Size in this complex is
  irreducibly relational.

With Prop 148 (raggedness — kills the rank chart) and Theorem 90 (bilaterality —
kills separable conservation), this gives the radix complex its **third independent
obstruction to being a number system**: frustration kills global magnitude. A
coupling complex is "a number" exactly when it clears all three; each failure leaves
a specific survivor (geometry, balance, per-edge ratios respectively).

The converse holds too (`gradable_of_trivial_holonomy`): on a connected complex,
trivial holonomy is sufficient — weigh every node by the factor of any walk from a
base; holonomy-triviality makes the choice immaterial. Together: **a connected
coupling complex is gradable IFF every loop has ratio-product 1** — the full
characterization of when "bigger" exists.

**Honest scope.** Potentials-on-graphs is classical mathematics (gauge theory on
graphs / discrete potential theory); the contribution is the placement and the
verified witnesses. Connectivity is stated as walk-reachability from a base node.
Leaf module. No `sorry`; axiom-clean.
-/
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.BigOperators.Group.List.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

namespace FdrsFormal.Modes.SyntheticPlace

/-! ## 1. Coupling graphs and traversals -/

/-- **A coupling graph**: digit nodes joined by directed coupling edges, each
carrying its ratio — how many source-increments one target-increment is worth
(composition currency; its reciprocal is the carry frequency). -/
structure CouplingGraph (V : Type*) where
  Edge : Type*
  src : Edge → V
  tgt : Edge → V
  ratio : Edge → ℚ
  ratio_pos : ∀ e, 0 < ratio e

namespace CouplingGraph

variable {V : Type*} (G : CouplingGraph V)

/-- A traversal step: an edge crossed forward (`true`) or backward (`false`). -/
def Step := G.Edge × Bool

def stepSrc (s : G.Step) : V := if s.2 then G.src s.1 else G.tgt s.1

def stepTgt (s : G.Step) : V := if s.2 then G.tgt s.1 else G.src s.1

/-- The size factor of a step: the ratio forward, its reciprocal backward. -/
def stepFactor (s : G.Step) : ℚ := if s.2 then G.ratio s.1 else (G.ratio s.1)⁻¹

/-- `IsWalk u steps v`: the steps chain from `u` to `v` through the graph. -/
def IsWalk : V → List G.Step → V → Prop
  | u, [], v => u = v
  | u, s :: rest, v => G.stepSrc s = u ∧ IsWalk (G.stepTgt s) rest v

/-- The size factor of a walk: the product of its step factors — size composes
multiplicatively along coupling paths. -/
def walkFactor (steps : List G.Step) : ℚ := (steps.map G.stepFactor).prod

@[simp] theorem walkFactor_nil : G.walkFactor [] = 1 := rfl

theorem walkFactor_cons (s : G.Step) (rest : List G.Step) :
    G.walkFactor (s :: rest) = G.stepFactor s * G.walkFactor rest := by
  simp [walkFactor, List.prod_cons]

/-! ## 2. Gradability: a global magnitude -/

/-- **Gradable**: the complex admits a global positive magnitude whose edge-wise law
is the coupling ratio — i.e., the size cocycle is exact, "bigger/smaller" is globally
well-defined. -/
def Gradable : Prop :=
  ∃ w : V → ℚ, (∀ v, 0 < w v) ∧ ∀ e, w (G.tgt e) = G.ratio e * w (G.src e)

theorem potential_step {w : V → ℚ}
    (hw : ∀ e, w (G.tgt e) = G.ratio e * w (G.src e)) (s : G.Step) :
    w (G.stepTgt s) = G.stepFactor s * w (G.stepSrc s) := by
  rcases s with ⟨e, b⟩
  cases b
  · simp only [stepSrc, stepTgt, stepFactor, Bool.false_eq_true, if_false]
    rw [hw e, inv_mul_cancel_left₀ (G.ratio_pos e).ne']
  · simp only [stepSrc, stepTgt, stepFactor, if_true]
    exact hw e

theorem potential_walk {w : V → ℚ}
    (hw : ∀ e, w (G.tgt e) = G.ratio e * w (G.src e)) :
    ∀ (steps : List G.Step) (u v : V), G.IsWalk u steps v →
      w v = G.walkFactor steps * w u := by
  intro steps
  induction steps with
  | nil =>
    intro u v h
    have huv : u = v := h
    subst huv
    simp
  | cons s rest ih =>
    intro u v h
    obtain ⟨hsrc, hrest⟩ := h
    have h1 := ih (G.stepTgt s) v hrest
    have h2 := G.potential_step hw s
    rw [hsrc] at h2
    rw [h1, h2, walkFactor_cons]
    ring

/-- **SU6a — THE HOLONOMY THEOREM.** In a gradable coupling complex, every closed
walk has size factor `1`: global magnitude exists only with trivial holonomy.
Direction is not geometry — it is exactness of the size cocycle. -/
theorem gradable_holonomy (hG : G.Gradable) {u : V} {steps : List G.Step}
    (h : G.IsWalk u steps u) : G.walkFactor steps = 1 := by
  obtain ⟨w, hpos, hw⟩ := hG
  have h1 := G.potential_walk hw steps u u h
  have h2 := hpos u
  have h3 : G.walkFactor steps * w u = 1 * w u := by linarith
  exact mul_right_cancel₀ (ne_of_gt h2) h3

/-! ## 2b. The converse: trivial holonomy suffices (the full characterization) -/

/-- Reverse a traversal step (flip its direction). -/
def revStep (s : G.Step) : G.Step := (s.1, !s.2)

@[simp] theorem stepSrc_revStep (s : G.Step) : G.stepSrc (G.revStep s) = G.stepTgt s := by
  rcases s with ⟨e, b⟩
  cases b <;> simp [revStep, stepSrc, stepTgt]

@[simp] theorem stepTgt_revStep (s : G.Step) : G.stepTgt (G.revStep s) = G.stepSrc s := by
  rcases s with ⟨e, b⟩
  cases b <;> simp [revStep, stepSrc, stepTgt]

theorem stepFactor_revStep (s : G.Step) :
    G.stepFactor (G.revStep s) = (G.stepFactor s)⁻¹ := by
  rcases s with ⟨e, b⟩
  cases b <;> simp [revStep, stepFactor, inv_inv]

theorem stepFactor_pos (s : G.Step) : 0 < G.stepFactor s := by
  rcases s with ⟨e, b⟩
  cases b
  · simpa [stepFactor] using inv_pos.mpr (G.ratio_pos e)
  · simpa [stepFactor] using G.ratio_pos e

/-- Reverse a walk: reverse the steps and flip each one. -/
def revWalk (steps : List G.Step) : List G.Step := steps.reverse.map G.revStep

theorem isWalk_append {u v x : V} {s t : List G.Step}
    (hs : G.IsWalk u s v) (ht : G.IsWalk v t x) : G.IsWalk u (s ++ t) x := by
  induction s generalizing u with
  | nil =>
    have huv : u = v := hs
    subst huv
    simpa using ht
  | cons a rest ih =>
    obtain ⟨ha, hrest⟩ := hs
    exact ⟨ha, ih hrest⟩

theorem isWalk_revWalk {u v : V} {s : List G.Step} (h : G.IsWalk u s v) :
    G.IsWalk v (G.revWalk s) u := by
  induction s generalizing u with
  | nil =>
    have huv : u = v := h
    subst huv
    simp [revWalk, IsWalk]
  | cons a rest ih =>
    obtain ⟨ha, hrest⟩ := h
    have hrev : G.revWalk (a :: rest) = G.revWalk rest ++ [G.revStep a] := by
      simp [revWalk, List.reverse_cons]
    rw [hrev]
    apply G.isWalk_append (ih hrest)
    refine ⟨G.stepSrc_revStep a, ?_⟩
    show G.stepTgt (G.revStep a) = u
    rw [G.stepTgt_revStep]
    exact ha

theorem walkFactor_append (s t : List G.Step) :
    G.walkFactor (s ++ t) = G.walkFactor s * G.walkFactor t := by
  simp [walkFactor, List.map_append, List.prod_append]

theorem walkFactor_pos (s : List G.Step) : 0 < G.walkFactor s := by
  induction s with
  | nil => norm_num
  | cons a rest ih =>
    rw [walkFactor_cons]
    exact mul_pos (G.stepFactor_pos a) ih

theorem walkFactor_revWalk (s : List G.Step) :
    G.walkFactor (G.revWalk s) = (G.walkFactor s)⁻¹ := by
  induction s with
  | nil => simp [revWalk]
  | cons a rest ih =>
    have hrev : G.revWalk (a :: rest) = G.revWalk rest ++ [G.revStep a] := by
      simp [revWalk, List.reverse_cons]
    rw [hrev, G.walkFactor_append, ih, G.walkFactor_cons, G.walkFactor_nil,
        G.stepFactor_revStep, G.walkFactor_cons]
    have h1 := (G.stepFactor_pos a).ne'
    have h2 := (G.walkFactor_pos rest).ne'
    field_simp

/-- **THE HOLONOMY CONVERSE.** On a connected complex (every node walk-reachable
from a base), trivial holonomy SUFFICES for gradability: weigh each node by the
factor of any walk from the base — closing any two such walks into a loop shows the
choice immaterial, and closing the triangle over an edge yields the edge law. With
`gradable_holonomy`, the dichotomy is a full characterization: **a connected coupling
complex admits a global magnitude iff every loop has ratio-product 1.** -/
theorem gradable_of_trivial_holonomy (base : V)
    (hconn : ∀ v : V, ∃ steps : List G.Step, G.IsWalk base steps v)
    (hhol : ∀ (u : V) (steps : List G.Step), G.IsWalk u steps u →
      G.walkFactor steps = 1) :
    G.Gradable := by
  classical
  choose path hpath using hconn
  refine ⟨fun v => G.walkFactor (path v), fun v => G.walkFactor_pos (path v), ?_⟩
  intro e
  have hstep : G.IsWalk (G.src e) ([(e, true)] : List G.Step) (G.tgt e) := ⟨rfl, rfl⟩
  have hloopwalk : G.IsWalk base
      (path (G.src e) ++ (([(e, true)] : List G.Step) ++ G.revWalk (path (G.tgt e)))) base := by
    apply G.isWalk_append (hpath (G.src e))
    exact G.isWalk_append hstep (G.isWalk_revWalk (hpath (G.tgt e)))
  have hloop := hhol base _ hloopwalk
  rw [G.walkFactor_append, G.walkFactor_append, G.walkFactor_revWalk,
      G.walkFactor_cons, G.walkFactor_nil] at hloop
  have hsf : G.stepFactor ((e, true) : G.Step) = G.ratio e := rfl
  rw [hsf] at hloop
  have hne : G.walkFactor (path (G.tgt e)) ≠ 0 := (G.walkFactor_pos (path (G.tgt e))).ne'
  have hres : (G.ratio e * G.walkFactor (path (G.src e)))
      * (G.walkFactor (path (G.tgt e)))⁻¹ = 1 := by
    rw [← hloop]; ring
  exact ((mul_inv_eq_one₀ hne).mp hres).symm

end CouplingGraph

/-! ## 3. The graded witness: the standard number line -/

/-- The standard radix line as a coupling chain: positions, each overflowing into the
next at its radix. Path topology — no loops. -/
def chainGraph (b : ℕ → ℕ) (hb : ∀ i, 0 < b i) : CouplingGraph ℕ where
  Edge := ℕ
  src e := e
  tgt e := e + 1
  ratio e := (b e : ℚ)
  ratio_pos e := by exact_mod_cast hb e

/-- The chain's global magnitude IS the place value `B_i`. -/
def chainPotential (b : ℕ → ℕ) : ℕ → ℚ
  | 0 => 1
  | i + 1 => (b i : ℚ) * chainPotential b i

/-- **The graded case**: the number line admits a global magnitude — the place value.
"Most significant digit" is well-defined because chains are trees: the holonomy
condition is vacuous. -/
theorem chainGraph_gradable (b : ℕ → ℕ) (hb : ∀ i, 0 < b i) :
    (chainGraph b hb).Gradable := by
  refine ⟨chainPotential b, ?_, fun e => rfl⟩
  intro v
  induction v with
  | zero => norm_num [chainPotential]
  | succ i ih =>
    have hbi : (0 : ℚ) < (b i : ℚ) := by exact_mod_cast hb i
    simpa [chainPotential] using mul_pos hbi ih

/-! ## 4. The frustrated witness: a Penrose staircase of digits -/

/-- Three digits, each overflowing into the next around a loop, each edge worth `2`:
A "bigger" than B, B than C, C than A. -/
def frustratedTriangle : CouplingGraph (Fin 3) where
  Edge := Fin 3
  src e := e
  tgt e := e + 1
  ratio _ := 2
  ratio_pos _ := by norm_num

/-- **SU6a — THE FRUSTRATED WITNESS (machine-checked).** The triangle admits NO
global magnitude: any candidate satisfies `w₀ = 2w₂ = 4w₁ = 8w₀`, forcing `w₀ ≤ 0`.
Size in this complex is irreducibly relational — "bigger" provably does not exist,
while the dynamics (and the per-edge balance laws of SU4b) remain perfectly
well-defined. The third obstruction to number-hood. -/
theorem frustratedTriangle_not_gradable : ¬ frustratedTriangle.Gradable := by
  rintro ⟨w, hpos, hw⟩
  have h0 := hw (0 : Fin 3)
  have h1 := hw (1 : Fin 3)
  have h2 := hw (2 : Fin 3)
  have e0 : ((0 : Fin 3) + 1) = 1 := by decide
  have e1 : ((1 : Fin 3) + 1) = 2 := by decide
  have e2 : ((2 : Fin 3) + 1) = 0 := by decide
  simp only [frustratedTriangle, e0, e1, e2] at h0 h1 h2
  have p0 := hpos 0
  have p1 := hpos 1
  have p2 := hpos 2
  linarith

-- the holonomy obstruction, computable: the loop factor around the triangle is 8 ≠ 1
#eval frustratedTriangle.walkFactor [((0 : Fin 3), true), ((1 : Fin 3), true), ((2 : Fin 3), true)]   -- 8

/-- The closed loop around the triangle, explicitly. -/
theorem frustrated_loop_isWalk :
    frustratedTriangle.IsWalk 0 [((0 : Fin 3), true), ((1 : Fin 3), true), ((2 : Fin 3), true)] 0 := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> first | rfl | decide

/-- Its size factor is `8` — by `gradable_holonomy`, an independent proof that the
triangle is ungradable (`8 ≠ 1`). -/
theorem frustrated_loop_factor :
    frustratedTriangle.walkFactor [((0 : Fin 3), true), ((1 : Fin 3), true), ((2 : Fin 3), true)] = 8 := by
  simp only [CouplingGraph.walkFactor, CouplingGraph.stepFactor, frustratedTriangle,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, if_true]
  norm_num

end FdrsFormal.Modes.SyntheticPlace
