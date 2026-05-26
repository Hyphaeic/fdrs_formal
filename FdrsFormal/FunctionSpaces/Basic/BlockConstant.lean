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

# Block-Constant Subspaces

This file defines the block-constant subspaces 𝕋_L(V) of tensors that are
constant on each cylinder at resolution L.

## Mathematical Content (fdrs.md lines 589-596)

**Definition 19 (Block-Constant Subspaces)**:
For each L ≥ 1, define
  𝕋_L(V) := {f ∈ 𝕋(V) : f is constant on every U(s), s ∈ Σ_L}.

Equivalently, f ∈ 𝕋_L(V) iff f is ℱ_L-measurable and depends only on the first L digits.

## Implementation Notes

- BlockConstantSpace L is a subtype of TensorSpace
- Elements are functions that factor through the prefix projection π_L
- This is the finite-dimensional approximation at resolution L
- dim(𝕋_L(V)) = B_L · dim(V)

## References

- fdrs.md, Section 2, Definition 19 (lines 589-596)
- THEOREM_MAPPING.md, FunctionSpaces/Basic section
-/

import FdrsFormal.FunctionSpaces.Basic.TensorSpace

namespace FdrsFormal.FunctionSpaces.Basic

open FdrsFormal.Core.Primitives FdrsFormal.Core.Infinite

/-!
## Block-Constant Definition
-/

/--
A tensor f is block-constant at level L if it is constant on each cylinder U(s).

**fdrs.md**: f ∈ 𝕋_L(V) iff f is constant on every U(s), s ∈ Σ_L.
-/
def IsBlockConstant {b : RadixSeq} {V : Type*} (f : TensorSpace b V) (L : ℕ) : Prop :=
  ∀ s : PrefixSet b L, ∀ x y : CompletedSpace b,
    x ∈ cylinderSet b L s → y ∈ cylinderSet b L s → f x = f y

/--
Alternative characterization: f depends only on the first L digits.
-/
def IsBlockConstant' {b : RadixSeq} {V : Type*} (f : TensorSpace b V) (L : ℕ) : Prop :=
  ∀ x y : CompletedSpace b, prefixOf b L x = prefixOf b L y → f x = f y

/--
The two characterizations are equivalent.
-/
theorem isBlockConstant_iff_isBlockConstant' {b : RadixSeq} {V : Type*}
    (f : TensorSpace b V) (L : ℕ) :
    IsBlockConstant f L ↔ IsBlockConstant' f L := by
  constructor
  · intro h x y hxy
    have hx := mem_cylinderSet_prefixOf b L x
    rw [hxy] at hx
    exact h (prefixOf b L y) x y hx (mem_cylinderSet_prefixOf b L y)
  · intro h s x y hx hy
    apply h
    rw [mem_cylinderSet_iff_prefixOf] at hx hy
    rw [hx, hy]

/--
The block-constant subspace 𝕋_L(V).

**fdrs.md Definition 19**: 𝕋_L(V) := {f ∈ 𝕋(V) : f is constant on every U(s), s ∈ Σ_L}
-/
def BlockConstantSpace (b : RadixSeq) (L : ℕ) (V : Type*) : Type _ :=
  {f : TensorSpace b V // IsBlockConstant f L}

/--
Coercion from BlockConstantSpace to TensorSpace.
-/
instance {b : RadixSeq} {L : ℕ} {V : Type*} : CoeOut (BlockConstantSpace b L V) (TensorSpace b V) :=
  ⟨Subtype.val⟩

/-!
## Construction from Prefix Functions
-/

/--
Any function on prefixes defines a block-constant tensor.

This is the inverse of the coordinate representation.
-/
def liftPrefix {b : RadixSeq} {L : ℕ} {V : Type*} (a : PrefixSet b L → V) :
    BlockConstantSpace b L V where
  val := fun x => a (prefixOf b L x)
  property := by
    intro s x y hx hy
    simp only
    rw [mem_cylinderSet_iff_prefixOf] at hx hy
    rw [hx, hy]

/--
The block-constant tensor determined by a prefix function.
-/
def BlockConstantSpace.ofPrefixFun {b : RadixSeq} {L : ℕ} {V : Type*}
    (a : PrefixSet b L → V) : BlockConstantSpace b L V :=
  liftPrefix a

/-!
## Algebraic Structure
-/

section Algebra

variable {b : RadixSeq} {L : ℕ} {V : Type*}

/--
Zero in BlockConstantSpace.
-/
instance [Zero V] : Zero (BlockConstantSpace b L V) where
  zero := ⟨0, fun _ _ _ _ _ => rfl⟩

/--
Addition in BlockConstantSpace.
-/
instance [Add V] : Add (BlockConstantSpace b L V) where
  add f g := ⟨f.val + g.val, by
    intro s x y hx hy
    show (f.val + g.val) x = (f.val + g.val) y
    rw [Pi.add_apply, Pi.add_apply, f.property s x y hx hy, g.property s x y hx hy]⟩

/--
Negation in BlockConstantSpace.
-/
instance [Neg V] : Neg (BlockConstantSpace b L V) where
  neg f := ⟨-f.val, by
    intro s x y hx hy
    show (-f.val) x = (-f.val) y
    rw [Pi.neg_apply, Pi.neg_apply, f.property s x y hx hy]⟩

/--
Subtraction in BlockConstantSpace.
-/
instance [Sub V] : Sub (BlockConstantSpace b L V) where
  sub f g := ⟨f.val - g.val, by
    intro s x y hx hy
    show (f.val - g.val) x = (f.val - g.val) y
    rw [Pi.sub_apply, Pi.sub_apply, f.property s x y hx hy, g.property s x y hx hy]⟩

/--
Scalar multiplication in BlockConstantSpace.
-/
instance [SMul R V] : SMul R (BlockConstantSpace b L V) where
  smul r f := ⟨r • f.val, by
    intro s x y hx hy
    show (r • f.val) x = (r • f.val) y
    rw [Pi.smul_apply, Pi.smul_apply, f.property s x y hx hy]⟩

/--
BlockConstantSpace is an AddCommMonoid when V is.
-/
instance instAddCommMonoidBlockConstantSpace [AddCommMonoid V] : AddCommMonoid (BlockConstantSpace b L V) :=
  Function.Injective.addCommMonoid
    (fun f => f.val)
    Subtype.val_injective
    rfl
    (fun _ _ => rfl)
    (fun _ _ => rfl)

/--
BlockConstantSpace is an AddCommGroup when V is.
-/
instance instAddCommGroupBlockConstantSpace [AddCommGroup V] : AddCommGroup (BlockConstantSpace b L V) :=
  Function.Injective.addCommGroup
    (fun f => f.val)
    Subtype.val_injective
    rfl
    (fun _ _ => rfl)
    (fun _ => rfl)
    (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun _ _ => rfl)

/--
BlockConstantSpace is a Module when V is.
-/
instance instModuleBlockConstantSpace [Semiring R] [AddCommMonoid V] [Module R V] :
    Module R (BlockConstantSpace b L V) where
  one_smul := fun f => Subtype.ext (one_smul R f.val)
  mul_smul := fun r s f => Subtype.ext (mul_smul r s f.val)
  smul_zero := fun r => Subtype.ext (smul_zero r)
  smul_add := fun r f g => Subtype.ext (smul_add r f.val g.val)
  add_smul := fun r s f => Subtype.ext (add_smul r s f.val)
  zero_smul := fun f => Subtype.ext (zero_smul R f.val)

end Algebra

/-!
## Nesting of Block-Constant Spaces

𝕋_L(V) ⊆ 𝕋_{L+1}(V): coarser resolutions are included in finer ones.
-/

/--
If f is block-constant at level L, it is also block-constant at level L+1.

**Proof idea**: Cylinders at level L+1 are subsets of cylinders at level L,
so constancy on level-L cylinders implies constancy on level-(L+1) cylinders.
-/
theorem isBlockConstant_of_le {b : RadixSeq} {V : Type*} {f : TensorSpace b V}
    {L M : ℕ} (hLM : L ≤ M) (hf : IsBlockConstant f L) : IsBlockConstant f M := by
  -- Use the alternative characterization: f depends only on first L digits
  rw [isBlockConstant_iff_isBlockConstant'] at hf ⊢
  intro x y hxy
  -- If x and y agree on first M digits, they agree on first L digits (since L ≤ M)
  apply hf
  -- Need: prefixOf b L x = prefixOf b L y
  funext i
  simp only [prefixOf]
  -- i : Fin L, so i.val < L ≤ M
  have hi_lt_M : i.val < M := Nat.lt_of_lt_of_le i.isLt hLM
  -- Use hxy at position i
  exact congrFun hxy ⟨i.val, hi_lt_M⟩

/--
Embedding 𝕋_L(V) ↪ 𝕋_{L+1}(V).
-/
def BlockConstantSpace.coarsenTo {b : RadixSeq} {L : ℕ} {V : Type*}
    (f : BlockConstantSpace b L V) : BlockConstantSpace b (L + 1) V :=
  ⟨f.val, isBlockConstant_of_le (Nat.le_succ L) f.property⟩

/--
The union ⋃_L 𝕋_L(V) consists of all "finite-resolution" tensors.
-/
def IsFiniteResolution {b : RadixSeq} {V : Type*} (f : TensorSpace b V) : Prop :=
  ∃ L : ℕ, IsBlockConstant f L

/-!
## Evaluation on Cylinders
-/

/--
A block-constant function has a well-defined value on each cylinder.
-/
def BlockConstantSpace.evalCylinder {b : RadixSeq} {L : ℕ} {V : Type*}
    (f : BlockConstantSpace b L V) (s : PrefixSet b L) : V :=
  -- Pick any representative point in the cylinder
  f.val (fun i => if h : i < L then s ⟨i, h⟩ else ⟨0, b.pos i⟩)

/--
The cylinder value is independent of the representative chosen.
-/
theorem BlockConstantSpace.evalCylinder_eq {b : RadixSeq} {L : ℕ} {V : Type*}
    (f : BlockConstantSpace b L V) (s : PrefixSet b L) (x : CompletedSpace b)
    (hx : x ∈ cylinderSet b L s) :
    f.val x = f.evalCylinder s := by
  -- The representative point used in evalCylinder
  set rep : CompletedSpace b := fun i => if h : i < L then s ⟨i, h⟩ else ⟨0, b.pos i⟩ with hrep_def
  -- Show rep is in the cylinder
  have hrep : rep ∈ cylinderSet b L s := by
    intro i
    simp only [rep, i.isLt, ↓reduceDIte]
  -- Apply block-constant property
  exact f.property s x rep hx hrep

end FdrsFormal.FunctionSpaces.Basic
