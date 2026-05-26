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

# Mixed-Radix Tensor Space

This file defines the tensor space 𝕋(V) of functions from R̂ to a coefficient space V.

## Mathematical Content (fdrs.md lines 581-587)

**Definition 18 (Mixed-Radix Tensor Space)**:
  𝕋(V) := {f : R̂ → V}

This is the basic "tensor-like" object: it is indexed by a mixed-radix coordinate
rather than by ℝⁿ.

## Implementation Notes

- For generality, V is a type with appropriate algebraic structure
- When V is a Banach space, 𝕋(V) inherits rich structure
- When V is an abelian group, we get 𝕋(V) as an abelian group
- The key subspaces are the block-constant spaces 𝕋_L(V)

## References

- fdrs.md, Section 2, Definition 18 (lines 581-587)
- THEOREM_MAPPING.md, FunctionSpaces/Basic section
-/

import FdrsFormal.FunctionSpaces.Basic.Cylinder
import Mathlib.Logic.Basic

open scoped Classical

namespace FdrsFormal.FunctionSpaces.Basic

open FdrsFormal.Core.Primitives FdrsFormal.Core.Infinite

/-!
## Tensor Space Definition
-/

/--
The mixed-radix tensor space 𝕋(V): all functions from R̂ to V.

**fdrs.md Definition 18**: 𝕋(V) := {f : R̂ → V}

This is the space of "tensors" indexed by mixed-radix coordinates.
-/
def TensorSpace (b : RadixSeq) (V : Type*) : Type _ :=
  CompletedSpace b → V

/--
Alternative notation emphasizing the function space structure.
-/
abbrev Tensor (b : RadixSeq) (V : Type*) := TensorSpace b V

/-!
## Algebraic Structure

When V has algebraic structure, TensorSpace inherits it pointwise.
-/

section Algebra

variable {b : RadixSeq} {V : Type*}

/--
Zero tensor when V has a zero.
-/
instance [Zero V] : Zero (TensorSpace b V) where
  zero := fun _ => 0

/--
Tensor addition when V is an AddGroup.
-/
instance [Add V] : Add (TensorSpace b V) where
  add f g := fun x => f x + g x

/--
Tensor negation when V has negation.
-/
instance [Neg V] : Neg (TensorSpace b V) where
  neg f := fun x => -f x

/--
Tensor subtraction when V has subtraction.
-/
instance [Sub V] : Sub (TensorSpace b V) where
  sub f g := fun x => f x - g x

/--
Scalar multiplication when V is a module.
-/
instance [SMul R V] : SMul R (TensorSpace b V) where
  smul r f := fun x => r • f x

/--
TensorSpace is an AddCommMonoid when V is.
-/
instance [AddCommMonoid V] : AddCommMonoid (TensorSpace b V) :=
  Pi.addCommMonoid

/--
TensorSpace is an AddCommGroup when V is.
-/
instance [AddCommGroup V] : AddCommGroup (TensorSpace b V) :=
  Pi.addCommGroup

/--
TensorSpace is a Module when V is.
-/
instance [Semiring R] [AddCommMonoid V] [Module R V] : Module R (TensorSpace b V) :=
  Pi.module _ _ _

end Algebra

/-!
## Evaluation and Construction
-/

section Evaluation

variable {b : RadixSeq} {V : Type*}

/--
Evaluate a tensor at a point.
-/
def TensorSpace.eval (f : TensorSpace b V) (x : CompletedSpace b) : V :=
  f x

/--
Construct a tensor from a function.
-/
def TensorSpace.mk (f : CompletedSpace b → V) : TensorSpace b V :=
  f

/--
Constant tensor: f(x) = v for all x.
-/
def TensorSpace.const (v : V) : TensorSpace b V :=
  fun _ => v

/--
Indicator function of a set.
-/
noncomputable def TensorSpace.indicator [Zero V] [One V] (S : Set (CompletedSpace b)) : TensorSpace b V :=
  fun x => if x ∈ S then 1 else 0

/--
Indicator of a cylinder set.
-/
noncomputable def TensorSpace.cylinderIndicator [Zero V] [One V] (L : ℕ) (s : PrefixSet b L) :
    TensorSpace b V :=
  TensorSpace.indicator (cylinderSet b L s)

end Evaluation

/-!
## Support and Cylinder Restriction
-/

section Support

variable {b : RadixSeq} {V : Type*}

/--
A tensor is supported on a set S if it is zero outside S.
-/
def TensorSpace.supportedOn [Zero V] (f : TensorSpace b V) (S : Set (CompletedSpace b)) : Prop :=
  ∀ x, x ∉ S → f x = 0

/--
A tensor is supported on a cylinder.
-/
def TensorSpace.cylinderSupported [Zero V] (f : TensorSpace b V) (L : ℕ) (s : PrefixSet b L) :
    Prop :=
  f.supportedOn (cylinderSet b L s)

/--
Restrict a tensor to a cylinder (zero outside).
-/
noncomputable def TensorSpace.restrictToCylinder [Zero V] (f : TensorSpace b V) (L : ℕ) (s : PrefixSet b L) :
    TensorSpace b V :=
  fun x => if x ∈ cylinderSet b L s then f x else 0

end Support

/-!
## Norm Structure

When V is a normed space, we can define norms on TensorSpace.
-/

section Norm

variable {b : RadixSeq} {V : Type*}

/--
Sup norm of a tensor (when it exists).

This is ‖f‖_∞ = sup_{x ∈ R̂} ‖f(x)‖.
-/
noncomputable def TensorSpace.supNorm [Norm V] (f : TensorSpace b V) : ℝ :=
  ⨆ x : CompletedSpace b, ‖f x‖

/--
A tensor is bounded if its sup norm is finite.
-/
def TensorSpace.IsBounded [Norm V] (f : TensorSpace b V) : Prop :=
  BddAbove (Set.range fun x => ‖f x‖)

end Norm

/-!
## Connection to DirectLimitSpace

We can also consider tensors on DirectLimitSpace (eventually-zero sequences).
-/

section DirectLimit

variable {b : RadixSeq} {V : Type*}

/--
Tensor space on DirectLimitSpace (finite support sequences).
-/
def TensorSpaceFinite (b : RadixSeq) (V : Type*) : Type _ :=
  DirectLimitSpace b → V

/--
Extend a tensor on DirectLimitSpace to CompletedSpace.

This uses the embedding DirectLimitSpace ↪ CompletedSpace.
-/
noncomputable def TensorSpaceFinite.extend [Zero V] (f : TensorSpaceFinite b V) : TensorSpace b V :=
  fun x =>
    -- Check if x has finite support (eventually zero)
    if h : ∃ K, ∀ i > K, x i = ⟨0, b.pos i⟩
    then f ⟨x, h⟩  -- x has finite support, so it's in DirectLimitSpace
    else 0          -- x has infinite support, return 0

end DirectLimit

end FdrsFormal.FunctionSpaces.Basic
