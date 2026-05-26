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
-/
import FdrsFormal.FunctionSpaces.Haar.ContrastBasis
import FdrsFormal.Core
import FdrsFormal.FunctionSpaces.Basic

/-!
# Haar Atoms for Mixed-Radix Spaces

This file defines the global mixed-radix Haar wavelet atoms as tensor products
of contrast vectors at each digit position.

## Main Definitions

* `HaarAtom` - Multi-index α specifying contrast pattern across digit positions
* `haarComponent` - Per-digit basis function: constant 1 or contrast vector
* `haarFunction` - The function h_α : R^(k) → ℝ defined by tensor product

## Main Results

* `haarFunction_product` - h_α factors as product of per-digit components
* `haarComponent_constant` - Component at α_i = 0 is constant 1
* `haarComponent_contrast` - Component at α_i ≥ 1 is a contrast vector

## References

* fdrs.md, Lines 1330-1350: Definition 35 and Theorem 11
-/

open FdrsFormal Core.Primitives

variable {b : RadixSeq} {k : ℕ}

instance RadixSeq.neZero_at (b : RadixSeq) (i : ℕ) : NeZero (b i) := ⟨b.ne_zero i⟩

namespace FdrsFormal.Haar

/--
A Haar multi-index specifies for each digit position i whether to use:
- α_i = 0: constant mode (use 1_i)
- α_i ≥ 1: contrast mode (use ψ^(b_i)_{α_i})

**fdrs.md Reference:** Lines 1330-1344, Definition 35
-/
def HaarAtom (b : RadixSeq) (k : ℕ) := (i : Fin (k + 1)) → Fin (b i)

instance : Fintype (HaarAtom b k) := by unfold HaarAtom; infer_instance
instance : DecidableEq (HaarAtom b k) := by unfold HaarAtom; infer_instance

/--
The component function at digit position i:
- If α_i = 0, returns 1 (constant mode)
- If α_i ≥ 1, returns contrast vector ψ^(b_i)_{α_i - 1}(d_i)

**fdrs.md Reference:** Lines 1339-1344
-/
noncomputable def haarComponent (i : Fin (k + 1)) (αᵢ : Fin (b i)) (dᵢ : Fin (b i)) : ℝ :=
  if h : αᵢ.val = 0 then 1
  else contrastVector (b.ge_two i) ⟨αᵢ.val - 1, by have := αᵢ.isLt; omega⟩ dᵢ

/--
The Haar basis function h_α defined by tensor product:
h_α(d_0,...,d_k) = ∏_{i=0}^k φ_{i,α_i}(d_i)

where φ_{i,0} is constant 1 and φ_{i,a} (a ≥ 1) is contrast vector ψ^(b_i)_{a-1}.

**fdrs.md Reference:** Lines 1335-1344
-/
noncomputable def haarFunction (α : HaarAtom b k) :
    Core.Finite.FiniteRadixSpace b k → ℝ :=
  fun d => ∏ i : Fin (k + 1), haarComponent i (α i) (d i)

-- fdrs.md lines 1335-1344, Definition 35
/--
The Haar function factors as a product of components:
h_α(d) = ∏_i haarComponent(i, α_i, d_i)
-/
@[simp] theorem haarFunction_product (α : HaarAtom b k)
    (d : Core.Finite.FiniteRadixSpace b k) :
    haarFunction α d = ∏ i : Fin (k + 1), haarComponent i (α i) (d i) := rfl

/--
When α_i = 0, the component is constant 1.

**fdrs.md Reference:** Line 1340
-/
@[simp] theorem haarComponent_constant (i : Fin (k + 1)) (dᵢ : Fin (b i)) :
    haarComponent i (0 : Fin (b i)) dᵢ = 1 := by
  simp [haarComponent]

/--
When α_i ≥ 1, the component uses the contrast vector.

**fdrs.md Reference:** Lines 1341-1344
-/
theorem haarComponent_contrast (i : Fin (k + 1)) (a : Fin (b i - 1)) (dᵢ : Fin (b i)) :
    haarComponent i ⟨a.val + 1, by have := a.isLt; have := b.ge_two i; omega⟩ dᵢ =
    contrastVector (b.ge_two i) a dᵢ := by
  simp only [haarComponent, show a.val + 1 ≠ 0 from by omega, ↓reduceDIte,
    show a.val + 1 - 1 = a.val from by omega]

end FdrsFormal.Haar
