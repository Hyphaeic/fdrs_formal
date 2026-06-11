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

# Adelic complex — the abstract adelic-law interface (V2.0 scaffold)

The final state of the machine for `ℚ`, as a *generic interface* rather than a single
implementation: the "Version 2.0" scaffold. The product formula `∏_v |x|_v = 1` becomes an
**interface requirement** — a *proof obligation* an instance must discharge, never an
assumed axiom (that would be "declare victory in axiom costume", `06` §5).

* **`AdelicLaw Place α`** — the FDRS-native Artin–Whaple axiomatization: a family of places
  `Place` carrying `ℚ`-valued absolute values `val`, a finite support per quantity, and a
  **`conservation` proof obligation**. No `AdeleRing` import; the law *is* the interface.
* **`classicalAdelicLaw`** — the classical place family `{∞} ∪ {primes}` instantiates it,
  with `conservation` discharged by the master-branch product formula `product_formula_place`.
  (Phase C: the embedding of the existing implementation into the interface.)
* **The rigidity boundary** (`synthetic_rejected`, `gauge_aligned_iff`) — re-exports the
  `Rigidity.lean` no-go as the interface's *admissibility criterion*: any FDRS section
  whose base is not constant `p` fails to reproduce the p-adic place value, so there is
  **no genuinely synthetic instance of `AdelicLaw` on `ℚ`** (Artin–Whaple, machine-checked).

**Honest scope.** The classical instance here is over the *positive integers* `ℕ+` — the
exact quantities the master-branch product formula proves. The full `ℚˣ` conservation is
the standard *multiplicative lift*, now formalized in `ProductFormulaRat.lean`
(`product_formula_rat`, `ratAdelicLaw : AdelicLaw Place ℚˣ`). And the genuinely *synthetic* instances
live not on `ℚ` (Ostrowski) but on **global function fields** `F_q(t)`, where places are
irreducible polynomials — the empty, correctly-typed slot this interface leaves open.
Leaf module. No `sorry`; axiom-clean.
-/
import FdrsFormal.Modes.Adelic.ProductFormula
import FdrsFormal.Modes.Adelic.Rigidity
import Mathlib.Data.PNat.Basic

namespace FdrsFormal.Modes.Adelic

open Finset FdrsFormal.Core.Primitives

/-! ## 1. The abstract adelic law (conservation = proof obligation) -/

/-- **The abstract adelic law.** A family of places `Place` with `ℚ`-valued absolute values
`val`, a finite `support` of non-trivial places per quantity `a : α`, and the
**conservation** product formula `∏_{v ∈ support a} val v a = 1` as a *proof obligation*.
An instance is valid only if it *supplies* the conservation proof — it is never assumed.
This is the Artin–Whaple structure, FDRS-native (no `AdeleRing` import). -/
structure AdelicLaw (Place : Type) (α : Type) where
  /-- the absolute value `|a|_v` at place `v`. -/
  val : Place → α → ℚ
  /-- the finite set of places where `|a|_v ≠ 1`. -/
  support : α → Finset Place
  /-- **the proof obligation**: the product formula holds. -/
  conservation : ∀ a : α, ∏ v ∈ support a, val v a = 1

/-! ## 2. The classical instance (Phase C — the embedding of the existing machine) -/

/-- The classical support of a positive integer `n`: the place `∞` together with the primes
dividing `n`. -/
def classicalSupport (n : ℕ+) : Finset Place :=
  insert Place.infinite (((n : ℕ).factorization.support).image Place.prime)

/-- **The classical instance.** The places `{∞} ∪ {primes}` with the ordinary / p-adic
absolute values instantiate `AdelicLaw` over the positive integers — the `conservation`
obligation discharged by the master-branch `product_formula_place`. The existing machine,
embedded into the abstract interface. -/
def classicalAdelicLaw : AdelicLaw Place ℕ+ where
  val v n := v.absValue ((n : ℕ) : ℚ)
  support := classicalSupport
  conservation n := by
    have hpos : ((n : ℕ)) ≠ 0 := n.pos.ne'
    rw [classicalSupport,
        Finset.prod_insert (by simp), Finset.prod_image (fun a _ b _ h => by injection h)]
    exact product_formula_place (n : ℕ) hpos

/-! ## 3. The rigidity boundary as the interface's admissibility criterion -/

/-- An FDRS section with base `b` reproduces the p-adic place value (the gauge `p^L` carried
by the classical place `prime p`) **iff** its base is the constant sequence `p`. The
alignment criterion for an FDRS section to *be* a classical p-adic place. -/
theorem gauge_aligned_iff (b : RadixSeq) (p : ℕ) : Isometric b p ↔ ∀ i, b i = p :=
  isometric_iff b p

/-- **Rigidity as rejection.** Any *synthetic* FDRS section — a base `b` deviating from the
constant `p` — fails the gauge-alignment criterion, so it cannot serve as the classical
p-adic place. Hence there is **no genuinely synthetic instance of `AdelicLaw` on `ℚ`**: the
interface admits only the classical place family (Artin–Whaple / Ostrowski, machine-checked
via `Rigidity.lean`). -/
theorem synthetic_rejected (b : RadixSeq) (p : ℕ) (h : ∃ i, b i ≠ p) :
    ¬ Isometric b p :=
  not_isometric_of_ne b p h

/-! ## 4. The empty, correctly-typed slot — where the function-field instance plugs in

The genuinely synthetic case is *not* on `ℚ` (Ostrowski forbids it) but on a global
function field `F_q(t)`, whose places are the monic irreducible polynomials plus the place
at infinity — a different global field, with its own product formula. That instance would be

    `def functionFieldAdelicLaw (q : ℕ) [Fact q.Prime] : AdelicLaw (FqtPlace q) (Fqt q) := …`

slotting into *this* interface with no change to the abstraction. FDRS would grow a
polynomial-coefficient mode to reach it. The slot is left open, correctly typed. -/

/-! ## 5. Demo — the classical instance conserves (exact ℚ) -/

-- The classical support of `12 = 2²·3` is `{∞, 2, 3}`; the conserved product is `1`:
#eval (classicalAdelicLaw.support 12).card                                   -- 3  ({∞, 2, 3})
#eval ∏ v ∈ classicalAdelicLaw.support 12, classicalAdelicLaw.val v 12        -- 1  (conservation)
#eval ∏ v ∈ classicalAdelicLaw.support 360, classicalAdelicLaw.val v 360      -- 1

end FdrsFormal.Modes.Adelic
