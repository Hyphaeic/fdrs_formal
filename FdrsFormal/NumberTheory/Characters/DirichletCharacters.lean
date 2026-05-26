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

# Dirichlet Characters

Multiplicative characters mod q and their orthogonality properties.

## Mathematical Content (fdrs.md lines 1850-1900)

**Definition**: A Dirichlet character mod q is a completely multiplicative function
χ : ℤ → ℂ that is periodic mod q and vanishes on non-units: χ(n) = 0 when gcd(n,q) > 1.

Equivalently: χ is a group character of (ℤ/qℤ)ˣ extended by 0 off units.

**Proposition 43** (orthogonality over units):
  ∑_{a ∈ (ℤ/qℤ)ˣ} χ(a) · conj(ψ(a)) = φ(q) · δ_{χ,ψ}

**Proposition 39** (dual orthogonality):
  (1/φ(q)) ∑_{χ} χ(a) · conj(χ(b)) = 𝟙_{a ≡ b (mod q)}

## References

- fdrs.md, Phase 3 Fragment 2, Section 2 (lines 1850-1900)
- Mathlib: ZMod.isUnit, Fintype.card_units
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import FdrsFormal.NumberTheory.ArithmeticFunctions.Definition
import FdrsFormal.NumberTheory.Characters.Oracle

namespace FdrsFormal.NumberTheory.Characters

open FdrsFormal.NumberTheory.ArithmeticFunctions

/-!
## Helper Lemmas
-/

/--
**Lemma**: gcd respects modular equivalence.

gcd a b = gcd (a % b) b

**Proof**: Direct from gcd_comm + gcd_rec.
-/
lemma Nat.gcd_eq_gcd_mod_right (a b : ℕ) : Nat.gcd a b = Nat.gcd (a % b) b := by
  calc
    Nat.gcd a b = Nat.gcd b a := by simpa using (Nat.gcd_comm a b)
    _ = Nat.gcd (a % b) b := by simpa using (Nat.gcd_rec b a)

/-!
## Dirichlet Character Type

We use the **Wrapper Pattern** to combine Mathlib rigor with FDRS architectural flexibility:
- Internally uses Mathlib's `MulChar (ZMod q)ˣ ℂ` for proven theorems
- Exposes FDRS-friendly `apply : ℕ → ℂ` interface
- Allows future extensibility (energy costs, FPGA variants)
-/

/--
A Dirichlet character mod q.

**Definition** (fdrs.md lines 1852-1854):
A Dirichlet character mod q is:
1. Completely multiplicative: χ(mn) = χ(m)χ(n)
2. Periodic mod q: χ(n) = χ(n + q)
3. Vanishes on non-units: χ(n) = 0 when gcd(n,q) > 1

**Implementation**: Wrapper around Mathlib's `MulChar (ZMod q) ℂ`.
-/
structure DirichletChar (q : ℕ) where
  toMathlib : MulChar (ZMod q) ℂ

/--
Apply a Dirichlet character to a natural number.

Returns χ(n) where:
- If gcd(n,q) = 1, applies the character to n as a unit in (ℤ/qℤ)ˣ
- If gcd(n,q) > 1, returns 0
-/
noncomputable def DirichletChar.apply {q : ℕ} (χ : DirichletChar q) (n : ℕ) : ℂ :=
  if h : Nat.Coprime n q then
    χ.toMathlib (ZMod.unitOfCoprime n h)
  else 0

/-!
## Periodicity
-/

/--
**Periodicity**: Dirichlet characters are periodic mod q.

If n ≡ m (mod q), then χ(n) = χ(m).

**Proof**: The character factors through ℤ/qℤ.
-/
theorem DirichletChar.periodic {q : ℕ} (χ : DirichletChar q) (n m : ℕ) :
    n % q = m % q → χ.apply n = χ.apply m := by
  intro h_mod
  simp only [apply]
  split_ifs with hn hm
  · -- Both coprime to q: n ≡ m (mod q) implies χ(n) = χ(m)
    have h_units_eq : (ZMod.unitOfCoprime n hn : ZMod q) = (ZMod.unitOfCoprime m hm : ZMod q) := by
      simp only [ZMod.coe_unitOfCoprime, ZMod.natCast_eq_natCast_iff']
      exact h_mod
    have : ZMod.unitOfCoprime n hn = ZMod.unitOfCoprime m hm := by
      ext
      exact h_units_eq
    rw [this]
  · -- Contradiction: n coprime, m not coprime, but n ≡ m (mod q)
    exfalso
    apply hm
    have hg : m.gcd q = n.gcd q := by
      calc m.gcd q = (m % q).gcd q := Nat.gcd_eq_gcd_mod_right m q
        _ = (n % q).gcd q := by rw [h_mod]
        _ = n.gcd q := (Nat.gcd_eq_gcd_mod_right n q).symm
    rw [Nat.Coprime, hg]
    exact hn
  · -- Contradiction: m coprime, n not coprime, but n ≡ m (mod q)
    exfalso
    apply hn
    rename_i hm_cop
    have hg : n.gcd q = m.gcd q := by
      calc n.gcd q = (n % q).gcd q := Nat.gcd_eq_gcd_mod_right n q
        _ = (m % q).gcd q := by rw [h_mod]
        _ = m.gcd q := (Nat.gcd_eq_gcd_mod_right m q).symm
    rw [Nat.Coprime, hg]
    exact hm_cop
  · -- Both not coprime: both evaluate to 0
    rfl

/-!
## Integration with ArithmeticFunction
-/

/--
Convert a Dirichlet character to an ArithmeticFunction.

This allows Dirichlet characters to work with existing convolution algebra.
-/
noncomputable def DirichletChar.toArithmeticFunction {q : ℕ} (χ : DirichletChar q) :
    ArithmeticFunction :=
  fun n => χ.apply n.val

/-!
## Orthogonality Relations
-/

-- Make DirichletChar finite to enable sums over characters
noncomputable instance DirichletChar.fintype {q : ℕ} [NeZero q]
    [HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod q)ˣ)] :
    Fintype (DirichletChar q) := by
  -- DirichletChar q is in bijection with MulChar (ZMod q) ℂ via .toMathlib
  -- Since MulChar is Fintype, so is DirichletChar
  letI : Fintype (MulChar (ZMod q) ℂ) := DirichletCharacter.fintype
  -- Use the equivalence via toMathlib field
  exact Fintype.ofEquiv (MulChar (ZMod q) ℂ)
    ⟨fun m => ⟨m⟩,              -- MulChar → DirichletChar
     fun χ => χ.toMathlib,      -- DirichletChar → MulChar
     fun m => rfl,              -- left_inv
     fun χ => by cases χ; rfl⟩  -- right_inv

/--
**Proposition 43**: Orthogonality over units.

**Mathematical content** (fdrs.md lines 1860-1865):
  ∑_{a ∈ (ℤ/qℤ)ˣ} χ(a) · conj(ψ(a)) = φ(q) · δ_{χ,ψ}

where φ(q) = |(ℤ/qℤ)ˣ| is Euler's totient function.

**Proof**: Delegates to Mathlib's DirichletCharacter orthogonality.
This is a direct consequence of the wrapper structure - the underlying
Mathlib characters satisfy orthogonality, so our wrapper does too.
-/
theorem dirichletChar_orthogonal (q : ℕ) [NeZero q] (χ ψ : DirichletChar q)
    [HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod q)ˣ)] :
    ∑ a : (ZMod q)ˣ, χ.toMathlib a * (starRingEnd ℂ) (ψ.toMathlib a) =
    (@ite ℂ (χ.toMathlib = ψ.toMathlib) (Classical.propDecidable _)
      (Nat.totient q) 0) := by
  -- Delegate to oracle (Mathlib wrapper)
  exact dirichlet_main_oracle q χ.toMathlib ψ.toMathlib

/--
**Proposition 39**: Dual orthogonality.

**Mathematical content** (fdrs.md lines 1866-1872):
  (1/φ(q)) ∑_{χ} χ(a) · conj(χ(b)) = 𝟙_{a ≡ b (mod q)}

**Proof**: Delegates to Mathlib's `DirichletCharacter.sum_char_inv_mul_char_eq`.
-/
theorem dirichletChar_dual_orthogonal (q : ℕ) [NeZero q]
    [HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod q)ˣ)]
    (a b : (ZMod q)ˣ) :  -- Units per spec
    ∑ χ : DirichletChar q, χ.toMathlib a * (starRingEnd ℂ) (χ.toMathlib b) =
    (@ite ℂ (a = b) (Classical.propDecidable _) (Nat.totient q) 0) := by
  -- Wrapper conversion + oracle delegation
  have h_equiv : ∑ χ : DirichletChar q, χ.toMathlib a * (starRingEnd ℂ) (χ.toMathlib b) =
                 ∑ m : DirichletCharacter ℂ q, m a * (starRingEnd ℂ) (m b) := by
    let e : DirichletCharacter ℂ q ≃ DirichletChar q :=
      ⟨fun m => ⟨m⟩, fun χ => χ.toMathlib, fun _ => rfl, fun χ => by cases χ; rfl⟩
    rw [Fintype.sum_equiv e.symm]
    intro m
    simp [e]
  rw [h_equiv]
  exact dirichlet_dual_oracle q a b

/-!
## Residue Projectors via Characters
-/

/--
**Proposition 45**: Character expansion of residue projectors (pointwise form).

**Mathematical content** (fdrs.md lines 1890-1896):
The projector onto residue class a (mod q) (on units) is:
  Π_{q,a} = (1/φ(q)) ∑_{χ} conj(χ(a)) · M_χ

Pointwise, this reduces to:
  ∑_χ conj(χ(a)) · χ(b) = φ(q) · δ_{a,b}

**Proof**: Dual orthogonality (`dirichletChar_dual_orthogonal`) with a,b swapped.
-/
theorem residueProjector_character_expansion (q : ℕ) [NeZero q]
    [HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod q)ˣ)]
    (a b : (ZMod q)ˣ) :
    ∑ χ : DirichletChar q, (starRingEnd ℂ) (χ.toMathlib a) * χ.toMathlib b =
    (@ite ℂ (a = b) (Classical.propDecidable _) (Nat.totient q) 0) := by
  have h := dirichletChar_dual_orthogonal q b a
  simp_rw [mul_comm] at h
  rwa [show (b = a) ↔ (a = b) from eq_comm] at h

end FdrsFormal.NumberTheory.Characters
