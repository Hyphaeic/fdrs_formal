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

# The canonical split: residue types found by the arithmetic (Phase 1 addendum, §3.22)

§3.15–3.21 took the free/tied split of the carry modulus `M = |B − c|` as data. Here it is
**derived** from the ring and its wrap gain alone.

- **The canonical family split** (Definition 244, Theorem 172): the residue types are the
  prime-power parts `p^{v_p(M)}` of `M` at the primes `p` it shares with the wrap gain `c`;
  the free part is the product of the remaining prime-power parts. This is a family split
  (§3.21) for every ring with `M ≠ 0` — no data supplied.
- **The free part is forced** (Theorem 173): every family split of `M` — whatever its types —
  has exactly the canonical free part, and its types multiply to exactly the canonical tied
  part. Only the grouping of the tied primes into types is a choice; the canonical split
  takes the finest grouping (one prime per type).
- **The rule closes the loop** (Corollary 59): with the canonical split, the cross-feeding
  rule of §3.21 grows the complex to its family normal form after one operation that is
  nonzero modulo two residue types. Ring, wrap gain and operations determine everything.

Witness: for the ring `(2, 3, 5)` with wrap gain `−180`, the canonical free part is `7` and
the canonical tied part is `30`, read off from the split of §3.21 by Theorem 173.

Reuses `FamilyBranches.lean` (family splits, the rule, `rule_normal_form`, the witness
split), `CarryQuotient.lean` (`modulus`), and Mathlib's prime factorization.

- **Definition 244** (`tiedPrimes`, `primePart`, `canonFree`, `canonTied`, `canonicalSplit`):
  the canonical family split.
- **Theorem 172** (`canon_mul`, `canonicalSplit`): it is a family split.
- **Theorem 173** (`free_forced`, `tied_forced`): the free part and the tied part are forced.
- **Corollary 59** (`canonical_rule_normal_form`): the rule closes the loop.
- **Proposition 190** (`canonFree_235`, `canonTied_235`): the witness.

**Honest scope.** Elementary (unique factorization). The corpus contributes the
identification of residue types with the prime-power parts of the carry modulus at the
primes shared with the wrap gain, the forcing of the free and tied parts, and the resulting
data-free pipeline from a wrapped ring to its family normal form. The balanced case
`M = 0` is excluded; `primeFactors` is not evaluated by the kernel, so witnesses go through
Theorem 173.
-/

import FdrsFormal.Modes.SyntheticPlace.FamilyBranches

namespace FdrsFormal.Modes.SyntheticPlace.CanonicalSplit

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite
open FdrsFormal.Modes.SyntheticPlace.CarryQuotient FdrsFormal.Modes.SyntheticPlace.FamilyBranches

section Canonical

variable {n : ℕ} (ρ : Fin (n + 1) → ℕ) (hρ : ∀ i, 2 ≤ ρ i) (c : ℤ)

/-! ## Definition 244: the canonical split -/

/-- The tied primes: primes dividing both the carry modulus and the wrap gain.

**fdrs.md**: Definition 244 (the canonical split). -/
def tiedPrimes : Finset ℕ := (modulus ρ hρ c).primeFactors.filter (fun p => (p : ℤ) ∣ c)

/-- The free primes: primes of the modulus not dividing the wrap gain. -/
def freePrimes : Finset ℕ := (modulus ρ hρ c).primeFactors.filter (fun p => ¬ (p : ℤ) ∣ c)

/-- The `p`-primary part of the modulus, `p^{v_p(M)}`.

**fdrs.md**: Definition 244 (the canonical split). -/
def primePart (p : ℕ) : ℕ := p ^ (modulus ρ hρ c).factorization p

/-- The canonical free part: the product of the prime-power parts at the free primes.

**fdrs.md**: Definition 244 (the canonical split). -/
def canonFree : ℕ := ∏ p ∈ freePrimes ρ hρ c, primePart ρ hρ c p

/-- The canonical tied part: the product of the prime-power parts at the tied primes. -/
def canonTied : ℕ := ∏ p ∈ tiedPrimes ρ hρ c, primePart ρ hρ c p

/-! ## Theorem 172: it is a family split -/

/-- **Theorem 172 (the canonical parts multiply to the modulus).**

**fdrs.md**: Theorem 172 (the canonical split is a family split). -/
theorem canon_mul (hM : modulus ρ hρ c ≠ 0) :
    canonFree ρ hρ c * canonTied ρ hρ c = modulus ρ hρ c := by
  have h := Nat.factorization_prod_pow_eq_self hM
  rw [Finsupp.prod, Nat.support_factorization] at h
  rw [canonFree, canonTied, freePrimes, tiedPrimes, mul_comm]
  conv_rhs => rw [← h]
  exact Finset.prod_filter_mul_prod_filter_not _ _ _

theorem prime_of_tied {p : ℕ} (hp : p ∈ tiedPrimes ρ hρ c) : p.Prime :=
  Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1

theorem prime_of_free {p : ℕ} (hp : p ∈ freePrimes ρ hρ c) : p.Prime :=
  Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1

theorem tied_dvd_c {p : ℕ} (hp : p ∈ tiedPrimes ρ hρ c) : (p : ℤ) ∣ c :=
  (Finset.mem_filter.mp hp).2

theorem free_not_dvd_c {p : ℕ} (hp : p ∈ freePrimes ρ hρ c) : ¬ (p : ℤ) ∣ c :=
  (Finset.mem_filter.mp hp).2

/-- The canonical free part is coprime to the wrap gain. -/
theorem canonFree_coprime_c : Nat.Coprime (canonFree ρ hρ c) c.natAbs :=
  Nat.Coprime.prod_left fun _ hp => Nat.Coprime.pow_left _
    ((Nat.Prime.coprime_iff_not_dvd (prime_of_free ρ hρ c hp)).mpr
      (fun h => free_not_dvd_c ρ hρ c hp (Int.natCast_dvd.mpr h)))

theorem canonFree_coprime_part {p : ℕ} (hp : p ∈ tiedPrimes ρ hρ c) :
    Nat.Coprime (canonFree ρ hρ c) (primePart ρ hρ c p) :=
  Nat.Coprime.prod_left fun _ hq => Nat.coprime_pow_primes _ _ (prime_of_free ρ hρ c hq)
    (prime_of_tied ρ hρ c hp)
    (fun hqp => free_not_dvd_c ρ hρ c hq (hqp ▸ tied_dvd_c ρ hρ c hp))

/-- **Theorem 172 (the canonical split).** For every wrapped ring with `M ≠ 0`, the tied
primes index a family split of the carry modulus whose types are the prime-power parts.

**fdrs.md**: Theorem 172 (the canonical split is a family split). -/
noncomputable def canonicalSplit (hM : modulus ρ hρ c ≠ 0) :
    FamilySplit ρ hρ c (tiedPrimes ρ hρ c) where
  free := canonFree ρ hρ c
  T := fun p => primePart ρ hρ c p.1
  laps := modulus ρ hρ c
  mul_eq := by
    rw [Finset.prod_coe_sort (tiedPrimes ρ hρ c) (fun p => primePart ρ hρ c p)]
    exact canon_mul ρ hρ c hM
  cop_free := fun p => canonFree_coprime_part ρ hρ c p.2
  cop_pair := fun p q hpq => Nat.coprime_pow_primes _ _ (prime_of_tied ρ hρ c p.2)
    (prime_of_tied ρ hρ c q.2) (fun h => hpq (Subtype.ext h))
  free_coprime := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    exact canonFree_coprime_c ρ hρ c
  tied_dvd := fun p => by
    show ((p.1 ^ (modulus ρ hρ c).factorization p.1 : ℕ) : ℤ) ∣ c ^ modulus ρ hρ c
    push_cast
    exact (pow_dvd_pow _ (Nat.factorization_lt _ hM).le).trans
      (pow_dvd_pow_of_dvd (tied_dvd_c ρ hρ c p.2) _)

/-! ## Theorem 173: the free part and the tied part are forced -/

/-- **Theorem 173 (the free part is forced).** Every family split of the carry modulus has
the canonical free part.

**fdrs.md**: Theorem 173 (the free and tied parts are forced). -/
theorem free_forced (hM : modulus ρ hρ c ≠ 0) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : FamilySplit ρ hρ c ι) : S.free = canonFree ρ hρ c := by
  have hcanon := canon_mul ρ hρ c hM
  have hS := S.mul_eq
  -- S.free is coprime to the wrap gain
  have hSc : Nat.Coprime S.free c.natAbs := by
    have := S.free_coprime
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm] at this
    exact this
  apply Nat.dvd_antisymm
  · -- S.free ∣ canonFree: it is coprime to the canonical tied part
    have hcop : Nat.Coprime S.free (canonTied ρ hρ c) :=
      Nat.Coprime.prod_right fun p hp => Nat.Coprime.pow_right _
        (Nat.Coprime.coprime_dvd_right (Int.natCast_dvd.mp (tied_dvd_c ρ hρ c hp)) hSc)
    exact hcop.dvd_of_dvd_mul_right (hcanon ▸ hS ▸ dvd_mul_right _ _)
  · -- canonFree ∣ S.free: it is coprime to every type of S
    have hcop : Nat.Coprime (canonFree ρ hρ c) (∏ i, S.T i) :=
      Nat.Coprime.prod_right fun i _ => by
        have h1 : S.T i ∣ c.natAbs ^ S.laps := by
          rw [← Int.natAbs_pow]; exact Int.natCast_dvd.mp (S.tied_dvd i)
        exact Nat.Coprime.coprime_dvd_right h1 (Nat.Coprime.pow_right _ (canonFree_coprime_c ρ hρ c))
    exact hcop.dvd_of_dvd_mul_right (hS ▸ hcanon ▸ dvd_mul_right _ _)

/-- **Theorem 173 (the tied part is forced).** The types of every family split multiply to
the canonical tied part.

**fdrs.md**: Theorem 173 (the free and tied parts are forced). -/
theorem tied_forced (hM : modulus ρ hρ c ≠ 0) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : FamilySplit ρ hρ c ι) : ∏ i, S.T i = canonTied ρ hρ c := by
  have hcanon := canon_mul ρ hρ c hM
  have hS := S.mul_eq
  rw [free_forced ρ hρ c hM S] at hS
  have hpos : 0 < canonFree ρ hρ c := by
    rcases Nat.eq_zero_or_pos (canonFree ρ hρ c) with h | h
    · rw [h, zero_mul] at hcanon; exact absurd hcanon.symm hM
    · exact h
  exact Nat.eq_of_mul_eq_mul_left hpos (hS.trans hcanon.symm)

/-! ## Corollary 59: the rule closes the loop -/

theorem primePart_ge_two {p : ℕ} (hp : p ∈ tiedPrimes ρ hρ c) : 2 ≤ primePart ρ hρ c p := by
  have hmem := (Finset.mem_filter.mp hp).1
  have he : (modulus ρ hρ c).factorization p ≠ 0 := by
    rw [← Finsupp.mem_support_iff, Nat.support_factorization]; exact hmem
  exact (prime_of_tied ρ hρ c hp).two_le.trans (Nat.le_self_pow he p)

/-- **Corollary 59 (the rule closes the loop).** For every wrapped ring with `M ≠ 0`: under the
canonical split, after one operation nonzero modulo two residue types the cross-feeding rule
has grown every branch to exact size, and every state of the resulting complex has a unique
family normal form. Nothing is supplied but the ring, the wrap gain and the operations.

**fdrs.md**: Corollary 59 (the rule closes the loop). -/
theorem canonical_rule_normal_form (hM : modulus ρ hρ c ≠ 0)
    (z : FSt n (fun _ : tiedPrimes ρ hρ c => 0)) :
    ∃! σ : (i : tiedPrimes ρ hρ c) →
        FiniteRadixSpace ((crossRule (canonicalSplit ρ hρ c hM).T).branch i
          ([(canonicalSplit ρ hρ c hM).T i] : List ℕ)) 0,
      z - famNF ρ hρ c (canonicalSplit ρ hρ c hM) (fun _ => 0)
          (fun i => (crossRule (canonicalSplit ρ hρ c hM).T).branch i
            ([(canonicalSplit ρ hρ c hM).T i] : List ℕ))
          (famValue ρ hρ c (canonicalSplit ρ hρ c hM) (fun _ => 0)
            (fun i => (crossRule (canonicalSplit ρ hρ c hM).T).branch i
              ([(canonicalSplit ρ hρ c hM).T i] : List ℕ)) z) σ ∈
        famLattice ρ hρ c (canonicalSplit ρ hρ c hM) (fun _ => 0)
          (fun i => (crossRule (canonicalSplit ρ hρ c hM).T).branch i
            ([(canonicalSplit ρ hρ c hM).T i] : List ℕ)) :=
  rule_normal_form ρ hρ c (canonicalSplit ρ hρ c hM) (fun i => primePart_ge_two ρ hρ c i.2) z

end Canonical

/-! ## Proposition 190: the witness -/

section Witness

theorem modulus_235_ne : modulus ring235 ring235_ge_two (-180) ≠ 0 := by
  rw [ring235_modulus]; decide

/-- **Proposition 190 (the canonical free part of `(2, 3, 5)`, `c = −180`, is `7`).** Read off
from the split of §3.21 by Theorem 173.

**fdrs.md**: Proposition 190 (the canonical split of the (2,3,5) ring). -/
theorem canonFree_235 : canonFree ring235 ring235_ge_two (-180) = 7 :=
  (free_forced ring235 ring235_ge_two (-180) modulus_235_ne split210).symm

/-- **Proposition 190 (its canonical tied part is `30 = 2 · 3 · 5`).**

**fdrs.md**: Proposition 190 (the canonical split of the (2,3,5) ring). -/
theorem canonTied_235 : canonTied ring235 ring235_ge_two (-180) = 30 := by
  rw [← tied_forced ring235 ring235_ge_two (-180) modulus_235_ne split210]
  show ∏ i : Fin 3, ![2, 3, 5] i = 30
  rw [Fin.prod_univ_three]; rfl

end Witness

end FdrsFormal.Modes.SyntheticPlace.CanonicalSplit
