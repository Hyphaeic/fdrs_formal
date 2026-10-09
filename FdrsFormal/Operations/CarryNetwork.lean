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

# Carry networks and the radix lattice (Phase 1 addendum, §3.8)

Carries as first-class structure. A **carry network** is a finite set of cells with
weights and a set of **radix lines** `u → v` with ratio `ρ` and `w(v) = ρ · w(u)`; a
carry along a line keeps `d(u) mod ρ` and sends `⌊d(u)/ρ⌋` to `v`. A **route** is a
sequence of carries, and its **ledger** records every transfer. A digit schedule is
a path network; the product of `r` numbers lives, carry-free, on the `r`-dimensional
**radix lattice** whose cells carry the products of place values, with one family of
radix lines per factor.

- **Definition 225** (`CarryNet`, `carry`, `run`, `transfers`): carry networks,
  carries, routes, ledgers.
- **Theorem 137** (`val_run`): every route conserves value.
- **Theorem 138** (`run_balance`): the ledger balances cell by cell:
  `final(u) = initial(u) + Σ inflow(u) − Σ ρ · outflow(u)`.
- **Definition 226** (`latticeWeight`, `latticeNet`): the radix lattice of `r`
  schedules.
- **Theorem 139** (`lattice_outer`, `lattice_route_product`): the product of `r`
  numbers is the value of their outer digit product on the lattice, and every carry
  route on the lattice preserves it.
- **Proposition 171** (`ratio_mul_eq`, `square_routes`): parallel lines have equal
  ratio products (zero curvature); two routes around a square deliver the same state
  with different ledgers — the ledger is route-dependent only by a circulation.

**Honest scope.** Elementary. The corpus contributes the network formulation of
carries on its schedules, the lattice of products, and the ledger. Holonomy of
carry *cycles* (Theorem 114, the wrap of a modular digit ring) lies outside
consistent networks and is not treated here.
-/

import FdrsFormal.Core.Finite

namespace FdrsFormal.Operations.CarryNetwork

open FdrsFormal.Core.Primitives FdrsFormal.Core.Finite

/-! ## Definition 225: carry networks, routes, ledgers -/

/-- A radix line `src → dst` with ratio `ρ`. -/
abbrev Line (V : Type*) := V × V × ℕ

/-- A carry network: cell weights and radix lines with `w(dst) = ρ · w(src)`.

**fdrs.md**: Definition 225 (carry networks). -/
structure CarryNet (V : Type*) where
  w : V → ℕ
  lines : List (Line V)
  consistent : ∀ e ∈ lines, e.1 ≠ e.2.1 ∧ 0 < e.2.2 ∧ w e.2.1 = e.2.2 * w e.1

set_option linter.unusedSectionVars false

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The value of a state: `Σ_u w(u) d(u)`. -/
def CarryNet.val (N : CarryNet V) (d : V → ℕ) : ℕ := ∑ u, N.w u * d u

/-- A carry along a line: keep `d(src) mod ρ`, send `⌊d(src)/ρ⌋` to `dst`.

**fdrs.md**: Definition 225 (carry networks). -/
def carry (e : Line V) (d : V → ℕ) : V → ℕ :=
  Function.update (Function.update d e.1 (d e.1 % e.2.2)) e.2.1 (d e.2.1 + d e.1 / e.2.2)

/-- Run a route. -/
def run : List (Line V) → (V → ℕ) → (V → ℕ)
  | [], d => d
  | e :: es, d => run es (carry e d)

/-- The ledger of a route: each transfer `(src, dst, ρ, amount)`. -/
def transfers : List (Line V) → (V → ℕ) → List (V × V × ℕ × ℕ)
  | [], _ => []
  | e :: es, d => (e.1, e.2.1, e.2.2, d e.1 / e.2.2) :: transfers es (carry e d)

theorem carry_src (e : Line V) (d : V → ℕ) (he : e.1 ≠ e.2.1) :
    carry e d e.1 = d e.1 % e.2.2 := by
  simp [carry, Function.update_of_ne he]

theorem carry_dst (e : Line V) (d : V → ℕ) : carry e d e.2.1 = d e.2.1 + d e.1 / e.2.2 := by
  simp [carry]

theorem carry_other (e : Line V) (d : V → ℕ) {u : V} (h1 : u ≠ e.1) (h2 : u ≠ e.2.1) :
    carry e d u = d u := by
  simp [carry, Function.update_of_ne h1, Function.update_of_ne h2]

/-! ## Theorem 137: conservation -/

theorem val_carry (N : CarryNet V) {e : Line V} (he : e ∈ N.lines) (d : V → ℕ) :
    N.val (carry e d) = N.val d := by
  obtain ⟨hne, hpos, hw⟩ := N.consistent e he
  obtain ⟨s, t, ρ⟩ := e
  simp only at hne hpos hw
  simp only [CarryNet.val]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ s),
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ t⟩),
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ t⟩)]
  have hrest : ∑ u ∈ (Finset.univ.erase s).erase t, N.w u * carry (s, t, ρ) d u =
      ∑ u ∈ (Finset.univ.erase s).erase t, N.w u * d u :=
    Finset.sum_congr rfl fun u hu => by
      have hut := Finset.ne_of_mem_erase hu
      have hus := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hu)
      rw [carry_other _ _ hus hut]
  rw [hrest, carry_src (s, t, ρ) d hne, carry_dst (s, t, ρ) d]
  simp only
  rw [hw]
  have := Nat.mod_add_div (d s) ρ
  nlinarith [this]

/-- **Theorem 137 (carries conserve value).** Every route of carries along the
network's radix lines preserves the value of the state.

**fdrs.md**: Theorem 137 (carries conserve value). -/
theorem val_run (N : CarryNet V) : ∀ (es : List (Line V)), (∀ e ∈ es, e ∈ N.lines) →
    ∀ d, N.val (run es d) = N.val d
  | [], _, _ => rfl
  | e :: es, h, d => by
    rw [run, val_run N es (fun e' he' => h e' (List.mem_cons_of_mem _ he')),
      val_carry N (h e (List.mem_cons_self))]

/-! ## Theorem 138: the ledger balances -/

/-- The net contribution of a transfer to cell `u`: `+amount` in, `−ρ · amount` out. -/
def contrib (u : V) (t : V × V × ℕ × ℕ) : ℤ :=
  (if t.2.1 = u then (t.2.2.2 : ℤ) else 0) - (if t.1 = u then (t.2.2.1 * t.2.2.2 : ℕ) else 0)

/-- **Theorem 138 (the ledger balances).** Along any route of lines with distinct
endpoints, every cell ends at its start plus its inflows minus `ρ` times its outflows.

**fdrs.md**: Theorem 138 (the ledger balances). -/
theorem run_balance : ∀ (es : List (Line V)), (∀ e ∈ es, e.1 ≠ e.2.1) →
    ∀ d u, (run es d u : ℤ) = d u + ((transfers es d).map (contrib u)).sum
  | [], _, _, _ => by simp [run, transfers]
  | e :: es, h, d, u => by
    rw [run, transfers, run_balance es (fun e' he' => h e' (List.mem_cons_of_mem _ he')),
      List.map_cons, List.sum_cons]
    have hne := h e List.mem_cons_self
    have hstep : (carry e d u : ℤ) = d u + contrib u (e.1, e.2.1, e.2.2, d e.1 / e.2.2) := by
      simp only [contrib]
      by_cases hs : e.1 = u
      · subst hs
        rw [carry_src e d hne, if_neg (Ne.symm hne), if_pos rfl]
        have := Nat.mod_add_div (d e.1) e.2.2
        push_cast
        linarith [show ((d e.1 % e.2.2 : ℕ) : ℤ) + (e.2.2 : ℤ) * (d e.1 / e.2.2 : ℕ) =
          (d e.1 : ℤ) by exact_mod_cast this]
      · by_cases ht : e.2.1 = u
        · subst ht
          rw [carry_dst, if_pos rfl, if_neg hs]
          push_cast; ring
        · rw [carry_other e d (Ne.symm hs) (Ne.symm ht), if_neg ht, if_neg hs]
          ring
    rw [hstep]
    ring

/-! ## Definition 226 and Theorem 139: the radix lattice of `r` products -/

section Lattice

variable {r : ℕ} (bs : Fin r → RadixSeq) (ks : Fin r → ℕ)

/-- The cells of the radix lattice: one digit position per factor. -/
abbrev LatticeCell := (s : Fin r) → Fin (ks s + 1)

/-- The weight of a lattice cell: the product of the factors' place values.

**fdrs.md**: Definition 226 (the radix lattice). -/
def latticeWeight (τ : LatticeCell ks) : ℕ := ∏ s, placeValue (bs s) (τ s)

/-- Moving one step along factor `s`. -/
def latticeStep (τ : LatticeCell ks) (s : Fin r) (h : (τ s : ℕ) + 1 < ks s + 1) :
    LatticeCell ks :=
  Function.update τ s ⟨τ s + 1, h⟩

theorem latticeWeight_step (τ : LatticeCell ks) (s : Fin r) (h : (τ s : ℕ) + 1 < ks s + 1) :
    latticeWeight bs ks (latticeStep ks τ s h) = bs s (τ s) * latticeWeight bs ks τ := by
  classical
  unfold latticeWeight latticeStep
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ s),
    ← Finset.mul_prod_erase _ (fun t => placeValue (bs t) (τ t)) (Finset.mem_univ s)]
  rw [Function.update_self, Finset.prod_congr rfl fun t ht =>
    by rw [Function.update_of_ne (Finset.ne_of_mem_erase ht)]]
  simp only [placeValue.succ]
  ring

/-- The radix lines of the lattice: from each cell, one step along each factor.

**fdrs.md**: Definition 226 (the radix lattice). -/
noncomputable def latticeLines : List (Line (LatticeCell ks)) :=
  (Finset.univ : Finset (LatticeCell ks × Fin r)).toList.filterMap fun p =>
    if h : (p.1 p.2 : ℕ) + 1 < ks p.2 + 1 then
      some (p.1, latticeStep ks p.1 p.2 h, bs p.2 (p.1 p.2))
    else none

/-- The radix lattice as a carry network.

**fdrs.md**: Definition 226 (the radix lattice). -/
noncomputable def latticeNet : CarryNet (LatticeCell ks) where
  w := latticeWeight bs ks
  lines := latticeLines bs ks
  consistent := by
    intro e he
    simp only [latticeLines, List.mem_filterMap, Finset.mem_toList, Finset.mem_univ,
      true_and] at he
    obtain ⟨⟨τ, s⟩, hp⟩ := he
    simp only at hp
    split_ifs at hp with h
    cases hp
    refine ⟨fun heq => ?_, (bs s).pos _, latticeWeight_step bs ks τ s h⟩
    have := congrArg Fin.val (congrFun heq s)
    simp [latticeStep] at this

/-- The outer digit product of `r` numbers: cell `τ` holds `∏_s x^{(s)}_{τ_s}`. -/
def outer (xs : (s : Fin r) → FiniteRadixSpace (bs s) (ks s)) (τ : LatticeCell ks) : ℕ :=
  ∏ s, (xs s (τ s) : ℕ)

/-- **Theorem 139 (products live on the radix lattice).** The value of the outer digit
product is the product of the decoded numbers: `Σ_τ w(τ) ∏_s x^{(s)}_{τ_s} = ∏_s dec x^{(s)}`.

**fdrs.md**: Theorem 139 (products live on the radix lattice). -/
theorem lattice_outer (xs : (s : Fin r) → FiniteRadixSpace (bs s) (ks s)) :
    (latticeNet bs ks).val (outer bs ks xs) = ∏ s, decodeFinite (bs s) (ks s) (xs s) := by
  classical
  simp only [CarryNet.val, latticeNet, latticeWeight, outer, decodeFinite]
  rw [Finset.prod_univ_sum]
  refine Fintype.sum_congr _ _ fun τ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  ring

/-- **Theorem 139 (carrying on the lattice preserves the product).** After any route of
carries along the lattice's radix lines, the state still has value `∏_s dec x^{(s)}`.

**fdrs.md**: Theorem 139 (products live on the radix lattice). -/
theorem lattice_route_product (xs : (s : Fin r) → FiniteRadixSpace (bs s) (ks s))
    (es : List (Line (LatticeCell ks))) (hes : ∀ e ∈ es, e ∈ latticeLines bs ks) :
    (latticeNet bs ks).val (run es (outer bs ks xs)) =
      ∏ s, decodeFinite (bs s) (ks s) (xs s) := by
  rw [val_run (latticeNet bs ks) es hes, lattice_outer]

end Lattice

/-! ## Proposition 171: zero curvature; ledgers differ by a circulation -/

/-- **Proposition 171 (zero curvature).** Two paths of radix lines from `u` to `z`
have the same product of ratios (when `w(u) > 0`).

**fdrs.md**: Proposition 171 (parallel routes). -/
theorem ratio_mul_eq (N : CarryNet V) {u v v' z : V} {ρ₁ ρ₂ ρ₁' ρ₂' : ℕ}
    (h1 : (u, v, ρ₁) ∈ N.lines) (h2 : (v, z, ρ₂) ∈ N.lines)
    (h1' : (u, v', ρ₁') ∈ N.lines) (h2' : (v', z, ρ₂') ∈ N.lines) (hu : 0 < N.w u) :
    ρ₁ * ρ₂ = ρ₁' * ρ₂' := by
  have e1 := (N.consistent _ h1).2.2
  have e2 := (N.consistent _ h2).2.2
  have e1' := (N.consistent _ h1').2.2
  have e2' := (N.consistent _ h2').2.2
  simp only at e1 e2 e1' e2'
  have : ρ₁ * ρ₂ * N.w u = ρ₁' * ρ₂' * N.w u := by
    rw [show ρ₁ * ρ₂ * N.w u = ρ₂ * (ρ₁ * N.w u) by ring, ← e1, ← e2,
      show ρ₁' * ρ₂' * N.w u = ρ₂' * (ρ₁' * N.w u) by ring, ← e1', ← e2']
  exact Nat.eq_of_mul_eq_mul_right hu this

/-- A single loaded cell. -/
def single (u : V) (a : ℕ) : V → ℕ := Function.update (fun _ => 0) u a

theorem carry_single {u v : V} (huv : u ≠ v) {ρ : ℕ} (hρ : 0 < ρ) (t : ℕ) :
    carry (u, v, ρ) (single u (ρ * t)) = single v t := by
  funext x
  simp only [carry, single]
  by_cases hxv : x = v
  · subst hxv
    simp [Function.update_of_ne huv.symm, Nat.mul_div_cancel_left _ hρ]
  · rw [Function.update_of_ne hxv, Function.update_of_ne hxv]
    by_cases hxu : x = u
    · subst hxu; simp
    · rw [Function.update_of_ne hxu, Function.update_of_ne hxu]

/-- **Proposition 171 (parallel routes).** A load of `ρ₁ρ₂ · t` at `u` sent around
either side of a square reaches `z` as the same state `t`, with ledgers
`[(u→v, ρ₂t), (v→z, t)]` and `[(u→v', ρ₂'t), (v'→z, t)]`: the routes differ only by a
circulation of the ledger.

**fdrs.md**: Proposition 171 (parallel routes). -/
theorem square_routes {u v v' z : V} (huv : u ≠ v) (hvz : v ≠ z) (huv' : u ≠ v')
    (hv'z : v' ≠ z) {ρ₁ ρ₂ ρ₁' ρ₂' : ℕ} (h1 : 0 < ρ₁) (h2 : 0 < ρ₂) (h1' : 0 < ρ₁')
    (h2' : 0 < ρ₂') (heq : ρ₁ * ρ₂ = ρ₁' * ρ₂') (t : ℕ) :
    run [(u, v, ρ₁), (v, z, ρ₂)] (single u (ρ₁ * ρ₂ * t)) = single z t ∧
    run [(u, v', ρ₁'), (v', z, ρ₂')] (single u (ρ₁ * ρ₂ * t)) = single z t ∧
    transfers [(u, v, ρ₁), (v, z, ρ₂)] (single u (ρ₁ * ρ₂ * t)) =
      [(u, v, ρ₁, ρ₂ * t), (v, z, ρ₂, t)] ∧
    transfers [(u, v', ρ₁'), (v', z, ρ₂')] (single u (ρ₁ * ρ₂ * t)) =
      [(u, v', ρ₁', ρ₂' * t), (v', z, ρ₂', t)] := by
  have hA : single u (ρ₁ * ρ₂ * t) = single u (ρ₁ * (ρ₂ * t)) := by rw [mul_assoc]
  have hB : single u (ρ₁ * ρ₂ * t) = single u (ρ₁' * (ρ₂' * t)) := by rw [heq, mul_assoc]
  have hu : ∀ (y : V) (a : ℕ), single y a y = a := fun y a => by simp [single]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hA]; simp only [run]; rw [carry_single huv h1, carry_single hvz h2]
  · rw [hB]; simp only [run]; rw [carry_single huv' h1', carry_single hv'z h2']
  · rw [hA]; simp only [transfers]; rw [carry_single huv h1, hu, hu,
      Nat.mul_div_cancel_left _ h1, Nat.mul_div_cancel_left _ h2]
  · rw [hB]; simp only [transfers]; rw [carry_single huv' h1', hu, hu,
      Nat.mul_div_cancel_left _ h1', Nat.mul_div_cancel_left _ h2']

end FdrsFormal.Operations.CarryNetwork
