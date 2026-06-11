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

# Synthetic place complex SU6b — currency balance (conservation is monoid-generic)

Second stone of the digit-coupling layer (`docs/synthetic-place/03-digit-coupling.md`
§currencies). Overflow can be **routed/split** (transport semantics: the carry is
conserved mass; distributed weights must sum) or **mirrored** (trigger semantics:
every coupled digit generates its own tick — the carry is *copied like information,
not moved like mass*). Mirrors look like they break conservation. They do not: they
change the conserved **currency**. SU4b's interface balance law never used
subtraction, order, or the size of the grant — only commutative-monoid addition — so
it holds verbatim with the ledger valued in ANY commutative monoid:

* **transport currency** (`M = ℕ`, grants = masses): SU4b's law — the instantiation
  `mass_balance`;
* **trigger currency** (`M = ℕ`, every overflow issues ONE event-token): mirrors
  conserve *event counts* — every trigger issued is consumed or pending
  (`trigger_balance`).

`currencyReachable_balanced` proves the law once, generically: every coupling edge
declares its currency, and conservation holds in the declared currency.

**Honest scope.** Single interface (one register), abstract grant set: this is the
*currency* axis isolated from the topology axis — multi-target fan-out (the
comultiplication: split vs broadcast across several edges) needs the network `Config`
and is deliberately deferred (design doc §distribution). The ℕ-machine of SU4b
remains the concrete instance with live fibers; this module is its algebra,
extracted. Leaf module. No `sorry`; axiom-clean; executable demos.
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Nat.Defs

namespace FdrsFormal.Modes.SyntheticPlace

/-! ## 1. The generic interface ledger -/

/-- An interface ledger valued in a commutative monoid: cumulative issued and
consumed totals, plus the in-flight grant (the declared extended state — no hidden
memory). -/
structure CurrencyConfig (M : Type*) where
  issued : M
  consumed : M
  pending : Option M
  deriving Repr, DecidableEq

variable {M : Type*} [AddCommMonoid M]

/-- The empty ledger. -/
def CurrencyConfig.init : CurrencyConfig M := ⟨0, 0, none⟩

/-- Issue a grant `g` into the (empty) interface. -/
def CurrencyConfig.issue (c : CurrencyConfig M) (g : M) : CurrencyConfig M :=
  ⟨c.issued + g, c.consumed, some g⟩

/-- Consume the pending grant. -/
def CurrencyConfig.consume (c : CurrencyConfig M) : CurrencyConfig M :=
  ⟨c.issued, c.consumed + c.pending.getD 0, none⟩

/-- Reachability under the guarded dynamics, with grants drawn from a declared set
`S` (the currency's legal denominations): issue only into an empty interface,
consume only a pending grant. -/
inductive CurrencyReachable (S : Set M) : CurrencyConfig M → Prop
  | init : CurrencyReachable S CurrencyConfig.init
  | issue {c : CurrencyConfig M} (g : M) (hg : g ∈ S) (hp : c.pending = none) :
      CurrencyReachable S c → CurrencyReachable S (c.issue g)
  | consume {c : CurrencyConfig M} {g : M} (hp : c.pending = some g) :
      CurrencyReachable S c → CurrencyReachable S c.consume

/-! ## 2. SU6b — the balance law, once, for every currency -/

/-- Balance: everything issued is consumed or in flight — in the monoid `M`. -/
def CurrencyBalanced (c : CurrencyConfig M) : Prop :=
  c.issued = c.consumed + c.pending.getD 0

/-- **SU6b — CURRENCY-GENERIC BALANCE.** Every reachable ledger is balanced, for ANY
commutative monoid of grants: the conservation law of the interface is independent of
what the carry *is* — mass, event-token, vector of obligations. Couplings declare
their currency; the law holds in the declared currency. -/
theorem currencyReachable_balanced {S : Set M} {c : CurrencyConfig M}
    (h : CurrencyReachable S c) : CurrencyBalanced c := by
  induction h with
  | init => simp [CurrencyBalanced, CurrencyConfig.init]
  | issue g hg hp _ ih =>
    unfold CurrencyBalanced CurrencyConfig.issue
    unfold CurrencyBalanced at ih
    rw [hp] at ih
    simp only [Option.getD_none, add_zero] at ih
    simp only [Option.getD_some]
    rw [ih]
  | consume hp _ ih =>
    unfold CurrencyBalanced CurrencyConfig.consume
    unfold CurrencyBalanced at ih
    rw [hp] at ih ⊢
    simp only [Option.getD_some, Option.getD_none, add_zero]
    exact ih

/-! ## 3. The two currencies -/

/-- **Transport currency**: grants are masses (`ℕ`, arbitrary weights — SU4b's
regime, the algebra extracted). Issued mass = consumed mass + in-flight mass. -/
theorem mass_balance {c : CurrencyConfig ℕ}
    (h : CurrencyReachable Set.univ c) : c.issued = c.consumed + c.pending.getD 0 :=
  currencyReachable_balanced h

/-- **Trigger currency** (mirrors): every overflow issues exactly ONE event-token.
Mirrored carries conserve *event counts*: triggers issued = triggers consumed +
triggers pending. Copying is conservation in the event currency. -/
theorem trigger_balance {c : CurrencyConfig ℕ}
    (h : CurrencyReachable {1} c) : c.issued = c.consumed + c.pending.getD 0 :=
  currencyReachable_balanced h

/-! ## 4. Demos — the two currencies, live -/

-- transport: a weighted grant of 5, issued then consumed — mass accounted exactly
#eval (CurrencyConfig.init (M := ℕ)).issue 5
  -- ⟨5, 0, some 5⟩ : balanced (5 = 0 + 5)
#eval ((CurrencyConfig.init (M := ℕ)).issue 5).consume
  -- ⟨5, 5, none⟩ : balanced (5 = 5 + 0)
-- trigger: two mirror events — event counts accounted exactly
#eval ((((CurrencyConfig.init (M := ℕ)).issue 1).consume).issue 1).consume
  -- ⟨2, 2, none⟩ : two triggers issued, two consumed

/-- A concrete two-cycle of the trigger currency, kernel-checked balanced. -/
theorem trigger_demo_balanced :
    CurrencyBalanced (((((CurrencyConfig.init (M := ℕ)).issue 1).consume).issue 1).consume) :=
  rfl

end FdrsFormal.Modes.SyntheticPlace
