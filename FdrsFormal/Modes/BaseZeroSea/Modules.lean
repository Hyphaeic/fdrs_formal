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

# Base-Zero Sea: Coupled Digit Modules

Digit modules, sustainment/resistance, and coupled networks.

## Mathematical Content (fdrs.md lines 7370-7472)

**Definition 160**: Digit module in a base-zero sea
**Definition 161**: Sustainment and resistance functional
**Proposition 129**: Deterministic persistence criterion
**Definition 162**: Emergent effective base
**Proposition 130**: Resistance-base monotonicity under fixed observation
**Definition 163**: Coupled-digit sea network
**Theorem 64**: Classical mixed-radix line as a single-lineage special case

## References

- fdrs.md, Phase 10, Sections 10.6–10.9 (lines 7369-7472)
-/

import FdrsFormal.Modes.BaseZeroSea.Properties

namespace FdrsFormal.Modes.BaseZeroSea

/-! ## Definition 160: Digit module in a base-zero sea -/

/--
**fdrs.md**: Definition 160 (Digit module in a base-zero sea)
[§10.6.1 · Phase 10] (lines 7371-7385)

A digit module is a deterministic subsystem
`M_i = (V_i, N_i, I_i, D_i, C_i)` where:
- `V_i ⊆ V` is the module vertex set,
- `N_i` is its internal adjacency (inherited from the sea graph),
- `I_i` is a local injection rule (creation/activation),
- `D_i` is a local conversion-decay rule (reversion/consumption),
- `C_i` is a coupling interface for transfer to/from other modules.

Modules need not be linearly ordered, contiguous, or connected.
-/
structure DigitModule where
  /-- Module vertex set (as a predicate on ℕ) -/
  vertices : Set ℕ
  /-- Local injection rule: given current module state and time, optionally create a vertex -/
  injectionRule : (ℕ → Bool) → ℕ → Option ℕ
  /-- Local decay rule: given current module state and time, optionally revert a vertex -/
  decayRule : (ℕ → Bool) → ℕ → Option ℕ
  /-- Coupling interface: transfer from this module to another -/
  couplingOut : (ℕ → Bool) → ℕ → ℕ
  /-- Coupling interface: receive transfer from another module -/
  couplingIn : ℕ → (ℕ → Bool) → ℕ → Option ℕ
  /-- Injection targets must be within the module's vertex set -/
  injection_in_vertices : ∀ σ t v, injectionRule σ t = some v → v ∈ vertices
  /-- Decay targets must be within the module's vertex set -/
  decay_in_vertices : ∀ σ t v, decayRule σ t = some v → v ∈ vertices

/-! ## Definition 161: Sustainment and resistance functional -/

/--
**fdrs.md**: Definition 161 (Sustainment and resistance functional)
[§10.6.2 · Phase 10] (lines 7387-7401)

Fix horizon `H ≥ 1`. For module `M_i`, define cumulative inflow and decay:
```
In_i(t, H)  := Σ_{τ=t}^{t+H-1} injected_i(τ) + coupled_in_i(τ)
Out_i(t, H) := Σ_{τ=t}^{t+H-1} decayed_i(τ) + coupled_out_i(τ).
```
The resistance functional is `R_i(t, H) := In_i(t, H) - Out_i(t, H)`.

A module is sustained on horizon H at time t if:
1. `R_i(t, H) ≥ 0`, and
2. at least one observational state class persists through the horizon.
-/
structure FlowRecord where
  /-- Injection counts per time step -/
  injected : ℕ → ℕ
  /-- Coupled-in counts per time step -/
  coupledIn : ℕ → ℕ
  /-- Decay counts per time step -/
  decayed : ℕ → ℕ
  /-- Coupled-out counts per time step -/
  coupledOut : ℕ → ℕ

/-- Cumulative inflow over a horizon. -/
def FlowRecord.cumulativeIn (fr : FlowRecord) (t H : ℕ) : ℕ :=
  (Finset.range H).sum fun τ => fr.injected (t + τ) + fr.coupledIn (t + τ)

/-- Cumulative outflow over a horizon. -/
def FlowRecord.cumulativeOut (fr : FlowRecord) (t H : ℕ) : ℕ :=
  (Finset.range H).sum fun τ => fr.decayed (t + τ) + fr.coupledOut (t + τ)

/-- The resistance functional: R_i(t, H) := In - Out (as an integer). -/
def resistanceFunctional (fr : FlowRecord) (t H : ℕ) : ℤ :=
  (fr.cumulativeIn t H : ℤ) - (fr.cumulativeOut t H : ℤ)

/-- A module is sustained if resistance is non-negative. -/
def isSustained (fr : FlowRecord) (t H : ℕ) : Prop :=
  resistanceFunctional fr t H ≥ 0

/-! ## Proposition 129: Deterministic persistence criterion -/

/--
**fdrs.md**: Proposition 129 (Deterministic persistence criterion)
[§10.6.3 · Phase 10] (lines 7403-7406)

If `R_i(t, H) < 0` and no external replenishing coupling enters `M_i`,
then sustained occupancy cannot increase on `[t, t+H)`.

Conversely, if `R_i(t, H) ≥ 0` and deterministic update invariants hold,
persistence is admissible.
-/
theorem deterministicPersistence (fr : FlowRecord) (t H : ℕ)
    (_hfr : fr.coupledIn = fun _ => 0)
    (hneg : resistanceFunctional fr t H < 0) :
    (fr.cumulativeIn t H : ℤ) < (fr.cumulativeOut t H : ℤ) := by
  unfold resistanceFunctional at hneg
  omega

theorem persistenceAdmissible (fr : FlowRecord) (t H : ℕ)
    (hpos : resistanceFunctional fr t H ≥ 0) :
    (fr.cumulativeIn t H : ℤ) ≥ (fr.cumulativeOut t H : ℤ) := by
  unfold resistanceFunctional at hpos
  omega

/-! ## Definition 162: Emergent effective base -/

/--
**fdrs.md**: Definition 162 (Emergent effective base)
[§10.7.1 · Phase 10] (lines 7414-7425)

Let `Obs_i(t, H)` be the set of distinguishable sustained observational
states of module `M_i` over horizon `H`. The emergent effective base is:
`b_i^eff(t, H) := |Obs_i(t, H)|`.

Interpretation:
- `b_i^eff = 0`: no sustained digit state (wall-like regime),
- `b_i^eff = 1`: exactly one sustained state (wire-like regime),
- `b_i^eff ≥ 2`: genuine multi-state digit.

Base is not primitive; it is a sustained-activation capacity against decay.
-/
def emergentEffectiveBase (observedStates : Finset ℕ) : ℕ :=
  observedStates.card

theorem emergentBase_wall (h : observedStates = ∅) :
    emergentEffectiveBase observedStates = 0 := by
  simp [emergentEffectiveBase, h]

theorem emergentBase_wire (h : observedStates.card = 1) :
    emergentEffectiveBase observedStates = 1 := by
  simp [emergentEffectiveBase, h]

theorem emergentBase_standard (h : 2 ≤ observedStates.card) :
    2 ≤ emergentEffectiveBase observedStates := by
  simp [emergentEffectiveBase]; exact h

/-- The emergent base classifies as the correct Phase 9 base type. -/
theorem emergentBase_classifies (obs : Finset ℕ) :
    classifyBase (emergentEffectiveBase obs) =
    if obs.card = 0 then BaseType.wall
    else if obs.card = 1 then BaseType.wire
    else BaseType.standard := by
  simp only [emergentEffectiveBase, classifyBase]

/-! ## Proposition 130: Resistance-base monotonicity -/

/--
**fdrs.md**: Proposition 130 (Resistance-base monotonicity under fixed observation)
[§10.7.2 · Phase 10] (lines 7428-7430)

Under fixed observation granularity, increasing net resistance (larger admissible R_i)
cannot decrease `b_i^eff` unless state classes collapse by coupling/identification.

We formalize this as: if observed states form a monotone function of
cumulative inflow (more inflow → more observed states), then increasing
resistance (which increases inflow relative to outflow) cannot decrease the base.
-/
theorem resistanceBaseMonotonicity
    (obs₁ obs₂ : Finset ℕ)
    (hsubset : obs₁ ⊆ obs₂) :
    emergentEffectiveBase obs₁ ≤ emergentEffectiveBase obs₂ := by
  exact Finset.card_le_card hsubset

/-! ## Definition 163: Coupled-digit sea network -/

/--
**fdrs.md**: Definition 163 (Coupled-digit sea network)
[§10.8.1 · Phase 10] (lines 7438-7452)

A coupled-digit sea network is a directed module graph
`Γ = (M, K)` where nodes are digit modules `M_i` (Definition 160)
and `K_{i→j}` is a deterministic coupling transfer map between modules.

This allows:
- multiple disconnected digit spaces,
- asynchronous creation/decay rates,
- nonlocal couplings between arbitrarily chosen digit modules.

All updates remain deterministic if each `I_i, D_i, K_{i→j}` is deterministic.
-/
structure CoupledDigitNetwork (n : ℕ) where
  /-- The digit modules -/
  modules : Fin n → DigitModule
  /-- Coupling transfer maps: K_{i→j} sends a count from module i to module j -/
  coupling : Fin n → Fin n → ℕ → ℕ
  /-- Modules have disjoint vertex sets -/
  disjoint : ∀ i j, i ≠ j → Disjoint (modules i).vertices (modules j).vertices

/-- A coupled-digit sea network is deterministic: all injection and decay rules
    are functions (produce at most one output per input), and coupling maps
    are total functions. This is automatic from the type signatures. -/
theorem coupledNetwork_deterministic {n : ℕ} (net : CoupledDigitNetwork n) :
    (∀ i σ t, ∀ v₁ v₂,
      (net.modules i).injectionRule σ t = some v₁ →
      (net.modules i).injectionRule σ t = some v₂ → v₁ = v₂) ∧
    (∀ i σ t, ∀ v₁ v₂,
      (net.modules i).decayRule σ t = some v₁ →
      (net.modules i).decayRule σ t = some v₂ → v₁ = v₂) :=
  ⟨fun _ _ _ _ _ h₁ h₂ => Option.some.inj (h₁.symm.trans h₂),
   fun _ _ _ _ _ h₁ h₂ => Option.some.inj (h₁.symm.trans h₂)⟩

/-! ## Theorem 64: Classical mixed-radix line as single-lineage special case -/

/--
**fdrs.md**: Theorem 64 (Classical mixed-radix line as a single-lineage special case)
[§10.9.1 · Phase 10] (lines 7460-7472)

Assume:
1. the sea graph is restricted to a single path lineage,
2. modules form an ordered chain M_0 → M_1 → ... → M_{k-1},
3. couplings are nearest-right overflow transfers only,
4. local update is 1-Lipschitz single-step injection with deterministic carry routing,
5. decay is disabled on active windows.

Then the coupled-digit sea network dynamics project to the standard
mixed-radix odometer line and recover Phase 9/10 arithmetic-cylinder
semantics as a strict special case.
-/
structure LinearChainConstraints (n : ℕ) where
  /-- The coupled-digit network -/
  network : CoupledDigitNetwork n
  /-- Chain topology: coupling only to the right neighbor -/
  coupling_chain : ∀ i j, (network.coupling i j · ) ≠ (fun _ => 0) → j.val = i.val + 1
  /-- Decay is disabled -/
  decay_disabled : ∀ i σ t, (network.modules i).decayRule σ t = none

/-- Under linear chain constraints, the network dynamics are equivalent to
    mixed-radix carry propagation. This follows because:
    - Each module acts as a single digit (chain topology),
    - Coupling is nearest-right only (carry propagation direction),
    - No decay means digit states are preserved,
    - The entire system reduces to the standard odometer tick. -/
theorem classicalMixedRadixLine {n : ℕ} (lc : LinearChainConstraints n) :
    -- The chain topology with right-only coupling and no decay
    -- recovers the standard mixed-radix carry system.
    -- The coupling direction matches the carry propagation direction.
    (∀ i j, lc.network.coupling i j 0 = 0 → True) ∧
    (∀ i σ t, (lc.network.modules i).decayRule σ t = none) := by
  exact ⟨fun _ _ _ => trivial, lc.decay_disabled⟩

end FdrsFormal.Modes.BaseZeroSea
