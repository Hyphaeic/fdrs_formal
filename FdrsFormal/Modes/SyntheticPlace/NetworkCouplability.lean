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

# Synthetic place complex SU7.3 — non-blocking couplability (the decidable check)

`04-network-config.md` §2 clause 2: *"these lines can couple" = the guard system is
non-blocking: every reachable `Config` has an enabled step; decidable via the SU2
uncertainty machinery (reachable-set fixpoint over the joint transfer structure);
blocked witnesses are grammars strangled by their own coupling — the empty-joint-
fiber phenomenon.* This module delivers the row (SU7.3: decidable check + soundness;
a blocked witness and a live witness):

* **`Enabled` / `NonBlocking`** — the step guards as a predicate; couplability =
  every reachable configuration has an enabled firing.
* **The fixpoint check** — `reachFix` iterates a declared abstract successor map
  over a finite-state abstraction (SU2's `stepSet` shape: a reachable-SET fixpoint,
  here over the abstraction's states rather than transfer states);
  **`couplableCheck`** (fixpoint closure ∧ all abstract states enabled) is
  **decidable** (`instDecidableCouplableCheck`).
* **Soundness** — `nonBlocking_of_couplableCheck`: an abstraction that (i) maps the
  initial configuration to `q0`, (ii) over-approximates every guarded firing
  (`abs (fireC …) ∈ stepFix succs {abs cfg}`), and (iii) reads enabledness back
  concretely, turns a `couplableCheck` success into `NonBlocking`. One direction
  only — the check is a certificate, not a characterization (no completeness
  claimed; a `false` verdict says nothing).
* **The live witness** — the constant coupled pair (`liveFiber`, the SU4b machine
  at `fiberA = 2`, `fiberB = 2`): abstracted to `Bool` (interface empty?), the
  check is discharged by `decide`, the pending-value invariant closes the concrete
  read-back, and **`live_nonBlocking`** lands: the coupled pair can always move.
* **The blocked witness** — `blockedRule`: the same shape with the **empty joint
  fiber** (`admit := False` — the receiver's window admits nothing). One A-step is
  reachable, and then nothing is enabled: A is capacity-blocked by its own
  unconsumed grant, B's joint fiber is empty (`blocked_stuck`), so
  **`blocked_not_nonBlocking`** — a grammar strangled by its own coupling,
  machine-checked.

**Honest scope.** The abstraction (state space, successor map, enabled read-back)
is per-instance declared data — the "finite-state window abstraction" of `04`; this
module supplies the generic fixpoint certificate, not an abstraction synthesizer.
Soundness is one-directional by design. `NonBlocking` says a step exists — it does
not say certificates fire (liveness of emissions is SU7.6) nor which step is fair
(determinacy is SU7.5). Leaf module over SU7.1. No `sorry`; axiom-clean;
kernel-checked witnesses.
-/
import FdrsFormal.Modes.SyntheticPlace.NetworkComplexStep

namespace FdrsFormal.Modes.SyntheticPlace

variable {N : NetworkShape} {M : Type*} [AddCommMonoid M] [DecidableEq N.V] [Fintype N.E]

/-! ## 1. Enabledness and non-blocking couplability -/

/-- The step guards of the three-clause machine, as a predicate: `d` is admitted by
the node's own law, by every in-edge's window against its pending grant (the joint
fiber), every out-edge has capacity, and the fan-out is lawful. -/
def Enabled (R : ComplexRule N M) (cfg : CConfig N M) (v : N.V) (d : ℕ) : Prop :=
  (∀ f, R.nodeFiber v = some f → d < f (cfg.word v)) ∧
  (∀ e, N.tgt e = v → ∃ g, (cfg.edge e).pending = some g ∧ R.admit e g d) ∧
  (∀ e, N.src e = v → (cfg.edge e).pending = none) ∧
  FanoutLawful R cfg v d

/-- An enabled firing really steps. -/
theorem Enabled.fire {R : ComplexRule N M} {cfg : CConfig N M} {v : N.V} {d : ℕ}
    (h : Enabled R cfg v d) (hr : ComplexReachable R cfg) :
    ComplexReachable R (fireC R cfg v d) :=
  ComplexReachable.fire hr v d h.1 h.2.1 h.2.2.1 h.2.2.2

/-- **Couplability** (`04` §2 clause 2): the guard system is non-blocking — every
reachable configuration has an enabled step. -/
def NonBlocking (R : ComplexRule N M) : Prop :=
  ∀ cfg, ComplexReachable R cfg → ∃ v d, Enabled R cfg v d

/-! ## 2. The reachable-set fixpoint over a finite abstraction (the SU2 shape) -/

variable {Q : Type*} [DecidableEq Q]

/-- One round of the abstract reachable-set iteration: keep what we have, add every
declared successor (SU2's `stepSet`, on the abstraction's states). -/
def stepFix (succs : Q → Finset Q) (S : Finset Q) : Finset Q :=
  S ∪ S.biUnion succs

theorem subset_stepFix {succs : Q → Finset Q} {S : Finset Q} : S ⊆ stepFix succs S :=
  Finset.subset_union_left

theorem stepFix_mono {succs : Q → Finset Q} {S T : Finset Q} (h : S ⊆ T) :
    stepFix succs S ⊆ stepFix succs T :=
  Finset.union_subset_union h (Finset.biUnion_subset_biUnion_of_subset_left _ h)

/-- The abstract reachable set after `n` rounds from `q0`. -/
def reachFix (succs : Q → Finset Q) (q0 : Q) (n : ℕ) : Finset Q :=
  (stepFix succs)^[n] {q0}

theorem reachFix_succ (succs : Q → Finset Q) (q0 : Q) (n : ℕ) :
    reachFix succs q0 (n + 1) = stepFix succs (reachFix succs q0 n) :=
  Function.iterate_succ_apply' _ _ _

theorem reachFix_mono {succs : Q → Finset Q} {q0 : Q} :
    ∀ {n m : ℕ}, n ≤ m → reachFix succs q0 n ⊆ reachFix succs q0 m := by
  intro n m h
  induction h with
  | refl => exact subset_rfl
  | step _ ih =>
    rw [reachFix_succ]
    exact ih.trans subset_stepFix

/-- Once the iteration closes, it stays closed. -/
theorem reachFix_stab {succs : Q → Finset Q} {q0 : Q} {fuel : ℕ}
    (hfix : stepFix succs (reachFix succs q0 fuel) = reachFix succs q0 fuel) :
    ∀ m, reachFix succs q0 (fuel + m) = reachFix succs q0 fuel := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih => rw [← Nat.add_assoc, reachFix_succ, ih, hfix]

/-- A closed iterate bounds every round. -/
theorem reachFix_subset_of_fix {succs : Q → Finset Q} {q0 : Q} {fuel : ℕ}
    (hfix : stepFix succs (reachFix succs q0 fuel) = reachFix succs q0 fuel)
    (n : ℕ) : reachFix succs q0 n ⊆ reachFix succs q0 fuel := by
  rcases Nat.le_total n fuel with h | h
  · exact reachFix_mono h
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [reachFix_stab hfix]

/-- **The decidable couplability check**: the abstract reachable set closes at
`fuel`, and every abstract state in it reads enabled.

**fdrs.md**: Definition 210 (non-blocking couplability; the decidable fixpoint check) [§14.12 · Phase 14] -/
def couplableCheck (succs : Q → Finset Q) (q0 : Q) (enabledB : Q → Bool)
    (fuel : ℕ) : Prop :=
  stepFix succs (reachFix succs q0 fuel) = reachFix succs q0 fuel ∧
  ∀ q ∈ reachFix succs q0 fuel, enabledB q = true

instance instDecidableCouplableCheck (succs : Q → Finset Q) (q0 : Q)
    (enabledB : Q → Bool) (fuel : ℕ) :
    Decidable (couplableCheck succs q0 enabledB fuel) := by
  unfold couplableCheck
  infer_instance

/-- Every concretely reachable configuration lands (abstractly) in some round. -/
theorem abstract_reach {R : ComplexRule N M} {Q : Type*} [DecidableEq Q]
    (abs : CConfig N M → Q) (succs : Q → Finset Q) (q0 : Q)
    (habs0 : abs (initC N M) = q0)
    (hstep : ∀ cfg v d, ComplexReachable R cfg → Enabled R cfg v d →
      abs (fireC R cfg v d) ∈ stepFix succs {abs cfg})
    {cfg : CConfig N M} (h : ComplexReachable R cfg) :
    ∃ n, abs cfg ∈ reachFix succs q0 n := by
  induction h with
  | init => exact ⟨0, by rw [habs0]; exact Finset.mem_singleton_self q0⟩
  | fire hr v d hown hin hout hlaw ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    rw [reachFix_succ]
    exact stepFix_mono (Finset.singleton_subset_iff.mpr hn)
      (hstep _ v d hr ⟨hown, hin, hout, hlaw⟩)

/-- **SU7.3 — soundness of the couplability check**: a finite-state abstraction that
over-approximates the firings and reads enabledness back concretely turns a
`couplableCheck` success into `NonBlocking`.

**fdrs.md**: Theorem 107 (couplability certificate soundness) [§14.12 · Phase 14] -/
theorem nonBlocking_of_couplableCheck {R : ComplexRule N M} {Q : Type*} [DecidableEq Q]
    (abs : CConfig N M → Q) (succs : Q → Finset Q) (q0 : Q) (enabledB : Q → Bool)
    (fuel : ℕ)
    (habs0 : abs (initC N M) = q0)
    (hstep : ∀ cfg v d, ComplexReachable R cfg → Enabled R cfg v d →
      abs (fireC R cfg v d) ∈ stepFix succs {abs cfg})
    (henabled : ∀ cfg, ComplexReachable R cfg → enabledB (abs cfg) = true →
      ∃ v d, Enabled R cfg v d)
    (hcheck : couplableCheck succs q0 enabledB fuel) :
    NonBlocking R := by
  intro cfg hcfg
  obtain ⟨n, hn⟩ := abstract_reach abs succs q0 habs0 hstep hcfg
  exact henabled cfg hcfg (hcheck.2 _ (reachFix_subset_of_fix hcheck.1 n hn))

/-! ## 3. The live witness — the constant coupled pair, certified through the check -/

/-- The constant coupled fiber: `fiberA = 2`, every grant `2`. -/
def liveFiber : CoupledFiber :=
  { fiberA := fun _ => 2, fiberB := fun _ _ => 2
    fiberA_ge_two := fun _ => le_refl 2, fiberB_ge_two := fun _ _ => le_refl 2 }

/-- The pending-value invariant of the live pair: the interface is empty or holds
the constant grant `2`. -/
theorem live_pending {cfg : CConfig pairShape ℕ}
    (h : ComplexReachable (ofRule (pairRule liveFiber)) cfg) :
    (cfg.edge ()).pending = none ∨ (cfg.edge ()).pending = some 2 := by
  induction h with
  | init => exact Or.inl rfl
  | fire hr v d hown hin hout hlaw ih =>
    cases v with
    | false =>
      right
      simp [fireC, ofRule, pairRule, liveFiber, CurrencyConfig.issue]
    | true =>
      left
      simp [fireC, CurrencyConfig.consume]

/-- **The live witness**: the constant coupled pair is non-blocking — certified by
the decidable fixpoint check (`decide`) over the `Bool` abstraction "is the
interface empty?", with the pending invariant closing the concrete read-back. The
coupled lines can always move. -/
theorem live_nonBlocking : NonBlocking (ofRule (pairRule liveFiber)) := by
  refine nonBlocking_of_couplableCheck
    (abs := fun cfg => (cfg.edge ()).pending.isNone)
    (succs := fun _ => {true, false}) (q0 := true) (enabledB := fun _ => true)
    (fuel := 1) rfl ?_ ?_ (by decide)
  · intro cfg v d _ _
    have : ∀ x b : Bool, x ∈ stepFix (fun _ => ({true, false} : Finset Bool)) {b} := by
      decide
    exact this _ _
  · intro cfg hcfg _
    rcases live_pending hcfg with hn | hs
    · refine ⟨false, 0, ?_, ?_, ?_, ofRule_fanoutLawful _ _ _ _⟩
      · intro f hf
        have : (fun _ : List ℕ => 2) = f := by simpa [ofRule, pairRule, liveFiber] using hf
        subst this
        norm_num
      · intro e he
        exact absurd he (by simp [pairShape])
      · intro e _
        cases e
        exact hn
    · refine ⟨true, 0, ?_, ?_, ?_, ofRule_fanoutLawful _ _ _ _⟩
      · intro f hf
        exact absurd hf (by simp [ofRule, pairRule])
      · intro e _
        cases e
        exact ⟨2, hs, Nat.zero_lt_two⟩
      · intro e he
        exact absurd he (by simp [pairShape])

/-! ## 4. The blocked witness — strangled by its own coupling (the empty joint fiber) -/

/-- The strangled pair: same shape, same laws — but the receiver's window admits
NOTHING (`admit := False`, the empty joint fiber). -/
def blockedRule : ComplexRule pairShape ℕ where
  nodeFiber := fun v => if v then none else some fun _ => 2
  carry := fun _ => none
  species := fun _ => Species.transport
  token := fun _ => 0
  fanout := fun _ _ _ => 2
  admit := fun _ _ _ => False
  deps := fun _ => ⟨∅⟩

/-- One A-step is reachable: nothing yet strangles the source. -/
theorem blocked_reachable :
    ComplexReachable blockedRule (fireC blockedRule (initC pairShape ℕ) false 0) := by
  refine ComplexReachable.fire (R := blockedRule) (ComplexReachable.init (R := blockedRule))
    false 0 ?_ ?_ ?_ ?_
  · intro f hf
    have : (fun _ : List ℕ => 2) = f := by simpa [blockedRule] using hf
    subst this
    norm_num
  · intro e he
    exact absurd he (by simp [pairShape])
  · intro e _
    rfl
  · constructor
    · intro c hc
      exact absurd hc (by simp [blockedRule])
    · intro e _ hs
      exact absurd hs (by simp [blockedRule])

/-- **The strangling**: after that step nothing is enabled — A is capacity-blocked
by its own unconsumed grant; B's joint fiber is empty. -/
theorem blocked_stuck (v : Bool) (d : ℕ) :
    ¬ Enabled blockedRule (fireC blockedRule (initC pairShape ℕ) false 0) v d := by
  intro h
  cases v with
  | false =>
    have hp := h.2.2.1 () rfl
    simp [fireC, blockedRule, CurrencyConfig.issue] at hp
  | true =>
    obtain ⟨g, _, hadm⟩ := h.2.1 () rfl
    exact hadm

/-- **The blocked witness**: the strangled pair is NOT non-blocking — a grammar
strangled by its own coupling, the empty-joint-fiber phenomenon of `04` §2,
machine-checked.

**fdrs.md**: Proposition 152 (witnesses on both sides of couplability) [§14.12 · Phase 14] -/
theorem blocked_not_nonBlocking : ¬ NonBlocking blockedRule := by
  intro h
  obtain ⟨v, d, henb⟩ := h _ blocked_reachable
  exact blocked_stuck v d henb

/-! ## Axiom audit -/

#print axioms nonBlocking_of_couplableCheck
#print axioms live_nonBlocking
#print axioms blocked_stuck
#print axioms blocked_not_nonBlocking

end FdrsFormal.Modes.SyntheticPlace
