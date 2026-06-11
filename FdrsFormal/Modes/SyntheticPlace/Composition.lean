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

# Synthetic place complex SU1 — nested / cross-timeline digit composition

The second stone of the Synthetic Place System (`docs/synthetic-place/00-thesis.md`;
roadmap `01-build-roadmap.md` §SU1). The object is the corpus's Phase 7 oracle
`Ω(s, c)` with **chain-valued context**: timeline B's digit fiber at its own prefix
depends on timeline A's prefix — *a digit composed out of the substrate it lives in*,
where the substrate crosses timelines. Scheduling convention D6: within a step, A's
digit is chosen first; B's fiber sees A's prefix including the current A-digit.

Three results, exactly the SU1 spec:

1. **SU survives level-only coupling** (`coupledCount_levelOnly`): when both fibers
   depend only on lengths, completion counts depend only on lengths — every pair of
   siblings has equal counts (the Definition 74 regime; the coupled echo of the
   Theorem 70 product regime).
2. **THE RAGGED REGIME, machine-checked** (`ragged_not_sibling_uniform`): an explicit
   coupled instance with two A-siblings of *different* completion counts. Phase 5.4
   §5's warning realized concretely: with coupling there is no rank chart, no
   odometer — and the structure is not a `RadixLaw` at all, since even one node's
   valid `(a, b)` pair-set is jagged (thesis ledger item 3).
3. **THE HEADLINE** (`coupled_ultrametric_triangle`, `coupled_ball_eq_cylinder`): the
   coupled chain's path place-value is a `PrefixGauge`, so by SU0 the coupled system
   carries a genuine ultrametric with ball = cylinder **even in the ragged regime** —
   refinement geometry survives the death of the odometer. This is the thesis §1
   claim ("the ultrametric basis is a representation-constraint generator") with its
   existence half proven; the restriction half is SU3.

**Honest scope.** Counts are finite-depth (`Definition 61`'s `W`, coupled); no measure,
no conserved quantity (thesis §3 — open), no claim of confluence for coupled steps
(post-SU3 arc). Leaf module. No `sorry`; axiom-clean; `decide` only (no
`native_decide` — ledger item 6).
-/
import FdrsFormal.Modes.SyntheticPlace.GaugeUltrametric

namespace FdrsFormal.Modes.SyntheticPlace

open Finset

/-! ## 1. The coupled fiber law (the chain-context oracle) -/

/-- **A coupled fiber law**: timeline A's fiber depends on its own prefix (a
`RadixLaw`); timeline B's fiber `fiberB sB sA` depends on its own prefix *and* on
timeline A's prefix — Phase 7's extended oracle `Ω(s, c)` (Definition 85) with the
context `c` instantiated as another chain's state. -/
structure CoupledFiber where
  /-- A's digit fiber at its prefix. -/
  fiberA : List ℕ → ℕ
  /-- B's digit fiber: own prefix, then A's prefix (including A's current digit — D6). -/
  fiberB : List ℕ → List ℕ → ℕ
  fiberA_ge_two : ∀ s, 2 ≤ fiberA s
  fiberB_ge_two : ∀ s t, 2 ≤ fiberB s t

/-! ## 2. Coupled completion counts (Definition 61's `W`, coupled) -/

/-- The number of admissible coupled paths of length `k` from the pair-prefix
`(sA, sB)`: at each step, an A-digit below `fiberA`, then a B-digit below the
A-aware `fiberB`. -/
def coupledCount (C : CoupledFiber) : ℕ → List ℕ → List ℕ → ℕ
  | 0, _, _ => 1
  | k + 1, sA, sB =>
    ∑ a ∈ Finset.range (C.fiberA sA),
      ∑ b ∈ Finset.range (C.fiberB sB (sA ++ [a])),
        coupledCount C k (sA ++ [a]) (sB ++ [b])

/-- Completion counts are positive (fibers are nonempty). -/
theorem coupledCount_pos (C : CoupledFiber) (k : ℕ) :
    ∀ sA sB, 0 < coupledCount C k sA sB := by
  induction k with
  | zero => intro sA sB; simp [coupledCount]
  | succ k ih =>
    intro sA sB
    simp only [coupledCount]
    apply Finset.sum_pos
    · intro a _
      apply Finset.sum_pos
      · intro b _; exact ih _ _
      · exact ⟨0, Finset.mem_range.mpr (by have := C.fiberB_ge_two sB (sA ++ [a]); omega)⟩
    · exact ⟨0, Finset.mem_range.mpr (by have := C.fiberA_ge_two sA; omega)⟩

/-! ## 3. When SU survives composition: the level-only regime -/

/-- Both fibers depend only on lengths (positions), not on digit values — the
coupled analogue of `RadixLaw.isPositionOnly`. -/
def CoupledFiber.IsLevelOnly (C : CoupledFiber) : Prop :=
  (∀ s t, s.length = t.length → C.fiberA s = C.fiberA t) ∧
  (∀ s s' t t', s.length = s'.length → t.length = t'.length →
    C.fiberB s t = C.fiberB s' t')

/-- **SU survives level-only coupling**: completion counts depend only on the
lengths of the pair-prefix. -/
theorem coupledCount_levelOnly (C : CoupledFiber) (h : C.IsLevelOnly) (k : ℕ) :
    ∀ sA sA' sB sB', sA.length = sA'.length → sB.length = sB'.length →
      coupledCount C k sA sB = coupledCount C k sA' sB' := by
  induction k with
  | zero => intros; simp [coupledCount]
  | succ k ih =>
    intro sA sA' sB sB' hA hB
    simp only [coupledCount]
    rw [h.1 sA sA' hA]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [h.2 sB sB' (sA ++ [a]) (sA' ++ [a]) hB (by simp [hA])]
    exact Finset.sum_congr rfl (fun b _ => ih _ _ _ _ (by simp [hA]) (by simp [hB]))

/-- Sibling uniformity in the level-only regime: all pair-siblings of a node have
equal completion counts (the Definition 74 condition, coupled). -/
theorem coupledCount_sibling_uniform (C : CoupledFiber) (h : C.IsLevelOnly) (k : ℕ)
    (sA sB : List ℕ) (a a' b b' : ℕ) :
    coupledCount C k (sA ++ [a]) (sB ++ [b])
      = coupledCount C k (sA ++ [a']) (sB ++ [b']) :=
  coupledCount_levelOnly C h k _ _ _ _ (by simp) (by simp)

/-! ## 4. The ragged regime, machine-checked -/

/-- A genuinely coupled instance: B's fiber is `2` when A's chain *opened* with the
digit `0`, else `3`. A's first digit reaches across the coupling into all of B's
future fibers. -/
def raggedFiber : CoupledFiber where
  fiberA _ := 2
  fiberB _ sA := if sA.head? = some 0 then 2 else 3
  fiberA_ge_two _ := le_refl 2
  fiberB_ge_two _ sA := by by_cases h : sA.head? = some 0 <;> norm_num [h]

/-- **THE RAGGED REGIME (Phase 5.4 §5, realized).** Two A-siblings with *different*
completion counts: under `a = 0` the subtree has `4` completions, under `a = 1` it
has `6`. Sibling uniformity fails, so there is no rank chart and no odometer — the
coupled structure is not a number system (thesis §1, correction 2). -/
theorem ragged_not_sibling_uniform :
    coupledCount raggedFiber 1 [0] [0] ≠ coupledCount raggedFiber 1 [1] [0] := by
  decide

/-- The witness is genuinely about the coupling: `raggedFiber` is not level-only. -/
theorem raggedFiber_not_levelOnly : ¬ raggedFiber.IsLevelOnly := fun h =>
  ragged_not_sibling_uniform (coupledCount_levelOnly raggedFiber h 1 _ _ _ _ rfl rfl)

/-! ## 5. The composite gauge — SU0 applies even when SU fails -/

/-- The path place-value of the coupled chain: the product of pair-fiber capacities
along a pair-word, threaded through both prefixes. -/
def coupledWeight (C : CoupledFiber) : List ℕ → List ℕ → List (ℕ × ℕ) → ℕ
  | _, _, [] => 1
  | sA, sB, p :: rest =>
    C.fiberA sA * C.fiberB sB (sA ++ [p.1]) *
      coupledWeight C (sA ++ [p.1]) (sB ++ [p.2]) rest

theorem coupledWeight_pos (C : CoupledFiber) :
    ∀ (s : List (ℕ × ℕ)) (sA sB : List ℕ), 0 < coupledWeight C sA sB s := by
  intro s
  induction s with
  | nil => intro _ _; simp [coupledWeight]
  | cons p rest ih =>
    intro sA sB
    simp only [coupledWeight]
    have h1 := C.fiberA_ge_two sA
    have h2 := C.fiberB_ge_two sB (sA ++ [p.1])
    exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (ih _ _)

/-- Appending one pair multiplies the weight by that step's pair-capacity (the
walked prefixes are just the component maps of the pair-word). -/
theorem coupledWeight_append (C : CoupledFiber) (p : ℕ × ℕ) :
    ∀ (s : List (ℕ × ℕ)) (sA sB : List ℕ),
      coupledWeight C sA sB (s ++ [p])
        = coupledWeight C sA sB s *
          (C.fiberA (sA ++ s.map Prod.fst) *
            C.fiberB (sB ++ s.map Prod.snd) ((sA ++ s.map Prod.fst) ++ [p.1])) := by
  intro s
  induction s with
  | nil => intro sA sB; simp [coupledWeight]
  | cons q rest ih =>
    intro sA sB
    simp only [List.cons_append, coupledWeight, List.map_cons]
    rw [ih (sA ++ [q.1]) (sB ++ [q.2])]
    simp only [List.append_assoc, List.singleton_append]
    ring

/-- **The composite gauge** of a coupled chain, as a `PrefixGauge` on pair digits
(design D1: pairs flow in directly, no re-encoding). -/
def coupledGauge (C : CoupledFiber) : PrefixGauge (ℕ × ℕ) where
  Adm _ := True
  gauge s := coupledWeight C [] [] s
  adm_append _ _ _ := trivial
  pos s _ := coupledWeight_pos C s [] []
  mono_append s p _ := by
    rw [coupledWeight_append]
    have h1 := C.fiberA_ge_two ([] ++ s.map Prod.fst)
    have h2 := C.fiberB_ge_two ([] ++ s.map Prod.snd) (([] ++ s.map Prod.fst) ++ [p.1])
    exact Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) (by omega))

/-- The composite gauge dominates `2^depth` (each step's pair-capacity is ≥ 4). -/
theorem two_pow_length_le_coupledWeight (C : CoupledFiber) :
    ∀ (s : List (ℕ × ℕ)) (sA sB : List ℕ), 2 ^ s.length ≤ coupledWeight C sA sB s := by
  intro s
  induction s with
  | nil => intro _ _; simp [coupledWeight]
  | cons p rest ih =>
    intro sA sB
    simp only [coupledWeight, List.length_cons]
    have hAB : 2 ≤ C.fiberA sA * C.fiberB sB (sA ++ [p.1]) := by
      have h1 := C.fiberA_ge_two sA
      have h2 := C.fiberB_ge_two sB (sA ++ [p.1])
      nlinarith
    calc 2 ^ (rest.length + 1) = 2 * 2 ^ rest.length := by ring
      _ ≤ (C.fiberA sA * C.fiberB sB (sA ++ [p.1])) *
            coupledWeight C (sA ++ [p.1]) (sB ++ [p.2]) rest :=
          Nat.mul_le_mul hAB (ih _ _)

/-- The composite gauge is unbounded along every pair-stream. -/
theorem coupledGauge_unbounded (C : CoupledFiber) (x : ℕ → ℕ × ℕ) :
    GaugeUnbounded (coupledGauge C) x := by
  intro M
  refine ⟨M, ?_⟩
  show M ≤ coupledWeight C [] [] (pre x M)
  calc M ≤ 2 ^ M := Nat.le_of_lt M.lt_two_pow_self
    _ ≤ coupledWeight C [] [] (pre x M) := by
        have h := two_pow_length_le_coupledWeight C (pre x M) [] []
        rwa [pre_length] at h

/-- **THE HEADLINE (strong triangle).** The coupled chain carries a genuine
ultrametric — *even in the ragged regime*, where sibling uniformity, the rank chart,
and the odometer are all dead. Refinement geometry survives the death of the
odometer: SU0 applied to the composite gauge. -/
theorem coupled_ultrametric_triangle (C : CoupledFiber) (x y z : ℕ → ℕ × ℕ) :
    gaugeDist (coupledGauge C) x z
      ≤ max (gaugeDist (coupledGauge C) x y) (gaugeDist (coupledGauge C) y z) :=
  gaugeDist_triangle _ (fun _ => trivial) y z

/-- **THE HEADLINE (`ball = cylinder`).** Every ball of the coupled chain is a
combinatorial pair-cylinder — the coupled system's refinement domains are exactly its
metric balls. -/
theorem coupled_ball_eq_cylinder (C : CoupledFiber) (x : ℕ → ℕ × ℕ)
    (r : ℝ) (hr : 0 < r) :
    ∃ n : ℕ, {y | gaugeDist (coupledGauge C) x y < r} = {y | pre y n = pre x n} :=
  ball_eq_cylinder _ (fun _ => trivial) (coupledGauge_unbounded C x) r hr

/-! ## 6. Demos — the ragged counts and the composite gauge (exact ℕ, computable) -/

-- the two A-siblings' completion counts: 4 vs 6 — sibling uniformity fails
#eval coupledCount raggedFiber 1 [0] [0]   -- 4
#eval coupledCount raggedFiber 1 [1] [0]   -- 6
-- deeper: the ragged tree keeps diverging
#eval coupledCount raggedFiber 2 [0] [0]   -- 16
#eval coupledCount raggedFiber 2 [1] [0]   -- 36
-- the composite gauge along a pair-word that opens with A-digit 1 (fiberB = 3 forever)
#eval coupledWeight raggedFiber [] [] [(1, 0), (0, 2), (1, 1)]   -- 6 * 6 * 6 = 216
-- and along one that opens with A-digit 0 (fiberB = 2 forever)
#eval coupledWeight raggedFiber [] [] [(0, 0), (1, 1), (0, 0)]   -- 4 * 4 * 4 = 64

end FdrsFormal.Modes.SyntheticPlace
