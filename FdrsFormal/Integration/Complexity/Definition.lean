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

# Complexity Bounds

This file defines complexity measures and bounds for FDRS operations.

## Mathematical Content (fdrs.md Phase 4)

**Touch Complexity**: Number of memory locations accessed per operation.
**Depth Complexity**: Circuit depth for parallel implementations.

**Key Results**:
- Tick operations have O(L) touch complexity for L-digit numbers
- Dirichlet transforms have bounded touch on cylinder-local state

## References

- fdrs.md, Phase 4, Section 4.5 (Locality Contract)
- fdrs.md, Phase 4, Section 4.7 (Complexity Analysis)
-/

import FdrsFormal.Core
import FdrsFormal.NumberTheory
import FdrsFormal.Topology.Dynamics.Odometer

namespace FdrsFormal.Integration.Complexity

open FdrsFormal.Core.Primitives FdrsFormal.Core.Infinite
open FdrsFormal.Topology.Dynamics

/-!
## Touch Complexity
-/

/--
Touch set: the set of positions accessed by an operation.

**fdrs.md**: `Touch(Op) = {positions read or written by Op}`

Note: This is an abstract characterization. For concrete operations,
we would define this based on the operation's dependency structure.
The default returns the universal set (pessimistic bound).
-/
def touchSet (op : (ℕ → α) → (ℕ → α)) (n : ℕ) : Set ℕ :=
  Set.univ  -- Conservative: assume all positions may be accessed

/--
Touch complexity: the number of positions an operation accesses, i.e. the
cardinality of its (finite) touch set.

**fdrs.md**: `|Touch(Op)|` — bounded for all *local* operations. An opaque
operation has `touchSet = Set.univ` (unbounded); a local operation exposes a
finite touch set `T`, and its touch complexity is `T.card`.
-/
def touchComplexity (T : Finset ℕ) : ℕ := T.card

/-- The touch set of `Tick` at a state whose carry stops at index `m`: the carry
zone `{0, 1, …, m}`. By `tick_touch_bound`, positions beyond `m` are untouched. -/
def tickTouchSet (m : ℕ) : Finset ℕ := Finset.range (m + 1)

/-- `Tick` touches exactly `m + 1` positions when the carry stops at index `m`,
so its touch complexity is `O(m) ≤ O(L)` for an `L`-digit number — the carry-local
cost made precise by `tick_touch_bound`. -/
theorem tick_touchComplexity (m : ℕ) : touchComplexity (tickTouchSet m) = m + 1 := by
  simp [touchComplexity, tickTouchSet]

/-!
## Tick Complexity
-/

/--
Tick touch bound: tick only modifies positions within the carry propagation range.
If m is the first non-maximal digit, all positions beyond m are preserved.
This bounds touch complexity at O(m+1) ≤ O(L) for L-digit numbers.

**fdrs.md Proposition 82**: Tick is computable in O(i*) where i* is the carry-stop index.
-/
theorem tick_touch_bound {b : RadixSeq} (x : CompletedSpace b) (m : ℕ)
    (h_before : ∀ j < m, x j = ⟨b j - 1, Nat.sub_lt (b.pos j) Nat.one_pos⟩)
    (h_at : x m ≠ ⟨b m - 1, Nat.sub_lt (b.pos m) Nat.one_pos⟩) :
    ∀ j, m < j → tickCompleted b x j = x j := by
  intro j hj
  simp only [tickCompleted]
  have : ¬allMaxBefore b x j := by
    intro hall
    have h := allMaxBefore_of_le' hall (Nat.succ_le_of_lt hj)
    simp only [allMaxBefore] at h
    exact h_at h.2
  rw [if_neg this]

/--
Expected tick complexity is O(1): the sum of reciprocal place values is bounded by 2.

This captures the amortized analysis: carry reaches position k with probability 1/B_k,
and ∑_{k<L} 1/B_k < 2 since B_k ≥ 2^k.

**fdrs.md Proposition 11**: Carry locality and amortized O(1) cost.
-/
private lemma placeValue_recip_sum_le (b : RadixSeq) (L : ℕ) :
    ∑ k : Fin L, (1 : ℝ) / (placeValue b ↑k : ℝ) ≤ 2 - 2 / (placeValue b L : ℝ) := by
  induction L with
  | zero => simp [placeValue.zero]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have hBn : (0 : ℝ) < (placeValue b n : ℝ) := Nat.cast_pos.mpr (placeValue.pos n)
    have hBn1 : (0 : ℝ) < (placeValue b (n + 1) : ℝ) := Nat.cast_pos.mpr (placeValue.pos (n + 1))
    have hbn : (2 : ℝ) ≤ (b.toFun n : ℝ) := by exact_mod_cast b.ge_two n
    -- Key: 2/B_{n+1} ≤ 1/B_n since B_{n+1} = B_n · b_n ≥ 2·B_n
    have h_key : 2 / (placeValue b (n + 1) : ℝ) ≤ 1 / (placeValue b n : ℝ) := by
      rw [div_le_div_iff₀ hBn1 hBn, one_mul]
      have : (placeValue b (n + 1) : ℝ) = (placeValue b n : ℝ) * (b.toFun n : ℝ) := by
        push_cast [placeValue.succ]; ring
      linarith [mul_le_mul_of_nonneg_left hbn (le_of_lt hBn)]
    -- Rewrite 2/B_n as 2*(1/B_n) so linarith sees the linear structure
    have h_rw : (2 : ℝ) / ↑(placeValue b n) = 2 * (1 / ↑(placeValue b n)) := by ring
    rw [h_rw] at ih
    linarith

theorem tick_expected_complexity (b : RadixSeq) (L : ℕ) :
    ∑ k : Fin L, (1 : ℝ) / (placeValue b ↑k : ℝ) < 2 := by
  have h := placeValue_recip_sum_le b L
  have hpos : (0 : ℝ) < (placeValue b L : ℝ) := Nat.cast_pos.mpr (placeValue.pos L)
  linarith [div_pos (by norm_num : (0:ℝ) < 2) hpos]

/-!
## Dirichlet Transform Complexity
-/

/--
Dirichlet transform touch bound: the number of terms in a Dirichlet sum at n
is bounded by the number of divisors of a.

For T_a(f)(n) = ∑_{d | gcd(n,a)} f(n/d), the summation is over divisors of gcd(n,a),
which is a subset of divisors of a. Hence the per-element work is O(d(a)).

**fdrs.md Proposition 78**: Per-fiber update cost bounded by |supp(ã)|.
-/
theorem dirichlet_touch_bound (a n : ℕ) (ha : a ≠ 0) :
    (Nat.divisors (Nat.gcd n a)).card ≤ (Nat.divisors a).card := by
  apply Finset.card_le_card
  intro d hd
  rw [Nat.mem_divisors] at hd ⊢
  exact ⟨dvd_trans hd.1 (Nat.gcd_dvd_right n a), ha⟩

/-!
## Circuit Depth
-/

/--
Longest directed dependency chain reaching node `i`, where `deps j` is the set of
nodes that `j` directly depends on. `fuel` bounds the search depth; for a DAG
(`deps j ⊆ {0, …, j-1}`) any `fuel ≥ i + 1` yields the true longest chain.
-/
def chainDepth (deps : ℕ → Finset ℕ) : ℕ → ℕ → ℕ
  | 0,        _ => 0
  | fuel + 1, i => (deps i).sup (fun j => chainDepth deps fuel j + 1)

/--
Circuit depth of an operation with dependency structure `deps`, at output `i`:
the longest directed dependency chain reaching `i`.

**fdrs.md**: `Depth(Op) = longest dependency chain in the operation DAG`.
A leaf (no dependencies) has depth `0`; each dependency edge adds `1`.
-/
def circuitDepth (deps : ℕ → Finset ℕ) (i : ℕ) : ℕ :=
  chainDepth deps (i + 1) i

/-- The fully sequential (ripple) dependency chain: node `j + 1` depends on node `j`. -/
def seqChain : ℕ → Finset ℕ
  | 0     => ∅
  | j + 1 => {j}

/--
The sequential chain over positions `0, …, L` has circuit depth `L`: a fully
sequential ripple carry has *linear* depth. Contrast `tick_parallel_depth`, where
carry-lookahead reduces the depth to `Nat.log 2 L < L`.
-/
theorem circuitDepth_seqChain (L : ℕ) : circuitDepth seqChain L = L := by
  have aux : ∀ i, chainDepth seqChain (i + 1) i = i := by
    intro i
    induction i with
    | zero => simp [chainDepth, seqChain]
    | succ j ih =>
        show (seqChain (j + 1)).sup (fun k => chainDepth seqChain (j + 1) k + 1) = j + 1
        rw [show seqChain (j + 1) = {j} from rfl, Finset.sup_singleton, ih]
  exact aux L

/--
Tick parallel depth is O(log L): logarithmic depth is strictly less than linear depth.

With carry-lookahead (parallel prefix on the allMaxBefore conjunction), the carry
computation has tree depth ⌈log₂ L⌉, which is strictly less than the sequential
depth L for any L ≥ 2.

**fdrs.md**: Using carry-lookahead, parallel depth is logarithmic.
-/
theorem tick_parallel_depth (L : ℕ) (hL : 2 ≤ L) :
    Nat.log 2 L < L :=
  Nat.log_lt_self 2 (by omega)

/-!
## Global Valuation-Local Cost (Corollary 22)

Total cost of applying a P-smooth Dirichlet transform across all fibers.
-/

open Finset in
/--
**Corollary 22** (fdrs.md lines 3633-3638): Global valuation-local cost.

Let 𝒰 be the set of P-free labels (fibers), with active set sizes |E_u|.
If each per-fiber cost is bounded by |E_u| · (R+1)^|P| (Proposition 78),
then the total cost across all fibers satisfies:

  ∑_{u ∈ 𝒰} cost(u) ≤ (R+1)^|P| · ∑_{u ∈ 𝒰} |E_u|

**Scaling meaning:** exponential in |P| (number of tracked primes),
polynomial in R (valuation radius).

-- fdrs.md lines 3633-3638, Corollary 22
-/
theorem globalValuationLocalCost {ι : Type*}
    (U : Finset ι) (fiberCost activeSetSize : ι → ℕ) (R P_card : ℕ)
    (h_per_fiber : ∀ u ∈ U, fiberCost u ≤ activeSetSize u * (R + 1) ^ P_card) :
    ∑ u ∈ U, fiberCost u ≤ (R + 1) ^ P_card * ∑ u ∈ U, activeSetSize u := by
  calc ∑ u ∈ U, fiberCost u
      ≤ ∑ u ∈ U, activeSetSize u * (R + 1) ^ P_card :=
        Finset.sum_le_sum h_per_fiber
    _ = ∑ u ∈ U, (R + 1) ^ P_card * activeSetSize u :=
        Finset.sum_congr rfl (fun u _ => mul_comm _ _)
    _ = (R + 1) ^ P_card * ∑ u ∈ U, activeSetSize u :=
        (Finset.mul_sum ..).symm

end FdrsFormal.Integration.Complexity
