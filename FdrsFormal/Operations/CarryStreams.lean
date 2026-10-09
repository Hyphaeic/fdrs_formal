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

# Carry streams (Phase 1 addendum, §3.9)

The ledger of a route records how much crossed each radix line. On a digit schedule
these line totals — the **carry streams** — are not arbitrary: a cut law (a Gauss law
for carries) fixes each of them from the start and end states alone, so every route,
every interleaving of a history, carries exactly the same amount on every line. The
streams are themselves FDRS data: for a counter they are the tails `⌊T/B_{i+1}⌋` of the
count, and in general they obey the carry recurrence `F_{i+1} = ⌊(F_i + d_{i+1})/b_{i+1}⌋`
— the stream into a line, plus the line's own digit mass, carried at its radix.

- **Theorem 140** (`cut_law`): for any network, route and set of cells `U`, the value
  in `U` changes by exactly the weighted flow across the boundary of `U`.
- **Definition 227** (`pathNet`, `lineFlux`, `blockVal`, `sweepTo`): the schedule as a
  path network, the stream on line `i`, the value of the block `0..i`, the sweep.
- **Theorem 141** (`flux_eq`): on a schedule, `B_{i+1} · F_i = V_{≤i}(start) − V_{≤i}(end)`.
- **Theorem 142** (`stream_eq`): if a route ends canonical on `0..i`, then
  `F_i = ⌊V_{≤i}(start)/B_{i+1}⌋` — the stream is route-independent.
- **Corollary 47** (`counter_stream`, `counter_stream_nest`): counting to `T`, the stream
  on line `i` is `⌊T/B_{i+1}⌋`, and `F_{i+1} = ⌊F_i / b_{i+1}⌋`: the carry stream of a
  carry stream is the next carry stream.
- **Corollary 48** (`stream_recurrence`): for any history, `F_{i+1} = ⌊(F_i + d_{i+1})/b_{i+1}⌋`.
- **Proposition 172** (`carry_mass`): every carry along a line of ratio `ρ` removes
  `ρ − 1` units of digit mass: `Σ_u d_end(u) + Σ (ρ − 1)·amount = Σ_u d_start(u)`.

**Honest scope.** Elementary. For a constant prime radix the mass identity with the
counter streams is Legendre's formula; the corpus contributes the network form on
arbitrary schedules, route independence, and the nesting of streams.
-/

import FdrsFormal.Operations.CarryNetwork

namespace FdrsFormal.Operations.CarryNetwork

open FdrsFormal.Core.Primitives

set_option linter.unusedSectionVars false

variable {V : Type*} [DecidableEq V] [Fintype V]

/-! ## Theorem 140: the cut law -/

theorem carry_eq_contrib (e : Line V) (d : V → ℕ) (hne : e.1 ≠ e.2.1) (u : V) :
    (carry e d u : ℤ) = d u + contrib u (e.1, e.2.1, e.2.2, d e.1 / e.2.2) := by
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

/-- The weighted flow of one transfer into a set of cells `U`. -/
def cutContrib (w : V → ℕ) (U : Finset V) (t : V × V × ℕ × ℕ) : ℤ :=
  (if t.2.1 ∈ U then ((w t.2.1 * t.2.2.2 : ℕ) : ℤ) else 0) -
    (if t.1 ∈ U then ((w t.1 * (t.2.2.1 * t.2.2.2) : ℕ) : ℤ) else 0)

theorem sum_contrib (w : V → ℕ) (U : Finset V) (t : V × V × ℕ × ℕ) :
    ∑ u ∈ U, (w u : ℤ) * contrib u t = cutContrib w U t := by
  simp only [contrib, cutContrib, Nat.cast_ite, Nat.cast_zero, mul_sub,
    Finset.sum_sub_distrib, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq, Finset.sum_ite_eq]
  push_cast
  ring

theorem sum_contrib_list (w : V → ℕ) (U : Finset V) :
    ∀ L : List (V × V × ℕ × ℕ),
      ∑ u ∈ U, (w u : ℤ) * (L.map (contrib u)).sum = (L.map (cutContrib w U)).sum
  | [] => by simp
  | t :: L => by
    simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib, sum_contrib,
      sum_contrib_list w U L]

/-- **Theorem 140 (the cut law).** For any route and any set of cells `U`, the value held
in `U` changes by exactly the weighted flow of the transfers across its boundary.

**fdrs.md**: Theorem 140 (the cut law for carries). -/
theorem cut_law (w : V → ℕ) (es : List (Line V)) (hes : ∀ e ∈ es, e.1 ≠ e.2.1)
    (d : V → ℕ) (U : Finset V) :
    ∑ u ∈ U, (w u : ℤ) * run es d u =
      ∑ u ∈ U, (w u : ℤ) * d u + ((transfers es d).map (cutContrib w U)).sum := by
  simp_rw [run_balance es hes d, mul_add]
  rw [Finset.sum_add_distrib, sum_contrib_list]

/-! ## Proposition 172: carry mass -/

theorem sum_contrib_univ (t : V × V × ℕ × ℕ) :
    ∑ u, contrib u t = (t.2.2.2 : ℤ) - ((t.2.2.1 * t.2.2.2 : ℕ) : ℤ) := by
  have := sum_contrib (fun _ => 1) Finset.univ t
  simp only [Nat.cast_one, one_mul] at this
  rw [this, cutContrib]
  simp

/-- **Proposition 172 (carry mass).** Every carry along a line of ratio `ρ` removes
`ρ − 1` units of digit mass per unit sent: `Σ_u d_end(u) + Σ (ρ − 1)·amount = Σ_u d_start(u)`.

**fdrs.md**: Proposition 172 (carry mass). -/
theorem carry_mass (es : List (Line V)) (hes : ∀ e ∈ es, e.1 ≠ e.2.1) (d : V → ℕ) :
    (∑ u, (run es d u : ℤ)) +
        ((transfers es d).map fun t => ((t.2.2.1 * t.2.2.2 : ℕ) : ℤ) - t.2.2.2).sum =
      ∑ u, (d u : ℤ) := by
  have h := cut_law (fun _ => 1) es hes d Finset.univ
  simp only [Nat.cast_one, one_mul] at h
  rw [h, add_assoc, ← List.sum_map_add]
  have h0 : ((transfers es d).map fun t => cutContrib (fun _ => 1) Finset.univ t +
      (((t.2.2.1 * t.2.2.2 : ℕ) : ℤ) - t.2.2.2)).sum = 0 := by
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx
    simp [cutContrib]
  rw [h0, add_zero]

/-! ## Definition 227: the schedule as a path network -/

section Path

variable (b : RadixSeq) (K : ℕ)

/-- Lines `i → i + 1` of ratio `b_i`, for `i < K`. -/
def pathLines : List (Line (Fin (K + 1))) :=
  (List.finRange K).map fun i : Fin K => (i.castSucc, i.succ, b i)

/-- The schedule as a carry network on cells `0, …, K` with weights `B_i`.

**fdrs.md**: Definition 227 (carry streams). -/
def pathNet : CarryNet (Fin (K + 1)) where
  w u := placeValue b u
  lines := pathLines b K
  consistent := by
    intro e he
    simp only [pathLines, List.mem_map, List.mem_finRange, true_and] at he
    obtain ⟨i, rfl⟩ := he
    refine ⟨fun h => ?_, b.pos _, ?_⟩
    · have := congrArg Fin.val h; simp at this
    · simp [placeValue.succ, mul_comm]

/-- The carry stream on line `i`: the total sent from cell `i` over the ledger.

**fdrs.md**: Definition 227 (carry streams). -/
def lineFlux (i : ℕ) (L : List (Fin (K + 1) × Fin (K + 1) × ℕ × ℕ)) : ℕ :=
  (L.map fun t => if (t.1 : ℕ) = i then t.2.2.2 else 0).sum

/-- The block `0, …, i` as a set of cells. -/
def blockSet (i : ℕ) : Finset (Fin (K + 1)) := Finset.univ.filter fun u => (u : ℕ) ≤ i

/-- The value held by the block `0, …, i`. -/
def blockVal (i : ℕ) (d : Fin (K + 1) → ℕ) : ℕ :=
  ∑ u ∈ blockSet K i, placeValue b u * d u

end Path

/-! ## Theorem 141: flux across a cut of a schedule -/

theorem transfers_shape : ∀ (es : List (Line V)) (d : V → ℕ),
    ∀ t ∈ transfers es d, ∃ e ∈ es, t.1 = e.1 ∧ t.2.1 = e.2.1 ∧ t.2.2.1 = e.2.2
  | [], _, t, ht => by simp [transfers] at ht
  | e :: es, d, t, ht => by
    simp only [transfers, List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact ⟨e, List.mem_cons_self, rfl, rfl, rfl⟩
    · obtain ⟨e', he', h⟩ := transfers_shape es (carry e d) t ht
      exact ⟨e', List.mem_cons_of_mem _ he', h⟩

theorem pathLines_ne (b : RadixSeq) (K : ℕ) : ∀ e ∈ pathLines b K, e.1 ≠ e.2.1 :=
  fun e he => ((pathNet b K).consistent e he).1

/-- Each transfer along a schedule line contributes to the block `0..i` exactly
`−B_{i+1}` per unit when it crosses line `i`, and nothing otherwise. -/
theorem cutContrib_path (b : RadixSeq) (K i : ℕ) (j : Fin K) (a : ℕ) :
    cutContrib (fun u : Fin (K + 1) => placeValue b u) (blockSet K i)
        (j.castSucc, j.succ, b j, a) =
      -((placeValue b (i + 1) : ℤ) * (if (j : ℕ) = i then (a : ℤ) else 0)) := by
  simp only [cutContrib, blockSet, Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.val_castSucc, Fin.val_succ]
  rcases lt_trichotomy (j : ℕ) i with h | h | h
  · rw [if_pos (by omega), if_pos h.le, if_neg (by omega), placeValue.succ]
    push_cast; ring
  · rw [if_neg (by omega), if_pos h.le, if_pos h, ← h, placeValue.succ]
    push_cast; ring
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp

/-- **Theorem 141 (flux across a cut).** On a schedule, every route of its lines
satisfies `B_{i+1} · F_i = V_{≤i}(start) − V_{≤i}(end)`.

**fdrs.md**: Theorem 141 (flux across a cut of a schedule). -/
theorem flux_eq (b : RadixSeq) (K i : ℕ) (es : List (Line (Fin (K + 1))))
    (hes : ∀ e ∈ es, e ∈ pathLines b K) (d : Fin (K + 1) → ℕ) :
    (placeValue b (i + 1) : ℤ) * lineFlux K i (transfers es d) =
      blockVal b K i d - blockVal b K i (run es d) := by
  have hne : ∀ e ∈ es, e.1 ≠ e.2.1 := fun e he => pathLines_ne b K e (hes e he)
  have hcut := cut_law (fun u : Fin (K + 1) => placeValue b u) es hne d (blockSet K i)
  have hsum : ((transfers es d).map
      (cutContrib (fun u : Fin (K + 1) => placeValue b u) (blockSet K i))).sum =
      -((placeValue b (i + 1) : ℤ) * lineFlux K i (transfers es d)) := by
    have hshape := transfers_shape es d
    generalize transfers es d = L at hshape ⊢
    induction L with
    | nil => simp [lineFlux]
    | cons t L ih =>
      obtain ⟨e, he, h1, h2, h3⟩ := hshape t List.mem_cons_self
      have := hes e he
      simp only [pathLines, List.mem_map, List.mem_finRange, true_and] at this
      obtain ⟨j, rfl⟩ := this
      obtain ⟨t1, t2, t3, a⟩ := t
      simp only at h1 h2 h3
      subst h1 h2 h3
      rw [List.map_cons, List.sum_cons, cutContrib_path,
        ih (fun t ht => hshape t (List.mem_cons_of_mem _ ht))]
      simp only [lineFlux, List.map_cons, List.sum_cons, Fin.val_castSucc]
      push_cast
      ring
  simp only [blockVal]
  push_cast
  rw [hcut, hsum]
  ring

/-! ## Theorem 142: carry streams are route-independent -/

theorem blockVal_lt (b : RadixSeq) (K : ℕ) : ∀ (i : ℕ) (d : Fin (K + 1) → ℕ),
    (∀ u : Fin (K + 1), (u : ℕ) ≤ i → d u < b u) → blockVal b K i d < placeValue b (i + 1)
  | 0, d, h => by
    simp only [blockVal, blockSet]
    rw [Finset.sum_eq_single (0 : Fin (K + 1))]
    · simpa using h 0 (by simp)
    · intro u hu hu0
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      exact absurd (Fin.ext (by rw [Fin.val_zero]; omega)) hu0
    · simp
  | i + 1, d, h => by
    by_cases hiK : i + 1 < K + 1
    · have hsplit : blockVal b K (i + 1) d =
          blockVal b K i d + placeValue b (i + 1) * d ⟨i + 1, hiK⟩ := by
        simp only [blockVal, blockSet]
        rw [show Finset.univ.filter (fun u : Fin (K + 1) => (u : ℕ) ≤ i + 1) =
            insert ⟨i + 1, hiK⟩ (Finset.univ.filter fun u : Fin (K + 1) => (u : ℕ) ≤ i) by
          ext u; simp [Fin.ext_iff]; omega]
        rw [Finset.sum_insert (by simp), add_comm]
      have ih := blockVal_lt b K i d fun u hu => h u (by omega)
      have hd := h ⟨i + 1, hiK⟩ le_rfl
      rw [hsplit, placeValue.succ (i + 1)]
      calc blockVal b K i d + placeValue b (i + 1) * d ⟨i + 1, hiK⟩
          < placeValue b (i + 1) + placeValue b (i + 1) * d ⟨i + 1, hiK⟩ := by omega
        _ = placeValue b (i + 1) * (d ⟨i + 1, hiK⟩ + 1) := by ring
        _ ≤ placeValue b (i + 1) * b (i + 1) := Nat.mul_le_mul_left _ hd
    · have hsame : blockVal b K (i + 1) d = blockVal b K i d := by
        simp only [blockVal, blockSet]
        congr 1; ext u; simp; have := u.isLt; omega
      rw [hsame]
      exact (blockVal_lt b K i d fun u hu => h u (by omega)).trans
        (placeValue.strictMono (Nat.lt_succ_self _))

/-- **Theorem 142 (carry streams are route-independent).** If a route on the schedule
ends with canonical digits on `0..i`, its carry stream on line `i` is
`F_i = ⌊V_{≤i}(start) / B_{i+1}⌋` and the block ends at `V_{≤i}(start) mod B_{i+1}`.

**fdrs.md**: Theorem 142 (carry streams are route-independent). -/
theorem stream_eq (b : RadixSeq) (K i : ℕ) (es : List (Line (Fin (K + 1))))
    (hes : ∀ e ∈ es, e ∈ pathLines b K) (d : Fin (K + 1) → ℕ)
    (hcan : ∀ u : Fin (K + 1), (u : ℕ) ≤ i → run es d u < b u) :
    lineFlux K i (transfers es d) = blockVal b K i d / placeValue b (i + 1) ∧
      blockVal b K i (run es d) = blockVal b K i d % placeValue b (i + 1) := by
  have hflux := flux_eq b K i es hes d
  have hlt := blockVal_lt b K i (run es d) hcan
  have hpos := placeValue.pos (b := b) (i + 1)
  have hnat : blockVal b K i (run es d) + placeValue b (i + 1) * lineFlux K i (transfers es d) =
      blockVal b K i d := by
    have : ((blockVal b K i (run es d) + placeValue b (i + 1) * lineFlux K i (transfers es d) :
        ℕ) : ℤ) = blockVal b K i d := by push_cast; linarith
    exact_mod_cast this
  obtain ⟨h1, h2⟩ := (Nat.div_mod_unique hpos).mpr ⟨hnat, hlt⟩
  exact ⟨h1.symm, h2.symm⟩

/-! ## The sweep: a canonical route always exists -/

theorem run_append : ∀ (l₁ l₂ : List (Line V)) (d : V → ℕ),
    run (l₁ ++ l₂) d = run l₂ (run l₁ d)
  | [], _, _ => rfl
  | e :: l₁, l₂, d => run_append l₁ l₂ (carry e d)

/-- The sweep over lines `0, …, n − 1` of the schedule.

**fdrs.md**: Definition 227 (carry streams). -/
def sweepTo (b : RadixSeq) (K : ℕ) : ℕ → List (Line (Fin (K + 1)))
  | 0 => []
  | n + 1 => sweepTo b K n ++
      (if h : n < K then [(Fin.castSucc ⟨n, h⟩, Fin.succ ⟨n, h⟩, b n)] else [])

theorem sweepTo_mem (b : RadixSeq) (K : ℕ) : ∀ n, ∀ e ∈ sweepTo b K n, e ∈ pathLines b K
  | 0, e, he => by simp [sweepTo] at he
  | n + 1, e, he => by
    simp only [sweepTo, List.mem_append] at he
    rcases he with he | he
    · exact sweepTo_mem b K n e he
    · split_ifs at he with h
      · simp only [List.mem_singleton] at he
        subst he
        exact List.mem_map.mpr ⟨⟨n, h⟩, List.mem_finRange _, rfl⟩
      · simp at he

theorem sweep_canonical (b : RadixSeq) (K : ℕ) : ∀ n, n ≤ K → ∀ (d : Fin (K + 1) → ℕ)
    (u : Fin (K + 1)), (u : ℕ) < n → run (sweepTo b K n) d u < b u
  | 0, _, _, u, hu => absurd hu (Nat.not_lt_zero _)
  | n + 1, hn, d, u, hu => by
    have hnK : n < K := by omega
    simp only [sweepTo, dif_pos hnK]
    rw [run_append]
    simp only [run]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hlt | heq
    · rw [carry_other _ _ (fun h => by have := congrArg Fin.val h; simp at this; omega)
        (fun h => by have := congrArg Fin.val h; simp at this; omega)]
      exact sweep_canonical b K n (by omega) d u hlt
    · have hu' : u = Fin.castSucc ⟨n, hnK⟩ := Fin.ext (by simp [heq])
      subst hu'
      rw [carry_src _ _ (fun h => by have := congrArg Fin.val h; simp at this)]
      exact Nat.mod_lt _ (b.pos _)

/-! ## Corollary 47: counter streams are tails, and they nest -/

theorem blockVal_single_zero (b : RadixSeq) (K i T : ℕ) :
    blockVal b K i (single (0 : Fin (K + 1)) T) = T := by
  simp only [blockVal, blockSet, single]
  rw [Finset.sum_eq_single (0 : Fin (K + 1))]
  · simp
  · intro u _ hu
    simp [Function.update_of_ne hu]
  · simp

/-- **Corollary 47 (counter streams are tails).** Counting to `T` on the schedule — the
load `T` at cell `0`, carried by any route that ends canonical on `0..i` — the carry
stream on line `i` is `⌊T / B_{i+1}⌋`.

**fdrs.md**: Corollary 47 (counter streams are tails, and they nest). -/
theorem counter_stream (b : RadixSeq) (K i T : ℕ) (es : List (Line (Fin (K + 1))))
    (hes : ∀ e ∈ es, e ∈ pathLines b K)
    (hcan : ∀ u : Fin (K + 1), (u : ℕ) ≤ i → run es (single 0 T) u < b u) :
    lineFlux K i (transfers es (single 0 T)) = T / placeValue b (i + 1) := by
  rw [(stream_eq b K i es hes _ hcan).1, blockVal_single_zero]

/-- The sweep realises Corollary 47 for every line `i < K`. -/
theorem counter_stream_sweep (b : RadixSeq) (K i T : ℕ) (hi : i < K) :
    lineFlux K i (transfers (sweepTo b K K) (single 0 T)) = T / placeValue b (i + 1) :=
  counter_stream b K i T _ (sweepTo_mem b K K)
    fun u hu => sweep_canonical b K K le_rfl _ u (by omega)

/-- **Corollary 47 (streams nest).** The carry stream of a carry stream is the next carry
stream: `F_{i+1} = ⌊F_i / b_{i+1}⌋` — line `i`'s stream, read as a counter on the shifted
schedule, carries exactly line `i + 1`'s stream.

**fdrs.md**: Corollary 47 (counter streams are tails, and they nest). -/
theorem counter_stream_nest (b : RadixSeq) (K i T : ℕ) (hi : i + 1 < K) :
    lineFlux K (i + 1) (transfers (sweepTo b K K) (single 0 T)) =
      lineFlux K i (transfers (sweepTo b K K) (single 0 T)) / b (i + 1) := by
  rw [counter_stream_sweep b K (i + 1) T hi, counter_stream_sweep b K i T (by omega),
    Nat.div_div_eq_div_mul, ← placeValue.succ]

/-! ## Corollary 48: the carry recurrence for any history -/

theorem blockVal_succ (b : RadixSeq) (K i : ℕ) (hiK : i + 1 < K + 1) (d : Fin (K + 1) → ℕ) :
    blockVal b K (i + 1) d = blockVal b K i d + placeValue b (i + 1) * d ⟨i + 1, hiK⟩ := by
  simp only [blockVal, blockSet]
  rw [show Finset.univ.filter (fun u : Fin (K + 1) => (u : ℕ) ≤ i + 1) =
      insert ⟨i + 1, hiK⟩ (Finset.univ.filter fun u : Fin (K + 1) => (u : ℕ) ≤ i) by
    ext u; simp [Fin.ext_iff]; omega]
  rw [Finset.sum_insert (by simp), add_comm]

/-- **Corollary 48 (the carry recurrence).** For any history — any start state, any route
ending canonical on `0..i+1` — the streams obey
`F_{i+1} = ⌊(F_i + d_{i+1}) / b_{i+1}⌋`: the stream into a line plus the line's own digit
mass, carried at the line's radix. The streams of every history are the carries of one
sweep of its stacked digits.

**fdrs.md**: Corollary 48 (the carry recurrence). -/
theorem stream_recurrence (b : RadixSeq) (K i : ℕ) (hiK : i + 1 < K + 1)
    (es : List (Line (Fin (K + 1)))) (hes : ∀ e ∈ es, e ∈ pathLines b K)
    (d : Fin (K + 1) → ℕ) (hcan : ∀ u : Fin (K + 1), (u : ℕ) ≤ i + 1 → run es d u < b u) :
    lineFlux K (i + 1) (transfers es d) =
      (lineFlux K i (transfers es d) + d ⟨i + 1, hiK⟩) / b (i + 1) := by
  rw [(stream_eq b K (i + 1) es hes d hcan).1,
    (stream_eq b K i es hes d fun u hu => hcan u (by omega)).1, blockVal_succ b K i hiK,
    placeValue.succ (i + 1), ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_left _ _ (placeValue.pos _)]

/-! ## Proposition 172 on a schedule: a Legendre-type identity -/

theorem mass_path (b : RadixSeq) (K : ℕ) (L : List (Fin (K + 1) × Fin (K + 1) × ℕ × ℕ))
    (hL : ∀ t ∈ L, ∃ j : Fin K, t.1 = j.castSucc ∧ t.2.2.1 = b j) :
    (L.map fun t => ((t.2.2.1 * t.2.2.2 : ℕ) : ℤ) - t.2.2.2).sum =
      ∑ j ∈ Finset.range K, ((b j : ℤ) - 1) * lineFlux K j L := by
  induction L with
  | nil => simp [lineFlux]
  | cons t L ih =>
    obtain ⟨j, h1, h2⟩ := hL t List.mem_cons_self
    rw [List.map_cons, List.sum_cons, ih fun t ht => hL t (List.mem_cons_of_mem _ ht)]
    simp only [lineFlux, List.map_cons, List.sum_cons]
    push_cast
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    rw [h1, h2, Fin.val_castSucc]
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq (Finset.range K) (j : ℕ) (fun x => ((b x : ℤ) - 1) * t.2.2.2)]
    simp [j.isLt]
    ring

/-- **Proposition 172 (carry mass on a schedule).** Counting to `T` by the sweep, the
digit mass left plus `Σ_{i<K} (b_i − 1)⌊T / B_{i+1}⌋` is `T`. For a constant prime radix
`p` this is Legendre's `(p − 1) v_p(T!) = T − s_p(T)`.

**fdrs.md**: Proposition 172 (carry mass). -/
theorem counter_mass (b : RadixSeq) (K T : ℕ) :
    (∑ u, (run (sweepTo b K K) (single 0 T) u : ℤ)) +
        ∑ j ∈ Finset.range K, ((b j : ℤ) - 1) * (T / placeValue b (j + 1) : ℕ) = T := by
  have hne : ∀ e ∈ sweepTo b K K, e.1 ≠ e.2.1 :=
    fun e he => pathLines_ne b K e (sweepTo_mem b K K e he)
  have h := carry_mass (sweepTo b K K) hne (single 0 T)
  have hshape : ∀ t ∈ transfers (sweepTo b K K) (single 0 T),
      ∃ j : Fin K, t.1 = j.castSucc ∧ t.2.2.1 = b j := by
    intro t ht
    obtain ⟨e, he, h1, _, h3⟩ := transfers_shape _ _ t ht
    have := sweepTo_mem b K K e he
    simp only [pathLines, List.mem_map, List.mem_finRange, true_and] at this
    obtain ⟨j, rfl⟩ := this
    exact ⟨j, h1, h3⟩
  rw [mass_path b K _ hshape] at h
  have hsum : ∑ j ∈ Finset.range K, ((b j : ℤ) - 1) *
      (lineFlux K j (transfers (sweepTo b K K) (single 0 T)) : ℤ) =
      ∑ j ∈ Finset.range K, ((b j : ℤ) - 1) * (T / placeValue b (j + 1) : ℕ) :=
    Finset.sum_congr rfl fun j hj => by
      rw [counter_stream_sweep b K j T (Finset.mem_range.mp hj)]
  rw [hsum] at h
  rw [h, Finset.sum_eq_single (0 : Fin (K + 1))
    (fun u _ hu => by simp [single, Function.update_of_ne hu]) (by simp)]
  simp [single]

end FdrsFormal.Operations.CarryNetwork
