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

# Realizability Conditions

This file defines the three conditions for ultrametric realizability.

## Mathematical Content (fdrs.md lines 5381-5402)

**Theorem 43** states that an ultrametric δ is realizable as δ_ω for some
SU radix function ω if and only if it satisfies three conditions:

1. **Cylinder correspondence**: Every ultrametric ball is a finite union of cylinders
2. **Monotone refinement**: U(s) ⊆ U(t) ⟹ rad(U(s)) ≤ rad(U(t))
3. **Finite branching**: Each cylinder has finitely many immediate sub-cylinders

## References

- fdrs.md, Phase 6, Section 6.6 (lines 5381-5402)
- Paper (external draft): Theorem B (§6.3)
-/

import FdrsFormal.Modes.VariableRadix.InducedUltrametric.InducedUltrametric

namespace FdrsFormal.Modes.VariableRadix

/-!
## Aliases for Ultrametric Concepts
-/

/-- Alias: the cylinder from CylinderBalls -/
abbrev cylinderInfinite (ω : RadixLaw) := cylinder ω

/-- The radius of a cylinder (inverse prefix weight) -/
noncomputable def variableRadixRadius (ω : RadixLaw) (s : PrefixWord) : ℝ :=
  (prefixWeight ω s : ℝ)⁻¹

/-!
## Ultrametric Ball and Cylinder Types
-/

/-- An ultrametric ball in the infinite space -/
structure UltrametricBall (X : Type*) [Dist X] where
  center : X
  radius : ℝ
  radius_pos : 0 < radius

/-- The set of points in an ultrametric ball -/
def UltrametricBall.toSet {X : Type*} [Dist X] (B : UltrametricBall X) : Set X :=
  {y | dist B.center y < B.radius}

/-!
## Condition 1: Cylinder Correspondence
-/

/--
**Cylinder Correspondence**: Every ultrametric ball is a finite union of cylinders.

This connects the topological structure (balls) to the combinatorial structure (cylinders).
-/
def hasCylinderCorrespondence (ω : RadixLaw) : Prop :=
  ∀ (x : InfiniteVariableSpace ω) (r : ℝ), r > 0 →
    ∃ (S : Finset PrefixWord),
      {y : InfiniteVariableSpace ω | ultrametricDist x y < r} =
        ⋃ s ∈ S, cylinderInfinite ω s

/--
Extend a valid prefix to an infinite sequence by appending zeros.

The digit function is: s[i] for i < s.length, 0 for i ≥ s.length.
-/
noncomputable def extendPrefixToInfinite (ω : RadixLaw) (s : PrefixWord)
    (hv : isValidPrefix' ω s) : InfiniteVariableSpace ω where
  digit i := if hi : i < s.length then s.get ⟨i, hi⟩ else 0
  valid i := by
    split_ifs with hi
    · -- i < s.length: digit is s[i], prefix is s.take i
      have h1 : (List.ofFn fun j : Fin i => if hj : j.val < s.length then s.get ⟨j, hj⟩ else 0) = s.take i := by
        apply List.ext_getElem
        · simp only [List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
        · intro j hj hj'
          simp only [List.length_ofFn] at hj
          simp only [List.getElem_ofFn]
          have hj_lt : j < s.length := Nat.lt_trans hj hi
          simp only [hj_lt, ↓reduceDIte, List.getElem_take, List.get_eq_getElem]
      rw [h1]
      exact hv i hi
    · -- i ≥ s.length: digit is 0, need 0 < ω.radix(prefix)
      exact ω.radix_pos _

/-- The extended sequence has the prefix s -/
theorem extendPrefixToInfinite_getPrefix (ω : RadixLaw) (s : PrefixWord)
    (hv : isValidPrefix' ω s) :
    (extendPrefixToInfinite ω s hv).getPrefix s.length = s := by
  simp only [InfiniteVariableSpace.getPrefix, extendPrefixToInfinite]
  apply List.ext_getElem
  · simp only [List.length_ofFn]
  · intro i hi _
    simp only [List.length_ofFn] at hi
    simp only [List.getElem_ofFn, hi, ↓reduceDIte, List.get_eq_getElem]

/-- The extended sequence is in the cylinder -/
theorem extendPrefixToInfinite_mem_cylinder (ω : RadixLaw) (s : PrefixWord)
    (hv : isValidPrefix' ω s) :
    extendPrefixToInfinite ω s hv ∈ cylinderInfinite ω s := by
  simp only [cylinderInfinite, cylinder, Set.mem_setOf_eq]
  exact extendPrefixToInfinite_getPrefix ω s hv

/--
Helper: if y ∈ cylinder(s) and x has prefix s and x ≠ y, then lcpLength x y ≥ s.length.

Note: The hypothesis x ≠ y is required because lcpLength returns 0 when x = y,
which wouldn't satisfy s.length ≤ 0 for non-empty s.
-/
theorem lcpLength_ge_of_same_prefix {ω : RadixLaw} (x y : InfiniteVariableSpace ω) (s : PrefixWord)
    (hx : x.getPrefix s.length = s) (hy : y.getPrefix s.length = s) (hne : x ≠ y) :
    s.length ≤ lcpLength x y := by
  -- Since x ≠ y, there exists a differing digit
  have hdiff : ∃ i, x.digit i ≠ y.digit i := by
    by_contra hall
    push_neg at hall
    apply hne
    ext i
    exact hall i
  simp only [lcpLength, dif_pos hdiff]
  -- Need: s.length ≤ Nat.find hdiff
  by_contra hlt
  push_neg at hlt
  -- At position Nat.find hdiff < s.length, x and y differ
  -- But x.digit i = s[i] = y.digit i for i < s.length
  simp only [InfiniteVariableSpace.getPrefix] at hx hy
  have hx_eq : x.digit (Nat.find hdiff) = s.get ⟨Nat.find hdiff, hlt⟩ := by
    have h := congrArg (·[Nat.find hdiff]?) hx
    simp only [List.getElem?_ofFn, hlt, ↓reduceDIte] at h
    simp only [List.getElem?_eq_getElem hlt] at h
    exact Option.some.inj h
  have hy_eq : y.digit (Nat.find hdiff) = s.get ⟨Nat.find hdiff, hlt⟩ := by
    have h := congrArg (·[Nat.find hdiff]?) hy
    simp only [List.getElem?_ofFn, hlt, ↓reduceDIte] at h
    simp only [List.getElem?_eq_getElem hlt] at h
    exact Option.some.inj h
  have hdiff_at := Nat.find_spec hdiff
  rw [hx_eq, hy_eq] at hdiff_at
  exact hdiff_at rfl

/--
Helper: if lcpLength x y < s.length where x has prefix s and x ≠ y, then y ∉ cylinder(s).

Note: The hypothesis x ≠ y is required. When x = y, lcpLength x y = 0, so
hlcp : 0 < s.length is consistent, but then y = x has the same prefix s as x,
making the conclusion false.
-/
theorem not_mem_cylinder_of_lcpLength_lt {ω : RadixLaw} (x y : InfiniteVariableSpace ω) (s : PrefixWord)
    (hx : x.getPrefix s.length = s) (hlcp : lcpLength x y < s.length) (hne : x ≠ y) :
    y.getPrefix s.length ≠ s := by
  intro hy
  have h := lcpLength_ge_of_same_prefix x y s hx hy hne
  omega

/-- Cylinders are balls (the forward direction) -/
theorem cylinder_is_ball (ω : RadixLaw) (s : PrefixWord) (hv : isValidPrefix' ω s) :
    ∃ (x : InfiniteVariableSpace ω) (r : ℝ), r > 0 ∧
      cylinderInfinite ω s = {y | ultrametricDist x y < r} := by
  -- Use the extended sequence as center
  let x := extendPrefixToInfinite ω s hv
  use x
  -- Key insight: cylinder(s) = {y | ultrametricDist x y ≤ (prefixWeight s)⁻¹}
  -- For s = [], use r = 2 (since max distance is 1)
  -- For s ≠ [], we use a gap in the discrete distance values
  cases hs : s with
  | nil =>
    -- s = []: cylinder is the whole space, use r = 2
    use 2
    constructor
    · norm_num
    · ext y
      simp only [cylinderInfinite, cylinder, Set.mem_setOf_eq]
      constructor
      · intro _
        -- ultrametricDist x y ≤ 1 < 2 always
        simp only [ultrametricDist]
        by_cases hdiff : ∃ i, x.digit i ≠ y.digit i
        · simp only [hdiff, ↓reduceIte]
          have hpw_pos : (0 : ℝ) < prefixWeight ω (lcp x y) :=
            Nat.cast_pos.mpr (prefixWeight_pos ω (lcp x y))
          have hpw_ge : prefixWeight ω (lcp x y) ≥ 1 := prefixWeight_pos ω (lcp x y)
          have hinv_le : (prefixWeight ω (lcp x y) : ℝ)⁻¹ ≤ 1 := by
            have h1 : (1 : ℝ) ≤ prefixWeight ω (lcp x y) := Nat.one_le_cast.mpr hpw_ge
            -- 1/a ≤ 1/b when b ≤ a (and both positive)
            -- Here: 1/pw ≤ 1/1 = 1 when 1 ≤ pw
            rw [← one_div, div_le_one hpw_pos]
            exact h1
          linarith
        · simp only [hdiff, ↓reduceIte]; norm_num
      · intro _
        -- getPrefix 0 = [] always
        simp only [InfiniteVariableSpace.getPrefix, List.length_nil, List.ofFn_zero]
  | cons d ds =>
    -- s = d :: ds, but hv is for s, not d :: ds
    have hv' : isValidPrefix' ω (d :: ds) := by rw [← hs]; exact hv
    -- Use the extended prefix as center
    let x' := extendPrefixToInfinite ω (d :: ds) hv'
    -- The construction uses x = extendPrefixToInfinite ω s hv, but s = d :: ds
    have hx_eq : x = x' := by
      apply InfiniteVariableSpace.ext
      intro i
      simp only [x, x', extendPrefixToInfinite]
      have hlen : s.length = (d :: ds).length := by rw [hs]
      by_cases hi : i < s.length
      · have hi' : i < (d :: ds).length := by rw [← hlen]; exact hi
        simp only [↓reduceDIte, hi', hs, List.get_eq_getElem]
      · have hi' : ¬i < (d :: ds).length := by rw [← hlen]; exact hi
        simp only [↓reduceDIte, hi, hi']
    -- Parent prefix: (d :: ds).dropLast
    let parent := (d :: ds).dropLast
    let pw_s := (prefixWeight ω (d :: ds) : ℝ)
    let pw_parent := (prefixWeight ω parent : ℝ)
    use (pw_s⁻¹ + pw_parent⁻¹) / 2
    have hpos_s : 0 < pw_s := Nat.cast_pos.mpr (prefixWeight_pos ω (d :: ds))
    have hpos_parent : 0 < pw_parent := Nat.cast_pos.mpr (prefixWeight_pos ω parent)
    constructor
    · -- r > 0
      linarith [inv_pos.mpr hpos_s, inv_pos.mpr hpos_parent]
    · -- Cylinder = ball
      -- Key: pw_s⁻¹ < r < pw_parent⁻¹ since pw_s > pw_parent (radix factor ≥ 2)
      have hparent_prefix : parent <+: (d :: ds) := List.dropLast_prefix (d :: ds)
      have hpw_lt : pw_parent < pw_s := by
        simp only [pw_s, pw_parent]
        -- parent is a strict prefix, so prefixWeight(parent) < prefixWeight(d :: ds)
        have hstrict : parent ++ [(d :: ds).getLast (List.cons_ne_nil d ds)] = d :: ds :=
          List.dropLast_append_getLast (List.cons_ne_nil d ds)
        have hlast_valid : (d :: ds).getLast (List.cons_ne_nil d ds) < ω.radix parent := by
          have hds_lt : ds.length < (d :: ds).length := by simp
          have h := hv' ds.length hds_lt
          -- h : (d :: ds).get ⟨ds.length, _⟩ < ω.radix ((d :: ds).take ds.length)
          -- Goal: (d :: ds).getLast _ < ω.radix parent
          -- First, show that (d :: ds).getLast = (d :: ds)[ds.length]
          have hlast_eq : (d :: ds).getLast (List.cons_ne_nil d ds) = (d :: ds)[ds.length] := by
            rw [List.getLast_eq_getElem]
            congr 1
          -- Then show parent = (d :: ds).take ds.length
          have hparent_eq : parent = (d :: ds).take ds.length := by
            simp only [parent, List.dropLast_eq_take, List.length_cons, Nat.add_sub_cancel]
          rw [hlast_eq, hparent_eq]
          simp only [List.get_eq_getElem] at h
          exact h
        have hpw := prefixWeight_strictMono ω parent _ hlast_valid
        rw [hstrict] at hpw
        exact_mod_cast hpw
      have hr_bounds : pw_s⁻¹ < (pw_s⁻¹ + pw_parent⁻¹) / 2 ∧
                       (pw_s⁻¹ + pw_parent⁻¹) / 2 < pw_parent⁻¹ := by
        have h1 : pw_s⁻¹ < pw_parent⁻¹ := (inv_lt_inv₀ hpos_s hpos_parent).mpr hpw_lt
        constructor <;> linarith
      ext y
      simp only [cylinderInfinite, cylinder, Set.mem_setOf_eq]
      rw [hx_eq]
      have hx_prefix : x'.getPrefix (d :: ds).length = d :: ds :=
        extendPrefixToInfinite_getPrefix ω (d :: ds) hv'
      have hparent_len : parent.length = ds.length := by simp [parent]
      -- Helper: getPrefix n is a prefix of getPrefix m when n ≤ m
      have getPrefix_prefix_of_le : ∀ (τ : InfiniteVariableSpace ω) (n m : ℕ), n ≤ m →
          τ.getPrefix n <+: τ.getPrefix m := by
        intro τ n m hnm
        simp only [InfiniteVariableSpace.getPrefix]
        rw [List.prefix_iff_eq_take]
        apply List.ext_getElem
        · simp only [List.length_take, List.length_ofFn, Nat.min_eq_left hnm]
        · intro i hi _
          simp only [List.length_ofFn] at hi
          simp only [List.getElem_take, List.getElem_ofFn]
      constructor
      · -- y in cylinder → dist < r
        intro hy
        simp only [ultrametricDist]
        by_cases hxy : x' = y
        · subst hxy
          have hno_diff : ¬∃ i, x'.digit i ≠ x'.digit i := by push_neg; intro _; rfl
          simp only [if_neg hno_diff]
          linarith [inv_pos.mpr hpos_s, inv_pos.mpr hpos_parent]
        · have hdiff : ∃ i, x'.digit i ≠ y.digit i := by
            by_contra hall; push_neg at hall
            exact hxy (InfiniteVariableSpace.ext (fun i => hall i))
          simp only [if_pos hdiff]
          have hlcp_ge : (d :: ds).length ≤ lcpLength x' y := by
            have hmem : y ∈ cylinder ω (x'.getPrefix (d :: ds).length) := by
              simp only [cylinder, Set.mem_setOf_eq, hx_prefix]; exact hy
            rw [mem_cylinder_getPrefix_iff] at hmem
            rcases hmem with rfl | hle
            · exact absurd rfl hxy
            · exact hle
          have hpw_ge : pw_s ≤ prefixWeight ω (lcp x' y) := by
            apply Nat.cast_le.mpr
            apply prefixWeight_mono
            simp only [lcp]
            rw [← hx_prefix]
            exact getPrefix_prefix_of_le x' (d :: ds).length (lcpLength x' y) hlcp_ge
          have hpw_pos : (0 : ℝ) < prefixWeight ω (lcp x' y) :=
            Nat.cast_pos.mpr (prefixWeight_pos ω (lcp x' y))
          calc (prefixWeight ω (lcp x' y) : ℝ)⁻¹
              ≤ pw_s⁻¹ := (inv_le_inv₀ hpw_pos hpos_s).mpr hpw_ge
            _ < (pw_s⁻¹ + pw_parent⁻¹) / 2 := hr_bounds.1
      · -- dist < r → y in cylinder
        intro hdist
        simp only [ultrametricDist] at hdist
        by_cases hxy : x' = y
        · subst hxy; exact hx_prefix
        · have hdiff : ∃ i, x'.digit i ≠ y.digit i := by
            by_contra hall; push_neg at hall
            exact hxy (InfiniteVariableSpace.ext (fun i => hall i))
          simp only [if_pos hdiff] at hdist
          by_contra hny
          have hlcp_lt : lcpLength x' y < (d :: ds).length := by
            by_contra hge; push_neg at hge
            have hmem : y ∈ cylinder ω (x'.getPrefix (d :: ds).length) := by
              rw [mem_cylinder_getPrefix_iff]; right; exact hge
            simp only [cylinder, Set.mem_setOf_eq, hx_prefix] at hmem
            exact hny hmem
          have hlcp_le : lcpLength x' y ≤ parent.length := by
            simp only [hparent_len, List.length_cons] at hlcp_lt ⊢; omega
          -- x'.getPrefix parent.length = parent
          have hx_parent : x'.getPrefix parent.length = parent := by
            have h := extendPrefixToInfinite_getPrefix ω (d :: ds) hv'
            simp only [InfiniteVariableSpace.getPrefix] at h ⊢
            apply List.ext_getElem
            · simp only [List.length_ofFn, parent, List.length_dropLast]
            · intro i hi _
              simp only [List.length_ofFn] at hi
              simp only [List.getElem_ofFn]
              have hi' : i < (d :: ds).length := by
                simp only [parent, List.length_dropLast] at hi; omega
              have h' := congrArg (·[i]?) h
              simp only [List.getElem?_ofFn, hi', ↓reduceDIte, List.getElem?_eq_getElem hi'] at h'
              simp only [parent, List.getElem_dropLast (by omega)]
              exact Option.some.inj h'
          have hpw_le : prefixWeight ω (lcp x' y) ≤ prefixWeight ω parent := by
            apply prefixWeight_mono
            simp only [lcp]; rw [← hx_parent]
            exact getPrefix_prefix_of_le x' (lcpLength x' y) parent.length hlcp_le
          have hpw_pos : (0 : ℝ) < prefixWeight ω (lcp x' y) :=
            Nat.cast_pos.mpr (prefixWeight_pos ω (lcp x' y))
          have hdist_ge : pw_parent⁻¹ ≤ (prefixWeight ω (lcp x' y) : ℝ)⁻¹ :=
            (inv_le_inv₀ hpos_parent hpw_pos).mpr (Nat.cast_le.mpr hpw_le)
          linarith [hr_bounds.2]

/-!
## Condition 2: Monotone Refinement
-/

/--
**Monotone Refinement**: Cylinder containment implies radius ordering.

U(s) ⊆ U(t) implies rad(U(s)) ≤ rad(U(t))

Note: We require the source cylinder to be non-empty (valid prefix) to avoid
the degenerate case where an empty cylinder is vacuously contained in everything
but its radius (defined via prefixWeight) doesn't respect this ordering.
-/
def hasMonotoneRefinement (ω : RadixLaw) : Prop :=
  ∀ (s t : PrefixWord),
    (cylinderInfinite ω s).Nonempty →
    cylinderInfinite ω s ⊆ cylinderInfinite ω t →
      variableRadixRadius ω s ≤ variableRadixRadius ω t

/-- Monotone refinement in terms of prefix relation -/
theorem monotoneRefinement_iff_prefix (ω : RadixLaw) :
    hasMonotoneRefinement ω ↔
      ∀ (s t : PrefixWord), (cylinderInfinite ω s).Nonempty →
        t <+: s → variableRadixRadius ω s ≤ variableRadixRadius ω t := by
  constructor
  · -- Forward: hasMonotoneRefinement → prefix implies radius order
    intro hmon s t hne hpre
    apply hmon
    · exact hne
    · -- Need: cylinder s ⊆ cylinder t when t <+: s
      -- If t <+: s, then s = t ++ u for some u, so s extends t
      obtain ⟨u, rfl⟩ := hpre
      -- cylinder(t ++ u) ⊆ cylinder(t)
      apply cylinder_subset_of_prefix
      · simp only [List.length_append]; omega
      · simp only [List.take_append_of_le_length (le_refl _), List.take_length]
  · -- Backward: prefix implies radius order → hasMonotoneRefinement
    intro h s t hne hsub
    -- In ultrametric trees, cylinder s ⊆ cylinder t iff t is a prefix of s
    obtain ⟨τ, hτs_mem⟩ := hne
    have hτt_mem := hsub hτs_mem
    have hτs : τ.getPrefix s.length = s := hτs_mem
    have hτt : τ.getPrefix t.length = t := hτt_mem
    -- τ is in both cylinders: τ.getPrefix s.length = s and τ.getPrefix t.length = t
    -- This means t is a prefix of s (or vice versa)
    have hpre : t <+: s := by
      rcases Nat.le_or_le t.length s.length with hle | hle
      · -- t.length ≤ s.length: t is a prefix of s
        have ht_eq : t = s.take t.length := by
          rw [← hτt, ← hτs]
          simp only [InfiniteVariableSpace.getPrefix]
          apply List.ext_getElem
          · simp only [List.length_take, List.length_ofFn, Nat.min_eq_left hle]
          · intro i hi _
            simp only [List.length_ofFn] at hi
            simp only [List.getElem_take, List.getElem_ofFn]
        rw [ht_eq]; exact List.take_prefix t.length s
      · -- s.length ≤ t.length: s is a prefix of t
        have hs_eq : s = t.take s.length := by
          rw [← hτs, ← hτt]
          simp only [InfiniteVariableSpace.getPrefix]
          apply List.ext_getElem
          · simp only [List.length_take, List.length_ofFn, Nat.min_eq_left hle]
          · intro i hi _
            simp only [List.length_ofFn] at hi
            simp only [List.getElem_take, List.getElem_ofFn]
        -- s <+: t, so cylinder(t) ⊆ cylinder(s)
        -- Combined with hsub : cylinder(s) ⊆ cylinder(t), we get cylinder(s) = cylinder(t)
        -- This implies s = t (they have same length up to common prefix)
        have s_eq_t : s = t := by
          by_contra hne'
          have hstrict : s.length < t.length := Nat.lt_of_le_of_ne hle (fun heq => hne' (by
            rw [hs_eq, heq, List.take_length]))
          -- s <+: t strictly (s is shorter than t)
          -- We'll show there exists τ' ∈ cylinder(s) \ cylinder(t)
          -- which contradicts hsub : cylinder(s) ⊆ cylinder(t)

          -- Get the digit at position s.length in t
          have hs_lt_t : s.length < t.length := hstrict
          let t_digit := t[s.length]'hs_lt_t
          -- Choose a different digit: if t_digit = 0, use 1, else use 0
          let alt_digit := if t_digit = 0 then 1 else 0
          have halt_ne : alt_digit ≠ t_digit := by
            simp only [alt_digit]
            split_ifs <;> omega

          -- We need s to be a valid prefix to extend it
          have hs_valid : isValidPrefix' ω s := by
            have hvalid := τ.getPrefix_valid s.length
            simp only [hτs] at hvalid
            exact hvalid

          -- alt_digit is valid: alt_digit < ω.radix s (since radix ≥ 2 and alt_digit ≤ 1)
          have halt_valid : alt_digit < ω.radix s := by
            have hge2 := ω.radix_ge_two s
            simp only [alt_digit]
            split_ifs <;> omega

          -- Construct extended prefix s ++ [alt_digit]
          let s_ext := s ++ [alt_digit]
          have hs_ext_valid : isValidPrefix' ω s_ext :=
            isValidPrefix'_append_singleton hs_valid halt_valid

          -- Extend s_ext to an infinite sequence
          let τ' := extendPrefixToInfinite ω s_ext hs_ext_valid
          have hτ'_in_cyl_s : τ' ∈ cylinder ω s := by
            simp only [cylinder, Set.mem_setOf_eq]
            have h' := extendPrefixToInfinite_getPrefix ω s_ext hs_ext_valid
            simp only [InfiniteVariableSpace.getPrefix] at h' ⊢
            apply List.ext_getElem
            · simp only [List.length_ofFn]
            · intro i hi _
              simp only [List.length_ofFn] at hi
              simp only [List.getElem_ofFn]
              have hi_ext : i < s_ext.length := by simp [s_ext]; omega
              have h'' := congrArg (·[i]?) h'
              simp only [List.getElem?_ofFn, hi_ext, ↓reduceDIte] at h''
              have hs_ext_eq : (s_ext : List ℕ)[i]? = s[i]? := by
                simp only [s_ext, List.getElem?_append_left hi]
              rw [hs_ext_eq, List.getElem?_eq_getElem hi] at h''
              exact Option.some.inj h''

          have hτ'_not_in_cyl_t : τ' ∉ cylinder ω t := by
            simp only [cylinder, Set.mem_setOf_eq]
            intro heq
            have h_at_s : τ'.digit s.length = alt_digit := by
              simp only [τ', extendPrefixToInfinite]
              have hlt : s.length < s_ext.length := by simp [s_ext]
              simp only [hlt, ↓reduceDIte, s_ext, List.get_eq_getElem]
              simp only [List.getElem_append_right (le_refl _), Nat.sub_self,
                         List.length_singleton, Nat.zero_lt_one, List.getElem_singleton]
            have h_from_eq : τ'.digit s.length = t_digit := by
              have hpref := congrArg (·[s.length]?) heq
              simp only [InfiniteVariableSpace.getPrefix, List.getElem?_ofFn, hstrict, ↓reduceDIte] at hpref
              simp only [List.getElem?_eq_getElem hs_lt_t] at hpref
              exact Option.some.inj hpref
            rw [h_at_s] at h_from_eq
            exact halt_ne h_from_eq

          exact hτ'_not_in_cyl_t (hsub hτ'_in_cyl_s)
        rw [s_eq_t]
    exact h s t ⟨τ, hτs_mem⟩ hpre

/-!
## Condition 3: Finite Branching
-/

/--
**Finite Branching**: Each cylinder has finitely many immediate sub-cylinders.

For any prefix s, the set of children {s∥d : d ∈ D_ω(s)} is finite.
This is automatically satisfied by RadixLaw since ω.radix s is a natural number.
-/
def hasFiniteBranching (ω : RadixLaw) : Prop :=
  ∀ (s : PrefixWord), ∃ n : ℕ, ω.radix s = n

/-- Finite branching is equivalent to radix being a natural number -/
theorem finiteBranching_iff_nat (ω : RadixLaw) :
    hasFiniteBranching ω ↔ ∀ s, ∃ n : ℕ, ω.radix s = n :=
  Iff.rfl

/-- RadixLaw always has finite branching by definition -/
theorem radixLaw_finiteBranching (ω : RadixLaw) : hasFiniteBranching ω := by
  intro s
  exact ⟨ω.radix s, rfl⟩

/-!
## Combined Realizability Conditions
-/

/-- The three realizability conditions combined -/
structure RealizabilityConditions (ω : RadixLaw) : Prop where
  cylinder_correspondence : hasCylinderCorrespondence ω
  monotone_refinement : hasMonotoneRefinement ω
  finite_branching : hasFiniteBranching ω

/-- Prefix relation implies radius ordering -/
theorem radius_le_of_prefix (ω : RadixLaw) (s t : PrefixWord) (h : t <+: s) :
    variableRadixRadius ω s ≤ variableRadixRadius ω t := by
  simp only [variableRadixRadius]
  -- Need: (prefixWeight ω s)⁻¹ ≤ (prefixWeight ω t)⁻¹
  -- This is equivalent to: prefixWeight ω t ≤ prefixWeight ω s
  have hmono := prefixWeight_mono ω t s h
  have ht_pos : (0 : ℝ) < prefixWeight ω t := Nat.cast_pos.mpr (prefixWeight_pos ω t)
  -- Use: 1/a ≤ 1/b iff b ≤ a (for positive a, b)
  rw [inv_eq_one_div, inv_eq_one_div]
  exact one_div_le_one_div_of_le ht_pos (Nat.cast_le.mpr hmono)

/-- Any RadixLaw has monotone refinement -/
theorem radixLaw_monotoneRefinement (ω : RadixLaw) : hasMonotoneRefinement ω := by
  rw [monotoneRefinement_iff_prefix]
  intro s t _hne hpre
  exact radius_le_of_prefix ω s t hpre

/--
Any open ball in the ultrametric is exactly a single cylinder.

This is a general property that doesn't require SU - the proof in Necessity.lean
uses an unused `_hsu` hypothesis. The key insight is that the ultrametric distance
is determined by the LCP, and prefix weights are discrete positive integers.
-/
theorem ball_is_cylinder (ω : RadixLaw) (x : InfiniteVariableSpace ω) (r : ℝ) (hr : r > 0) :
    ∃ s : PrefixWord, {y : InfiniteVariableSpace ω | ultrametricDist x y < r} =
      cylinderInfinite ω s := by
  by_cases hr1 : r > 1
  · -- r > 1: ball is the whole space = cylinder([])
    use []
    ext y
    simp only [Set.mem_setOf_eq, cylinderInfinite, cylinder, InfiniteVariableSpace.getPrefix,
               List.length_nil, List.ofFn_zero, Set.mem_setOf_eq]
    constructor
    · intro _; trivial
    · intro _
      -- ultrametricDist x y ≤ 1 < r
      have hle : ultrametricDist x y ≤ 1 := by
        simp only [ultrametricDist]
        split_ifs with hdiff
        · have hpw_ge : prefixWeight ω (lcp x y) ≥ 1 := prefixWeight_pos ω (lcp x y)
          have hpw_pos : (0 : ℝ) < prefixWeight ω (lcp x y) :=
            Nat.cast_pos.mpr (prefixWeight_pos ω (lcp x y))
          rw [← one_div, div_le_one hpw_pos]
          exact Nat.one_le_cast.mpr hpw_ge
        · norm_num
      linarith
  · -- r ≤ 1: find n such that ball = cylinder(x.getPrefix n)
    push_neg at hr1
    -- We need to find minimal n with prefixWeight(x.getPrefix n) > 1/r
    -- Since prefixWeight grows unboundedly, such n exists
    have hexists : ∃ n, (prefixWeight ω (x.getPrefix n) : ℝ) > 1/r := by
      -- prefixWeight(x.getPrefix n) ≥ 2^n (each radix ≥ 2)
      have hpw_growth : ∀ n, prefixWeight ω (x.getPrefix n) ≥ 2^n := by
        intro n
        induction n with
        | zero =>
          simp only [InfiniteVariableSpace.getPrefix, List.ofFn_zero, prefixWeight_nil, pow_zero,
                     ge_iff_le, le_refl]
        | succ n ih =>
          have hget : x.getPrefix (n + 1) = x.getPrefix n ++ [x.digit n] := by
            simp only [InfiniteVariableSpace.getPrefix]
            apply List.ext_getElem
            · simp only [List.length_append, List.length_ofFn, List.length_singleton]
            · intro i hi _
              simp only [List.length_ofFn] at hi
              by_cases hi' : i < n
              · rw [List.getElem_append_left (by simp only [List.length_ofFn]; exact hi')]
                simp only [List.getElem_ofFn]
              · have hi'' : i = n := by omega
                subst hi''
                rw [List.getElem_append_right (by simp only [List.length_ofFn]; omega)]
                simp only [List.length_ofFn, Nat.sub_self, List.getElem_singleton,
                           List.getElem_ofFn]
          rw [hget, prefixWeight_append]
          calc prefixWeight ω (x.getPrefix n) * ω.radix (x.getPrefix n)
              ≥ 2^n * ω.radix (x.getPrefix n) := Nat.mul_le_mul_right _ ih
            _ ≥ 2^n * 2 := Nat.mul_le_mul_left _ (ω.radix_ge_two _)
            _ = 2^(n+1) := by ring
      -- Now use Archimedean property
      have ⟨N, hN⟩ := exists_nat_gt (1/r)
      use N
      have hN_le : N ≤ 2^N := Nat.le_of_lt Nat.lt_two_pow_self
      calc (prefixWeight ω (x.getPrefix N) : ℝ)
          ≥ 2^N := by exact_mod_cast hpw_growth N
        _ ≥ N := by exact_mod_cast hN_le
        _ > 1/r := hN
    -- Choose the minimal such n
    let n := Nat.find hexists
    use x.getPrefix n
    ext y
    have hlen : (x.getPrefix n).length = n := InfiniteVariableSpace.getPrefix_length x n
    simp only [Set.mem_setOf_eq, cylinderInfinite, cylinder, Set.mem_setOf_eq, hlen]
    constructor
    · -- y in ball → y in cylinder
      intro hdist
      simp only [ultrametricDist] at hdist
      by_cases hxy : x = y
      · subst hxy; rfl
      · -- x ≠ y: dist = (prefixWeight(lcp))⁻¹ < r
        have hdiff : ∃ i, x.digit i ≠ y.digit i := by
          by_contra hall; push_neg at hall
          exact hxy (InfiniteVariableSpace.ext (fun i => hall i))
        simp only [if_pos hdiff] at hdist
        -- (prefixWeight(lcp))⁻¹ < r → prefixWeight(lcp) > 1/r
        have hpw_pos : (0 : ℝ) < prefixWeight ω (lcp x y) :=
          Nat.cast_pos.mpr (prefixWeight_pos ω (lcp x y))
        have hpw_gt : (prefixWeight ω (lcp x y) : ℝ) > 1/r := by
          have h : (prefixWeight ω (lcp x y) : ℝ)⁻¹ < r := hdist
          have h2 := (inv_lt_comm₀ hpw_pos hr).mp h
          rw [one_div]; exact h2
        -- lcp x y = x.getPrefix (lcpLength x y)
        -- We need: y.getPrefix n = x.getPrefix n
        -- Sufficient: lcpLength x y ≥ n
        have hlcp_ge : n ≤ lcpLength x y := by
          by_contra hlt; push_neg at hlt
          -- By minimality of n, prefixWeight(x.getPrefix (lcpLength x y)) ≤ 1/r
          have hmin := Nat.find_min hexists hlt
          push_neg at hmin
          -- But lcp x y = x.getPrefix (lcpLength x y)
          have hlcp_eq : lcp x y = x.getPrefix (lcpLength x y) := rfl
          rw [hlcp_eq] at hpw_gt
          linarith
        -- Now show y.getPrefix n = x.getPrefix n using mem_cylinder_getPrefix_iff
        have hmem : y ∈ cylinder ω (x.getPrefix n) := by
          rw [mem_cylinder_getPrefix_iff x y n]
          right; exact hlcp_ge
        simp only [cylinder, Set.mem_setOf_eq, hlen] at hmem
        exact hmem
    · -- y in cylinder → y in ball
      intro hmem
      simp only [ultrametricDist]
      by_cases hxy : x = y
      · subst hxy
        have hno : ¬∃ i, x.digit i ≠ x.digit i := by push_neg; intro _; rfl
        simp only [if_neg hno]
        exact hr
      · have hdiff : ∃ i, x.digit i ≠ y.digit i := by
          by_contra hall; push_neg at hall
          exact hxy (InfiniteVariableSpace.ext (fun i => hall i))
        simp only [if_pos hdiff]
        -- hmem : y.getPrefix n = x.getPrefix n
        have hmem' : y ∈ cylinder ω (x.getPrefix n) := by
          simp only [cylinder, Set.mem_setOf_eq, hlen]
          exact hmem
        rw [mem_cylinder_getPrefix_iff x y n] at hmem'
        rcases hmem' with rfl | hle
        · exact absurd rfl hxy
        · -- hle : n ≤ lcpLength x y
          -- prefixWeight(lcp) ≥ prefixWeight(x.getPrefix n) > 1/r
          have hpw_pos : (0 : ℝ) < prefixWeight ω (lcp x y) :=
            Nat.cast_pos.mpr (prefixWeight_pos ω (lcp x y))
          have hn_spec := Nat.find_spec hexists
          have hpw_ge : prefixWeight ω (x.getPrefix n) ≤ prefixWeight ω (lcp x y) := by
            apply prefixWeight_mono
            -- x.getPrefix n <+: lcp x y = x.getPrefix (lcpLength x y)
            -- Since hle : n ≤ lcpLength x y, we have x.getPrefix n <+: x.getPrefix (lcpLength x y)
            -- First show x.getPrefix n = (x.getPrefix (lcpLength x y)).take n
            have hpre : x.getPrefix n = (x.getPrefix (lcpLength x y)).take n := by
              simp only [InfiniteVariableSpace.getPrefix]
              apply List.ext_getElem
              · simp only [List.length_take, List.length_ofFn, Nat.min_eq_left hle]
              · intro i hi _
                simp only [List.length_ofFn] at hi
                simp only [List.getElem_take, List.getElem_ofFn]
            rw [hpre]
            exact List.take_prefix n _
          have hpw_gt : (prefixWeight ω (lcp x y) : ℝ) > 1/r := by
            calc (prefixWeight ω (lcp x y) : ℝ)
                ≥ prefixWeight ω (x.getPrefix n) := by exact_mod_cast hpw_ge
              _ > 1/r := hn_spec
          -- Convert: pw > 1/r to pw⁻¹ < r
          have h2 : r⁻¹ < (prefixWeight ω (lcp x y) : ℝ) := by
            rw [inv_eq_one_div]; exact hpw_gt
          exact (inv_lt_comm₀ hpw_pos hr).mpr h2

/-- Cylinder correspondence holds for any RadixLaw -/
theorem radixLaw_hasCylinderCorrespondence (ω : RadixLaw) : hasCylinderCorrespondence ω := by
  intro x r hr
  obtain ⟨s, hs⟩ := ball_is_cylinder ω x r hr
  use {s}
  rw [hs]
  simp only [Finset.mem_singleton, Set.iUnion_iUnion_eq_left]

/-- Any RadixLaw satisfies the realizability conditions -/
theorem radixLaw_satisfies_conditions (ω : RadixLaw) :
    RealizabilityConditions ω := by
  constructor
  · exact radixLaw_hasCylinderCorrespondence ω
  · exact radixLaw_monotoneRefinement ω
  · exact radixLaw_finiteBranching ω

end FdrsFormal.Modes.VariableRadix
