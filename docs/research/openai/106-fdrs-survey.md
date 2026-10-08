# Survey — FDRS touchpoints for OpenAI family 106 (independent sets in three-colorable graphs)

*Provenance: agent survey (read-only pass over `docs/fdrs.md`, `docs/fdrs-index.md`,
`data/fdrs-index.yaml`, `docs/fourier/01-schedule-search.md` and the Lean tree
`FdrsFormal/`), 2026-10-08. Nothing in the repository was modified except the creation
of this file. Line numbers refer to the working tree at commit `9dc1098`. Claims about
what is "missing" are the result of `grep`/`rg` over the whole tree for the listed
vocabulary (Lipschitz, junta, influence, Efron, Walsh, Vilenkin, Parseval/Plancherel,
condExp, PseudoMetric, PMF, SimpleGraph, chromatic, coloring, AddCircle, Int.fract,
half-shift, digit sum) and inspection of the files they hit.*

Themes of the paper, in the caller's labelling: (a) Fourier / Efron–Stein on `∏ ℤ/D`,
influences, half-shift sign change; (b) dimension-free junta approximation of
sup-metric Lipschitz functions; (c) phase grids, sup circle metric, link-graph
pseudometrics with zero-length projection links, nonexpanding evaluation maps; (d) the
thirds colouring of the circle; (e) rational product experiments expanded to uniform
laws; (f) independence numbers and colourings.

---

## 1. Theme-by-theme inventory

### (a) Characters, Efron–Stein, influences, half-shift

**Already there.**

*Characters on `ℤ/N` (Phase 3, Fragment 2, §1.1–1.3; spec lines 1792–1849).*
`FdrsFormal/NumberTheory/Characters/AdditiveCharacters.lean`:

```lean
noncomputable def additiveCharacter (N m : ℕ) (hN : 0 < N) (x : ZMod N) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (ZMod.val x : ℂ) / (N : ℂ))
theorem additiveCharacter_orthogonal (N m m' : ℕ) (hN : 0 < N) [Fintype (ZMod N)] :
    (1 / (N : ℂ)) * (∑ x : ZMod N, additiveCharacter N m hN x *
      (starRingEnd ℂ) (additiveCharacter N m' hN x)) =
    if (m : ZMod N) = (m' : ZMod N) then 1 else 0          -- spec Proposition 41 (line 1812)
theorem residueClassProjector (q : ℕ) (hq : 0 < q) [Fintype (ZMod q)] (x a : ZMod q) : …  -- Prop 42
noncomputable def fourierTransform (N : ℕ) (hN : 0 < N) (f : ZMod N → ℂ) (m : ℕ) [Fintype (ZMod N)] : ℂ
theorem convolutionTheorem … : fourierTransform N hN (cyclicConv N f g) m =
    fourierTransform N hN f m * fourierTransform N hN g m                      -- Theorem 16
```
(Note: the docstrings in this file call orthogonality "Proposition 38"; the spec heading
at line 1812 is Proposition 41. The index matches by line range, so this is cosmetic.)
A Mathlib bridge `standardAddChar (N) [NeZero N] (m : ZMod N) : AddChar (ZMod N) ℂ`
exists (same file, via `AddChar.zmodChar`).

*The carry-free product group `∏ ℤ/b_i` and its Vilenkin kernel (Phase 3 addenda
§1.4–1.6, spec lines 9090–9230).* `FdrsFormal/NumberTheory/Characters/MixedRadixFFT.lean`:

```lean
noncomputable def zeta (n : ℕ) : ℂ := exp (2 * Real.pi * I / n)
def reverseDecode (b : RadixSeq) (k : ℕ) (σ : FiniteRadixSpace b k) : ℕ
noncomputable def vilenkinKernel (k : ℕ) (τ σ : FiniteRadixSpace b k) : ℂ :=
  ∏ i : Fin (k + 1), zeta (b i) ^ ((τ i : ℕ) * σ i)
noncomputable def twiddleKernel (k : ℕ) (τ σ : FiniteRadixSpace b k) : ℂ
theorem character_factor (k : ℕ) (τ σ : FiniteRadixSpace b k) :
    zeta (placeValue b (k + 1)) ^ (reverseDecode b k σ * decodeFinite b k τ) =
      vilenkinKernel k τ σ * twiddleKernel k τ σ                            -- Corollary 32
noncomputable def dft (N : ℕ) (x : ℕ → ℂ) (m : ℕ) : ℂ := ∑ n ∈ Finset.range N, x n * zeta N ^ (m * n)
theorem dft_factor / fourier_factor …                                        -- Corollary 32
theorem twiddleKernel_trivial_iff (k : ℕ) : (∀ τ σ, twiddleKernel k τ σ = 1) ↔ k = 0  -- Prop 154
```
`GoodThomas.lean` adds `crtChart`, `ruritanian`, `zeta_pow_ruritanian_mul` (Theorem 121)
and `dft_goodThomas` (Corollary 33): for pairwise-coprime radices the DFT *is* the
Vilenkin transform. `MixedRadixStages.lean` has the in-place digit-summing operator

```lean
noncomputable def stage (k : ℕ) (i : Fin (k + 1)) (y : FiniteRadixSpace b k → ℂ)
    (ρ : FiniteRadixSpace b k) : ℂ :=
  ∑ t : Fin (b i), y (Function.update ρ i t) * stageFactor k i t ρ          -- Definition 214
theorem stage_readsAtMost (k : ℕ) (i : Fin (k + 1)) : ReadsAtMost (stage (b := b) k i) (b i)
```
which is syntactically the per-coordinate averaging operator `E_i` with a different kernel.
Root-of-unity orthogonality is in `RaderBluestein.lean`:
`theorem sum_zeta_pow_mul (n s : ℕ) (hn : n ≠ 0) : ∑ k ∈ Finset.range n, zeta n ^ (k * s) = if n ∣ s then (n : ℂ) else 0` (Proposition 161), and `PairKernel.lean` has `zeta_pow_mod (n a) (hn : n ≠ 0) : zeta n ^ a = zeta n ^ (a % n)`.

*A real tensor-product basis of exactly Efron–Stein shape (Phase 2, Fragment 4;
spec lines 1296–1394).* `FdrsFormal/FunctionSpaces/Haar/Definition.lean`,
`Orthonormality.lean`, `SupportLevel.lean`, `ProjectionAction.lean`:

```lean
def HaarAtom (b : RadixSeq) (k : ℕ) := (i : Fin (k + 1)) → Fin (b i)
noncomputable def haarFunction (α : HaarAtom b k) : FiniteRadixSpace b k → ℝ :=
  fun d => ∏ i : Fin (k + 1), haarComponent i (α i) (d i)                   -- Definition 35
theorem haarBasis_orthonormal (α β : HaarAtom b k) :
    ∑ σ, haarFunction α σ * haarFunction β σ = if α = β then (∏ i, (b i : ℝ)) else 0  -- Theorem 11
theorem haarBasis_complete (σ τ : FiniteRadixSpace b k) : ∑ α, haarFunction α σ * haarFunction α τ = …
theorem haarComponent_inner (i) (αᵢ βᵢ : Fin (b i)) : ∑ d, haarComponent i αᵢ d * haarComponent i βᵢ d = if αᵢ = βᵢ then (b i : ℝ) else 0
def supportLevel (α : HaarAtom b k) : Fin (k + 1)            -- Definition 36: max{i : α_i ≠ 0}
theorem blockProjection_haarAtom (α) (L : ℕ) (hL : L < k + 1) : …   -- Proposition 33
```
Atom `α` has a mean-zero factor exactly on `supp α = {i : α_i ≠ 0}`; this is the
Efron–Stein subset `S`, but the corpus only ever classifies atoms by `max S` (the prefix
filtration), never by `S` itself or by `i ∈ S`.

*Conditional expectations / averaging.* Only **prefix** σ-algebras: Definition 27,
`FdrsFormal/FunctionSpaces/Commutant/FiniteProjection.lean:75`

```lean
noncomputable def finiteBlockProjection (b : RadixSeq) (k L : ℕ) (hLk : L ≤ k + 1)
    [AddCommGroup V] [Module ℝ V] (f : FiniteRadixSpace b k → V) : FiniteRadixSpace b k → V :=
  fun τ => let s := finitePrefix b L τ hLk
           let m_kL := placeValue b (k + 1) / placeValue b L
           (m_kL : ℝ)⁻¹ • ∑ σ : (finiteCylinderSet b k L hLk s), f σ.val
```
with `finiteBlockProjection_idempotent/_tower/_comm/_telescoping`,
`fiberwiseAveraging` (Prop 23: average over the suffix digits `≥ L`),
`finiteBlockProjection_isOrthogonalProjection` (self-adjointness w.r.t. `∑ τ, f τ * g τ`,
`Contraction.lean:449`), `finiteBlockProjection_Lp_norm_le` (Theorem 5, every `1 ≤ p ≤ ∞`),
`multiresolution_decomposition` (Theorem 7, `OrthogonalDecomp.lean:75`), and on the
completed space `L2_norm_decomposition` (`Projections/Details.lean:492`, a Parseval
identity for the prefix filtration against `uniformProductMeasure`). Mathlib's `condExp`
is only *mentioned* in docstrings (`Projections/Properties.lean:233`, `Contraction.lean:445`);
no bridge is proven.

*Shifts.* `cyclicTick` (Definition 33, `Commutant/TickPullback.lean:58`), with
`cyclicTick_measurePreserving : ∑ τ, g (cyclicTick b k τ) = ∑ τ, g τ` and
`tickPullback_commutes_projection` (Theorem 10); and the per-position permutations
`structure DigitPermutation (b) (k) where position : Fin (k+1); perm : Equiv.Perm (Fin (b position))`
with `digitPermutation_isometry` (Prop 34, `LocalOperators/DigitPermutation.lean`).

**Missing.** Per-coordinate averaging `E_i`; influences `D_i(H) = ‖(id − E_i)H‖₂` and
their spectral formula; a complex `L²` inner product / Plancherel on
`FiniteRadixSpace b k → ℂ` (`finiteLpNorm` is `ℝ≥0∞`-valued, `LpNorm.lean:65`, awkward
for Parseval); orthogonality of `vilenkinKernel` itself (only `ζ_n`-power and `ℤ/N`
orthogonality are proven); subset-indexed Efron–Stein decomposition; the half-shift
`τ ↦ (τ_i + b_i/2)_i` and the "odd digit sum" support criterion (`grep` for half-shift,
digit-sum parity: no hits; `digitSum` only appears in `Core/PrefixValue.lean` and
`Applications/Field25519Carry.lean` in unrelated senses).

### (b) Dimension-free junta approximation for sup-Lipschitz functions

**There.** 1-Lipschitz statements only for arithmetic in the *prefix ultrametric*:
Corollary 1, Proposition 13, Corollary 2 (`FdrsFormal/Topology/Continuity/Operations.lean`,
`Operations/Predecessor/Locality.lean`); the finite-dependence Corollary 3
(`Topology/Locality/Properties.lean:58–133`, `finite_dependence_tick/_pred/_add`); the sup
norm `finiteSupNorm b k f := ⨆ τ, ↑‖f τ‖₊` and `finiteBlockProjection_supNorm_le`
(`Contraction.lean:90`). The closest thing to a junta is "depends on the first `L`
digits": `IsBlockConstant` / `BlockConstantSpace` (Definition 19,
`FunctionSpaces/Basic/BlockConstant.lean:57–88`) and the Phase 4 Fragment 4.2 depth-`L`
gates (Propositions 72–74). Mathlib's `LipschitzWith` is used nowhere.

**Missing.** Any product/sup metric on `FiniteRadixSpace` other than the ultrametric;
juntas on arbitrary coordinate sets; any approximation theorem of the paper's type. The
dimension-free approximation is a genuinely analytic result and would be out of scale for a
first addendum; only its statement could be recorded (the corpus already does this for
family 130's `MainStatement`, `FourierCircuit.lean:97`).

### (c) Phase grids, sup circle metric, link-graph pseudometrics, nonexpanding evaluations

**There.** The digit alphabets `Fin (b i)` are the phase grids `(1/b_i)ℤ/ℤ` without the
circle embedding. A discretised circle with sectors exists as a leaf module,
`FdrsFormal/Modes/SyntheticPlace/CircleEmit.lean` (Definition 206, Theorem 100; spec
lines 8675–8690):

```lean
def circ (cellWidth M : ℕ) : ℕ := M * cellWidth
def sector (cellWidth M p : ℕ) : ℕ := (p % circ cellWidth M) / cellWidth
theorem emitSector_sound (cellWidth M lo w k v : ℕ) (hemit : emitSector cellWidth M lo w = some k)
    (hlv : lo ≤ v) (hvw : v ≤ lo + w) : sector cellWidth M v = k
```
Mathlib's unit circle `Circle` is used in `SE2Pose.lean` (`rot : Circle`). The sup-over-places
distance of Definition 200, `Modes/SyntheticPlace/NetworkGauge.lean:67`,

```lean
noncomputable def netDist (G : V → PrefixGauge D) (x y : V → ℕ → D) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun v => gaugeDist (G v) (x v) (y v)
theorem gaugeDist_le_netDist (G) (x y) (v : V) : gaugeDist (G v) (x v) (y v) ≤ netDist G x y
```
is a sup metric on a product whose coordinate projections are nonexpanding — the shape of
the paper's "evaluation maps are nonexpanding" — but over ultrametric factors.
`Modes/VariableRadix/InducedUltrametric/Axioms.lean` builds a genuine `MetricSpace`
instance (`variableRadixMetricSpace`), and `TraceGeometry.lean` has projections of traces
to places (`proj v`) and the scalar-gauge no-go (Theorem 91).

**Missing.** The circle metric `‖x − y‖_{ℝ/ℤ}` (no `AddCircle`, `Int.fract`, or
`toIcoMod` anywhere); the sup circle metric on `∏ (1/b_i)ℤ/ℤ`; pseudometrics generated by
link graphs with zero-length pull-back links along `x ↦ x ∘ π`; any quotient-pseudometric
construction.

### (d) The thirds colouring

**There.** For `M = 3`, `CircleEmit.sector w 3 p` *is* "which third of the circle
`ℤ/3w`" and equals the first base-3 digit of `p / 3w`; in FDRS terms it is digit `0` of
`encodeFinite` on a schedule with `b 0 = 3` (`Core/Finite/Bijection.lean:81,415`). Nothing
states this, and nothing uses it as a colouring.

**Missing.** The colouring as a map `Fin (b i) → Fin 3` (needs `3 ∣ b i`), the fact that
two phases in the same third are at circle distance `< 1/3`, and any notion of proper
colouring.

### (e) Product probability, rational laws, integer multiplicities

**There.** Uniform laws only: `digitMeasure b i := (1 / (b i : ℝ≥0∞)) • Measure.count`
and `uniformProductMeasure b := Measure.infinitePi (fun i => digitMeasure b i)` with
`IsProbabilityMeasure` instances (`FunctionSpaces/Measure/ProductMeasure.lean:72,140`),
`cylinder_measure` (cylinder of depth `L` has mass `1/B_L`), and the finite
`finiteUniformMeasure b k := (1 / (placeValue b (k+1) : ℝ≥0∞)) • Measure.count`
(`Commutant/FiniteHorizon.lean:321`). The only non-uniform law is the Parry measure of
the golden-mean shift (`goldenPMF`, `goldenStatPMF`, Ionescu–Tulcea path measure;
Definitions 185–187, `Modes/VariableRadix/SubshiftParry.lean`). `ProbSpace` in
`Modes/ContextDependent/Variations/Stochastic.lean:49` is a bare `Ω : Type*` with
`Nonempty`, not a measure.

**Missing.** Product laws with rational marginals; the expansion of a rational law
`p_i(t) = n_{i,t}/m_i` into a uniform law on `Fin m_i` pushed forward along a multiplicity
map `Fin m_i → Fin (b i)`. This is a natural FDRS statement: the expanded index set is
itself `FiniteRadixSpace m k` for the schedule `m`.

### (f) Independence numbers and colourings

**There.** Four directed graph structures with walks, acyclicity and holonomy —
`CouplingGraph` (Definition 201, `Modes/SyntheticPlace/Grading.lean:71`), `GroupGraph`
(`GroupGrading.lean`), `TimelineGraph` (`Composition/TimelineGraphs/Definition.lean:77`),
`DependencyGraph` (`Composition/DeadlockAnalysis/Definition.lean:57`). None is a
`SimpleGraph`.

**Missing.** Everything: `SimpleGraph`, independent sets, `α(G)`, chromatic number,
colourability, the paper's graph families. This theme has no foothold in the corpus and
should not be the first addendum.

---

## 2. Machinery a theme-(a) addendum would build on

- **The finite radix space** (`Core/Finite/Bijection.lean:38–59`):
  `def FiniteRadixSpace (b : RadixSeq) (k : ℕ) := (i : Fin (k + 1)) → Fin (b i)` with
  `Fintype`, `MeasurableSpace`, `MeasurableSingletonClass`, `Inhabited` instances and
  `ext`; `decodeFinite`, `encodeFinite`, `finiteRadixEquiv : FiniteRadixSpace b k ≃ Fin (placeValue b (k+1))`;
  `card_finiteRadixSpace : Fintype.card (FiniteRadixSpace b k) = placeValue b (k + 1)`
  (`MixedRadixStages.lean`). `structure RadixSeq where toFun : ℕ → ℕ; ge_two : ∀ i, 2 ≤ toFun i`
  with `b.pos`, `b.ne_zero`.
- **Roots of unity and the Vilenkin kernel**: `zeta`, `zeta_pow_self`, `zeta_ne_one`,
  `zeta_pow_self_mul`, `zeta_mul_pow_mul`, `zeta_pow_mod`, `zeta_isPrimitiveRoot`,
  `sum_zeta_pow_mul`, `vilenkinKernel` (all quoted above). Orthogonality of the
  Vilenkin kernel is one `Fintype.prod_sum` away: the pattern is exactly
  `haarBasis_orthonormal` (`Haar/Orthonormality.lean:112`), whose helper
  `sum_prod_eq_prod_sum_frs : ∑ σ : FiniteRadixSpace b k, ∏ i, g i (σ i) = ∏ i, ∑ d, g i d`
  is `private` and must be restated (one line: `unfold FiniteRadixSpace; exact (Fintype.prod_sum g).symm`).
- **Digit-local operators**: `stage` (Definition 214) and `Function.update ρ i t`, with
  `stage_readsAtMost` as the template for proving that `E_i` reads `b_i` entries.
- **Averaging / projections**: `finiteBlockProjection`, `fiberwiseAveraging`,
  `finiteBlockProjection_isOrthogonalProjection`, `finiteBlockProjection_Lp_norm_le`,
  `finiteBlockProjection_supNorm_le`, `multiresolution_decomposition`,
  `finiteBlockProjection_telescoping`, `detailSubspace_span` (Corollary 8,
  `Haar/ProjectionAction.lean:147`).
- **Norms and measure**: `finiteLpNorm`, `finiteSupNorm`, `finiteUniformMeasure`. There is
  **no** complex inner product on `FiniteRadixSpace b k → ℂ`; the Fourier files work with
  bare `Finset.sum` and `starRingEnd ℂ`, and the new addendum should do the same
  (`(1 / N) * ∑ τ, f τ * conj (g τ)`), as in `additiveCharacter_orthogonal`.
- **Group actions**: `cyclicTick`/`tickPullback` and `cyclicTick_measurePreserving`
  (`Fintype.sum_equiv` over a bijection), `DigitPermutation`/`digitPermutation_isometry`.
  The half-shift is a product of `DigitPermutation`s (one per position, `perm := Equiv.addRight (b_i/2)`).

---

## 3. Candidate items for a new addendum (§1.13, Phase 3 Fragment 2)

Numbering continues from the stated free numbers. Notation as in §1.4: `𝓡^{(k)}`,
`N = B_{k+1}`, `V(τ,σ) = ∏_i ζ_{b_i}^{τ_iσ_i}`, `τ[i := t]` for `Function.update`.

**Definition 218 (digit averaging; influence; the half-shift).** For `f : 𝓡^{(k)} → ℂ`
and a digit position `i`: `(E_i f)(τ) := (1/b_i) Σ_{t<b_i} f(τ[i:=t])`; the *influence*
`D_i(f)² := (1/N) Σ_τ |f(τ) − (E_i f)(τ)|²`; the *Vilenkin coefficients*
`f̂(σ) := (1/N) Σ_τ f(τ) conj V(τ,σ)`; the global mean `E f := (1/N) Σ_τ f(τ)`. When
every `b_i` is even, the *half-shift* `h(τ)_i := τ_i + b_i/2 (mod b_i)` and the *digit sum*
`|σ| := Σ_i σ_i`. Lean: `digitAvg`, `influenceSq`, `vilenkinCoeff`, `halfShift`,
`digitSum`, all in a new `FdrsFormal/NumberTheory/Characters/DigitInfluence.lean`.
Effort S.

**Proposition 162 (digit averaging is a commuting family of projections; the prefix
projection is a product of them).** `E_i E_i = E_i`, `E_i E_j = E_j E_i`, `E_i` is
self-adjoint for `(1/N)Σ f conj g`, `‖E_i f‖_p ≤ ‖f‖_p` for `1 ≤ p ≤ ∞`, `E_i` reads at
most `b_i` entries per output (`ReadsAtMost (digitAvg k i) (b i)`), and
`P^{(k)}_L = E_L E_{L+1} ⋯ E_k` (Definition 27). Uses `fiberwiseAveraging`,
`stage_readsAtMost`'s proof, `Function.update` lemmas. The last clause is the bridge to
Phase 2 and is the only nontrivial one (induction on `k − L` through `cylinderSuffixEquiv`).
Effort M.

**Theorem 131 (Vilenkin orthogonality and Plancherel on the carry-free group).**
`(1/N) Σ_τ V(τ,σ) conj V(τ,σ') = δ_{σσ'}` and `(1/N) Σ_σ V(τ,σ) conj V(τ',σ) = δ_{ττ'}`;
hence `f = Σ_σ f̂(σ) V(·,σ)` and `(1/N) Σ_τ |f(τ)|² = Σ_σ |f̂(σ)|²`. Proof: product form of
`vilenkinKernel`, `Fintype.prod_sum`, `zeta_pow_mod` and `sum_zeta_pow_mul` per digit
(the digit difference `τ_i − τ'_i` handled mod `b_i`, as `exp_zmod_sub_eq` does on `ℤ/N`).
Remark for the spec: by Corollary 32 and `|T| = 1`, Proposition 41 on `ℤ/N` at frequency
`rdec σ` is the same statement twisted by `T`. Effort M.

**Theorem 132 (the spectral formula for influences; Efron–Stein).**
`E_i V(·,σ) = [σ_i = 0] · V(·,σ)` (from `sum_zeta_pow_mul` with `s = σ_i`); therefore
`(E_i f)^(σ) = [σ_i = 0] f̂(σ)`, `D_i(f)² = Σ_{σ : σ_i ≠ 0} |f̂(σ)|²`, and with
`f_S := Σ_{supp σ = S} f̂(σ) V(·,σ)` for `S ⊆ {0,…,k}`: `f = Σ_S f_S`, the `f_S` are
orthogonal, `E_i f_S = f_S` for `i ∉ S` and `E_i f_S = 0` for `i ∈ S`,
`Σ_i D_i(f)² = Σ_σ |supp σ| |f̂(σ)|² ≥ (1/N) Σ_τ |f(τ) − E f|²` (Poincaré, constant 1).
Corollary for Phase 2: `D_L = ⊕_{max S = L} span f_S`, i.e. Corollary 8 with
`supportLevel` read on `σ` instead of the real Haar atom `α`. Uses Theorem 131,
Proposition 162. Effort M–L (the subset-indexed sums need `Finset.filter` bookkeeping;
the per-`i` spectral formula alone is M).

**Proposition 163 (the half-shift changes the sign of odd-digit-sum characters).** For an
even schedule, `h` is an involution and measure-preserving (`Fintype.sum_equiv`),
`V(h τ, σ) = (−1)^{|σ|} V(τ, σ)` (from `ζ_b^{b/2} = −1`, via `Complex.exp_pi_mul_I` and
`zeta_mul_pow_mul`), and for every `f`: `f ∘ h = −f ⟺ (∀ σ, |σ| even → f̂(σ) = 0)`, while
`f ∘ h = f ⟺ (∀ σ, |σ| odd → f̂(σ) = 0)`. Effort S–M.

**Corollary 39 (sign-changing functions carry their whole energy on odd characters).** If
`f ∘ h = −f` then `E f = 0`, `(1/N)Σ|f|² = Σ_{|σ| odd} |f̂(σ)|²`, and
`Σ_i D_i(f)² ≥ (1/N) Σ_τ |f(τ)|²` (every odd-sum `σ` has nonempty support); moreover the
sup-norm half of the paper's argument, `max_τ |f(τ) − f(h τ)| = 2 ‖f‖_∞`, is immediate.
Effort S.

**Definition 219 (phase grid, circle distance, sup phase metric, the thirds).** `phase_i(t) := t / b_i ∈ ℚ`,
`d_circ(s,t) := min (fract (s − t)) (fract (t − s))` on `ℚ`, `d_∞(τ,σ) := max_i d_circ(phase_i τ_i, phase_i σ_i)`,
and for `3 ∣ b_i` the colour `third_i(t) := (3 t) / b_i ∈ Fin 3` (`= CircleEmit.sector (b_i/3) 3 t`).
**Proposition 164:** `d_∞` is a metric on `𝓡^{(k)}` invariant under the half-shift and
under every `DigitPermutation` by a rotation; `third_i` is the first base-3 digit of the phase;
`third_i s = third_i t → d_circ(s,t) < 1/3`; and each coordinate evaluation
`τ ↦ phase_i τ_i` is nonexpanding from `d_∞`. Effort M (the `fract`-based circle distance
and its triangle inequality are the cost; Mathlib's `AddCircle` could be used instead but
the corpus has never imported it).

**Definition 220 / Proposition 165 (rational product laws as uniform radix spaces).** Given
multiplicities `n : (i : Fin (k+1)) → Fin (b i) → ℕ` with `m_i := Σ_t n_{i,t} ≥ 2`, the
expanded schedule `m` and the digit-wise coarsening `c : FiniteRadixSpace m k → FiniteRadixSpace b k`
(fiber of `t` has `n_{i,t}` preimages); then `(1/M) #{ρ : c ρ = τ} = ∏_i n_{i,τ_i}/m_i`, i.e.
the pushforward of `finiteUniformMeasure m k` is the product law with marginals
`n_{i,t}/m_i`. Effort M (`Fintype.card_pi`, `Finset.card_filter` products). This is the
only theme-(e) statement with FDRS content ("a rational experiment is a uniform number line
seen through a coarsening").

Not proposed as theorems: the dimension-free junta approximation (b) and anything in (f).
If wanted, (b) can be recorded as a `MainStatement`-style `Prop` with an explicit "not
proven here" line, as `FourierCircuit.lean:94–100` does for family 130.

Suggested file split: `DigitInfluence.lean` (Definition 218, Proposition 162, Theorems
131–132, Proposition 163, Corollary 39) importing `MixedRadixStages`; `PhaseMetric.lean`
(Definition 219, Proposition 164) importing `CircleEmit` only if the `sector` identity is
kept; `MultiplicityExpansion.lean` (Definition 220, Proposition 165) under
`FunctionSpaces/Measure/`.

---

## 4. House conventions the addendum must follow

1. **Spec first, at the end of the file.** New items go into `docs/fdrs.md` under the
   existing block `# Phase 3 addenda — the mixed-radix Fourier arc (§1.4–1.12)` (line 9086),
   as a new `## 1.13 … (addendum, 2026-10-08)` so earlier line references stay stable.
   Heading format is exact and parsed by `scripts/fdrs_parse.py`:
   `### Theorem 131 (the title)  [§1.13 · Phase 3, Fragment 2]` (two spaces before the
   bracket). Numbers are global and monotonic; next free: Definition 218, Proposition 162,
   Theorem 131, Corollary 39.
2. **Provenance paragraph + honest scope.** Each addendum section opens with an italic
   provenance note naming the external source (compare §1.4: "*Provenance: OpenAI's
   mathematics collection, family 130 …*") and closes with `**Honest scope (§1.13).**`
   citing the classical sources (Efron–Stein 1981; Vilenkin 1947; the Walsh case) and
   saying what is *not* claimed. The README's rule: "Classical is cited as classical";
   contribution = placement + verified artifact.
3. **`*Lean:*` lines** in the spec after each group of items, naming the module path(s).
4. **Lean module shape.** HPL licence header (copy from any `Characters/*.lean`), a
   module docstring listing each item with the declaration names that prove it and an
   `**Honest scope.**` paragraph; namespace `FdrsFormal.NumberTheory.Characters.<…>`;
   `variable {b : RadixSeq}`; wire the new module into the aggregator
   `FdrsFormal/NumberTheory/Characters.lean` (and its contents list) so the default
   `lake build` covers it (`docs/TESTING.md`: every module must be reachable from the root).
5. **Anchors.** Every theorem/def docstring that realises an item ends with a line
   `**fdrs.md**: Theorem 131 (the title).` The scanner regex (`scripts/lean_scan.py:176`)
   is `fdrs\.md[*\s:]*\(?\s*(Theorem|Definition|Proposition|Corollary|Lemma)\s+(\d+)`; the
   anchor overrides heuristic matching and lets stubs downgrade an item honestly. Multiple
   declarations may anchor one item (e.g. `stages_apply`, `fft_apply`, `fft_eq_dft` all
   cite Theorem 120).
6. **No `sorry`, no `axiom`, no `native_decide`.** Finite witnesses use `decide +kernel`
   (SearchCertificates) or `norm_num` (`CircleEmit.lean`). Scaffolds must carry
   `@scaffold-ok` or they are flagged by `fdrs-summary --stubs`.
7. **Regenerate, never hand-edit, `data/` and `docs/fdrs-index.md`:**
   `python3 scripts/fdrs-summary --rebuild` then `--check` after the build; commit
   messages follow the pattern `Phase 3 §1.13: …` (see `git log`).
8. **Design records** for a research thread go in `docs/fourier/NN-….md` with sections
   "Formal status" and an "Anti-confabulation ledger" (proven / checked numerically /
   not claimed), as in `01-schedule-search.md`.
9. **Style of statements.** Theorems are stated over `Finset.sum` with
   `starRingEnd ℂ`, normalisation written explicitly (`(1 / (N : ℂ)) * ∑ …`), kernels as
   `∏ i : Fin (k + 1), …`, and `if … then … else` Kronecker deltas, matching
   `additiveCharacter_orthogonal` and `haarBasis_orthonormal`; reuse `Function.update`
   for digit replacement as `stage` does.
