# OpenAI families 106 and 109 — reading notes and FDRS crossover

*Status: research notes, 2026-10-08. Nothing here is a claim of the corpus; items
enter `docs/fdrs.md` only when specified and proven. Source repository:
`github.com/openai/math`.*

| file | what |
|---|---|
| [`106-paper.md`](106-paper.md) | Agent reading of family 106, *Hardness of finding large independent sets in three-colorable graphs*, and its Lean formalization (`OAI/Combinatorics/IndependentSets/`, ~94k lines, no sorries). |
| [`109-paper.md`](109-paper.md) | Agent reading of family 109, *Integer multiplication below n log n* (paper only; no Lean). Displayed constants re-checked by exact computation. |
| [`106-fdrs-survey.md`](106-fdrs-survey.md) | Read-only survey of where FDRS touches 106's themes, with candidate items. |
| [`109-fdrs-survey.md`](109-fdrs-survey.md) | Read-only survey of where FDRS touches 109's themes, with candidate items. |

The two surveys were written independently and both number from Definition 218 /
Proposition 162 / Theorem 131 / Corollary 39; the numbers below are placeholders to
be reassigned when a section is written.

## The papers in one paragraph each

**106.** For every fixed `0 < δ < 1/3` it is NP-hard to distinguish three-colorable
graphs from graphs with independence ratio `< δ` (hence NP-hard to `c`-color
three-colorable graphs for every fixed `c`). Construction: Label Cover → layered
tuples → phase grids `(ℤ/D)^M` with zero-length pullback links and a half-shift
`T`; edges join points within `1/8` of each other's antipode. Completeness colors by
which third of the circle a phase lies in. Soundness: odd Lipschitz functions, a
dimension-free junta theorem, separated subchain lists, distributional alignment,
geometric coefficient levels. The Lean proves its junta theorem from scratch
(Bonami + dyadic discretization, not Austin) and replaces orthogonal Efron–Stein by
a refresh inequality, at the cost of a `4^J` factor.

**109.** One fixed multitape Turing machine multiplies `n`-bit integers in
`O(n (lg n)^{1−κ})`, `κ = 2^{−182}`. Chain: radix-digit convolution → CRT onto
distinct prime cyclic axes → Gaussian resampling with retained permutations →
Bluestein → negacyclic twist into `ℂ[y]/(y^r+1)` → synthetic transforms → signed
Kronecker packing → carries. New: two finite linear networks on 3-subsets of
`[100]` (an `F₂` one and a Gaussian-dyadic one) whose total sub-call rank `s` is
below `W·m`; recursion turns that deficit into a sub-linear-scan field interchange
(three shears) and simultaneous butterfly layers. The network fixes `1 − τ = 2^{−50}`;
`κ` comes from deliberately conservative `ε = 2^{−75}`, `c = 2^{−56}`. The same
network drives the companion every-length exact DFT in `o(n log n)` (family 130's
uniform version).

## Ranked crossover candidates

Ordered by (FDRS content) × (feasibility). Effort: S / M / L.

1. **Constant radix ⇔ multiplicative place values** (109 survey, Prop "162"). `B_i B_j
   = B_{i+j}` for all `i, j` iff `b` is constant. **S.** The multiplication twin of
   Prop 154: on a variable schedule, multiplication is not a digit convolution.
2. **Digit convolution + carries = product, constant radix** (109 survey, Thm "131",
   Cor "39"). Generalises `Field25519Carry.carryStep` to any `RadixSeq`; the
   boundary corollary for variable schedules. **M.**
3. **Vilenkin orthogonality, Plancherel, digit averaging `E_i`, influences**
   (106 survey, Def "218"–Thm "132"). `D_i(f)² = Σ_{σ_i≠0} |f̂(σ)|²`, Efron–Stein on
   `∏ ℤ/b_i`, Poincaré with constant 1; prefix projection `P_L = E_L ⋯ E_k`. Builds on
   `vilenkinKernel`, Haar bases, `finiteBlockProjection`. **M–L.**
4. **Half-shift parity** (106 survey, Prop "163", Cor "39"). On even schedules,
   `f ∘ h = −f` iff `f̂` lives on odd digit sums. **S–M.**
5. **Residue chart carries convolution** (109 survey, Prop "165"). Cyclic convolution
   of length `N` is `(k+1)`-dimensional convolution on the Vilenkin group under
   pairwise-coprime radices; convolution twin of Corollary 33. **M.**
6. **Negacyclic twist** (109 survey, Prop "164"). `w_j = ζ_{2r}^j` turns negacyclic
   into cyclic convolution. **S–M.**
7. **Digit-field interchange by three shears** (109 survey, Def "220"/Prop "163").
   `FiniteRadixSpace` position swap as shears plus a within-digit negation, with
   `dec(swap τ) = dec τ + (τ_j − τ_i)(B_i − B_j)`. **M.**
8. **Bilinear gate model and an exact convolution circuit** (109 survey, Def "219",
   Thm "132"). Product gate; `3|C| + M` gates for acyclic convolution from any exact
   Fourier circuit of length `M ≥ 2n − 1`. **L** (touches every builder lemma).
9. **Phase metric and thirds coloring; rational product laws** (106 survey,
   Def "219"/Prop "164", Def "220"/Prop "165"). **M** each; lower priority.

Out of scope: 106's junta theorem, Label Cover/PCP, alignment; 109's networks
themselves (`W ≈ 10^{21}` roles), bit-complexity accounting, resampling analysis.

## Corpus issues found by the surveys

- `FunctionSpaces/LocalOperators/DigitPermutation.lean`: the Lean for Proposition 35
  (`digitPermutation_commutation`) is vacuous — its conclusion is `f x = f x` by `rfl`.
- `Modes/VariableRadix/Realizability/Examples.lean:239`: `factorial_spaceSize` uses
  `native_decide`, against house rule.
- `AdditiveCharacters.lean` docstrings call orthogonality "Proposition 38"; the spec
  item is Proposition 41 (cosmetic; the index matches by line range).
