# Function-field complex — preparation (the FF series)

**Status:** design + verified ingredient survey. FF0 (the degree keystone) is **BUILT**
(`FdrsFormal/Modes/Adelic/FunctionFieldDegree.lean`, 0 sorries, axiom-clean). FF1–FF4 are
designs, not claims.

**Goal.** Fill the empty, correctly-typed slot left by `AdelicInterface.lean` §4:

```lean
def functionFieldAdelicLaw (q : ℕ) [Fact q.Prime] : AdelicLaw (FqtPlace q) (RatFunc (𝔽_q))ˣ
```

— the first *genuinely synthetic* instance of the abstract adelic law. On `ℚ` the
rigidity theorem (`Rigidity.lean`, machine-checked) closes the door: no synthetic
places exist; the classical family is forced. On a global function field `K = 𝔽_q(t)`
the places are monic irreducible polynomials plus the place at infinity — a different
global field with its own product formula, slotting into the *same* `AdelicLaw`
interface with no change to the abstraction.

---

## 1. The target, stated

Places of `𝔽_q(t)`:

- **Finite places**: monic irreducible `P ∈ 𝔽_q[X]`, with valuation `v_P(x)` and
  absolute value `|x|_P := q^{−v_P(x)·deg P}` (the residue field at `P` has size
  `q^{deg P}` — the "weight" of the place).
- **The place at infinity**: `v_∞(x) := −intDegree x = deg(denom) − deg(num)`, with
  `|x|_∞ := q^{intDegree x}`.

**Conservation** (the product formula): for `x ∈ 𝔽_q(t)ˣ`,

```
∏_v |x|_v = 1     ⟺     intDegree x = ∑_P v_P(x) · deg P          (additive form)
```

The additive form is `q`-free and generic over the coefficient field — it is pure
unique-factorization bookkeeping. **Prove the additive identity first; exponentiate
last** (design decision D5 below). For `x = f/g` in lowest terms the additive form
splits into the keystone applied to `f` and to `g` separately:

```
deg f − deg g = ∑_P (v_P(f) − v_P(g)) · deg P
```

and the keystone — `deg h = ∑_P v_P(h) · deg P` for `h ∈ K[X]`, `h ≠ 0` — **is now
proven** (FF0, `natDegree_eq_sum_polyValuation`). This is the function-field
`Nat.factorization_prod_pow_eq_self`: the fact the whole law bottoms out in.

---

## 2. Verified Mathlib ingredients (pinned revision; all names grep-confirmed)

| Ingredient | Mathlib name / location | Role |
|---|---|---|
| Rational function field | `RatFunc K` (`Mathlib.FieldTheory.RatFunc.*`) | the carrier `𝔽_q(t)` |
| num/denom in lowest terms | `RatFunc.num`, `RatFunc.denom`, **`RatFunc.isCoprime_num_denom`** (`RatFunc/Basic.lean:985`) | the FF analogue of `Rat.reduced` — drives the disjoint support split |
| Degree at infinity | `RatFunc.intDegree = natDegree num − natDegree denom`, with `intDegree_mul`, `intDegree_inv` (`FieldTheory/RatFunc/Degree.lean`) | `v_∞` |
| ∞-valuation (heavyweight) | `FunctionField.inftyValuation : Valuation (RatFunc Fq) ℤᵐ⁰` (`NumberTheory/FunctionField.lean:152`, `= exp ∘ intDegree`) | cross-check target; NOT imported by the lightweight route |
| Finite places (heavyweight) | `IsDedekindDomain.HeightOneSpectrum` + `adicValuation` (`RingTheory/DedekindDomain/AdicValuation.lean`) | the ideal-theoretic place set; NOT imported by the lightweight route |
| Ideal factorization (heavyweight keystone) | `finprod_heightOneSpectrum_factorization` (`DedekindDomain/Factorization.lean:192`) | the ideal-language analogue of FF0 |
| UFD factorization (lightweight) | `UniqueFactorizationMonoid.normalizedFactors`, `prod_normalizedFactors_eq`, `irreducible_of_normalized_factor` (`RingTheory/UniqueFactorizationDomain/NormalizedFactors.lean`) | **used by FF0** |
| Degree of a product | `Polynomial.natDegree_multiset_prod` (`Algebra/Polynomial/BigOperators.lean:333`) | **used by FF0** |
| Multiset → counted Finset sum | `Finset.sum_multiset_map_count` (`Algebra/BigOperators/Group/Finset/Basic.lean`) | **used by FF0** |
| Normalization is a constant | `Polynomial.coe_normUnit` (`FieldDivision.lean:222`), `natDegree_mul_C` (`Degree/Lemmas.lean:377`) | **used by FF0** |
| Coprime ⇒ no common prime divisor | `IsCoprime.isUnit_of_dvd'` | FF2's disjointness step (replaces `Nat.Coprime.disjoint_primeFactors`) |

**What is NOT in Mathlib** (as of the pinned revision): the function-field product
formula. `Height.AdmissibleAbsValues` (`NumberTheory/Height/Basic.lean`) packages
"family of absolute values satisfying a product formula", but `Height/Instances.lean`
provides **number fields only** — *"Fields of rational functions in `n` variables"* is
an explicit upstream **TODO**. So FF2/FF3 fill a slot that is empty in Mathlib too.
State this honestly: classical mathematics, machine-checked assembly — the first
such *in this corpus's ecosystem*, not new mathematics.

---

## 3. Design decisions (recorded with recommendations)

- **D1 — value type: exact `ℚ`, not `ℤᵐ⁰`.** `|x|_v = q^{±k}` as `ℚ`-zpow, matching
  `Place.absValue` and the no-floats discipline. Mathlib's `ℤᵐ⁰`-valued valuations are
  a cross-check target (an optional compatibility lemma against `inftyValuationDef`),
  not a dependency.
- **D2 — place type: FDRS-native inductive.**
  `FqtPlace q := infty | finite (P : {h : 𝔽_q[X] // h.Monic ∧ Irreducible h})`,
  mirroring `Place`. Over a field the `normalizedFactors` are monic irreducibles, so
  `polySupport` (FF0) lands exactly in the `finite` constructor's subtype. The
  heavyweight alternative (`HeightOneSpectrum 𝔽_q[X]`) is deliberately not used,
  exactly as M4a avoided `AdeleRing`.
- **D3 — carrier: `(RatFunc 𝔽_q)ˣ`**, mirroring `ratAdelicLaw : AdelicLaw Place ℚˣ`.
- **D4 — the split is `ProductFormulaRat.lean` with a dictionary.** The proof shape
  is *identical* to today's ℚˣ lift:

  | ℚˣ lift (`ProductFormulaRat.lean`) | FF2 (`𝔽_q(t)ˣ`) |
  |---|---|
  | `x.num`, `x.den` | `x.num`, `x.denom` (`RatFunc`) |
  | `Rat.reduced` (Nat.Coprime) | `RatFunc.isCoprime_num_denom` (IsCoprime) |
  | disjoint supports via `Nat.Coprime.disjoint_primeFactors` | disjoint `polySupport`s via `IsCoprime.isUnit_of_dvd'` + `Irreducible.not_isUnit` |
  | `padicNorm.div` per-prime split | `v_P(f/g) = v_P(f) − v_P(g)` (count arithmetic) |
  | `product_formula_nat` on num and den | FF0 keystone on `num` and `denom` |
  | `\|x\| = natAbs num / den` | `intDegree x = deg num − deg denom` (defn) |

- **D5 — additive first, exponential last.** FF2a proves the `ℤ`-valued degree
  identity; FF2b wraps it in `q^(·)` (one `zpow_add`/`zpow_sub` argument). All
  `q`-bookkeeping is confined to FF2b and FF3.

---

## 4. The engine half (FF4 — the genuinely FDRS-native part)

The law (FF1–FF3) is classical. The *machine* observations are where FDRS adds
something of its own:

- **Every place of `𝔽_q(t)` is non-Archimedean** — the place at infinity is just the
  `1/t`-adic place. So the engine story is *uniform*: every place runs the Hensel-shift
  ledger with a **congruence certificate**; there is no order trap, no four-corner
  floor, no `nlinarith` anywhere. The function-field complex is in this precise sense
  *simpler* than the `{∞, p}` complex on `ℚ`.
- **The ledger algebra is already payload-agnostic.** `PadicLedger`'s recurrences and
  the `det ↦ P·det` law are ring identities (`ring`-closed); a polynomial ledger over
  `𝔽_q[X]` with digits in the residue field `𝔽_q[X]/(P)` (a finite *field*, for every
  place) transfers the M0 layer verbatim. `ready`/`candidate` live in `𝔽_q[X]/(P)`
  exactly as they live in `ZMod p`.
- **The rigidity analogue.** The FDRS gauge aligned to the place `P` forces the
  constant base `q^{deg P}` (residue-field size) — `placeValue b L = (q^{deg P})^L`,
  the direct transplant of `isometric_iff`. Worth proving early in FF4: it is cheap
  (the `Rigidity.lean` proof is base-agnostic) and it pins the engine's boundary
  before any engine is built.
- **Scheduler confluence transfers for free**: `AdelicConfig`-style two-place (or
  finite-`S`) configurations over function-field engines commute by disjointness of
  state, exactly as in `Complex.lean` — nothing about that argument used `ℚ`.

---

## 5. Milestones

| ID | Content | Status |
|---|---|---|
| **FF0** | Degree keystone `deg h = ∑_P v_P(h)·deg P` (`FunctionFieldDegree.lean`) | ✅ **BUILT** (0 sorries, axiom-clean) |
| **FF1** | `FqtPlace`, `polyValuation` on `RatFunc` (num/denom difference, `ℤ`-valued), absolute values `\|·\|_v : RatFunc 𝔽_q → ℚ`, support | 🔨 design above |
| **FF2** | Product formula: (a) additive `intDegree x = ∑ v_P(x)·deg P`; (b) multiplicative `∏_v \|x\|_v = 1` | 🔨 proof = D4 dictionary |
| **FF3** | `functionFieldAdelicLaw : AdelicLaw (FqtPlace q) (RatFunc 𝔽_q)ˣ` | 🔨 mirrors `ratAdelicLaw` |
| **FF4** | Polynomial Hensel ledger + congruence certificate at a place `P`; rigidity analogue; (optional) two-place confluence | 🔬 open design; the FDRS-native payoff |

Order of attack: FF1 → FF2a → FF2b → FF3 are one arc (the ℚˣ-lift template); FF4 is
independent and can interleave.

---

## 6. Anti-confabulation ledger

1. **Do not claim Ostrowski for `𝔽_q(t)`.** Classifying *all* places of the function
   field is background mathematics; FF builds the classical family and its law, full
   stop. (Same discipline as `Rigidity.lean`'s "honest naming" note.)
2. **Do not call FF2 new mathematics.** It is the Artin–Whaples product formula for
   the simplest global function field — classical; the contribution is the
   machine-checked, lightweight, interface-shaped artifact (and, as of the pinned
   revision, its absence upstream).
3. **The ∞-place engine is not Gosper.** There is no continued-fraction/order engine
   anywhere in FF; the `1/t`-adic place runs the *Hensel* recurrence. Do not transplant
   `RemainderState`/`BihTensor` language into FF4.
4. **`q^{deg}` vs `deg` bookkeeping.** Every multiplicative statement must name its
   additive form; mismatched exponent conventions (`v_∞ = −intDegree`) are the one
   place this design can silently break. FF2b owns all exponentiation.
5. **FF0's `polyValuation` is defined on `K[X]`, not on `RatFunc`.** The `RatFunc`
   valuation (FF1) is the num/denom *difference* and is `ℤ`-valued; do not conflate
   the two when wiring FF2.
