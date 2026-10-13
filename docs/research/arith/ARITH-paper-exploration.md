# ARITH paper exploration: carry quotients and product coefficients on mixed-radix limb schedules

*Status: exploration, 2026-10-13. Companion to `reports/Carry theory novelty survey.md`.*

## 1. The problem with the original pitch

The novelty survey rated the three planned results as follows:

| Planned result | Survey verdict | Referee risk |
|---|---|---|
| Carry quotient ℤⁿ/carries ≅ ℤ/(B − c) | Known in parts. The soundness direction is machine-checked in fiat-crypto; the completeness direction is unstated but a two-line cokernel argument. | "Folklore" |
| Product coefficients κ(m,j) = B_m B_j / B_{m+j} | Known in substance. fiat-crypto's `place` computes κ without naming it; Crandall–Fagin hide it in their weights. | "fiat-crypto already does this" |
| Landing criterion gcd(ε·B_k, M) ∣ B_m B_j | Possibly novel, but a corollary of linear-congruence solvability. Only bites when the wrap gain shares primes with the radices, which never happens for prime fields. | "Trivial, and irrelevant to fields" |

As pitched, this is a weak ARITH paper: everything is either known or small.

## 2. What the exploration found: a sharper result

Exploring *which* schedules are product-closed, rather than taking the schedule as given, produced a clean characterization. It was checked by brute force over 30,617 product-closed schedules (`schedule_experiment.py`, N ≤ 8) and then proved in Lean (§3.23, `ChristoffelSchedule.lean`).

Take a power-of-two schedule for 2^q − c with N limbs. Its bit positions satisfy W₀ = 0 and W_{k+N} = W_k + q. The defect of a product is d(a,b) = W_a + W_b − W_{a+b}, and κ = 2^d.

- **Defect bounds (Thm 174).** If all defects lie in [0, δ], then qa ≤ N·W_a ≤ qa + (N−1)δ. Every product-closed schedule lies pointwise above ⌈qa/N⌉.
- **Christoffel optimality (Thm 175).** The schedules whose product coefficients are all 1 or 2 are exactly one schedule: the ceiling schedule W_a = ⌈qa/N⌉. Its limb widths are the Christoffel (balanced) word of slope q/N.
- **Why radix 2^25.5 (Cor 60).** The 25519 ladder 26, 25, 26, … is the unique 10-limb schedule of 2^255 whose schoolbook products need at most a doubling. The gains 2 and 38 are forced, not chosen.

The proof is three lines: periodicity gives W_{Na} = qa, non-negative defects give W_{Na} ≤ N·W_a, and bounded defects give W_{Na} ≥ N·W_a − (N−1)δ.

**Measured cost.** The number of doubled partial products in an N×N schoolbook multiplication on the ceiling schedule matched N²(b−1)/(2b) in every case tested, where b = N / gcd(q, N). This is observed, not yet proved.

| Modulus / limbs | Widths | Doubled products |
|---|---|---|
| 2²⁵⁵−19, 10 limbs (32-bit) | 25, 26 | 25/100 |
| 2²⁵⁵−19, 5 limbs (64-bit) | 51 | 0/25 |
| 2²⁵⁵−19, 9 / 11 / 12 limbs | 28–29 / 23–24 / 21–22 | 27/81, 55/121, 54/144 |
| 2¹³⁰−5 (Poly1305), 5 limbs | 26 | 0/25 |
| 2⁴⁴⁸ (Ed448), 8 / 16 limbs | 56 / 28 | 0 |
| 2⁵²¹−1, 9 limbs (64-bit) | 57, 58 | 36/81 |
| 2⁵²¹−1, 19 limbs (32-bit) | 27, 28 | 171/361 |

## 3. Revised paper thesis

**Working title:** *Product coefficients of mixed-radix limb schedules: a machine-checked theory, and why radix 2^25.5.*

Contributions, in order of strength:

1. **Christoffel optimality** (new as far as the survey found, proved in Lean). It gives a lower bound for all product-closed schedules and makes the ceiling schedule the unique minimum-defect schedule. This explains a design choice practitioners make by hand: Bernstein's radix 2^25.5, P-521 limb layouts, and fiat-crypto's synthesized weights.
2. **The cost law.** The ceiling schedule has N²(b−1)/(2b) doubled products. This is still to be proved; it gives a closed-form way to choose N for a given q and word size.
3. **Product coefficients on arbitrary (non-power-of-two) schedules.**
   - Product-closed iff, for every prime p, the p-adic valuation sequence of the place values has non-negative defects.
   - The ceiling result then applies prime by prime, covering mixed 2/3 schedules such as SIDH-style moduli 2^a·3^b − 1.
   - Both statements are still to be formalized.
4. **Carry quotient completeness (Thm 147).** Two limb vectors are equal mod B − c iff they differ by carry moves. This is the formal justification for reordering carries freely (vectorized and interleaved carry chains, as in Sandy2x/AVX2). Present it as a foundation, not as the headline.
5. **The landing criterion,** kept as a short remark for non-field moduli.
6. **Everything machine-checked in Lean 4/Mathlib,** positioned as complementary to fiat-crypto (Coq).

## 4. What still needs doing before submission

- **Literature check on the headline (critical).** Search for "unique schedule with κ ≤ 2", "Beatty/Christoffel/balanced word" together with "limb", "radix 2^25.5" and "unsaturated". Places to look:
  - fiat-crypto's synthesis notes and issues;
  - Granger–Scott and Granger–Moss;
  - the Crandall–Fagin full text, §6;
  - Berstel–Lauve–Reutenauer–Saliola, *Combinatorics on Words: Christoffel Words and Repetitions in Words*.

  The survey could not read several of these PDFs.
- **Prove the cost law** N²(b−1)/(2b), in Lean or on paper.
- **Formalize the valuation criterion** for arbitrary schedules (contribution 3).
- **Evaluation.** A small schedule-search tool (Rust, alongside `tools/carry-lattice`) that, for a given q and word size, lists product-closed schedules with defects, doubled-product counts and accumulator headroom, and reproduces the table above. An optional micro-benchmark of 9- vs 10- vs 11-limb 25519 would strengthen an ARITH submission.
- **Venue and dates.**
  - IEEE ARITH: 8 pages, IEEE format. The 2027 call has not been found yet.
  - Fallbacks: IEEE Transactions on Computers (journal), or a Lean-centred version at ITP 2027.

## 5. Risks

- The Christoffel result may be folklore among crypto implementers even if unpublished. The literature check above is the gate.
- The power-of-two case is the practically relevant one. The non-power-of-two generalization is mathematically nicer but practically niche, except possibly in RNS or decimal settings.
- ARITH values implementations. A purely theoretical submission needs the evaluation table and tool at minimum.

## 6. Files

- Lean: `FdrsFormal/Modes/SyntheticPlace/ChristoffelSchedule.lean` (§3.23); carry quotient in `CarryQuotient.lean` (§3.12); κ and product-closed rings in `MixedRingProduct.lean` (§3.13); landing criterion in `ProductSpread.lean` (§3.14).
- Experiment: `docs/research/arith/schedule_experiment.py`.
- Survey: `reports/Carry theory novelty survey.md` and `research_notes/Carry theory novelty survey/`.
