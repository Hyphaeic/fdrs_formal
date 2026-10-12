# Carry theory's novelty lives in packaging and proofs

**Most of the mathematics in this Lean 4 carry-theory development is known or is an elementary specialisation of known theory. The parts that look new are a few specific statements, a unifying framing, and the fact that it is a Lean/Mathlib formalization at all.** The carry quotient Z^n/carries ≅ Z/(B − c) is a two-line Smith-normal-form fact about a generalized Laplacian of a directed cycle. Its "soundness" half (carries preserve value mod B − c) is already machine-checked for arbitrary integer weights in fiat-crypto's Coq library. Mixed-radix multiplication mod B − c, the product coefficients κ(m,j) = B_m B_j / B_{m+j} and the 25519 gains 19/2/38 are known in substance from Crandall–Fagin, Bernstein and fiat-crypto. Gain-graph balance, potentials and derived covers are textbook (Zaslavsky; Gross–Tucker). The free/tied split is Fitting's lemma plus CRT, and both are already in Mathlib. Four things were not found anywhere in the literature searched:

- the landing criterion gcd(ε·B_k, M) | B_m B_j for non-product-closed schedules;
- the explicit gain-graph/holonomy/helix framing of carry networks;
- the "hop complex" construction with its canonical normal form;
- operation-spawned, payload-fed branches with a growth law.

All four are best called possibly novel. The first three are short corollaries of classical facts. The fourth rests on the shallowest search in the survey. On the formal side, nothing comparable was found in Lean: no generic limb/weight library, no mixed-radix digits in Mathlib, and no gain-graph formalization in any proof assistant. The most defensible publication is therefore a Lean library paper (ITP 2027, CPP 2028 or JAR), with a short computer-arithmetic note on the carry quotient and the landing criterion (IEEE ARITH) as a secondary target.

One caveat applies to every verdict. The research sandbox could not reach arxiv.org, ams.org, cr.yp.to, eprint.iacr.org, HAL, combinatorics.org, isa-afp.org or Wikipedia. Many primary sources were therefore checked only through search-engine snippets or from the researchers' recall. The sources that *were* read in full are fiat-crypto's `Core.v` and `ModOps.v` (GitHub master, fetched 2026-10-12) and the Mathlib checkout vendored in this repo (commit `79a359df`, 2026-01-14). Items resting on recall are flagged below and need checking against the PDFs before they appear in a paper.

## Summary table: eight items, four "possibly novel" kernels

| # | Item | Closest prior work | Verdict |
|---|------|-------------------|---------|
| 1 | Carry quotient Z^n/carries ≅ Z/(B − c); relation to sandpiles and pseudo-Mersenne | Critical groups / cokernels of diag(d) − A ([Alfaro–Valencia–Vázquez-Ávila, arXiv:1703.08621](https://arxiv.org/pdf/1703.08621); [Corrales–Valencia, LAA 2013, arXiv:1205.3105](https://arxiv.org/pdf/1205.3105)); chip-firing on invertible integer matrices ([Guzmán–Klivans, arXiv:1508.04262](https://arxiv.org/pdf/1508.04262)); fiat-crypto `eval_carry_reduce` / `eval_reduce` ([Core.v](https://github.com/mit-plv/fiat-crypto/blob/master/src/Arithmetic/Core.v)) | **Known in parts.** Soundness is known and verified. The full isomorphism follows directly from the cokernel framework but was not found stated for mixed radices with a general wrap gain. |
| 2 | Mixed-radix multiplication mod B − c, κ(m,j) = B_m B_j / B_{m+j}, gains 19/2/38 | [Crandall–Fagin, Math. Comp. 62 (1994) 305–324](https://www.ams.org/mcom/1994-62-205/S0025-5718-1994-1185244-1/) (IBDWT); [Erbsen et al., IEEE S&P 2019](https://adam.chlipala.net/papers/FiatCryptoSP19/FiatCryptoSP19.pdf) (`place`, `mulmod`); Bernstein's Curve25519 (2006); [Bajard–Imbert–Plantard AMNS](https://hal-lirmm.ccsd.cnrs.fr/lirmm-00109208/document); [Granger–Moss, arXiv:1108.3054](https://arxiv.org/pdf/1108.3054) | **Known.** The "product-closed" hypothesis as a named ring-level condition is a new *packaging* only. |
| 3 | Product-closed vs. non-product-closed schedules; landing criterion gcd(ε·B_k, M) \| B_m B_j | fiat-crypto `place`, which handles non-divisible weights only by exact fallback to a lower limb ([Core.v](https://github.com/mit-plv/fiat-crypto/blob/master/src/Arithmetic/Core.v)); the classical linear-congruence solvability theorem | **Possibly novel** (small lemma). |
| 4 | Carry networks as gain/voltage graphs; frustration = holonomy ≠ 1; derived cover as helix | Zaslavsky, "Biased graphs I", JCTB 47 (1989) ([bibliography home](https://people.math.binghamton.edu/zaslav/Bsg/index.html)); Gross, "Voltage graphs" (1974) and Gross–Tucker ([MathWorld](https://mathworld.wolfram.com/VoltageGraph.html)); exploding dots / fractional-base chip-firing ([arXiv:1809.09676](https://arxiv.org/abs/1809.09676)); arithmetical-graph currencies ([Asadi–Backman, arXiv:1012.0287](https://arxiv.org/pdf/1012.0287)) | **Known in parts.** The theorems are standard. The application to carries is possibly novel as a framing. |
| 5 | Free/tied split (Fitting), "rho" of place values, CRT idempotents | Hardy & Wright Thms 135–136 on pure/mixed recurring decimals ([scan](https://www.lamfa.u-picardie.fr/sorlin/HW4.pdf)); Fitting's lemma; Mathlib `LinearMap.eventually_isCompl_ker_pow_range_pow`, `ZMod.equivPi`, `CompleteOrthogonalIdempotents` | **Known**, with existing Mathlib support. |
| 6 | Hop complex: Z/M as a carry network with branch lines and hops; canonical normal form | RNS / mixed-radix conversion ([US 4,752,904](https://patents.google.com/patent/US4752904)); hybrid position-residue systems ([Bigou–Tisserand, ARITH-23](https://hal.archives-ouvertes.fr/hal-01314232); [HyPoRes, ARITH 2019](https://hal.sorbonne-universite.fr/hal-02337787v1)); chip-firing normal forms ([Guzmán–Klivans, arXiv:1403.1635](https://arxiv.org/pdf/1403.1635)); abelian networks ([Bond–Levine, arXiv:1309.3445](https://ar5iv.arxiv.org/html/1309.3445)) | **Known in parts.** The ingredients are standard. The specific construction is possibly novel and mathematically elementary. |
| 7 | Context-dependent radix laws, coupled branches fed by residue payloads, growth rules | Abstract numeration systems ([Lecomte–Rigo, cs/9903005](https://arxiv.org/pdf/cs/9903005)); G-odometers / Bratteli–Vershik ([Grabner–Liardet–Tichy, Acta Arith. 70 (1995)](https://impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/70/2/108520/odometers-and-systems-of-numeration)); rational-base trees ([Akiyama–Marsault–Sakarovitch, arXiv:1706.08266](https://arxiv.org/pdf/1706.08266)); ANS ([Duda, arXiv:1311.2540](https://ar5iv.arxiv.org/html/1311.2540)) | **Known in parts.** Context-dependent radices are known. Payload-driven branch spawning and the growth law are possibly novel, but on weak evidence. |
| 8 | Proof-assistant formalizations | fiat-crypto (Coq); HACL* (F*) ([arXiv:1703.00053](https://arxiv.org/pdf/1703.00053)); CryptoLine; Lean chip-firing ([arXiv:2606.16679](https://arxiv.org/pdf/2606.16679)); FFT in Coq/Isabelle ([Théry, arXiv:2210.05225](https://ar5iv.labs.arxiv.org/html/2210.05225); [AFP FFT](https://devel.isa-afp.org/entries/FFT.html)) | **Possibly novel as a Lean development.** fiat-crypto pre-empts the crypto-arithmetic content. |

## Items 1–3: the crypto literature proved the arithmetic, not the structure

### Item 1: the carry quotient is folklore-in-principle, but the completeness direction is unstated

The carry matrix is cyclic bidiagonal. It has −ρ_i on the diagonal, 1 on the subdiagonal, and the wrap gain c in the corner. Its determinant is ±(B − c). Deleting the first row and last column leaves a triangular minor equal to ±1. So the cokernel is cyclic of order |B − c|, and evaluation x ↦ Σ x_i B_i mod (B − c) is an explicit isomorphism.

This is precisely the cokernel of a generalized Laplacian diag(d) − A of a directed n-cycle with one weighted arc. That is the setting of critical groups and critical ideals ([arXiv:1703.08621](https://arxiv.org/pdf/1703.08621)), whose cycle case Corrales and Valencia treat ([arXiv:1205.3105](https://arxiv.org/pdf/1205.3105)). It is also the setting of Guzmán–Klivans chip-firing on arbitrary invertible integer matrices, where configuration classes are cosets of the lattice of firing moves ([arXiv:1508.04262](https://arxiv.org/pdf/1508.04262)). A negative wrap gain is a signed arc, covered by signed-graph chip-firing ([arXiv:2306.09315](https://arxiv.org/pdf/2306.09315)). Propp-style chip-firing on a line explicitly identifies firing with carrying in fractional bases, but it has no wrap and no quotient ([Chip-Firing and Fractional Bases](https://pubs.lib.umn.edu/index.php/mjum/article/download/4235/2906/19697)).

On the crypto side, fiat-crypto proves only the soundness half for arbitrary nonzero integer weights. `eval_carry` preserves `eval` exactly, and `eval_reduce` / `eval_carry_reduce` preserve value mod `s − eval c`. **No fiat-crypto lemma states that the kernel of evaluation equals the carry lattice** ([Core.v](https://github.com/mit-plv/fiat-crypto/blob/master/src/Arithmetic/Core.v)). Erbsen's S&P 2019 talk names "a weight w with w mod m = c" as the single idea behind pseudo-Mersenne, Solinas and mixed-radix reduction ([slides](https://www.ieee-security.org/TC/SP2019/SP19-Slides-pdfs/Andres_Erbsen_-_14-Andres_Erbsen-Simple_High-Level_Code_For_Cryptographic_Arithmetic_-_With_Proofs_Without_Compromises.pdf)). Hardware end-around carry (c = 1) and pseudo-Mersenne folding are the same congruence in circuit form ([Guyot lecture notes](https://www.ece.ucdavis.edu/~vojin/CLASSES/EPFL/Lectures/Guyot/english/Modulo.htm)).

**Verdict: known in parts.** A critical-group specialist would call the isomorphism routine. The citable contribution is the explicit identification of positional carry arithmetic with this cokernel, together with a machine-checked proof of both directions. One gap remains: the researchers could not read Corrales–Valencia §4, so it is unconfirmed whether a *directed* cycle with a weighted arc is treated explicitly there.

### Item 2: mixed-radix multiplication and the 19/2/38 gains are known in substance

Crandall and Fagin's irrational-base DWT represents residues mod 2^q − 1 as Σ x_j 2^{⌈qj/N⌉}, with weights a_j = 2^{⌈qj/N⌉ − qj/N} ([Math. Comp. 1994](https://www.ams.org/mcom/1994-62-205/S0025-5718-1994-1185244-1/); [IBDWT summary](https://en.wikipedia.org/wiki/Irrational_base_discrete_weighted_transform)). These weights absorb exactly the coefficients κ(m,j) ∈ {1, 2}, because a_m a_j / a_{m+j} = 2^{⌈qm/N⌉ + ⌈qj/N⌉ − ⌈q(m+j)/N⌉}. So **κ is implicit in Crandall–Fagin for c = 1**. The recalled-but-unverified reading is that their general DWT gives convolution mod X^N − A only for A = ±1, not for a gain such as 19.

fiat-crypto's `Positional.place` computes exactly `fst t / weight i`. With fst t = B_m B_j and i = m + j, that is κ(m,j), so fiat-crypto *computes* the coefficient without *stating* it as a theorem. `eval_mulmod` holds for any nonzero integer weights. The code generator, however, uses only the power-of-two weights 2^{⌈(num/den)·i⌉} ([ModOps.v](https://github.com/mit-plv/fiat-crypto/blob/master/src/Arithmetic/ModOps.v)).

The 25519 rule is standard implementation knowledge: ×19 on wrap, ×2 when both limb indices are odd, hence 38. It appears in Chou's Sandy2x ([ePrint 2015/943](https://eprint.iacr.org/2015/943.pdf)), it is the radix-2^25.5 code fiat-crypto ships in BoringSSL ([README](https://boringssl.googlesource.com/boringssl.git/+show/9770532afa91dd1441ba0d3e9d4bb86d7e501f19/third_party/fiat/README.md)), and it originates in Bernstein's PKC 2006 paper ([cr.yp.to](https://cr.yp.to/ecdh/curve25519-20060209.pdf)). The Bernstein attribution and its ref10 details are recalled, not re-read.

The polynomial view of multiplication mod X^n − λ, evaluated at γ, is Bajard–Imbert–Plantard's AMNS ([HAL](https://hal-lirmm.ccsd.cnrs.fr/lirmm-00109208/document); [PMNS, arXiv:2001.03741](https://arxiv.org/pdf/2001.03741)). AMNS is positioned against Chung–Hasan's "more generalized Mersenne numbers". Crucially, AMNS uses a uniform evaluation point, so all κ = 1. Granger and Moss revisit generalized Mersenne numbers through cyclotomic primes ([arXiv:1108.3054](https://arxiv.org/pdf/1108.3054)).

**Verdict: known.** The closed form κ(m,j) on an arbitrary product-closed (including non-power-of-two) schedule is a clean generalization. It should be framed as a generalization and formalization, not as a discovery.

### Item 3: the landing criterion is the most plausibly new mathematical statement

No source studies mixed-radix wrap-around multiplication where B_{m+j} ∤ B_m B_j. fiat-crypto stays correct on such schedules only by exact placement: a misaligned term falls to a lower limb with a larger coefficient, ultimately to limb 0. `split s` wraps a term only when s divides its weight ([Core.v](https://github.com/mit-plv/fiat-crypto/blob/master/src/Arithmetic/Core.v)). fiat-crypto never lands a term "modulo B − c" by using invertibility of ε·B_k. The practical schedules 2^{⌈qj/N⌉} are always product-closed, since ⌈a⌉ + ⌈b⌉ ≥ ⌈a + b⌉.

The criterion is the standard fact that a·x ≡ b (mod m) is solvable iff gcd(a, m) | b, applied to limb placement. The corollary is that a wrap gain making every ε·B_k invertible mod M makes every schedule "residue-closed".

**Verdict: possibly novel, but small.** Present it as a useful lemma. One practical caveat: Granger–Scott's F_{2^521−1} representation is recalled to use t^9 = 2^522 ≡ 2 (mod p), which gives B − c = 2p ([Springer](https://link.springer.com/content/pdf/10.1007/978-3-662-46447-2_24.pdf)); this was not verified. If it holds, deployed systems work mod a proper divisor of B − c, a case the criterion as stated does not cover.

## Items 4–5: standard theorems wearing new clothes

### Item 4: the gain-graph framing is new, the theorems under it are not

The project's "a consistent place-value weighting exists iff every cycle has ratio product 1" is Zaslavsky's balance–potential equivalence specialised to the gain group (Q_{>0}, ·). Balance is invariant under switching, and it suffices to check a fundamental system of cycles. These statements are restated from Zaslavsky (1989) in [arXiv:1812.03747](https://arxiv.org/pdf/1812.03747). In the ±1 case the equivalence is Harary's signed-graph balance theorem.

The "helix" is the standard lift of a cycle to the derived graph of a voltage graph ([MathWorld: Voltage Graph](https://mathworld.wolfram.com/VoltageGraph.html); [Derived Graph](https://mathworld.wolfram.com/DerivedGraph.html)). When the net voltage has infinite order, as any holonomy ≠ 1 in Q_{>0} does, the lift is a two-way infinite path. The recalled Gross–Tucker theorem numbering is unverified, and MathWorld and Wikipedia disagree on authorship of the 1977 covering paper.

Three neighbouring literatures come close without using balance, holonomy or covers. Exploding dots and fractional-base chip-firing make "ρ units become 1 unit next door" literal ([Tanton](https://gdaymath.com/lessons/explodingdots/9-2-base-one-half/); [arXiv:1809.09676](https://arxiv.org/abs/1809.09676)). Asadi–Backman give each vertex its own "currency" with an integer exchange rate ([arXiv:1012.0287](https://arxiv.org/pdf/1012.0287)). Odometers on numeration scales describe carry trees ([Barat et al., Colloq. Math.](https://impan.pl/pl/wydawnictwa/czasopisma-i-serie-wydawnicze/colloquium-mathematicum/all/84/2/111615/proprietes-topologiques-et-combinatoires-des-echelles-de-numeration)).

**Verdict: known in parts.** The unification (carry network = positive-ratio gain graph, frustration = unbalanced ring, periodic mixed radix = derived-cover sheet) was not found. The single most important unfinished check is a manual search of Zaslavsky's DS8 bibliography ([2018 PDF](https://www.combinatorics.org/files/Surveys/ds8/ds8v9-2018.pdf)) for "carry", "radix", "numeration" or "odometer". It could not be downloaded. The same theorem also appears as arbitrage-free exchange rates and as consistent AHP matrices, so a referee may see the framing as a relabelling.

### Item 5: the free/tied split is Fitting + CRT, already in Mathlib

The eventually periodic "rho" of B_k mod M is Hardy & Wright's pure/mixed recurring-decimal theorem transposed from 1/q to place values ([H&W Ch. IX](https://www.lamfa.u-picardie.fr/sorlin/HW4.pdf)). The tail comes from the primes shared with the base, and the period is the order of the base on the coprime part. Fitting's lemma gives Z/M = ker(c^n) ⊕ im(c^n), which here is Z/T ⊕ Z/F. Mathlib already has the following:

- the Fitting decomposition, `LinearMap.eventually_isCompl_ker_pow_range_pow` ([Artinian/Module.lean L338](https://github.com/leanprover-community/mathlib4/blob/79a359dfe4682c5ca375c39522d7c64e95659d5a/Mathlib/RingTheory/Artinian/Module.lean#L338));
- the p-part and p-coprime-part notations `ordProj` / `ordCompl` ([Factorization/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/79a359dfe4682c5ca375c39522d7c64e95659d5a/Mathlib/Data/Nat/Factorization/Defs.lean#L262));
- the CRT isomorphisms `ZMod.chineseRemainder` and `ZMod.equivPi` ([QuotientRing.lean](https://github.com/leanprover-community/mathlib4/blob/79a359dfe4682c5ca375c39522d7c64e95659d5a/Mathlib/Data/ZMod/QuotientRing.lean));
- `CompleteOrthogonalIdempotents` ([Idempotents.lean](https://github.com/leanprover-community/mathlib4/blob/79a359dfe4682c5ca375c39522d7c64e95659d5a/Mathlib/RingTheory/Idempotents.lean)).

The "forced free part" is unique factorization into a c-smooth and a c-coprime part. **Verdict: known.** The development should build on these Mathlib lemmas rather than claim them. The recalled general-base preperiod formula, max_{p | c} ⌈v_p(q)/v_p(c)⌉, and the H&W Thm 136 wording need checking before citation.

## Items 6–7: the constructions with the thinnest prior art

### Item 6: the hop complex inverts known hybrid layering

The ingredients of the hop complex are each standard:

- RNS and residue-to-mixed-radix conversion ([US 4,752,904](https://patents.google.com/patent/US4752904); Garner 1959, whose venue and pages are inconsistent across reference lists, e.g. [arXiv:2605.18415](https://arxiv.org/pdf/2605.18415));
- prime-power RNS channels stored as binary strings ([LSU thesis](https://repository.lsu.edu/gradschool_theses/1242));
- hybrid position-residue systems ([Bigou–Tisserand, ARITH-23](https://hal.archives-ouvertes.fr/hal-01314232); [HyPoRes](https://hal.sorbonne-universite.fr/hal-02337787v1)).

The known hybrids put positional digits outside and RNS inside. The hop complex inverts that layering and, more distinctively, **splits the modulus by the wrap gain** (the Fitting split) rather than by hardware-friendly moduli. No source was found that does this or that presents Z/M as states modulo carry and hop moves.

Structurally, "states modulo moves" is a chip-firing cokernel. Unique representatives per class are known there: Gabrielov's critical configurations, and Guzmán–Klivans energy minimizers on M-matrices ([arXiv:1403.1635](https://arxiv.org/pdf/1403.1635)). Bond–Levine abelian networks generalize the critical group further ([arXiv:1409.0170](https://www.arxiv.org/pdf/1409.0170)). Isaksen's carry-as-2-cocycle viewpoint is a further cousin ([Swenberg, "The carrying cocycle"](https://www.math.ucla.edu/~jaswenberg/CarryingCocycle.pdf)). A hop removes ε_i units at the ring root and adds one unit at a branch root. Hops are not topplings, so the M-matrix theorems probably do not apply verbatim. The researchers also found no analogue of "return to a sheet only via a hop".

The exactly-sized-branch normal form is ordinary mixed-radix uniqueness. The dead-cell criterion (T_i divides the place value) is p-adic truncation overflow. **Verdict: known in parts.** The construction is possibly novel as a packaged, formalized statement, but it is mathematically elementary.

### Item 7: adaptive radices are mature, typed payload-fed branches are not

Prefix- or state-dependent radices are well studied. Examples are abstract numeration systems on regular languages ([Lecomte–Rigo](https://arxiv.org/pdf/cs/9903005); [Rigo, TCS 2001](https://orbi.uliege.be/handle/2268/15868)), G-odometers and Bratteli–Vershik systems ([Grabner–Liardet–Tichy](https://impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/70/2/108520/odometers-and-systems-of-numeration); [arXiv:2101.00868](https://arxiv.org/pdf/2101.00868)), Cantor real bases ([Res. Number Theory](https://link.springer.com/10.1007/s40993-024-00542-5)) and rational-base representation trees ([arXiv:1706.08266](https://arxiv.org/pdf/1706.08266)). Asymmetric numeral systems make the effective radix depend on a probability model ([Duda](https://arxiv.org/abs/0902.0271v2)).

A Bratteli diagram with vertex-dependent edge counts already is "a mixed-radix counter whose next radix depends on the prefix". What was not found is branches **spawned by operations**, **typed by CRT components**, **fed by a carry-invariant residue payload**, and growing by an exact law. **Verdict: known in parts.** The concept is known, and the coupled-branch mechanism is possibly novel. This is the weakest search in the survey: lazy exact reals, on-demand precision, redundant/carry-save representations and the content of US 7,650,372 ([patent](https://image-ppubs.uspto.gov/dirsearch-public/print/downloadPdf/7650372)) were not checked. Do not claim novelty here until that follow-up is done.

## Item 8: no Lean counterpart exists, but fiat-crypto sets the bar

fiat-crypto's `Arithmetic` library is the decisive formal prior art ([repo](https://github.com/mit-plv/fiat-crypto)). It is generic over divisibility-chain weights and supports list-valued (multi-term) gains c. It proves carry preservation, Solinas reduction and `mulmod` correctness, and it is deployed in BoringSSL and in the Linux kernel's 32-bit Curve25519 ([LKML](https://lkml.iu.edu/hypermail/linux/kernel/1903.2/05625.html)).

The other verified 25519 work proves implementation correctness for fixed radices, not a theory of carries. This includes HACL* in F* ([arXiv:1703.00053](https://arxiv.org/pdf/1703.00053)), the SMT-based "Verifying Curve25519 Software" ([CCS 2014](https://www.cryptojedi.org/papers/verify25519-20140428.pdf)) and the CryptoLine line ([ASE 2019](https://troll.iis.sinica.edu.tw/by-publ/recent/verify-llvm.pdf)). Lean crypto work, SymCrypt via Aeneas ([arXiv:2609.15648](https://arxiv.org/pdf/2609.15648)) and AMO-Lean ([Reservoir](https://reservoir.lean-lang.org/@manuelpuebla/amo-lean)), targets ML-KEM, SHA-3 and NTT code.

The vendored Mathlib was searched by grep. It has only fixed-base `Nat.digits` ([Digits/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/79a359dfe4682c5ca375c39522d7c64e95659d5a/Mathlib/Data/Nat/Digits/Defs.lean)). It has nothing on mixed radix, factoradic, chip-firing, sandpiles or gain graphs, and its `ZMod.dft` has no fast factorization ([Fourier/ZMod.lean](https://github.com/leanprover-community/mathlib4/blob/79a359dfe4682c5ca375c39522d7c64e95659d5a/Mathlib/Analysis/Fourier/ZMod.lean)). The nearest Lean neighbour is a June 2026 chip-firing/Riemann–Roch formalization ([arXiv:2606.16679](https://arxiv.org/pdf/2606.16679)), which must be cited; its contents were not read.

FFT formalizations exist for radix-2 Cooley–Tukey: Capretta in Coq ([TPHOLs 2001](https://unpaywall.org/10.1007%2F3-540-44755-5_12)), Théry in Coq ([arXiv:2210.05225](https://ar5iv.labs.arxiv.org/html/2210.05225)), Ballarin in Isabelle ([AFP](https://devel.isa-afp.org/entries/FFT.html)), plus an Isabelle NTT entry ([AFP NTT](https://www.isa-afp.org/browser_info/current/AFP/Number_Theoretic_Transform/document.pdf)) and an F* NTT ([MIT thesis](https://dspace.mit.edu/handle/1721.1/157189)). **No formalization of Good–Thomas, Rader, Bluestein or general mixed-radix Cooley–Tukey was found.**

**Verdict: possibly novel as a Lean development.** That novelty is real but bounded. Unchecked: whether Mathlib's `finPiFinEquiv` already gives a mixed-radix `Fin` bijection, fiat-crypto's `Freeze.v` canonicalization lemmas, Jasmin/EasyCrypt and Bedrock2, and an AFP search for RNS or positional notation.

## Conclusion

The honest position is that this body of work **re-derives known arithmetic in a new and more structural language, and formalizes it in a proof assistant where nothing comparable exists**. It does not open a new branch of mathematics. Its genuine intellectual additions are narrow:

- the completeness direction of the carry quotient, packaged as an explicit isomorphism;
- the landing criterion and residue-closedness for non-product-closed schedules;
- the gain-graph/holonomy view that makes "frustrated ring unrolls to a periodic helix" a single picture covering end-around carry, pseudo-Mersenne folding and periodic mixed radix;
- the hop-complex and branch-growth constructions, pending a deeper search.

A referee from chip-firing would call item 1 folklore. A referee from cryptographic engineering would point to fiat-crypto for item 2. A referee from combinatorics would call item 4 a relabelling of Zaslavsky. The work survives those objections only if it is framed as a unifying, machine-checked theory rather than as new theorems.

The most plausibly publishable contributions are the following.

- **A Lean library paper.** The pitch is "a Mathlib-integrated theory of carries: quotients, gain graphs, Fitting/CRT normal forms, and mixed-radix FFTs". The target is ITP 2027 (deadline expected around February 2027), CPP 2028 or JAR/LMCS. CPP 2027's September 2026 deadline has passed ([CPP 2027](https://popl27.sigplan.org/home/CPP-2027)).
- **Mathlib PRs.** Candidates are mixed-radix digits, the carry-lattice quotient, and FFT factorizations of `ZMod.dft`. These build credibility and are likely welcome.
- **A short computer-arithmetic note.** It would cover the carry-quotient isomorphism, κ on arbitrary schedules and the landing criterion, for IEEE ARITH. ARITH lists number systems and cryptography as topics and uses 8-page papers ([ARITH 2026 CFP](https://lists.mcs.anl.gov/pipermail/hpc-announce/2025-December/011658.html)). IEEE Transactions on Computers is the journal alternative.
- **The gain-graph and branch-growth material**, once DS8 and the adaptive-representation literature have been checked. This would suit an arXiv math.CO/cs.DM note aimed at the Electronic Journal of Combinatorics or Integers. These journal-fit judgements are the researchers' own, since the journals' scope statements were not fetched.

TCHES and CHES are a poor fit without an implementation or a verified-code-generation result.
