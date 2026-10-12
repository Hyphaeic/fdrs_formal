# Existing proof-assistant formalizations related to FDRS (mixed-radix / multi-limb modular arithmetic, carries, CRT, FFT) and plausible publication venues

Research date: 2026-10-12. Method: web search (several primary hosts, including arxiv.org and isa-afp.org, were unreachable from this sandbox, so some entries rely on search-result snippets); direct reading of fiat-crypto Coq sources downloaded from GitHub (`src/Arithmetic/Core.v`, `src/Arithmetic/ModOps.v`, master branch); and direct grep of the Mathlib checkout vendored in this repo (`.lake/packages/mathlib`, commit `79a359dfe4682c5ca375c39522d7c64e95659d5a`, dated 2026-01-14). Mathlib links below are pinned to that commit.

## Q1. fiat-crypto (Coq): what does its Arithmetic library prove, and is it generic over arbitrary weight functions / non-power-of-two radices?

### Takeaway
fiat-crypto already has a machine-checked, generic multi-limb arithmetic library. It covers lists of (weight, coefficient) pairs ("Associational"), positional representations over an abstract weight function `weight : nat -> Z`, carrying, the Solinas/pseudo-Mersenne reduction rule `(a + s*b) mod (s - c) = (a + c*b) mod (s - c)`, `mulmod`, and `carry_reduce`. Its concrete weight `2^ceil(limbwidth*i)` with rational limbwidth covers radix 2^25.5. So FDRS's Curve25519 limb-multiplication results and its "wrap gain c" evaluation identities are not new in substance. They are new only as Lean/Mathlib developments, and possibly in their algebraic packaging: a group/ring isomorphism Z^n/carries ≅ Z/(B−c) rather than "eval ... mod (s − c) = ...".

### Cited Findings
- `Associational.eval` evaluates a `list (Z*Z)` of (weight, coefficient) pairs with arbitrary integer weights. `Associational.reduce s c p` splits off the terms whose weight is divisible by `s` and multiplies them by `c`. The lemma `eval_reduce` states `eval (reduce s c p) mod (s - eval c) = eval p mod (s - eval c)`, based on `reduction_rule : (a + s * b) mod (s - c) = (a + c * b) mod (s - c)`. This is the "wrap gain" identity: modulus s − c, gain c. — [fiat-crypto src/Arithmetic/Core.v](https://github.com/mit-plv/fiat-crypto/blob/master/src/Arithmetic/Core.v)
- Core.v also defines `carryterm`/`carry (w fw)` with `eval_carry`, `split_one`/`reduce_one`, `splitQ` with rational split points, and `reduce_square`. Each comes with an evaluation-preservation lemma. — [Core.v](https://github.com/mit-plv/fiat-crypto/blob/master/src/Arithmetic/Core.v)
- The weight hypotheses are the class fields `weight_0 : weight 0 = 1`, `weight_positive : forall i, 0 < weight i`, `weight_multiples : forall i, weight (S i) mod weight i = 0`, and `weight_divides : forall i, 0 < weight (S i) / weight i`. Any divisibility chain of weights qualifies, which is an arbitrary mixed radix and need not be a power of two. Derived lemmas include `weight_multiples_full` and `weight_divides_full`. — [Core.v (lines ~643–676)](https://github.com/mit-plv/fiat-crypto/blob/master/src/Arithmetic/Core.v)
- `Positional.mulmod n a b` goes to associational form, multiplies, applies `repeat_reduce n s c`, and converts back to positional form. `eval_mulmod` states `eval n (mulmod n f g) mod (s - Associational.eval c) = (eval n f * eval n g) mod (s - Associational.eval c)`. The proof uses only `weight_0` and `weight_nz` (nonzero weights). `carry_reduce` and `eval_carry_reduce` are analogous. — [Core.v (lines ~920–995)](https://github.com/mit-plv/fiat-crypto/blob/master/src/Arithmetic/Core.v)
- The concrete weight used for code generation is `weight i := 2^(-(-(limbwidth_num * i) / limbwidth_den))`, proved equal to `2^Qceiling(limbwidth*i)` with rational limbwidth. It is instantiated as a `weight_properties` instance (`wprops`). — [fiat-crypto src/Arithmetic/ModOps.v](https://github.com/mit-plv/fiat-crypto/blob/master/src/Arithmetic/ModOps.v)
- fiat-crypto's generated 32-bit Curve25519 code uses "10 limbs of radix 2^25.5" in BoringSSL, and its unsaturated-Solinas strategy is used in production. — [BoringSSL third_party/fiat README](https://boringssl.googlesource.com/boringssl/+show/bb3a456930f731563c7dfbd08656d1dff767e6d0/third_party/fiat/README.md)
- The S&P 2019 talk (Erbsen, "Simple High-Level Code for Cryptographic Arithmetic – With Proofs, Without Compromises") presents one shared approach to pseudo-Mersenne, Solinas, and mixed-radix reduction, based on a weight w with w mod m = c. — [IEEE S&P 2019 slides](https://www.ieee-security.org/TC/SP2019/SP19-Slides-pdfs/Andres_Erbsen_-_14-Andres_Erbsen-Simple_High-Level_Code_For_Cryptographic_Arithmetic_-_With_Proofs_Without_Compromises.pdf)
- Citation: A. Erbsen, J. Philipoom, J. Gross, R. Sloan, A. Chlipala, "Simple High-Level Code for Cryptographic Arithmetic – With Proofs, Without Compromises," IEEE S&P 2019. — [slides above](https://www.ieee-security.org/TC/SP2019/SP19-Slides-pdfs/Andres_Erbsen_-_14-Andres_Erbsen-Simple_High-Level_Code_For_Cryptographic_Arithmetic_-_With_Proofs_Without_Compromises.pdf); repo [mit-plv/fiat-crypto](https://github.com/mit-plv/fiat-crypto)

### Inferences
- Compared with the FDRS feature list, fiat-crypto already proves the following:
  - Mixed-radix positional evaluation with an arbitrary divisibility-chain weight.
  - Carries that preserve evaluation (the "conservation law" `eval_carry`).
  - The wrap/Solinas rule with gain c, including a list c of several (weight, gain) terms, which is more general than a single gain.
  - Correct multi-limb modular multiplication for radix 2^25.5. Its gains 19 and 38 arise from `c = [(1,19)]` plus the doubled odd-limb products in the half-integer radix.

  FDRS's Curve25519 multiplication theorem is therefore a re-proof in Lean and is not novel in content. A paper should cite fiat-crypto as the main prior art.
- fiat-crypto states its results as congruences of evaluations mod (s − eval c). They do not appear as algebraic structure theorems: quotient of Z^n by the carry lattice ≅ Z/(B − c), digit bijections or normal forms, gain-graph holonomy covers. I did not grep the whole repo for such statements, so this is an inference from the files read.
- FDRS's "mixed (weight-function) convolution" matches fiat-crypto's `Associational.mul` plus `reduce` in spirit. Novelty claims should focus on the lattice/quotient view, uniqueness of digit normal forms, and integration with Mathlib (ZMod, ideals, AddSubgroup quotients).

### Gaps
- I could not open the S&P 2019 paper PDF (host unreachable). Exact paper wording about "mixed radix" and the paper's own definitions are taken from the slides and source code only.
- I did not check whether fiat-crypto has a uniqueness or bijection theorem for canonical digit representations (e.g., `freeze`/canonicalization lemmas in `src/Arithmetic/Freeze.v`). A follow-up should grep `Freeze.v`, `Saturated*.v`, and `MontgomeryReduction` files.

## Q2. HACL*/Vale/EverCrypt (F*), Jasmin/EasyCrypt, CryptoLine, Bedrock2, Isabelle Curve25519: what overlaps?

### Takeaway
Several verified Curve25519 field-arithmetic developments exist (F*/HACL*, SMT/Boolector, CryptoLine/CoqCryptoLine). All of them target implementation correctness of specific radices such as 2^51 and 2^25.5. None is a general algebraic theory of carries or mixed radix. Lean work in this space (SymCrypt via Aeneas, AMO-Lean) targets ML-KEM/SHA-3/NTT code, not a carry/numeration theory.

### Cited Findings
- HACL* is a Low*/F* library implementing the NaCl API (Curve25519, ChaCha20, Salsa20, Poly1305) with memory safety, functional correctness, and side-channel resistance proven. The same paper cites Zinzindohoué et al. (2016) as an earlier F*-verified library of three curves including Curve25519. — [Protzenko et al., "Verified Low-Level Programming Embedded in F*", arXiv:1703.00053](https://arxiv.org/pdf/1703.00053)
- HACL* ships a 51-bit-limb Curve25519 variant (`Hacl_Curve25519_51`) in Firefox/NSS. — [searchfox NSS](https://arai.searchfox.org/firefox-main/source/security/nss/lib/freebl/verified/internal/Hacl_Curve25519_51.h)
- In the Linux kernel's WireGuard/Zinc Curve25519, the 64-bit version comes from HACL* and the 32-bit version from Fiat. — [LKML zinc patch](https://lkml.iu.edu/hypermail/linux/kernel/1903.2/05625.html)
- "Verifying Curve25519 Software" (Chen, Hsu, Lin, Schwabe, Tsai, Wang, B.-Y. Yang, S.-Y. Yang, CCS 2014) verifies hand-optimized assembly with Boolector (SMT). It notes that modular-multiplication correctness is the hard part. — [paper PDF](https://www.cryptojedi.org/papers/verify25519-20140428.pdf)
- "Verifying Arithmetic in Cryptographic C Programs" (Liu, Shi, Tsai, Wang, Yang, ASE 2019) verifies OpenSSL arithmetic for P-224, P-256, P-521, and Curve25519. — [PDF](https://troll.iis.sinica.edu.tw/by-publ/recent/verify-llvm.pdf)
- The CryptoLine line of work includes "Signed Cryptographic Program Verification with Typed CryptoLine" (CCS 2019) and "CoqCryptoLine: A Verified Model Checker with Certified Results" (CAV 2023). — [dblp: Bow-Yaw Wang](https://dblp.dagstuhl.de/pers/hj55/w/Wang:Bow=Yaw)
- Microsoft's SymCrypt team verifies Rust cryptography (ML-KEM, SHA-3) in Lean via Aeneas. A 2026 arXiv paper reports a 237 KLOC Lean development proving safety, panic-freedom, and functional correctness of 16.7 KLOC of Rust. — [arXiv:2609.15648](https://arxiv.org/pdf/2609.15648); [MSR blog](https://www.microsoft.com/en-us/research/blog/verifying-rust-cryptography-in-symcrypt-from-standards-to-code)
- Cryspen verified libcrux ML-KEM using hax and F* (not Lean). — [Cryspen post](https://cryspen.com/post/ml-kem-verification/)
- AMO-Lean is a Lean 4 project that compiles Lean specifications to optimized C/Rust with correctness guarantees. It covers the NTT among other primitives and lists fiat-crypto as related work. — [Reservoir: AMO-Lean](https://reservoir.lean-lang.org/@manuelpuebla/amo-lean)

### Inferences
- These tools prove implementation-level correctness (code matches a mod-p spec). FDRS proves structural mathematics (place values, carry quotients, holonomy covers). FDRS should position itself as complementary: a mathematical theory layer that could in principle serve as a specification library for Lean-based crypto verification (Aeneas/SymCrypt, AMO-Lean).
- In Lean, I found no existing generic multi-limb/weight-function arithmetic library comparable to fiat-crypto's `Arithmetic`. FDRS appears to be the first Lean/Mathlib library of this kind, but see Gaps.

### Gaps
- Jasmin/EasyCrypt (Almeida et al.) and Bedrock2 Curve25519 developments were not researched within the tool budget. I found no source on whether they contain generic weight-function theory. My recollection is that they reuse fiat-crypto-style specs or concrete radix-2^51 specs, but this is unverified.
- No search result confirmed a "Verified Curve25519 in Isabelle" development. I did not find one.
- I did not inspect the Lean sources of SymCrypt/Aeneas or AMO-Lean for any mixed-radix/limb lemmas. They could contain Lean limb-arithmetic lemmas, likely radix-2^k and specific to the implementation.

## Q3. Lean 4 Mathlib: CRT, digits, mixed radix, Fitting decomposition, idempotents, DFT; chip-firing and gain graphs in proof assistants

### Takeaway
Mathlib (Jan 2026) has rich CRT infrastructure, including the full prime-power decomposition `ZMod.equivPi`. It also has complete orthogonal idempotents, a Fitting-type decomposition, and a finite DFT on `ZMod N` with no FFT factorization. Mathlib's only digit expansion is fixed-base (`Nat.digits`/`Nat.ofDigits`). There is no mixed-radix, factorial-base, carry-network, chip-firing, or gain-graph material in Mathlib. A June 2026 Lean 4 chip-firing/Riemann–Roch-for-graphs project exists outside Mathlib.

### Cited Findings
- `ZMod.chineseRemainder {m n} (h : m.Coprime n) : ZMod (m * n) ≃+* ZMod m × ZMod n`. — [Mathlib/Data/ZMod/Basic.lean L874](https://github.com/leanprover-community/mathlib4/blob/79a359dfe4682c5ca375c39522d7c64e95659d5a/Mathlib/Data/ZMod/Basic.lean)
- `ZMod.prodEquivPi (a : ι → ℕ) (coprime : Pairwise (Nat.Coprime on a)) : ZMod (∏ i, a i) ≃+* Π i, ZMod (a i)` and `ZMod.equivPi (hn : n ≠ 0) : ZMod n ≃+* Π (p : n.primeFactors), ZMod (p ^ (n.factorization p))`. Both are built on `Ideal.quotientInfRingEquivPiQuotient`. — [Mathlib/Data/ZMod/QuotientRing.lean L73–90](https://github.com/leanprover-community/mathlib4/blob/79a359dfe4682c5ca375c39522d7c64e95659d5a/Mathlib/Data/ZMod/QuotientRing.lean)
- `OrthogonalIdempotents` and `CompleteOrthogonalIdempotents` (families with eᵢeⱼ = 0 and ∑ eᵢ = 1), plus lifting results. — [Mathlib/RingTheory/Idempotents.lean](https://github.com/leanprover-community/mathlib4/blob/79a359dfe4682c5ca375c39522d7c64e95659d5a/Mathlib/RingTheory/Idempotents.lean)
- Fitting-type decomposition: `Module.End.eventually_isCompl_ker_pow_range_pow [IsNoetherian R M]` (in `RingTheory/Artinian/Module.lean` L338), with alternative spelling `LinearMap.isCompl_iSup_ker_pow_iInf_range_pow`, used in Lie weight theory. — [Mathlib/RingTheory/Artinian/Module.lean](https://github.com/leanprover-community/mathlib4/blob/79a359dfe4682c5ca375c39522d7c64e95659d5a/Mathlib/RingTheory/Artinian/Module.lean)
- `Nat.digits : ℕ → ℕ → List ℕ` (single fixed base, little-endian) and `Nat.ofDigits (b : α) : List ℕ → α`. — [Mathlib/Data/Nat/Digits/Defs.lean L78, L145](https://github.com/leanprover-community/mathlib4/blob/79a359dfe4682c5ca375c39522d7c64e95659d5a/Mathlib/Data/Nat/Digits/Defs.lean); docs [Mathlib.Data.Nat.Digits](https://leansearch.net/doc/Mathlib.Data.Nat.Digits.html)
- A case-insensitive grep of the whole Mathlib tree for `mixed.radix`, `mixedRadix`, `factorial number system`, `factoradic`, `chip.firing`, `sandpile`, and `gain graph` returned no matches. — local grep of [mathlib4 @79a359df](https://github.com/leanprover-community/mathlib4/tree/79a359dfe4682c5ca375c39522d7c64e95659d5a)
- Finite DFT: `ZMod.dft : (ZMod N → E) ≃ₗ[ℂ] (ZMod N → E)` with inversion (`dft_dft`), unit-multiplication twisting (`dft_comp_unitMul`), and Gauss-sum links. It contains no Cooley–Tukey, PFA, Rader, or Bluestein factorization. — [Mathlib/Analysis/Fourier/ZMod.lean](https://github.com/leanprover-community/mathlib4/blob/79a359dfe4682c5ca375c39522d7c64e95659d5a/Mathlib/Analysis/Fourier/ZMod.lean)
- A Lean 4 chip-firing formalization (arXiv:2606.16679, June 2026) claims "the first formalized proof of Riemann–Roch for graphs in any proof assistant" and formalizes a version of Dhar's burning algorithm. — [arXiv:2606.16679](https://arxiv.org/pdf/2606.16679); related repo [Chip-Firing-with-Lean (Reservoir)](https://reservoir.lean-lang.org/@DhyeyMavani2003/chip-firing-with-lean)

### Inferences
- FDRS's CRT "branch" decomposition is new as a formalization only in its normal-form layer: free part plus digit strings on prime-power branches. The ring isomorphism itself is `ZMod.equivPi`, and idempotent decompositions can be phrased with `CompleteOrthogonalIdempotents`. A paper must present the CRT layer as built on Mathlib, not as new.
- Mixed-radix digit bijections (variable-base `digits`/`ofDigits`, and factorial base as a special case) appear absent from Mathlib. They are a natural, likely welcome Mathlib contribution (e.g., `Nat.mixedDigits`, or `Fin`-product ≃ `Fin (∏ bᵢ)`; compare existing `finProdFinEquiv`/`finPiFinEquiv` in Mathlib, which I did not verify this session).
- The carry quotient Z^n/carries ≅ Z/(B − c) is closely related to the sandpile/critical group of a cycle-like graph with a gain on the wrap edge. The Lean chip-firing project (arXiv:2606.16679) is the nearest formal neighbour and should be cited. Gain graphs (Zaslavsky) appear to have no formalization in any proof assistant, though this was not exhaustively verified.

### Gaps
- I could not open arXiv:2606.16679 (host blocked), so the authors and whether it formalizes the sandpile (critical) group as a quotient Z^n / Laplacian lattice are unverified.
- I did not check `Mathlib/Logic/Equiv/Fin` for `finPiFinEquiv`, which gives a mixed-radix `Fin` equivalence. If it exists it is a partial precedent for digit bijections.
- I did not do an exhaustive search for gain graphs or voltage graphs in Isabelle/Coq/HOL (search returned nothing relevant).

## Q4. Formalized FFTs/NTTs: Cooley–Tukey, mixed radix, Good–Thomas PFA, Rader, Bluestein

### Takeaway
Radix-2 FFT formalizations exist in Coq (Capretta 2001; Théry, SSReflect) and Isabelle (Ballarin, AFP 2005). There is also an Isabelle NTT entry, and F*/Lean NTT work tied to post-quantum crypto. No search result showed a formalization of Good–Thomas PFA, Rader, or Bluestein, or of general mixed-radix Cooley–Tukey, in any proof assistant. This is likely the most clearly novel FDRS component as formalization.

### Cited Findings
- Isabelle AFP "Fast Fourier Transform" (Clemens Ballarin, 2005): a functional FFT over ℂ and its inverse, shown equivalent to the Vandermonde-matrix definitions. — [AFP entry FFT](https://devel.isa-afp.org/entries/FFT.html)
- Isabelle AFP "Number_Theoretic_Transform": NTT and inverse with O(n log n) bounds (latest 2026 version). — [AFP NTT document](https://www.isa-afp.org/browser_info/current/AFP/Number_Theoretic_Transform/document.pdf)
- Laurent Théry, "A Formalisation of a Fast Fourier Transform" (Coq/SSReflect; recursive even/odd split, applied to polynomial multiplication), arXiv:2210.05225. — [ar5iv 2210.05225](https://ar5iv.labs.arxiv.org/html/2210.05225)
- Capretta, "Certifying the Fast Fourier Transform with Coq" (TPHOLs 2001, LNCS, DOI 10.1007/3-540-44755-5_12): type-theoretic FFT formalization. — [unpaywall DOI](https://unpaywall.org/10.1007%2F3-540-44755-5_12)
- A 2024 MIT master's thesis proves the NTT and a Cooley–Tukey fast NTT correct in F*. — [DSpace@MIT 1721.1/157189](https://dspace.mit.edu/handle/1721.1/157189)
- A search specifically for Bluestein, Rader, or prime-factor FFT formalizations in proof assistants returned only prose/code (DSP references, C libraries), with no formal developments. — [Rader's FFT (DSPRelated, prose)](https://www.dsprelated.com/freebooks/mdft/Rader_s_FFT_Algorithm_Prime.html); [Théry FFT (only formal hit)](https://ar5iv.labs.arxiv.org/html/2210.05225)
- Mathlib has the finite DFT on `ZMod N` but no fast factorization. — [Mathlib/Analysis/Fourier/ZMod.lean](https://github.com/leanprover-community/mathlib4/blob/79a359dfe4682c5ca375c39522d7c64e95659d5a/Mathlib/Analysis/Fourier/ZMod.lean)

### Inferences
- Within FDRS, the strongest formalization-novelty claims are probably general mixed-radix Cooley–Tukey (index map n = n₁ + N₁n₂), Good–Thomas via CRT index maps (which ties directly to `ZMod.chineseRemainder`), Rader via a generator of (ZMod p)ˣ, and Bluestein via the chirp identity. All are stated against Mathlib's `ZMod.dft`. Connecting them to `ZMod.dft` would also be a strong Mathlib PR candidate.
- Prior art on HOL4/HOL Light FFT (e.g., Akbarpour & Tahar's error analysis of FFT in HOL) exists from memory but is not verified here. Cite it only after checking.

### Gaps
- I could not fetch the AFP NTT entry page, so authors are unverified (recollection: Thomas Ammer and Katharina Kreuzer, ~2022). Whether it includes Gentleman–Sande or mixed radix is also unverified.
- A HOL4/HOL Light FFT and Coq "FFT in Rocq for NTT/Kyber" check was not completed. Some 2023–2025 NTT verification (e.g., Jasmin/EasyCrypt Kyber, CryptoLine NTT) exists per my background knowledge, but no source was retrieved in this session.

## Q5. Isabelle AFP / HOL Light / ACL2 on residue number systems, positional notation, carry propagation; Russinoff

### Takeaway
I found no AFP entry dedicated to residue number systems or mixed-radix positional notation, though the search was snippet-level only. RNS↔mixed-radix conversion via CRT is an active computer-arithmetic topic outside proof assistants, so a verified RNS/MRC layer would also be relevant to ARITH-style venues.

### Cited Findings
- Searching for an Isabelle AFP residue-number-system or positional-notation entry returned only non-formal RNS papers. — [search-result example: Lutsenko, Babenko, Khamidov, Proc. ISP RAS 2024](https://ispras.ru/proceedings/docs/2024/36/4/isp_36_2024_4_117.pdf)
- Reverse conversion RNS → mixed-radix via CRT remains a studied computer-arithmetic problem (e.g., an efficient parallel reverse conversion to mixed-radix representation). — [PMC8871111](https://www.ncbi.nlm.nih.gov/pmc/articles/PMC8871111/); [Selianinau, Computer Science (AGH) 2020](https://journals.agh.edu.pl/csci/article/download/3616/2456/15455)

### Inferences
- If FDRS includes mixed-radix conversion (MRC) to/from CRT residues, it could be pitched to the RNS community as "the first machine-checked mixed-radix conversion / RNS theory in Lean". That claim depends on a proper AFP/Coq check.

### Gaps
- ACL2 RTL library and Russinoff's "Formal Verification of Floating-Point Hardware Design" (Springer, 2nd ed. 2022) contain bit-vector carry/adder theory. I did not retrieve sources this session. They are relevant prior art for carry-propagation lemmas in hardware adders, not for mixed radix.
- No direct AFP index search (isa-afp.org was unreachable via fetch).

## Q6. Plausible publication venues (as of Oct 2026)

### Takeaway
For the formalization itself, CPP and ITP are the primary venues. CPP 2027's deadline (Sep 10, 2026) has passed, so the next realistic targets are ITP 2027 (deadline expected ~Feb 2027) and CPP 2028 (~Sep 2027), or JAR/JFR/LMCS journals at any time. For the computer-arithmetic content (mixed-radix limb multiplication, carry quotients, mixed-radix FFT circuits), ARITH and IEEE Transactions on Computers are the natural venues. ARITH 2026 explicitly lists number systems and cryptography as topics. The ARITH 2027 CFP was not found.

### Cited Findings
- CPP 2027 is co-located with POPL 2027 in Mexico City, 11–12 Jan 2027. Abstracts were due 3 Sep 2026 and papers 10 Sep 2026. At least one author is expected to attend in person. — [CPP 2027 (POPL 2027 site)](https://popl27.sigplan.org/home/CPP-2027); [CFP on Rocq Discourse](https://discourse.rocq-prover.org/t/cfp-cpp-2027-certified-programs-and-proofs/3063)
- ITP 2026 was held 26–29 July 2026 in Lisbon as part of FLoC'26 (paper deadline 12 Feb 2026). — [myhuiban ITP listing (aggregator)](https://www.myhuiban.com/conference/2415?lang=ko)
- ARITH 2026 (33rd) was held in Fulda, Germany, 28 Jun–1 Jul 2026, with double-blind review and 8-page full papers. Topics include number systems and cryptography, and the paper deadline was 30 Jan 2026. — [ARITH 2026 CFP (hpc-announce)](https://lists.mcs.anl.gov/pipermail/hpc-announce/2025-December/011658.html); [SIGARCH CFP page](https://www.sigarch.org/call-contributions/ieee-symposium-on-computer-arithmetic-arith/)
- IEEE Transactions on Computers has run special sections on computer arithmetic. — [TC special section CFP (closed)](https://computer.org/digital-library/journals/ec/cfp-trends-computer-arithmetic)

### Inferences
- **(a) The formalization:**
  - CPP (ACM SIGPLAN, at POPL): the best fit for a library paper with a crypto-arithmetic angle.
  - ITP (LIPIcs).
  - Journal of Automated Reasoning, or LMCS / Journal of Formalized Reasoning for an extended library paper.
  - Lean-specific outlets: Mathlib PRs, which build credibility. Candidate PRs are mixed-radix digits, CRT idempotent normal forms, and FFT factorizations of `ZMod.dft`.
  - CICM (Intelligent Computer Mathematics) for library/"mathematical components" papers.
  - LICS is a poor fit unless there is a logical or semantic contribution.
- **(b) Mathematical and computer-arithmetic content:**
  - IEEE ARITH (8-page, number systems and crypto arithmetic) and IEEE Transactions on Computers, for limb-multiplication-from-place-values, carry-quotient, and mixed-radix FFT circuits.
  - TCHES/CHES and the Journal of Cryptographic Engineering, only if there is an implementation or performance or verified-code-generation result. Pure re-proof of Curve25519 gains (19, 2, 38) is unlikely to be accepted there, given fiat-crypto.
  - For the gain-graph holonomy / sandpile-like carry quotients: Electronic Journal of Combinatorics, Discrete Mathematics, or Integers / Journal of Integer Sequences for numeration-system content (mixed-radix, context-dependent radix laws).
  - Journal of Number Theory is likely too far, unless genuinely new number theory emerges.
  - arXiv categories: cs.LO (primary for the formalization), with cross-lists math.NT, math.CO (gain graphs and chip-firing), cs.SC, cs.CR (Curve25519), and cs.DM or eess.SP (FFT).

### Gaps
- The ARITH 2027 dates and location, the ITP 2027 CFP, and the CPP 2028 CFP were not yet found or published in search results.
- TCHES, JCEN, EJC, Integers, JAR, CICM, and LMCS scope statements were not fetched this session. Venue fit for them is my judgement, not sourced.
