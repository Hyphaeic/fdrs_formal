# Hybrid residue/mixed-radix representations and context-dependent (adaptive, branching) radix systems: prior work vs. the "hop complex" formalization

Scope reminder. (a) The "hop complex": Z/M (M = F * prod_i T_i, F coprime to the wrap gain c, T_i the prime-power parts shared with c) presented as a carry network. It has a ring of mixed-radix cells plus one mixed-radix branch per residue type i. The moves are ring carries, line carries and "hops" (eps_i units leave the ring root and one unit appears at branch i's root). Results: states modulo moves = Z/M; a unique normal form when branches are exactly sized; a dead-cell criterion; a path back to a sheet only via a hop. (b) Branch radix schedules chosen by "context" (prefix plus an external event-driven state), branches spawned by operations, payload invariance, and a growth law.

Method note. The search engine worked. Direct fetches of arxiv.org, ar5iv, hal.archives-ouvertes.fr and lab-sticc.univ-brest.fr all failed with DNS errors (getaddrinfo ENOTFOUND). Most findings below therefore rest on search-result abstracts and excerpts, not full texts; these points are flagged. Items from background knowledge with no retrieved source appear only under Gaps or Inferences.

## Q1. RNS, mixed-radix conversion and hybrid positional/residue representations: is there a canonical "positional unit part + digit strings for prime-power parts" normal form?

### Takeaway
RNS, mixed-radix conversion (MRC) and "hybrid position-residue" systems are well established. In the known hybrids, the positional part is outermost and RNS sits inside each digit (Bigou–Tisserand, HyPoRes). None of the sources found splits Z/M into a part coprime to a "wrap gain" (written positionally around a ring) and the prime-power parts shared with c (each written as its own mixed-radix digit string). The searches also found no move-equivalence presentation of such a hybrid. Verdict for the representation itself: known in parts (CRT splitting + mixed radix); the specific normal form appears possibly novel as a packaged statement, but it is mathematically elementary.

### Cited Findings
- H. L. Garner, "The residue number system", IRE Transactions on Electronic Computers EC-8(6):140–147, June 1959, as given in a 2026 arXiv reference list. Another reference list cites a Western Joint Computer Conference (March 3–5, 1959) version, pp. 146–153, so the venue and pages are inconsistent between sources. — [arXiv 2605.18415 (RNS comparison revisited)](https://arxiv.org/pdf/2605.18415); conflicting citation in [JQCSM article](https://jqcsm.qu.edu.iq/index.php/journalcm/article/view/1276)
- Residue-to-mixed-radix conversion is the standard reverse converter. A classic pipelined MRC algorithm "sequentially inverts" the residue equations using RNS adders and multipliers by modulus inverses. — [US Patent 4,752,904, "Efficient structure for computing mixed-radix projections from residue number systems"](https://patents.google.com/patent/US4752904)
- Garner's University of Michigan group was among those funded by the U.S. Air Force to study residue-number-system computers (historical context). — [UMD report](https://drum.lib.umd.edu/bitstream/1903/28283/1/1484631.pdf)
- Moduli of the forms 2^a, 2^b−1, 2^c+1 dominate practical RNS because they map onto binary hardware. These include sets with a prime-power modulus 2^{2n}, e.g. {2^{2n}, 2^n−1, 2^{n+1}−1}, converted to binary via MRC. In other words, RNS routinely contains a prime-power channel stored as a base-2 digit string. — [LSU thesis](https://repository.lsu.edu/gradschool_theses/1242); [Oxford RDM record: converters for {2^n, 2^{n+1}−1, 2^n−1, 2^{n−1}−1}](https://rdm.ox.ac.uk/publications/1332903)
- If the last modulus is 2, the corresponding mixed-radix digit acts as a sign indicator "exactly analogous to one's and two's complement" (a residue digit doubling as a positional digit). — [US Patent 4,107,783 / related RNS patents](https://image-ppubs.uspto.gov/dirsearch-public/print/downloadPdf/4107783)
- K. Bigou and A. Tisserand, "Hybrid Position-Residues Number System", ARITH-23 (the 23rd IEEE Symposium on Computer Arithmetic; ARITH-23 was held in 2016). It "mixes a high-radix positional representation with digits represented in RNS", is aimed at large integers and prime-field elements for asymmetric cryptography, and reduces the cost of some modular operations versus RNS-only solutions. The search summary dated it "2023", which looks like a confusion with "ARITH23". Full text was not retrieved. — [HAL hal-01314232](https://hal.archives-ouvertes.fr/hal-01314232); [author PDF](https://lab-sticc.univ-brest.fr/~kbigou/ARITH23.pdf)
- P. Martins, J. Marrez, J.-C. Bajard, L. Sousa, "HyPoRes: An Hybrid Representation System for ECC", ARITH 2019. It is a polynomial variant of hybrid position-residue systems that gives improved modular reduction for any prime. — [HAL hal-02337787](https://hal.sorbonne-universite.fr/hal-02337787v1)
- Hybrid "weighted + residue" notations were already studied around 1989. Numbers are split into two parts, "a residue and a representation". Only CNR repository metadata was seen. — [IRIS CNR 20.500.14243/376999](https://iris.cnr.it/handle/20.500.14243/376999); [IRIS CNR 20.500.14243/374834](https://iris.cnr.it/handle/20.500.14243/374834)
- No source was found for a "hybrid position-residue number system" by Chiang & Lu. The search returned only Bigou–Tisserand and successors. — [search outcome; HAL hal-01314232](https://hal.archives-ouvertes.fr/hal-01314232)

### Inferences
- **Layering in known hybrids.** Bigou–Tisserand/HyPoRes put positional (high-radix) digits outside and RNS digits inside. The hop complex inverts this: CRT components are outermost (eps_F part, eps_i parts) and each component has its own positional/mixed-radix encoding. "RNS whose channels are stored as mixed-radix strings" is common practice (e.g. the 2^k channel stored in binary), so the inverted layering per se is not new.
- **Choice of splitting.** The hop complex splits by the wrap gain c into F (coprime to c) and T_i (prime powers dividing a power of c). This is the Fitting-type decomposition of multiplication-by-c on Z/M: invertible on Z/F, nilpotent on prod Z/T_i. None of the RNS sources found splits the modulus this way or ties it to a ring carry with gain c. This is likely the distinctive design choice of (a).
- **Carry moves.** In RNS literature, "mixed radix" is a conversion target computed by arithmetic (MRC), not a presentation by carry moves. No source found treats RNS/MRC states as a rewriting system modulo carry/hop moves with a normal-form theorem.
- **Overall verdict for (a), representation part:** known in parts. The ingredients are CRT idempotents (Garner/Szabo–Tanaka era), mixed-radix digits for prime-power residues (standard 2^k channels) and hybrid positional/residue systems (Bigou–Tisserand 2016, HyPoRes 2019). The combination "eps_F * W on a gain-c ring + one exactly-sized digit string per c-sharing prime-power part" was not found and is possibly novel as a packaged, formalized statement.

### Gaps
- Szabo & Tanaka, *Residue Arithmetic and Its Applications to Computer Technology* (McGraw-Hill, 1967) and Omondi & Premkumar, *Residue Number Systems: Theory and Implementation* (Imperial College Press, 2007) were not retrieved. Bibliographic data is from background knowledge and was not verified this session. In particular, I could not check Szabo–Tanaka's exact treatment of the "associated mixed-radix system" or the redundant-RNS chapters.
- Redundant residue number systems (RRNS): no search was run within the budget, so there is no citation here.
- Garner's venue and pages are inconsistent across reference lists (see above). IEEE Xplore was not checked.
- The Bigou–Tisserand full text (exact digit/RNS layout and their related-work list) was unreachable because of DNS failures.

## Q2. Z/p^k via base-p digits combined with CRT (p-adic truncations, Hensel lifting, prime-power RNS channels)

### Takeaway
It is common practice to represent a prime-power residue channel in radix p, especially p = 2 with 2^k channels, and to combine channels by CRT/MRC. No source found presents a canonical normal form in which the prime-power part is an exactly-sized mixed-radix string (radices multiplying to T_i, not necessarily all equal to p) attached to a CRT idempotent. Verdict: known (in substance) for the radix-p special case; the generalization to arbitrary exactly-sized schedules is a routine extension, not found stated as such.

### Cited Findings
- Power-of-two moduli 2^a (and 2^{2n}) are among the most-used RNS moduli because the channel is a plain binary (radix-2) register. — [LSU thesis](https://repository.lsu.edu/gradschool_theses/1242)
- Moduli sets such as {2^{2n}, 2^n−1, 2^{n+1}−1} pair a prime-power channel with odd channels and are converted back via MRC/CRT. — [Oxford RDM record](https://rdm.ox.ac.uk/publications/1332903)
- A search for "p-adic residue number system / prime-power moduli in radix p" returned only power-of-two RNS hardware results. Nothing turned up on general p-adic digits inside RNS. — [search outcome; LSU thesis](https://repository.lsu.edu/gradschool_theses/1242)

### Inferences
- **Radix-p special case.** Z/p^k ≅ base-p digit strings of length k is the standard p-adic truncation. Combined with CRT, it gives exactly the "one digit string per prime-power part" shape. The hop complex's "exactly sized branch" theorem (radices multiply to T_i ⇒ unique normal form) generalizes this from radix p to any factorization of T_i. That generalization is immediate from ordinary mixed-radix uniqueness (Cantor/Knuth mixed radix).
- **Dead-cell criterion.** A line cell is equivalent to nothing iff T_i divides its place value. This is the statement that a place value of p^j·(...) ≥ T_i is 0 in Z/T_i, i.e. p-adic truncation overflow. It is elementary and known in substance, though no named statement was found.

### Gaps
- Computer-algebra multi-modular/p-adic (Hensel lifting) literature was not searched within budget. No citation is offered for "multi-modular p-adic" representations.
- Knuth TAOCP Vol. 2 §4.1 (mixed radix) and §4.3.2 (modular arithmetic) were not retrieved. Both are presumed relevant background only (not verified this session).

## Q3. Presentations of Z/M as "states modulo carry moves" with unique normal forms (closest structural prior art for (a))

### Takeaway
This was not in the original key-question list, but it is the closest structural prior art for (a). Taking states modulo local integer "moves" (fire r units at a cell, deposit units elsewhere) yields the cokernel Z^n / (move lattice). This is exactly the framework of chip-firing, sandpile/critical groups and their matrix generalizations (Gabrielov; Guzmán–Klivans), together with abelian networks (Bond–Levine). Unique representatives per class (critical / z-superstable / energy-minimizing configurations) are theorems there. Carries as cocycles/group extensions are classical (Isaksen 2002). Verdict: the quotient-by-moves paradigm and unique-normal-form-per-class results are known. A specific "ring + branches + hop" network realizing the c-Fitting decomposition of Z/M was not found and is possibly novel as a construction.

### Cited Findings
- Guzmán & Klivans, "Chip-firing and energy minimization on M-matrices". Chip-firing is defined by an arbitrary M-matrix. Each equivalence class has a unique energy-minimizing configuration, and z-superstable configurations coincide with the energy minimizers and are dual to critical configurations. — [arXiv 1403.1635](https://arxiv.org/pdf/1403.1635)
- Gabrielov showed that critical configurations exist and are unique per equivalence class for avalanche-finite matrices. Guzmán–Klivans later identified avalanche-finite matrices with M-matrices and extended chip-firing to general invertible integer matrices. — [Guzmán & Klivans, "Chip-firing on general invertible matrices", arXiv 1508.04262](https://arxiv.org/pdf/1508.04262)
- The critical/z-superstable duality extends to (L, M) "chip-firing pairs" (FPSAC 2025). — [FPSAC 2025 paper 110](https://www.mat.univie.ac.at/~slc/wpapers/FPSAC2025/110.pdf)
- The order of the sandpile group equals the number of directed spanning trees in which the sink is reachable from every vertex. — [Klivans, *Chip-Firing* notes (Brown)](https://www.dam.brown.edu/people/cklivans/Chip-Firing.pdf)
- Bond & Levine, "Abelian Networks I. Foundations and Examples": networks of communicating automata where two axioms make the output independent of processing order (local commutativity), with a least-action principle. — [arXiv 1309.3445 (ar5iv)](https://ar5iv.arxiv.org/html/1309.3445)
- "Abelian Networks III. The Critical Group" generalizes the sandpile group to abelian networks. The critical group acts freely and transitively on recurrent states, and Dhar's burning algorithm is generalized. — [arXiv 1409.0170](https://www.arxiv.org/pdf/1409.0170)
- Chan & Levine, "Abelian Networks IV. Dynamics of Nonhalting Networks", Memoirs AMS (2022). — [AMS Memoirs 1358](https://www.ams.org/books/memo/1358/)
- Isaksen, "A Cohomological Viewpoint on Elementary School Arithmetic", *Amer. Math. Monthly* 109(9) (2002) 796–805. The carry is a 2-cocycle, and Z/100 is an extension of Z/10 by Z/10. — [nLab, D. Corfield, "intuitions about cohomology"](https://ncatlab.org/davidcorfield/show/intuitions+about+cohomology); [Swenberg, "The carrying cocycle" (UCLA)](https://www.math.ucla.edu/~jaswenberg/CarryingCocycle.pdf); [arXiv 2507.10678 (follows Isaksen)](https://arxiv.org/pdf/2507.10678)
- Search found no source explicitly linking chip-firing/sandpile groups to mixed-radix numeration carries. — [search outcome, e.g. arXiv 2510.26021](https://arxiv.org/pdf/2510.26021)

### Inferences
- **Each move is a chip-firing vector.** A mixed-radix carry (r units at cell j → 1 unit at cell j+1) is a firing vector. A ring with wrap gain c is a bidiagonal-plus-corner integer matrix whose cokernel has order |prod r_j − c|-type determinant. Hops are additional integer move vectors. So "states modulo moves = Z/M" is a cokernel/Smith-normal-form computation in the Gabrielov/Guzmán–Klivans setting. "Any branch schedules give Z/M" is then a determinant/cokernel identity.
- **Normal forms.** The unique-normal-form theorem for exactly-sized branches is analogous to existence/uniqueness of z-superstable/critical representatives. More directly, it is analogous to the fact that for a triangular (Hermite-form) lattice basis with diagonal d_j, the box prod [0, d_j) is a complete system of coset representatives. (This last fact is standard lattice theory from background knowledge; no source was retrieved.)
- **Relation to M-matrices.** Whether the hop complex's move matrix is an M-matrix or avalanche-finite (so Gabrielov/Guzmán–Klivans applies verbatim) depends on the hop vector (−eps_i at the root, +1 at the branch root). eps_i can be large and the hop is not a "toppling", so the theorems are probably not directly instances. The claim "a path back to a sheet exists only via a hop" has no analogue found in the chip-firing literature.
- **Verdict.** "Same construction" not found; "related idea" is strong (chip-firing cokernels, carry cocycles, abelian networks). A Lean 4 formalization of such a network with these theorems appears possibly novel. Mathlib-style formalizations of sandpile groups were not checked (out of scope).

### Gaps
- I could not open full texts of Gabrielov ("Abelian avalanches and Tutte polynomials", 1993, as recalled from background), Guzmán–Klivans or Bond–Levine to check whether non-M-matrix "transfer" moves like hops are covered.
- No search for "Hermite normal form coset representatives box" with a citable source.
- No search for existing Lean/Coq/Isabelle formalizations of chip-firing, RNS or mixed radix.

## Q4. Variable/mixed-radix numeration with context-dependent or branching bases (closest prior art for (b))

### Takeaway
Context-dependent radices are well developed in several mature literatures:
- position-dependent bases: Cantor/mixed radix, Cantor real bases, G-odometers;
- prefix/state-dependent digit sets: abstract numeration systems on regular languages, Bratteli–Vershik odometers, rational-base representation trees;
- probability/state-dependent radices: asymmetric numeral systems and arithmetic coding.

Bratteli–Vershik odometers in particular are mixed-radix counters whose admissible next digit depends on the current vertex (a context). Nothing found combines this with CRT-typed branches that are spawned by operations and fed by invariant residue payloads. Verdict: the idea of a prefix/context-dependent radix law is known. The specific coupled-branch, payload-driven growth rule appears possibly novel.

### Cited Findings
- Lecomte & Rigo, "Numeration systems on a regular language": integers are represented by the genealogical (radix) order of an arbitrary infinite regular language, so admissible digits depend on the prefix (the automaton state). Ultimately periodic sets are recognizable. — [arXiv cs/9903005](https://arxiv.org/pdf/cs/9903005)
- Rigo, "Numeration systems on a regular language: Arithmetic operations, Recognizability and Formal power series", *Theoret. Comput. Sci.* 269 (2001) 469–498. Recognizable sets are characterized via N-rational series, with results on multiplication by constants. — [ORBi ULiège 2268/15868](https://orbi.uliege.be/handle/2268/15868)
- Lecomte & Rigo extend abstract numeration systems to real numbers. — [arXiv cs/0212018](https://arxiv.org/abs/cs/0212018)
- Survey chapter "Abstract numeration systems" in *Combinatorics, Automata and Number Theory* (Cambridge). — [Cambridge Core](https://www.cambridge.org/core/books/abs/combinatorics-automata-and-number-theory/abstract-numeration-systems/E6B96F9718288F6A2F8B2D89BB2A7B6D)
- Akiyama, Marsault & Sakarovitch: in rational base p/q, every integer has a unique finite representation, and the prefix-closed set of representations forms a "highly non-regular tree" whose subtrees are all distinct. A sequential transducer computing the minimal word of n+1 from that of n has essentially the same graph as the tree. — [arXiv 1706.08266](https://arxiv.org/pdf/1706.08266); [DMTCS 4331](https://dmtcs.episciences.org/4331/pdf)
- Marsault & Sakarovitch: languages of integer representations in base p/q have purely periodic "signatures" derived from the Christoffel word of slope p/q. Breadth-first signatures serialize trees, and signatures of rational languages are substitutive. — [arXiv 1403.5190](https://arxiv.org/abs/1403.5190); [arXiv 1404.0798](https://arxiv.org/abs/1404.0798v1)
- Enumeration of tree vertices is linked to abstract numeration systems (tree traversal = radix enumeration of the language). — [arXiv 2102.10828](https://arxiv.org/pdf/2102.10828v3)
- Grabner, Liardet & Tichy, "Odometers and systems of numeration", *Acta Arith.* 70 (1995) 103–123. Odometers are defined for a general base sequence G = (G_n), noting a "strong connection to the Bratteli diagram introduced by A. M. Vershik". — [IMPAN Acta Arithmetica 70(2)](https://impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/70/2/108520/odometers-and-systems-of-numeration); [Iacò–Steiner–Tichy, "Linear recursive odometers and beta-expansions", arXiv 1604.07223](https://ar5iv.labs.arxiv.org/html/1604.07223)
- Every minimal Cantor homeomorphism has a Bratteli–Vershik model (Herman–Putnam–Skau), extended to aperiodic ones by Medynets. Durand, "Combinatorics on Bratteli diagrams and dynamical systems" (Encycl. Math. Appl. 135, 2010, 324–372) and Downarowicz, "Survey of odometers and Toeplitz flows" (Contemp. Math. 385, 2005) are the standard surveys. — [Rotated Odometers, arXiv 2101.00868](https://arxiv.org/pdf/2101.00868)
- Bratteli–Vershik systems from stationary, properly ordered diagrams split into substitution minimal systems and stationary odometers. — [arXiv 0807.3621](https://arxiv.org/pdf/0807.3621.pdf)
- Cantor real bases generalize Rényi β-expansions with a sequence of bases, x = Σ x_k / prod_{i≤k} β_i. The base depends on position, not on previous digits. — [Springer, Research in Number Theory, 10.1007/s40993-024-00542-5](https://link.springer.com/10.1007/s40993-024-00542-5)
- Mixed-radix numeration bases have been studied in connection with Horner's rule, the Yang–Baxter equation and Furstenberg's conjecture (D. Simon). — [normalesup.org/~dsimon](https://www.normalesup.org/~dsimon/recherche/publication/numerationyb/)
- Fraenkel (1985) is credited with initiating the study of positional numeration systems with general base sequences. The venue (Amer. Math. Monthly, "Systems of numeration") was not confirmed by the search. — [arXiv 2405.19798](https://arxiv.org/html/2405.19798v2)
- Duda's asymmetric numeral systems (ANS) are "a family of generalizations of standard numeral systems". A plain base-b system is the equiprobable case, and ANS adapts the effective radix per symbol to its probability. Context modelling makes the radix state-dependent. — [Duda, arXiv 0902.0271](https://arxiv.org/abs/0902.0271v2); [Duda, arXiv 1311.2540](https://ar5iv.arxiv.org/html/1311.2540)
- A US patent titled "Method and apparatus for varying-radix numeration system" exists. Contents were not read. — [US 7,650,372](https://image-ppubs.uspto.gov/dirsearch-public/print/downloadPdf/7650372)
- No source was found in which "each digit sets the base for the next" as a named general framework, beyond regular-language, Bratteli and tree systems. — [search outcome; arXiv 1706.08266](https://arxiv.org/pdf/1706.08266)

### Inferences
- **Bratteli–Vershik.** A Bratteli diagram with vertex-dependent edge counts is a mixed-radix system whose radix at level n depends on the path so far (the prefix). The successor map is a carry. This is the closest mathematical precedent for "radix laws depending on the prefix". "Radix depending on an external context evolving with events" adds an input-driven automaton, similar to stateful encoders (ANS/arithmetic coding with adaptive models) and Lecomte–Rigo's automaton-state-dependent digit sets.
- **Branch spawning.** Branches spawned by operations, whose radix schedules are fed by a residue payload w mod T_j that is invariant under carries and hops, were not found anywhere. The closest analogues are:
  - carry-save / redundant representations (not searched);
  - Bigou–Tisserand hybrid digits carrying RNS sub-digits;
  - odometer "towers" in Bratteli–Vershik theory.

  None ties branch creation to CRT types.
- **Growth rule.** "A branch records a radix of its own type when another type's residue is nonzero" with an exact growth law has no precedent found. It resembles growth-rate/complexity counting in abstract numeration systems, where the number of length-n words follows a linear recurrence, but only loosely. Judged possibly novel.
- **Overall verdict for (b):** the context-dependent radix concept is known (abstract numeration systems, Bratteli–Vershik/G-odometers, ANS/adaptive arithmetic coding, rational-base trees). Coupled CRT-typed branches with invariant payloads and the stated growth law are possibly novel, though conceptually close to stateful encoders.

### Gaps
- Lothaire / Berthé–Rigo (eds.), *Combinatorics, Automata and Number Theory* (2010), and Rigo's *Formal Languages, Automata and Numeration Systems* (2014) were not retrieved beyond the Cambridge chapter landing page.
- Ostrowski numeration, Pisot/β-numeration, factorial number system and Lehmer codes: no searches run within budget (well-known background; no citations here).
- "Markov odometers" and "Cantor odometers with varying alphabets" as named concepts were not confirmed by search.
- The content of US 7,650,372 is unknown.

## Q5. Number systems whose radices are grown/allocated by the arithmetic operations themselves (self-adaptive representation, on-demand precision, lazy exact reals)

### Takeaway
No source surfaced describing a number representation in which arithmetic operations themselves allocate new radix positions or branches with typed radices. Closest known: adaptive coding (ANS/arithmetic coding, where the model evolves with events) and hybrid systems whose digit sizes are chosen per application. Verdict: no prior art found. This is weak evidence of novelty, because the search was shallow on this sub-question.

### Cited Findings
- ANS treats numeral systems as encoders whose per-symbol digit-set size is adapted to probabilities. The rANS/tANS variants used in practice (Duda 2013) give ~50% faster decoding than Huffman for 256-symbol alphabets with arithmetic-coding-like compression. This is the most mature "state-dependent radix" engineering literature found. — [Duda, arXiv 1311.2540](https://ar5iv.arxiv.org/html/1311.2540)
- Hybrid position-residue systems choose positional radix and RNS base by application (crypto field size). This is a design-time choice, not operation-driven growth. — [Bigou & Tisserand, HAL hal-01314232](https://hal.archives-ouvertes.fr/hal-01314232); [HyPoRes, HAL hal-02337787](https://hal.sorbonne-universite.fr/hal-02337787v1)

### Inferences
- **Nearest families.** Dynamic radix growth driven by operations most resembles:
  - lazy exact real arithmetic (digit streams produced on demand);
  - arbitrary-precision integers that extend limbs on overflow;
  - adaptive arithmetic coding.

  None of these use radices typed by CRT components. The hop complex's "branch spawned by an operation, receiving a payload" mechanism appears to have no direct antecedent.

### Gaps
- "Lazy exact real arithmetic", "on-demand precision", "self-adaptive number representation" and redundant/carry-save literatures were not searched within the tool budget. This sub-question deserves a dedicated follow-up before claiming novelty.
- Lean/Mathlib formalization prior art (e.g. Mathlib's `Nat.digits`, `ZMod` CRT, any chip-firing formalization) was not surveyed here.
