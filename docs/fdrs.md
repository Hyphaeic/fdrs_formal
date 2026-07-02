## Phase 1 — Foundations, Fragment 1

### Mixed-radix space, Tick operator, ultrametric topology (with proofs)

### 1. Base data and notation

Fix a **radix sequence** $(b=(b_i)_{i\ge 0})$ with integers $(b_i\ge 2)$.
Define digit alphabets $(D_i := {0,1,\dots,b_i-1})$.

Define the cumulative radix products
$[
B_0 := 1,\qquad B_{m} := \prod_{i=0}^{m-1} b_i \ \ \text{for }m\ge 1.
]$
So $(B_m)$ is the “place value” of digit position $(m)$ (least significant position is $(0)$).

---

## 2. Finite mixed-radix spaces and decoding

### Definition 1 (finite horizon space)  [§2.1 · Phase 1, Fragment 1]

For $(k\in\mathbb N)$, define the **finite mixed-radix space**
$[
\mathcal R^{(k)} := \prod_{i=0}^{k} D_i.
]$
An element $(\tau\in\mathcal R^{(k)})$ is a digit vector $(\tau=(d_0,\dots,d_k))$ with $(d_i\in D_i)$.

### Definition 2 (finite decoding / encoding)  [§2.2 · Phase 1, Fragment 1]

Define the **decode** map (\operatorname{dec}*k:\mathcal R^{(k)}\to {0,1,\dots,B*{k+1}-1}) by
$[
\operatorname{dec}*k(d_0,\dots,d_k) := \sum*{i=0}^{k} d_i, B_i.
]$
Define $(\operatorname{enc}*k:{0,\dots,B*{k+1}-1}\to \mathcal R^{(k)})$ as the unique mixed-radix expansion map (defined below via existence/uniqueness).

### Proposition 1 (representation theorem, finite case)  [§2.3 · Phase 1, Fragment 1]

$(\operatorname{dec}*k)$ is a bijection $(\mathcal R^{(k)} \cong {0,\dots,B*{k+1}-1})$. Consequently, $(|\mathcal R^{(k)}|=B_{k+1})$.

**Proof.**
**(Existence of $(\operatorname{enc}_k)$)** Let $(n\in{0,\dots,B_{k+1}-1})$. Define digits recursively:

* $(d_0 := n \bmod b_0)$, $(n_1 := \lfloor n/b_0\rfloor)$.
* $(d_1 := n_1 \bmod b_1)$, $(n_2 := \lfloor n_1/b_1\rfloor)$.
* Continue until $(d_k := n_k \bmod b_k)$, $(n_{k+1}:=\lfloor n_k/b_k\rfloor)$.

Since $(n < \prod_{i=0}^k b_i = B_{k+1})$, repeated division yields $(n_{k+1}=0)$. Thus we obtain digits $(d_i\in D_i)$. Set $(\operatorname{enc}*k(n)=(d_0,\dots,d_k)$). By construction,
$[
n = \sum*{i=0}^k d_i B_i = \operatorname{dec}_k(\operatorname{enc}_k(n)),
]$
so $(\operatorname{dec}_k)$ is surjective and $(\operatorname{enc}_k)$ is a right-inverse.

**(Uniqueness)** Suppose $(\sum_{i=0}^k d_i B_i = \sum_{i=0}^k e_i B_i)$ with $(d_i,e_i\in D_i)$. Reduce both sides modulo $(b_0)$: since $(B_0=1)$ and $(B_i)$ for $(i\ge 1)$ is divisible by $(b_0)$, we get $(d_0\equiv e_0 \pmod{b_0})$. But both are in $({0,\dots,b_0-1})$, hence $(d_0=e_0)$. Subtract $(d_0B_0)$ and divide by $(b_0)$ to repeat the argument at the next digit. Inductively, $(d_i=e_i)$ for all $(i)$. Thus the representation is unique, so $(\operatorname{dec}_k)$ is injective. ∎

---

## 3. Direct-limit (unbounded) mixed-radix time

The finite horizons embed into each other by adding a new most-significant digit (0).

### Definition 3 (direct-limit space)  [§3.1 · Phase 1, Fragment 1]

Define embeddings $(\iota_k:\mathcal R^{(k)}\hookrightarrow \mathcal R^{(k+1)})$ by
$[
\iota_k(d_0,\dots,d_k) := (d_0,\dots,d_k,0).
]$
Define the **direct limit**
$[
\mathcal R^{(\infty)}*{\mathrm{fin}} := \varinjlim_k \mathcal R^{(k)}.
]$
Concretely, $(\mathcal R^{(\infty)}*{\mathrm{fin}})$ is the set of infinite digit sequences
$[
(d_0,d_1,d_2,\dots),\quad d_i\in D_i,
]$
that are **eventually zero**: $(\exists K)$ such that $(d_i=0)$ for all $(i>K)$. (This is the union of all finite-horizon spaces under the embeddings.)

### Definition 4 (unbounded decoding)  [§3.2 · Phase 1, Fragment 1]

Define $(\operatorname{dec}:\mathcal R^{(\infty)}*{\mathrm{fin}}\to \mathbb N)$ by
$[
\operatorname{dec}((d_i)*{i\ge0}) := \sum_{i=0}^{\infty} d_i B_i,
]$
where the sum is finite because the digits are eventually zero.

### Theorem 1 (order-theoretic isomorphism with (\mathbb N))  [§3.3 · Phase 1, Fragment 1]

$(\operatorname{dec})$ is a bijection $(\mathcal R^{(\infty)}*{\mathrm{fin}} \cong \mathbb N)$.
Define an order $(\preceq) on (\mathcal R^{(\infty)}*{\mathrm{fin}})$ by $(\tau\preceq \sigma \iff \operatorname{dec}(\tau)\le \operatorname{dec}(\sigma))$. Then $((\mathcal R^{(\infty)}_{\mathrm{fin}},\preceq))$ is order-isomorphic to $((\mathbb N,\le))$ and is well-founded.

**Proof.**
**(Surjectivity)** Given $(n\in\mathbb N)$, apply the same repeated-division construction as in Proposition 1, but without stopping at a fixed $(k)$. After $(m)$ steps we have digits $(d_0,\dots,d_{m-1})$ and a quotient $(n_m=\lfloor n/B_m\rfloor)$. Once $(B_m>n)$, we get $(n_m=0)$, and all subsequent digits are $(0)$. Hence we produce an eventually-zero sequence $(\tau)$ with $(\operatorname{dec}(\tau)=n)$.

**(Injectivity)** If $(\operatorname{dec}(\tau)=\operatorname{dec}(\sigma))$, pick $(k)$ large enough that both sequences are zero beyond $(k)$. Then $(\tau,\sigma\in\mathcal R^{(k)})$, and injectivity follows from Proposition 1. Thus $(\operatorname{dec})$ is bijective.

**(Order isomorphism and well-foundedness)** By definition, $(\operatorname{dec})$ is order-preserving and order-reflecting, hence an order isomorphism. Since $((\mathbb N,\le))$ has no infinite strictly descending chains, neither does $((\mathcal R^{(\infty)}_{\mathrm{fin}},\preceq))$. ∎

---

## 4. Tick operator (mixed-radix increment with carry)

### Definition 5 (Tick on finite horizon; partial successor)  [§4.1 · Phase 1, Fragment 1]

On (\mathcal R^{(k)}), define the **successor (Tick)** (T_k) as the mixed-radix increment **when it does not overflow**:

* If (\tau \neq (b_0-1,\dots,b_k-1)), define (T_k(\tau)) by the usual carry rule:
  find the smallest index (j) such that (d_j < b_j-1) and (d_i=b_i-1) for all (i<j); then set
  [
  d'_i :=
  \begin{cases}
  0,& i<j,\
  d_j+1,& i=j,\
  d_i,& i>j,
  \end{cases}
  \quad\text{and }T_k(\tau)=(d'_0,\dots,d'_k).
  ]
* If (\tau = (b_0-1,\dots,b_k-1)), leave (T_k(\tau)) undefined.

### Proposition 2 (Tick corresponds to (+1) in decoded coordinates, finite case)  [§4.2 · Phase 1, Fragment 1]

For all (\tau\in\mathcal R^{(k)}) where (T_k(\tau)) is defined,
[
\operatorname{dec}_k(T_k(\tau)) = \operatorname{dec}_k(\tau)+1.
]

**Proof.**
Let (j) be the carry index described in Definition 5. Then for (i<j), (d_i=b_i-1) and (d'*i=0). Compute the difference:
[
\operatorname{dec}*k(T_k(\tau))-\operatorname{dec}*k(\tau)
= (d_j+1-d_j)B_j + \sum*{i<j}(0-(b_i-1))B_i.
]
So
[
= B_j - \sum*{i=0}^{j-1}(b_i-1)B_i.
]
But (\sum*{i=0}^{j-1}(b_i-1)B_i = B_j-1) (the maximum value representable in the first (j) digits). Hence the difference is (B_j-(B_j-1)=1). ∎

### Definition 6 (Tick on the direct-limit space; total successor)  [§4.3 · Phase 1, Fragment 1]

Define (T:\mathcal R^{(\infty)}*{\mathrm{fin}}\to \mathcal R^{(\infty)}*{\mathrm{fin}}) by
[
T(\tau) := \operatorname{enc}(\operatorname{dec}(\tau)+1),
]
where (\operatorname{enc}) is the (unique) mixed-radix expansion into an eventually-zero digit sequence.

### Theorem 2 (Tick is total and matches successor on (\mathbb N))  [§4.4 · Phase 1, Fragment 1]

For all (\tau\in\mathcal R^{(\infty)}*{\mathrm{fin}}),
[
\operatorname{dec}(T(\tau))=\operatorname{dec}(\tau)+1.
]
In particular, (T) is total, and ((\mathcal R^{(\infty)}*{\mathrm{fin}},T)) is a successor system isomorphic to ((\mathbb N,n\mapsto n+1)).

**Proof.** Immediate from the definition of (T) and (\operatorname{enc}) as inverse to (\operatorname{dec}). ∎

---

## 5. Ultrametric topology via cylinder sets

To define a clean ultrametric, it is convenient to work first on the full infinite product, then restrict.

### Definition 7 (completed mixed-radix space)  [§5.1 · Phase 1, Fragment 1]

Define the **completed digit space**
[
\widehat{\mathcal R} := \prod_{i=0}^{\infty} D_i
]
(all infinite digit sequences, not necessarily eventually zero).

### Definition 8 (cylinder sets)  [§5.2 · Phase 1, Fragment 1]

For a finite prefix (s=(s_0,\dots,s_{L-1})\in \prod_{i=0}^{L-1} D_i), define the **cylinder set**
[
U(s) := {x=(d_i)_{i\ge0}\in \widehat{\mathcal R} : d_i=s_i \text{ for } 0\le i < L}.
]

### Definition 9 (ultrametric)  [§5.3 · Phase 1, Fragment 1]

Define (\delta:\widehat{\mathcal R}\times \widehat{\mathcal R}\to \mathbb R_{\ge 0}) by
[
\delta(x,y)=
\begin{cases}
0,& x=y,[4pt]
B_m^{-1},& \text{where } m:=\min{i\ge 0: x_i\ne y_i}.
\end{cases}
]
(So two points are closer when they agree on a longer initial digit prefix (d_0,d_1,\dots).)

### Proposition 3 ((\delta) is an ultrametric)  [§5.4 · Phase 1, Fragment 1]

For all (x,y,z\in\widehat{\mathcal R}),

1. (\delta(x,y)=0 \iff x=y);
2. (\delta(x,y)=\delta(y,x));
3. **Strong triangle inequality:** (\delta(x,z)\le \max{\delta(x,y),\delta(y,z)}).

**Proof.** (1) and (2) are immediate.

For (3), let
[
m_{xy}=\min{i:x_i\ne y_i},\quad m_{yz}=\min{i:y_i\ne z_i},
]
and set (m:=\min{m_{xy},m_{yz}}). Then for all (i<m), we have (x_i=y_i) (since (i<m\le m_{xy})) and also (y_i=z_i) (since (i<m\le m_{yz})), hence (x_i=z_i) for all (i<m). Therefore the first index where (x) and (z) differ satisfies (m_{xz}\ge m), so
[
\delta(x,z)=B_{m_{xz}}^{-1}\le B_m^{-1}=\max{B_{m_{xy}}^{-1},B_{m_{yz}}^{-1}}=\max{\delta(x,y),\delta(y,z)},
]
because (B_n) is strictly increasing in (n). ∎

### Proposition 4 (open balls are cylinders; cylinders form a clopen basis)  [§5.5 · Phase 1, Fragment 1]

Fix (x\in\widehat{\mathcal R}) and (L\ge 1). Let (s=(x_0,\dots,x_{L-1})). Then
[
U(s)={y\in\widehat{\mathcal R}: \delta(x,y) < B_L^{-1}}.
]
Hence cylinders are open, and (by a symmetric argument) also closed. The cylinders form a basis for the topology induced by (\delta).

**Proof.**
(\delta(x,y) < B_L^{-1}) holds iff the first differing index (m) satisfies (m\ge L), i.e. iff (y_i=x_i) for all (i<L), i.e. (y\in U(s)). This shows cylinders are metric-open balls. In an ultrametric space, every open ball is also closed (its complement is a union of open balls), so cylinders are clopen. Basis follows because any metric-open set is a union of open balls, hence a union of cylinders. ∎

### Restriction to the direct-limit space

(\mathcal R^{(\infty)}_{\mathrm{fin}}\subset \widehat{\mathcal R}). Restrict (\delta) and the cylinder sets to obtain an ultrametric topology on the computable, well-founded time space.

### Proposition 5 (cylinders correspond to congruence classes under decoding)  [§5.6 · Phase 1, Fragment 1]

Let (s=(s_0,\dots,s_{L-1})) and define the residue
[
r(s):=\sum_{i=0}^{L-1} s_i B_i \in {0,\dots,B_L-1}.
]
Then for (\tau\in\mathcal R^{(\infty)}*{\mathrm{fin}}),
[
\tau\in U(s)\cap \mathcal R^{(\infty)}*{\mathrm{fin}}
\quad\Longleftrightarrow\quad
\operatorname{dec}(\tau)\equiv r(s)\pmod{B_L}.
]

**Proof.**
(\tau\in U(s)) iff its first (L) digits equal (s). Writing (n=\operatorname{dec}(\tau)=\sum_{i\ge0} d_iB_i), we have
[
n \equiv \sum_{i=0}^{L-1} d_iB_i \pmod{B_L},
]
because (B_L\mid B_i) for all (i\ge L). Thus fixing ((d_0,\dots,d_{L-1})=(s_0,\dots,s_{L-1})) is equivalent to (n\equiv r(s)\pmod{B_L}). ∎

---

## What we have now (Phase 1, Fragment 1 complete)

* A **computable, well-founded** mixed-radix time space (\mathcal R^{(\infty)}_{\mathrm{fin}}) that is **order-isomorphic to (\mathbb N)** via (\operatorname{dec}).
* A **Tick** operator (T) that is exactly “(+1)” under decoding.
* An **ultrametric topology** (via (\delta)) whose **clopen cylinder sets** are exactly **radix-prefix constraints**, equivalently **congruence classes modulo (B_L)**.

---

## Leading questions for the next fragment (Phase 1, Fragment 2)

1. **Predecessor and subtraction:** define (\operatorname{pred}), mixed-radix subtraction with borrow, and prove partial inverses / correctness under (\operatorname{dec}).
2. **Addition as an internal operation:** define (\oplus) on (\mathcal R^{(\infty)}_{\mathrm{fin}}) induced by (+) on (\mathbb N), and prove associativity/commutativity; characterize carry locality in digit space.
3. **Continuity of Tick and arithmetic:** prove (T) is continuous (indeed 1-Lipschitz in (\delta)); same for (\oplus). This is what you later need to treat “Markovian after augmenting with radix phase” as a formal measurable dynamical system on cylinders.

## Phase 1 — Foundations, Fragment 2

### Predecessor, addition/subtraction with borrow/carry, and continuity/locality in the ultrametric

We continue with the same radix sequence (b=(b_i)*{i\ge0}), digit sets (D_i={0,\dots,b_i-1}), and place-values (B_m=\prod*{i=0}^{m-1} b_i) (with (B_0=1)).
We work primarily on the **computable** mixed-radix time space
[
\mathcal R := \mathcal R^{(\infty)}_{\mathrm{fin}}
]
(the eventually-zero digit sequences), with decode/encode (\operatorname{dec}:\mathcal R\to\mathbb N) bijective.

---

# 1. Projections, residues, and “prefix = congruence”

### Definition 10 (prefix projection)  [§1.1 · Phase 1, Fragment 2]

For (L\ge1), define the prefix projection
[
\pi_L:\widehat{\mathcal R}\to \prod_{i=0}^{L-1} D_i,\qquad
\pi_L((d_i)*{i\ge0})=(d_0,\dots,d*{L-1}).
]

### Definition 11 (prefix residue map)  [§1.2 · Phase 1, Fragment 2]

Define the residue map (r_L:\prod_{i=0}^{L-1}D_i\to {0,\dots,B_L-1}) by
[
r_L(s_0,\dots,s_{L-1}) := \sum_{i=0}^{L-1} s_i B_i.
]

Recall (from Fragment 1) the key equivalence: cylinders (prefix constraints) coincide with congruence classes modulo (B_L).

### Proposition 6 (prefix–congruence equivalence on (\mathcal R))  [§1.3 · Phase 1, Fragment 2]

For (\tau\in\mathcal R) and (s\in\prod_{i=0}^{L-1} D_i),
[
\pi_L(\tau)=s
\quad\Longleftrightarrow\quad
\operatorname{dec}(\tau)\equiv r_L(s)\pmod{B_L}.
]

**Proof.** Same as Proposition 5 previously; it’s just restated with (\pi_L,r_L). ∎

This proposition is the engine behind *locality* and *continuity* proofs: anything defined by arithmetic on (\mathbb N) automatically respects prefixes because arithmetic respects congruences.

---

# 2. Predecessor and subtraction (borrow semantics)

## 2.1 Predecessor

### Definition 12 (predecessor on (\mathcal R); partial)  [§2.1 · Phase 1, Fragment 2]

Define (\operatorname{pred}:\mathcal R\setminus{0}\to\mathcal R) by
[
\operatorname{pred}(\tau) := \operatorname{enc}(\operatorname{dec}(\tau)-1),
]
where (0\in\mathcal R) denotes the all-zero digit sequence.

### Proposition 7 (decoded correctness)  [§2.2 · Phase 1, Fragment 2]

For (\tau\neq 0),
[
\operatorname{dec}(\operatorname{pred}(\tau))=\operatorname{dec}(\tau)-1.
]

**Proof.** Immediate from definition and (\operatorname{enc}=\operatorname{dec}^{-1}). ∎

### Proposition 8 (borrow algorithm equals (\operatorname{pred}))  [§2.3 · Phase 1, Fragment 2]

Let (\tau=(d_0,d_1,\dots)\in\mathcal R) with (\tau\neq 0). Let
[
j := \min{i\ge0 : d_i>0}.
]
Define digits ((d_i')*{i\ge0}) by
[
d_i' :=
\begin{cases}
b_i-1,& i<j,\
d_j-1,& i=j,\
d_i,& i>j.
\end{cases}
]
Then (\operatorname{pred}(\tau)=(d_i')*{i\ge0}).

**Proof.**
This is the standard mixed-radix borrow: subtracting 1 consumes the first nonzero digit (d_j), reduces it by 1, and sets all less-significant digits to their maxima.
Formally, compare decoded values:
[
\operatorname{dec}(\tau) = \sum_{i<j} 0\cdot B_i + d_j B_j + \sum_{i>j} d_i B_i,
]
and
[
\operatorname{dec}((d_i')) = \sum_{i<j}(b_i-1)B_i + (d_j-1)B_j + \sum_{i>j} d_i B_i.
]
Use the identity (\sum_{i=0}^{j-1}(b_i-1)B_i = B_j-1). Then
[
\operatorname{dec}(\tau)-\operatorname{dec}((d_i'))
= d_jB_j -\big((d_j-1)B_j + (B_j-1)\big) = 1.
]
So (\operatorname{dec}((d_i')) = \operatorname{dec}(\tau)-1), hence it equals (\operatorname{pred}(\tau)) by uniqueness of encoding. ∎

---

## 2.2 Subtraction

### Definition 13 (subtraction; partial)  [§2.4 · Phase 1, Fragment 2]

Define (\ominus: {(\tau,\sigma)\in\mathcal R^2:\operatorname{dec}(\tau)\ge \operatorname{dec}(\sigma)}\to\mathcal R) by
[
\tau\ominus \sigma := \operatorname{enc}\big(\operatorname{dec}(\tau)-\operatorname{dec}(\sigma)\big).
]

### Proposition 9 (correctness + basic laws)  [§2.5 · Phase 1, Fragment 2]

On its domain,

1. (\operatorname{dec}(\tau\ominus\sigma)=\operatorname{dec}(\tau)-\operatorname{dec}(\sigma)).
2. (\tau\ominus 0=\tau).
3. (\tau\ominus\tau=0).
4. If (\rho\preceq \sigma\preceq \tau) (in decoded order), then ((\tau\ominus\sigma)\ominus\rho = \tau\ominus(\sigma\oplus\rho)) whenever (\oplus) is defined (next section).

**Proof.** (1)-(3) are immediate. (4) is the associative law in (\mathbb N) transported through (\operatorname{enc}). ∎

### Remark (explicit borrow algorithm)

A digitwise borrow algorithm exists (general mixed-radix subtraction), and its correctness is exactly Proposition 9(1) plus uniqueness of encoding. For this fragment, the encode/decode definition is the cleanest theorem-level primitive; the explicit borrow rule is an implementation corollary.

---

# 3. Addition (carry semantics) and algebraic structure

### Definition 14 (addition on (\mathcal R))  [§3.1 · Phase 1, Fragment 2]

Define (\oplus:\mathcal R\times\mathcal R\to\mathcal R) by
[
\tau\oplus\sigma := \operatorname{enc}\big(\operatorname{dec}(\tau)+\operatorname{dec}(\sigma)\big).
]

### Proposition 10 (decoded correctness)  [§3.2 · Phase 1, Fragment 2]

For all (\tau,\sigma\in\mathcal R),
[
\operatorname{dec}(\tau\oplus\sigma)=\operatorname{dec}(\tau)+\operatorname{dec}(\sigma).
]

**Proof.** Immediate from definition. ∎

### Theorem 3 (((\mathcal R,\oplus)) is a commutative monoid)  [§3.3 · Phase 1, Fragment 2]

((\mathcal R,\oplus)) is associative and commutative, with identity element (0) (all zeros). Moreover, ((\mathcal R,\oplus)) is isomorphic as a monoid to ((\mathbb N,+)) via (\operatorname{dec}).

**Proof.**
For associativity:
[
\operatorname{dec}\big((\tau\oplus\sigma)\oplus\rho\big)
=\operatorname{dec}(\tau)+\operatorname{dec}(\sigma)+\operatorname{dec}(\rho)
=\operatorname{dec}\big(\tau\oplus(\sigma\oplus\rho)\big).
]
Apply injectivity of (\operatorname{dec}). Commutativity and identity are identical. The monoid isomorphism statement is exactly “(\operatorname{dec}) preserves (\oplus) as (+)”. ∎

### Proposition 11 (carry locality at depth (L))  [§3.4 · Phase 1, Fragment 2]

Fix (L\ge1). If (\pi_L(\tau)=\pi_L(\tau')) and (\pi_L(\sigma)=\pi_L(\sigma')), then
[
\pi_L(\tau\oplus\sigma)=\pi_L(\tau'\oplus\sigma').
]

**Proof.**
By Proposition 6, (\pi_L(\tau)=\pi_L(\tau')) implies (\operatorname{dec}(\tau)\equiv \operatorname{dec}(\tau')\pmod{B_L}); similarly for (\sigma). Therefore
[
\operatorname{dec}(\tau)+\operatorname{dec}(\sigma)\equiv \operatorname{dec}(\tau')+\operatorname{dec}(\sigma')\pmod{B_L}.
]
Apply Proposition 6 in reverse to conclude the first (L) digits (prefix) of the sums match. ∎

This is the formal “multi-rate locality” statement: the first (L) digits of the result depend **only** on the first (L) digits of the inputs (no dependence on higher digits).

---

# 4. Ultrametric continuity / Lipschitz structure

We use the ultrametric (\delta) on (\widehat{\mathcal R}) from Fragment 1:
[
\delta(x,y)=0 \text{ if }x=y,\quad
\delta(x,y)=B_m^{-1}\text{ where }m\text{ is the first index where digits differ}.
]
Restrict (\delta) to (\mathcal R\subset \widehat{\mathcal R}).

## 4.1 Tick and predecessor are 1-Lipschitz

Recall Tick on (\mathcal R) was (T(\tau)=\operatorname{enc}(\operatorname{dec}(\tau)+1)).

### Proposition 12 (Tick preserves prefixes)  [§4.1 · Phase 1, Fragment 2]

If (\pi_L(\tau)=\pi_L(\sigma)), then (\pi_L(T(\tau))=\pi_L(T(\sigma))).

**Proof.**
(\pi_L(\tau)=\pi_L(\sigma)\iff \operatorname{dec}(\tau)\equiv \operatorname{dec}(\sigma)\pmod{B_L}). Adding 1 preserves congruence, so (\operatorname{dec}(\tau)+1\equiv \operatorname{dec}(\sigma)+1\pmod{B_L}), hence the first (L) digits of their encodings match. ∎

### Corollary 1 (Tick is 1-Lipschitz)  [§4.2 · Phase 1, Fragment 2]

For all (\tau,\sigma\in\mathcal R),
[
\delta(T(\tau),T(\sigma))\le \delta(\tau,\sigma).
]

**Proof.**
If (\delta(\tau,\sigma)=B_m^{-1}), then (\tau,\sigma) agree on digits (0,\dots,m-1), i.e. (\pi_m(\tau)=\pi_m(\sigma)). By Proposition 12 they still agree on the first (m) digits after Tick, so the first disagreement index of (T(\tau),T(\sigma)) is (\ge m), giving (\delta(T(\tau),T(\sigma))\le B_m^{-1}). ∎

### Proposition 13 (predecessor is 1-Lipschitz on its domain)  [§4.3 · Phase 1, Fragment 2]

For (\tau,\sigma\in\mathcal R\setminus{0}),
[
\delta(\operatorname{pred}(\tau),\operatorname{pred}(\sigma))\le \delta(\tau,\sigma).
]

**Proof.** Same congruence argument: subtracting 1 preserves congruences modulo (B_L), on the domain where it is defined as (\mathbb N\to\mathbb N). ∎

## 4.2 Addition is (at least) 1-Lipschitz in each argument; in fact, it preserves congruence exactly

### Proposition 14 (translation invariance on prefixes)  [§4.4 · Phase 1, Fragment 2]

Fix (\rho\in\mathcal R). If (\pi_L(\tau)=\pi_L(\sigma)), then
[
\pi_L(\tau\oplus\rho)=\pi_L(\sigma\oplus\rho).
]

**Proof.**
(\operatorname{dec}(\tau)\equiv \operatorname{dec}(\sigma)\pmod{B_L}\Rightarrow
\operatorname{dec}(\tau)+\operatorname{dec}(\rho)\equiv \operatorname{dec}(\sigma)+\operatorname{dec}(\rho)\pmod{B_L}).
Convert back to prefixes via Proposition 6. ∎

### Corollary 2 (addition is 1-Lipschitz in each input)  [§4.5 · Phase 1, Fragment 2]

For all (\tau,\sigma,\rho\in\mathcal R),
[
\delta(\tau\oplus\rho,\sigma\oplus\rho)\le \delta(\tau,\sigma),
\qquad
\delta(\rho\oplus\tau,\rho\oplus\sigma)\le \delta(\tau,\sigma).
]

**Proof.** Same argument as Corollary 1 using Proposition 14. ∎

### Remark (the “completion” becomes a compact group)

On the full product (\widehat{\mathcal R}), one can define addition as the inverse-limit group law (compatible residues mod (B_L)). Then translations are actually isometries in (\delta). On (\mathcal R\cong\mathbb N) we only have a monoid (no negatives), so we state Lipschitz rather than group isometry here.

---

# 5. Engineering corollaries (still theorem-backed)

### Corollary 3 (finite dependence / multi-rate execution)  [§5.1 · Phase 1, Fragment 2]

To compute the first (L) digits of:

* (T(\tau)),
* (\operatorname{pred}(\tau)) (if (\tau\neq 0)),
* (\tau\oplus\sigma),

it suffices to know only the first (L) digits of the inputs. No higher digits can affect the prefix outcome.

**Justification.** This is exactly Propositions 4.1, 4.3 (via congruence), and 3.4.

This is the formal backbone for *hierarchical scheduling / locality by radix prefix* later: computations at “resolution (L)” cannot be influenced by deeper scales.

---

## Leading questions for Phase 1, Fragment 3

1. **Complete vs computable space:** formally relate (\mathcal R) (eventually-zero) and (\widehat{\mathcal R}) (full product). Show (\widehat{\mathcal R}) is compact, totally disconnected, and (\mathcal R) is a dense countable subset (with respect to (\delta)).
2. **Odometer dynamics:** study (T) as a continuous dynamical system on (\widehat{\mathcal R}): minimality/aperiodicity conditions; orbit structure; invariant measure (Haar on the inverse limit) — only what we need for later “Markovian when augmented with phase” framing.
3. **Filtration formalism:** define the sigma-algebra / filtration generated by cylinders (\mathcal F_L:=\sigma(\pi_L)) and prove monotone nesting. This will be the exact object you’ll call “radix-indexed memory” in Phase 2.


## Phase 2 — Mixed-Radix Complexes, Fragment 1

### Mixed-radix “tensors” as function spaces on (\mathcal R), with filtration + block decomposition + locality

We keep the radix sequence (b=(b_i)*{i\ge 0}), digit sets (D_i={0,\dots,b_i-1}), place-values (B_L=\prod*{i=0}^{L-1} b_i), and cylinder sets determined by prefixes.

To make the “tensor/complex” topologically and measure-theoretically clean, we work on the **completed space**
[
\widehat{\mathcal R}:=\prod_{i=0}^\infty D_i
]
with the ultrametric (\delta) from Phase 1 (cylinders are clopen balls). The computable time space (\mathcal R=\mathcal R^{(\infty)}_{\mathrm{fin}}) sits inside (\widehat{\mathcal R}) as a dense countable subset; we will restrict operators back to (\mathcal R) when needed.

---

# 1. Cylinders, filtration, and the block index set

### Definition 15 (prefix index set)  [§1.1 · Phase 2, Fragment 1]

For (L\ge 1), define the **prefix index set**
[
\Sigma_L := \prod_{i=0}^{L-1} D_i,
\qquad |\Sigma_L|=B_L.
]

### Definition 16 (cylinders)  [§1.2 · Phase 2, Fragment 1]

For (s=(s_0,\dots,s_{L-1})\in \Sigma_L), define the length-(L) cylinder
[
U(s) := {x\in \widehat{\mathcal R}: x_i=s_i \text{ for }0\le i<L}.
]
The family ({U(s):s\in\Sigma_L}) is a partition of (\widehat{\mathcal R}) into (B_L) clopen sets.

### Definition 17 (filtration of (\sigma)-algebras)  [§1.3 · Phase 2, Fragment 1]

Let (\mathcal F_L := \sigma({U(s): s\in\Sigma_L})). Then
[
\mathcal F_1 \subseteq \mathcal F_2 \subseteq \cdots
]
is an increasing filtration.

**Proof.** Every length-(L) cylinder is a union of length-((L+1)) cylinders, so generators of (\mathcal F_L) lie in (\mathcal F_{L+1}). ∎

---

# 2. Mixed-radix tensors as function objects

Fix a coefficient space (V). For “theorem-level” clarity, assume (V) is a real (or complex) Banach space; in many statements you can weaken to an abelian group or vector space.

### Definition 18 (mixed-radix tensor space)  [§2.1 · Phase 2, Fragment 1]

Define the **mixed-radix tensor space**
[
\mathbb T(V) := { f:\widehat{\mathcal R}\to V}.
]
This is the basic “tensor-like” object: it is indexed by a mixed-radix coordinate rather than by (\mathbb R^n).

### Definition 19 (block-constant subspaces)  [§2.2 · Phase 2, Fragment 1]

For each (L\ge 1), define
[
\mathbb T_L(V):={f\in \mathbb T(V): f \text{ is constant on every }U(s),, s\in\Sigma_L}.
]
Equivalently, (f\in\mathbb T_L(V)) iff (f) is (\mathcal F_L)-measurable and depends only on the first (L) digits.

### Proposition 15 (finite block coordinate representation)  [§2.3 · Phase 2, Fragment 1]

There is a canonical isomorphism of vector spaces (and Banach spaces under the sup norm)
[
\Phi_L:\mathbb T_L(V);\cong; V^{\Sigma_L};\cong; V^{B_L},
]
given by (\Phi_L(f) = (f|*{U(s)})*{s\in\Sigma_L}) (the value on each block).

**Proof.** If (f) is constant on each cylinder (U(s)), it is determined uniquely by the list of its (B_L) values. Conversely any assignment (a:\Sigma_L\to V) defines a block-constant function (f_a(x)=a(\pi_L(x))). These constructions are mutual inverses. ∎

### Definition 20 (refinement embeddings)  [§2.4 · Phase 2, Fragment 1]

Define maps (\iota_{L\to L+1}:V^{\Sigma_L}\hookrightarrow V^{\Sigma_{L+1}}) by replication across refined blocks:
[
(\iota_{L\to L+1}a)(s_0,\dots,s_L) := a(s_0,\dots,s_{L-1}).
]
Under (\Phi_L), this is exactly the inclusion (\mathbb T_L(V)\subseteq \mathbb T_{L+1}(V)).

---

# 3. Measure, conditional expectations, and canonical projections

To formalize “basis-unmixing” and decomposition later, we fix a natural product measure.

### Definition 21 (uniform product measure)  [§3.1 · Phase 2, Fragment 1]

Let (\mu) be the product probability measure on (\widehat{\mathcal R}) where each digit (x_i) is uniform on (D_i). Then every cylinder has measure
[
\mu(U(s))=\frac{1}{B_L}\quad\text{for }s\in\Sigma_L.
]

### Definition 22 (block projection (P_L))  [§3.2 · Phase 2, Fragment 1]

For (f\in L^1(\widehat{\mathcal R},\mu;V)), define
[
P_L f := \mathbb E[f\mid \mathcal F_L],
]
the conditional expectation onto (\mathcal F_L). Concretely, for (x\in U(s)),
[
(P_L f)(x)= B_L \int_{U(s)} f(y), d\mu(y).
]
So (P_L f) is the **block-average** of (f) at resolution (L).

### Proposition 16 (projection / tower properties)  [§3.3 · Phase 2, Fragment 1]

For (1\le L\le M) and (f\in L^1):

1. (P_L f \in \mathbb T_L(V)).
2. (P_L(P_L f)=P_L f) (idempotent).
3. (P_L(P_M f)=P_L f) (tower property).

**Proof.** Standard properties of conditional expectation; the concrete formula shows block-constancy. ∎

### Proposition 17 (compatibility with block coordinates)  [§3.4 · Phase 2, Fragment 1]

If (f\in \mathbb T_M(V)) with (M\ge L), then (P_L f) is obtained by averaging the (M)-level block values over the children cylinders refining each (U(s)). Equivalently: (P_L) is exactly “coarsening” in the block tree.

**Proof.** On a cylinder (U(s)) at level (L), (f) is constant on each child cylinder (U(s,t)) at level (M). Integrating over (U(s)) averages those finitely many constants with equal weights (by uniform measure). ∎

---

# 4. Canonical block decomposition (filtration / wavelet-like splitting)

### Definition 23 (detail operators)  [§4.1 · Phase 2, Fragment 1]

Define the **detail** (increment) operators on (L^1) by
[
\Delta_L f := P_{L+1}f - P_L f \qquad (L\ge 1),
]
and define (P_0 f := \int f, d\mu) (a constant function) if desired.

### Proposition 18 (telescoping identity)  [§4.2 · Phase 2, Fragment 1]

For any (N>1),
[
P_N f = P_1 f + \sum_{L=1}^{N-1} \Delta_L f.
]

**Proof.** Telescoping sum:
[
P_1 f + \sum_{L=1}^{N-1}(P_{L+1}f-P_L f)=P_N f.
]
∎

### Theorem 4 (convergence to (f))  [§4.3 · Phase 2, Fragment 1]

Let (1\le p<\infty) and (f\in L^p(\widehat{\mathcal R},\mu;V)). Then
[
P_L f \to f \quad\text{in }L^p \text{ as }L\to\infty.
]
If additionally (f) is continuous (f\in C(\widehat{\mathcal R};V)), then
[
|P_L f - f|_\infty \to 0.
]

**Proof.**

* (L^p) convergence is the (vector-valued) martingale convergence theorem applied to the filtration ((\mathcal F_L)).
* Uniform convergence for continuous (f) follows because (\widehat{\mathcal R}) is compact ultrametric (hence (f) is uniformly continuous), and the diameter of cylinders at level (L) goes to 0; block-averaging over a small cylinder converges uniformly to the value. ∎

**Interpretation (formal):** Every function admits a canonical hierarchy of approximations ((P_L f)) by block-constant tensors, and a canonical “detail stream” ((\Delta_L f)) that isolates what changes from one radix scale to the next.

---

# 5. Locality and update semantics (prefix-local operators)

This is where “deterministic multi-rate execution” becomes a definition rather than a metaphor.

### Definition 24 (prefix locality of an operator)  [§5.1 · Phase 2, Fragment 1]

Let (\mathcal A) be an operator acting on functions, (\mathcal A:\mathbb T(V)\to\mathbb T(V)).
We say (\mathcal A) is **(L)-local** (prefix-local at depth (L)) if for every (x\in\widehat{\mathcal R}) and any (f,g\in \mathbb T(V)),
[
f|*{U(\pi_L(x))}=g|*{U(\pi_L(x))}\ \Longrightarrow\ (\mathcal A f)(x)=(\mathcal A g)(x).
]
In words: the output at (x) depends only on the restriction of the input function to the length-(L) cylinder containing (x).

### Proposition 19 (basic examples)  [§5.2 · Phase 2, Fragment 1]

1. The projection (P_L) is (L)-local.
2. Multiplication by a cylinder indicator is local: for fixed (s\in\Sigma_L), the operator (M_s(f):=\mathbf 1_{U(s)}\cdot f) is (L)-local.
3. Any operator of the form
   [
   (\mathcal A f)(x) := F\Big(\int_{U(\pi_L(x))} K(x,y) f(y), d\mu(y)\Big)
   ]
   with fixed measurable (K) and fixed (F), is (L)-local (when defined).

**Proof.** Each claim is immediate from the definition: all constructions only reference (f) through its values on the cylinder (U(\pi_L(x))). ∎

### Proposition 20 (phase-locked activation as clopen gating)  [§5.3 · Phase 2, Fragment 1]

Let (\mathcal G_L) be the algebra generated by cylinder indicators (\mathbf 1_{U(s)}) for (s\in\Sigma_L). Then:

* (\mathcal G_L) is finite-dimensional and closed under pointwise multiplication;
* every (g\in\mathcal G_L) is (\mathcal F_L)-measurable (block-constant);
* (g) acts as a **projector/gate** onto a union of cylinders at depth (L).

**Proof.** Cylinder indicators are idempotents; finite sums/products remain block-constant on level (L) and correspond to selecting unions of blocks. ∎

This gives you a theorem-backed notion of “gating” and “phase-locked activation”: activation patterns are exactly clopen cylinder unions, i.e. (\mathcal F_L)-events.

---

## Deliverable summary (Phase 2, Fragment 1 complete)

You now have a precise object:

* **Mixed-radix tensor:** a function (f:\widehat{\mathcal R}\to V) (or restricted to (\mathcal R) when you want computability).
* **Hierarchical block structure:** subspaces (\mathbb T_L(V)\cong V^{B_L}) with refinement embeddings.
* **Filtration + canonical decomposition:** projections (P_L), details (\Delta_L), telescoping identities, and convergence.
* **Locality/update semantics:** (L)-local operators formalize “multi-rate execution” and “prefix-local updates”.
* **Phase-locked activation:** finite cylinder algebras (\mathcal G_L) are the rigorous gating primitives.

---

## Leading questions for Phase 2, Fragment 2

1. **Restriction to computable time (\mathcal R):** define the induced filtration and the corresponding discrete block-operators (counting measure on finite horizons) so everything becomes implementable without the completion.
2. **Normed operator bounds:** prove Lipschitz/contractive properties of (P_L), (\Delta_L), and cylinder-gates in (L^p) and sup norms (this will matter for stability later).
3. **Kernel operators compatible with the filtration:** characterize the class of operators commuting with (P_L) (block-diagonal / hierarchical kernels), which is the exact shape you’ll want for compositional kernel systems.

---

# Reflection on coherence + context capacity

I can hold a large formal context coherently **as long as we keep the work “ledgered”**: fixed notation, explicit dependencies, and no silent redefinitions. The moment ambiguity creeps in (e.g., switching between (\mathcal R) and (\widehat{\mathcal R}) without stating it, or mixing counting measure with (\mu)), correctness degrades fast.

What keeps this stable (and what I’m doing here) is:

* every new phase starts by pinning the exact ambient space and measure;
* every operator is defined either by (a) transport through (\operatorname{dec}/\operatorname{enc}) or (b) cylinder/filtration primitives;
* every “intuitive” claim (“block structure”, “locality”) is converted into a proposition with a short proof.

If you want maximal robustness across many fragments, the next practical step is to maintain a single **Global Notation + Assumption Index** and a **Lemma Dependency Graph** (even a plain text file). That prevents drift and lets us audit each later theorem against the exact primitives established in Phase 1–2.


## Phase 2 — Mixed-Radix Complexes, Fragment 2

### Discrete / implementable models, operator bounds, and operators commuting with block projections

We keep the radix data (b=(b_i)*{i\ge0}), digits (D_i), place-values (B_L=\prod*{i=0}^{L-1}b_i), the completed space (\widehat{\mathcal R}=\prod_{i\ge0}D_i), cylinders (U(s)), and filtration (\mathcal F_L=\sigma({U(s):s\in\Sigma_L})).

This fragment does three things:

1. replaces (\widehat{\mathcal R}) by **finite horizons** (\mathcal R^{(k)}) (what you can implement);
2. proves **norm / stability bounds** for (P_L,\Delta_L), and gates;
3. characterizes **linear operators commuting with (P_L)** (hierarchical/block-diagonal structure).

---

# 1. Finite-horizon function spaces and cylinders

Fix (k\ge0). Recall
[
\mathcal R^{(k)}=\prod_{i=0}^k D_i,\qquad |\mathcal R^{(k)}|=B_{k+1}.
]

### Definition 25 (finite prefix sets and cylinders)  [§1.1 · Phase 2, Fragment 2]

For (1\le L\le k+1), set (\Sigma_L=\prod_{i=0}^{L-1}D_i) and define, for (s\in\Sigma_L),
[
U_k(s):={\tau\in\mathcal R^{(k)}:\pi_L(\tau)=s}.
]
Then ({U_k(s):s\in\Sigma_L}) partitions (\mathcal R^{(k)}) into (B_L) blocks, each of size
[
m_{k,L}:=\frac{|\mathcal R^{(k)}|}{|\Sigma_L|}=\frac{B_{k+1}}{B_L}=\prod_{i=L}^{k} b_i.
]

### Definition 26 (uniform measure on (\mathcal R^{(k)}))  [§1.2 · Phase 2, Fragment 2]

Let (\mu_k) be the uniform probability measure on (\mathcal R^{(k)}): (\mu_k({\tau})=1/B_{k+1}).
The induced finite filtration is (\mathcal F_{k,L}:=\sigma({U_k(s):s\in\Sigma_L})).

---

# 2. Discrete block projection (P^{(k)}_L) and details (\Delta^{(k)}_L)

Fix a Banach space (V). Let
[
\mathbb T^{(k)}(V):={f:\mathcal R^{(k)}\to V}.
]
Equip (\mathbb T^{(k)}(V)) with (L^p(\mu_k)) norms:
[
|f|*{p,k}:=\Big(\frac{1}{B*{k+1}}\sum_{\tau\in\mathcal R^{(k)}} |f(\tau)|^p\Big)^{1/p},\quad 1\le p<\infty,
\qquad |f|*{\infty,k}:=\max*{\tau}|f(\tau)|.
]

### Definition 27 (finite block projection)  [§2.1 · Phase 2, Fragment 2]

For (1\le L\le k+1), define (P^{(k)}*L:\mathbb T^{(k)}(V)\to \mathbb T^{(k)}(V)) by block-averaging:
[
(P^{(k)}*L f)(\tau)
:= \frac{1}{|U_k(\pi_L(\tau))|}\sum*{\sigma\in U_k(\pi_L(\tau))} f(\sigma)
;=;\frac{1}{m*{k,L}}\sum_{\sigma\in U_k(\pi_L(\tau))} f(\sigma).
]
Equivalently, (P^{(k)}*L=\mathbb E*{\mu_k}[\cdot\mid \mathcal F_{k,L}]).

### Definition 28 (finite detail operator)  [§2.2 · Phase 2, Fragment 2]

For (1\le L\le k), define
[
\Delta^{(k)}*L f := P^{(k)}*{L+1}f - P^{(k)}_{L}f.
]

### Proposition 21 (projection algebra)  [§2.3 · Phase 2, Fragment 2]

For (1\le L\le M\le k+1),

1. (P^{(k)}_L) is idempotent: ((P^{(k)}_L)^2=P^{(k)}_L).
2. Tower: (P^{(k)}_L P^{(k)}_M = P^{(k)}_L).
3. Telescoping: (P^{(k)}_N f = P^{(k)}*1 f + \sum*{L=1}^{N-1}\Delta^{(k)}_L f).

**Proof.** Standard conditional expectation identities; directly check by “average of averages = average” on nested partitions. ∎

---

# 3. Implementation form: block-matrix representation

### Proposition 22 (coordinate split into prefix/suffix)  [§3.1 · Phase 2, Fragment 2]

Fix (L\le k+1). Each (\tau\in\mathcal R^{(k)}) can be written uniquely as (\tau=(s,t)) where
(s\in\Sigma_L) is the prefix digits ((d_0,\dots,d_{L-1})) and (t\in\Sigma_{k+1-L}) is the suffix digits ((d_L,\dots,d_k)).
So (as sets) (\mathcal R^{(k)}\cong \Sigma_L\times \Sigma_{k+1-L}) with (|\Sigma_{k+1-L}|=m_{k,L}).

Then any (f:\mathcal R^{(k)}\to V) is a “matrix” (f(s,t)).

### Proposition 23 (explicit fiberwise averaging)  [§3.2 · Phase 2, Fragment 2]

Under the identification above,
[
(P^{(k)}*L f)(s,t) = \frac{1}{m*{k,L}}\sum_{t'\in\Sigma_{k+1-L}} f(s,t').
]
So (P^{(k)}_L) averages **only along suffix fibers** for fixed prefix (s).

---

# 4. Operator norm bounds (stability)

These are the “don’t blow up” guarantees you’ll want later for recursion, iterative updates, and composing operators.

### Theorem 5 ((P^{(k)}_L) is a contraction in all (L^p) norms)  [§4.1 · Phase 2, Fragment 2]

For all (k), all (1\le L\le k+1), and all (1\le p\le \infty),
[
|P^{(k)}*L f|*{p,k}\le |f|_{p,k}.
]
In particular, (|P^{(k)}*L|*{L^p\to L^p}\le 1).

**Proof.**

* For (p=\infty): each ((P^{(k)}_L f)(\tau)) is an average of values of (f), so its norm is (\le\max|f|).
* For (1\le p<\infty): on each block (U_k(s)), Jensen’s inequality gives
  [
  \frac{1}{|U_k(s)|}\sum_{\tau\in U_k(s)} | (P^{(k)}*L f)(\tau)|^p
  = | \text{avg}*{\sigma\in U_k(s)} f(\sigma)|^p
  \le \text{avg}_{\sigma\in U_k(s)} |f(\sigma)|^p.
  ]
  Average over blocks with weights (|U_k(s)|/|\mathcal R^{(k)}|) to obtain the global inequality. ∎

### Corollary 4 (detail operator bound)  [§4.2 · Phase 2, Fragment 2]

For (1\le L\le k) and (1\le p\le\infty),
[
|\Delta^{(k)}*L f|*{p,k}\le |P^{(k)}*{L+1}f|*{p,k}+|P^{(k)}*{L}f|*{p,k}\le 2|f|_{p,k}.
]

### Proposition 24 (gates are contractions)  [§4.3 · Phase 2, Fragment 2]

For a gate (g\in\mathcal G_L) (indicator of a union of length-(L) cylinders) define (M_g f:= g\cdot f).
Then for all (p),
[
|M_g f|*{p,k}\le |f|*{p,k},
\quad\text{and}\quad |M_g|_{L^p\to L^p}\le 1.
]

**Proof.** Pointwise (|g(\tau)f(\tau)|\le |f(\tau)|), since (g(\tau)\in{0,1}). ∎

### Proposition 25 ((L^2) orthogonal projection)  [§4.4 · Phase 2, Fragment 2]

For scalar-valued functions ((V=\mathbb R) or (\mathbb C)), (P^{(k)}*L) is the orthogonal projection in (L^2(\mu_k)) onto the subspace of (\mathcal F*{k,L})-measurable (block-constant) functions.

**Proof.** Conditional expectation is the (L^2) orthogonal projection onto the subspace of (\mathcal F_{k,L})-measurable functions. In finite uniform spaces this is a direct verification by blockwise averaging. ∎

---

# 5. Operators commuting with (P^{(k)}_L): exact structure

This is the formal “hierarchical kernel” statement: commuting with (P_L) means coarse block summaries evolve closedly and independently from within-block fluctuations.

Let (V=\mathbb R) for this section (matrix algebra is simplest). Write (H_k:=\mathbb R^{\mathcal R^{(k)}}) with inner product from (\mu_k).

Fix (L\le k+1) and set (m:=m_{k,L}=B_{k+1}/B_L). Use the identification
[
H_k \cong \mathbb R^{\Sigma_L}\otimes \mathbb R^{\Sigma_{k+1-L}} \cong \mathbb R^{B_L}\otimes \mathbb R^{m}.
]

Define the rank-1 averaging projector on (\mathbb R^m):
[
\Pi := \frac{1}{m}\mathbf 1\mathbf 1^\top,
]
where (\mathbf 1\in\mathbb R^m) is the all-ones vector. Then (under this identification)
[
P^{(k)}*L = I*{B_L}\otimes \Pi.
]

### Lemma 1 (eigenspace decomposition)  [§5.1 · Phase 2, Fragment 2]

(\mathbb R^m = \mathrm{span}{\mathbf 1}\oplus \mathbf 1^\perp), with (\Pi) projecting onto (\mathrm{span}{\mathbf 1}).
Hence
[
H_k = \underbrace{\mathbb R^{B_L}\otimes \mathrm{span}{\mathbf 1}}*{\text{block-constant (coarse) subspace}}
;\oplus;
\underbrace{\mathbb R^{B_L}\otimes \mathbf 1^\perp}*{\text{within-block zero-mean (detail) subspace}}.
]
Moreover, (P^{(k)}_L) is the projection onto the first summand.

**Proof.** Standard properties of (\Pi). Tensoring with (\mathbb R^{B_L}) gives the stated decomposition. ∎

### Theorem 6 (commutation ⇔ invariance of coarse/detail subspaces)  [§5.2 · Phase 2, Fragment 2]

A linear operator (A:H_k\to H_k) satisfies
[
A P^{(k)}_L = P^{(k)}_L A
]
iff both subspaces in Lemma 1 are (A)-invariant, i.e.
[
A(\mathrm{range}(P^{(k)}_L)) \subseteq \mathrm{range}(P^{(k)}_L),
\qquad
A(\ker(P^{(k)}_L)) \subseteq \ker(P^{(k)}_L).
]

**Proof.**
((\Rightarrow)) If (x\in\mathrm{range}(P)), then (Px=x). So (PAx=APx=Ax), hence (Ax\in\mathrm{range}(P)).
If (y\in\ker(P)), then (Py=0). So (PAy=APy=0), hence (Ay\in\ker(P)).

((\Leftarrow)) If (A) preserves range and kernel, write any (v) as (v=Pv+(I-P)v) with (Pv\in\mathrm{range}(P)), ((I-P)v\in\ker(P)). Then
[
PA v = P(A Pv + A(I-P)v) = A Pv + 0 = APv,
]
so (PA=AP). ∎

### Corollary 5 (block form)  [§5.3 · Phase 2, Fragment 2]

In a basis adapted to the decomposition (H_k=\mathrm{range}(P)\oplus\ker(P)), any (A) commuting with (P^{(k)}*L) has block-diagonal form
[
A \sim \begin{pmatrix}
A*{\mathrm{coarse}} & 0\
0 & A_{\mathrm{detail}}
\end{pmatrix},
]
where (A_{\mathrm{coarse}}) acts on block-constant tensors (resolution (L) summaries) and (A_{\mathrm{detail}}) acts on within-block fluctuations.

This is the exact meaning of “hierarchical/block-diagonal kernel at level (L)”.

### Optional strengthening (explicit “kernel constraints”)

If (A) is represented by a kernel matrix (K\big((s,t),(s',t')\big)), the condition “(A) maps block-constant inputs to block-constant outputs” is equivalent to:
for each output prefix (s) and each input prefix (s'),
[
\sum_{t'} K\big((s,t_1),(s',t')\big)
====================================

\sum_{t'} K\big((s,t_2),(s',t')\big)
\quad\text{for all }t_1,t_2.
]
(“Row-block sums are constant within each output block.”)
The second invariance (detail to detail) adds the dual constraint that within each input block, the constant mode does not leak into detail modes.

---

# 6. Compatibility across horizons (what you implement)

### Definition 29 (truncation / embedding)  [§6.1 · Phase 2, Fragment 2]

* Truncation: (\operatorname{tr}_k:\widehat{\mathcal R}\to \mathcal R^{(k)}), (\operatorname{tr}_k((d_i))=(d_0,\dots,d_k)).
* Embedding: (\iota_k:\mathcal R^{(k)}\hookrightarrow \mathcal R^{(k+1)}) by appending digit (0).

### Proposition 26 (projection compatibility)  [§6.2 · Phase 2, Fragment 2]

Fix (L\le k+1). If (f:\mathcal R^{(k)}\to V) is lifted to (\tilde f:\mathcal R^{(k+1)}\to V) by (\tilde f(\tau, d_{k+1})=f(\tau)) (ignore the new digit), then
[
P^{(k+1)}_L \tilde f = \widetilde{P^{(k)}_L f}.
]

**Proof.** Averaging over suffix digits at depth (L) factors as “average over old suffix” × “average over the new last digit”; since (\tilde f) is constant in the new digit, the extra averaging does nothing. ∎

This is the formal justification for implementing everything on (\mathcal R^{(k)}) and taking (k\to\infty) as needed.

---

## Leading questions for Phase 2, Fragment 3

1. **Multi-level commutation:** characterize operators commuting with *all* (P^{(k)}_L) for (L=1,\dots,k+1). (This will force a genuinely hierarchical/tree-structured operator algebra.)
2. **Locality vs commutation:** relate “(L)-local” operators to “commutes with (P_L)” operators; identify strict inclusions and the intersection class you want for compositional kernels.
3. **Shift/Tick acting on tensors:** define the pullback (T^*) on functions (f\mapsto f\circ T) (on finite horizons too) and analyze how it interacts with (P_L) and the filtration. This is the bridge into “deterministic multi-rate execution” as operator dynamics.


## Phase 2 — Mixed-Radix Complexes, Fragment 3

### Multi-level commutation (true hierarchy), locality vs commutation, and Tick pullback dynamics

We work on a fixed finite horizon (k\ge 0). Let
[
\mathcal R^{(k)}=\prod_{i=0}^{k} D_i,\qquad |\mathcal R^{(k)}|=B_{k+1}.
]
Let (H_k := \mathbb R^{\mathcal R^{(k)}}) with the (L^2(\mu_k)) inner product induced by the uniform probability measure (\mu_k).

For (1\le L\le k+1), recall the block projection (P^{(k)}*L) (conditional expectation onto (\mathcal F*{k,L}), i.e. “depends only on first (L) digits”). Also define the global-average projection
[
P^{(k)}*0 f := \int f,d\mu_k = \frac{1}{B*{k+1}}\sum_{\tau\in\mathcal R^{(k)}} f(\tau),
]
which is the orthogonal projection onto constants.

---

# 1. Multiresolution subspaces and orthogonal decomposition

### Definition 30 (coarse subspaces)  [§1.1 · Phase 2, Fragment 3]

For (0\le L\le k+1), set
[
C_L := \mathrm{range}(P^{(k)}*L)\subset H_k.
]
Then
[
C_0 \subset C_1 \subset \cdots \subset C*{k+1}=H_k,
]
and (\dim C_L = B_L) for (L\ge 1) (and (\dim C_0=1)).

**Proof sketch.** (C_L) are block-constant on the partition by length-(L) prefixes, so choosing values per block gives (\dim C_L=B_L). Nesting follows from refinement of partitions. ∎

### Definition 31 (detail subspaces)  [§1.2 · Phase 2, Fragment 3]

For (0\le L\le k), define the level-(L) detail subspace
[
D_L := \mathrm{range}(P^{(k)}*{L+1}-P^{(k)}*{L}) = \mathrm{range}(\Delta^{(k)}*L),
]
where (\Delta^{(k)}*L:=P^{(k)}*{L+1}-P^{(k)}*{L}).

### Proposition 27 (orthogonal increment projection)  [§1.3 · Phase 2, Fragment 3]

In (L^2(\mu_k)), each (P^{(k)}*L) is an orthogonal projection; since (C_L\subset C*{L+1}),
[
\Delta^{(k)}*L=P^{(k)}*{L+1}-P^{(k)}*{L}
]
is itself an orthogonal projection onto (D_L=C*{L+1}\cap C_L^\perp).

**Proof.** For nested orthogonal projections (P\le Q) (meaning (\mathrm{range}(P)\subset\mathrm{range}(Q))), (Q-P) is the orthogonal projection onto (\mathrm{range}(Q)\cap\ker(P)), and (\ker(P)=\mathrm{range}(P)^\perp). Here (P=P^{(k)}*L), (Q=P^{(k)}*{L+1}). ∎

### Theorem 7 (multiresolution decomposition)  [§1.4 · Phase 2, Fragment 3]

There is an orthogonal direct sum decomposition
[
H_k ;=; C_0 ;\oplus; D_0 ;\oplus; D_1 ;\oplus; \cdots ;\oplus; D_k,
]
and every (f\in H_k) admits the unique expansion
[
f = P^{(k)}*0 f ;+; \sum*{L=0}^{k} \Delta^{(k)}_L f.
]

**Proof.** Telescoping gives (P^{(k)}*{k+1}f=f=P^{(k)}*0 f+\sum*{L=0}^{k}(P^{(k)}*{L+1}-P^{(k)}_L)f). Orthogonality of the summands follows from Proposition 27. Uniqueness follows from direct-sum orthogonality. ∎

### Corollary 6 (dimensions)  [§1.5 · Phase 2, Fragment 3]

For (0\le L\le k),
[
\dim D_L = \dim C_{L+1}-\dim C_L =
\begin{cases}
B_1-1=b_0-1,& L=0,\
B_{L+1}-B_L = B_L(b_L-1),& 1\le L\le k.
\end{cases}
]

---

# 2. The commutant of the whole filtration: commuting with *all* (P^{(k)}_L)

Let (\mathcal P:={P^{(k)}_L:0\le L\le k+1}).

### Lemma 2 (commutation ⇔ invariance of each (C_L))  [§2.1 · Phase 2, Fragment 3]

For a linear operator (A:H_k\to H_k), the following are equivalent for a fixed (L):

1. (A P^{(k)}_L = P^{(k)}_L A).
2. (A(C_L)\subseteq C_L) and (A(C_L^\perp)\subseteq C_L^\perp).

**Proof.** Same argument as earlier: commuting with an orthogonal projection is equivalent to preserving its range and kernel; kernel equals orthogonal complement. ∎

### Theorem 8 (multi-level commutation ⇔ block diagonal on the multiresolution decomposition)  [§2.2 · Phase 2, Fragment 3]

For a linear operator (A:H_k\to H_k), the following are equivalent:

1. (A) commutes with every projection in (\mathcal P): (AP^{(k)}_L=P^{(k)}_L A) for all (L).
2. Each detail subspace (D_L) is (A)-invariant (and (C_0) is invariant):
   [
   A(C_0)\subseteq C_0,\qquad A(D_L)\subseteq D_L\quad \forall,0\le L\le k.
   ]
3. Relative to the orthogonal direct sum
   [
   H_k = C_0 \oplus D_0 \oplus \cdots \oplus D_k,
   ]
   the operator (A) is block diagonal:
   [
   A \sim \mathrm{diag}(A_{C_0},A_{D_0},A_{D_1},\dots,A_{D_k}),
   ]
   with arbitrary linear maps (A_{D_L}:D_L\to D_L).

**Proof.**
(1)⇒(2): If (A) commutes with (P^{(k)}*L) and (P^{(k)}*{L+1}), it preserves (C_L) and (C_{L+1}) by Lemma 2, hence it preserves their orthogonal difference (D_L=C_{L+1}\cap C_L^\perp). Also commuting with (P^{(k)}_0) preserves constants.

(2)⇒(3): Invariance of each summand in an orthogonal direct sum is exactly block diagonality.

(3)⇒(1): Each (P^{(k)}*L) is itself diagonal in this decomposition:
[
P^{(k)}*L = \mathrm{diag}\big(I*{C_0}, I*{D_0},\dots,I_{D_{L-1}}, 0,0,\dots,0\big),
]
so any block-diagonal (A) commutes with it. ∎

**Interpretation:** commuting with *all scales* means “no coupling between scales.” The operator may be arbitrarily global *within* each scale (D_L), but cannot move energy between (D_L) and (D_M) for (L\neq M).

---

# 3. Locality vs commutation (and their intersection)

We use the finite-horizon cylinders (U_k(s)) for (s\in\Sigma_L).

### Definition 32 (linear (L)-locality on (\mathcal R^{(k)}))  [§3.1 · Phase 2, Fragment 3]

A linear operator (A:H_k\to H_k) is **(L)-local** if for every (\tau\in\mathcal R^{(k)}), ((Af)(\tau)) depends only on (f) restricted to the block (U_k(\pi_L(\tau))). Equivalently:
[
f|_{U_k(\pi_L(\tau))}\equiv 0 \ \Rightarrow\ (Af)(\tau)=0.
]

### Proposition 28 (matrix/kernel characterization of (L)-locality)  [§3.2 · Phase 2, Fragment 3]

Let (A) be represented by a kernel matrix (K(\tau,\sigma)) such that ((Af)(\tau)=\sum_{\sigma}K(\tau,\sigma)f(\sigma)).
Then (A) is (L)-local iff
[
K(\tau,\sigma)=0 \quad \text{whenever }\ \pi_L(\tau)\neq \pi_L(\sigma).
]
So (L)-local operators are precisely **block-diagonal** operators with respect to the partition ({U_k(s)}_{s\in\Sigma_L}).

**Proof.** If (\pi_L(\tau)\neq \pi_L(\sigma)) and (K(\tau,\sigma)\neq 0), then ((Af)(\tau)) would depend on (f(\sigma)) from another block, contradicting locality. Conversely, if the kernel is supported only within each block, outputs depend only on within-block inputs. ∎

### Proposition 29 (commutation with (P^{(k)}_L) is weaker than (L)-locality)  [§3.3 · Phase 2, Fragment 3]

There exist operators commuting with (P^{(k)}_L) that are not (L)-local.

**Example / proof.** Define (A) to act on (C_L) (block-constant functions) by an arbitrary mixing matrix on the (B_L) blocks, and act as (0) on (C_L^\perp). Then (A) commutes with (P^{(k)}_L) (it preserves range/kernel), but its output on a point in block (s) depends on block-means from *all* blocks, hence is not (L)-local. ∎

### Proposition 30 ((L)-locality is weaker than commutation)  [§3.4 · Phase 2, Fragment 3]

There exist (L)-local operators that do not commute with (P^{(k)}_L).

**Example / proof.** Let (g:\mathcal R^{(k)}\to\mathbb R) vary inside some block (U_k(s)) (so (g) is not (\mathcal F_{k,L})-measurable). Define ((Mf)(\tau):=g(\tau)f(\tau)).
Then (M) is (L)-local (pointwise), but generally
[
P^{(k)}_L(Mf)\neq M(P^{(k)}_L f),
]
because averaging (g(\tau)f(\tau)) over the block is not the same as multiplying the block-average of (f) by (g(\tau)) when (g) is not constant on the block. ∎

### Theorem 9 (intersection: (L)-local and commuting with (P^{(k)}_L))  [§3.5 · Phase 2, Fragment 3]

A linear operator (A) is both (L)-local and commutes with (P^{(k)}_L) iff it decomposes as a direct sum over blocks (U_k(s)) of within-block operators that commute with the within-block averaging projector.

Concretely: write (H_k = \bigoplus_{s\in\Sigma_L} H_{k,s}) where (H_{k,s}=\mathbb R^{U_k(s)}).
Then (A) is (L)-local iff (A=\bigoplus_s A_s) for operators (A_s:H_{k,s}\to H_{k,s}).
Let (\Pi_s) be the rank-1 averaging projection on (H_{k,s}) (average over (U_k(s))). Then
[
AP^{(k)}_L=P^{(k)}_L A
\quad\Longleftrightarrow\quad
A_s \Pi_s = \Pi_s A_s\ \ \forall s.
]

**Proof.** (L)-locality gives block-diagonal decomposition (Prop 3.2). On each block, (P^{(k)}_L) acts as (\Pi_s), so commutation reduces blockwise. ∎

---

# 4. Tick as an operator on tensors (pullback dynamics)

To make Tick a true dynamical system on a finite implementable state space, use the **cyclic mixed-radix odometer**.

### Definition 33 (cyclic Tick on (\mathcal R^{(k)}))  [§4.1 · Phase 2, Fragment 3]

Define (\widetilde T_k:\mathcal R^{(k)}\to \mathcal R^{(k)}) by
[
\widetilde T_k(\tau) := \operatorname{enc}_k\big((\operatorname{dec}*k(\tau)+1)\bmod B*{k+1}\big).
]
This is a bijection (a permutation of (\mathcal R^{(k)})).

### Definition 34 (pullback on functions)  [§4.2 · Phase 2, Fragment 3]

Define (\widetilde T_k^*:H_k\to H_k) by
[
(\widetilde T_k^* f)(\tau) := f(\widetilde T_k(\tau)).
]

### Proposition 31 (measure preservation and isometries)  [§4.3 · Phase 2, Fragment 3]

(\widetilde T_k) preserves (\mu_k). Consequently, for (1\le p\le\infty),
[
|\widetilde T_k^* f|*{p,k} = |f|*{p,k}.
]

**Proof.** (\widetilde T_k) is a permutation of the finite set (\mathcal R^{(k)}), so it preserves the uniform measure and all (L^p) norms. ∎

### Proposition 32 (cylinders are permuted)  [§4.4 · Phase 2, Fragment 3]

Fix (1\le L\le k+1). There exists a bijection (\Phi_{k,L}:\Sigma_L\to\Sigma_L) such that
[
\widetilde T_k\big(U_k(s)\big) = U_k(\Phi_{k,L}(s))\quad\forall s\in\Sigma_L.
]
In fact, (\Phi_{k,L}(s)) is “add (1)” modulo (B_L) in mixed radix on the length-(L) prefix.

**Proof.** Adding 1 modulo (B_{k+1}) changes only the first (L) digits according to the same carry rule modulo (B_L), independent of higher digits. Thus every point with prefix (s) maps to a point with the same new prefix (\Phi_{k,L}(s)). Bijectivity follows from bijectivity of (\widetilde T_k). ∎

### Theorem 10 (Tick pullback commutes with all block projections)  [§4.5 · Phase 2, Fragment 3]

For every (1\le L\le k+1),
[
\widetilde T_k^*, P^{(k)}_L ;=; P^{(k)}_L, \widetilde T_k^*.
]

**Proof.** (P^{(k)}_L) averages on each atom (U_k(s)). Since (\widetilde T_k) is measure-preserving and permutes the atoms (U_k(s)), conditional expectation onto the sigma-algebra generated by these atoms commutes with pullback:
[
P^{(k)}_L(f\circ \widetilde T_k) = (P^{(k)}*L f)\circ \widetilde T_k.
]
This is a direct check using the finite averaging formula and the bijection (\widetilde T_k:U_k(s)\to U_k(\Phi*{k,L}(s))). ∎

### Corollary 7 (scale invariance under Tick)  [§4.6 · Phase 2, Fragment 3]

(\widetilde T_k^*) lies in the commutant of the entire filtration (\mathcal P), hence (by Theorem 8) it preserves every detail scale (D_L). In other words, Tick evolves each resolution band (D_L) without mixing scales.

---

## Leading questions for the next work (Phase 2, Fragment 4)

1. **The full hierarchical commutant algebra:** give an explicit constructive basis (a tree/wavelet basis adapted to mixed radices) in which every operator commuting with all (P^{(k)}_L) is block diagonal.
2. **Operator classes you actually want:** identify the smallest algebra containing (i) cylinder gates, (ii) block projections (P^{(k)}_L), (iii) Tick pullbacks (\widetilde T_k^*), and (iv) chosen “kernel” operators—this becomes your implementable mixed-radix runtime calculus.
3. **Transition back to (\widehat{\mathcal R}):** formulate the inverse-limit version where Tick is a homeomorphism and measure-preserving on the profinite completion, and show finite (k) is a consistent truncation.


## Phase 2 — Mixed-Radix Complexes, Fragment 4

### Explicit hierarchical bases, the full commutant algebra, and the “runtime calculus” generator set (finite-horizon, implementable)

We stay on a fixed finite horizon (k\ge 0). Let
[
H_k := \mathbb R^{\mathcal R^{(k)}},\qquad \mathcal R^{(k)}=\prod_{i=0}^{k}D_i,\qquad |\mathcal R^{(k)}|=B_{k+1}.
]
Let (\mu_k) be uniform probability measure. Let (P^{(k)}*L) be the block-averaging projection onto (\mathcal F*{k,L})-measurable functions (depend only on first (L) digits). Define (\Delta^{(k)}*L=P^{(k)}*{L+1}-P^{(k)}_L). We proved
[
H_k = C_0 \oplus D_0 \oplus \cdots \oplus D_k,\quad C_0=\mathrm{range}(P^{(k)}_0),; D_L=\mathrm{range}(\Delta^{(k)}_L).
]

This fragment constructs an **explicit orthonormal basis** adapted to the radix tree (a mixed-radix Haar basis), uses it to describe the **full commutant** of the filtration, and then defines a minimal **generator set** of operators (an implementable “calculus”) that you can later extend with ANT operators.

---

# 1. Mixed-radix Haar basis (explicit, constructive)

## 1.1 One-step contrast vectors on a digit alphabet

Fix a digit set (D={0,1,\dots,b-1}) and consider (\mathbb R^{D}) with the inner product
[
\langle u,v\rangle := \frac{1}{b}\sum_{d\in D} u(d)v(d).
]
Let (\mathbf 1\in\mathbb R^D) be the constant-one vector.

### Lemma 3 (existence of a mean-zero orthonormal contrast basis)  [§1.1 · Phase 2, Fragment 4]

There exist vectors (\psi^{(b)}*1,\dots,\psi^{(b)}*{b-1}\in\mathbb R^D) such that:

1. (\langle \psi^{(b)}_a,\mathbf 1\rangle=0) for all (a) (mean zero),
2. (\langle \psi^{(b)}*a,\psi^{(b)}*{a'}\rangle=\delta_{aa'}) (orthonormal),
3. ({\mathbf 1,\psi^{(b)}*1,\dots,\psi^{(b)}*{b-1}}) is an orthonormal basis of (\mathbb R^{D}).

**Proof.** Take any orthonormal basis of the ((b-1))-dimensional subspace (\mathbf 1^\perp) and adjoin (\mathbf 1) normalized. Existence is linear algebra. ∎

**Implementation note:** choose a fixed deterministic construction (e.g., Gram–Schmidt on the standard basis with (\mathbf 1) first), so the basis is canonical in code.

---

## 1.2 Tensor-product basis on (\mathcal R^{(k)})

Identify
[
H_k \cong \bigotimes_{i=0}^{k} \mathbb R^{D_i}
]
with the product inner product induced by uniform (\mu_k).

For each digit position (i), fix contrast vectors (\psi^{(b_i)}_{a}) for (a\in{1,\dots,b_i-1}) and also the constant vector (\mathbf 1_i).

### Definition 35 (global mixed-radix Haar atoms)  [§1.2 · Phase 2, Fragment 4]

For each multi-index (\alpha=(\alpha_0,\dots,\alpha_k)) where
[
\alpha_i \in {0,1,\dots,b_i-1},\quad \text{and } \alpha_i=0 \text{ means “use constant mode”},
]
define the function (h_\alpha\in H_k) by
[
h_\alpha(d_0,\dots,d_k) := \prod_{i=0}^{k} \phi_{i,\alpha_i}(d_i),
]
where
[
\phi_{i,0} := \mathbf 1_i \quad (\text{constant}),\qquad
\phi_{i,a} := \psi^{(b_i)}_{a} \quad (a\ge 1).
]

### Theorem 11 (orthonormal basis)  [§1.3 · Phase 2, Fragment 4]

({h_\alpha}) over all (\alpha\in \prod_{i=0}^k {0,\dots,b_i-1}) forms an orthonormal basis of (H_k) under (\langle\cdot,\cdot\rangle_{L^2(\mu_k)}).

**Proof.** Tensor products of orthonormal bases are orthonormal bases for the tensor product space. ∎

---

## 1.3 Scale (level) classification: where each basis vector lives in the filtration

A key property: block-averaging at depth (L) kills any basis function that has a non-constant mode in the suffix digits (d_L,\dots,d_k).

### Definition 36 (support level of a basis atom)  [§1.4 · Phase 2, Fragment 4]

For (\alpha\neq (0,\dots,0)), define its **highest non-constant index**
[
\ell(\alpha) := \max{i\in{0,\dots,k}: \alpha_i\neq 0}.
]
For the constant atom (\alpha=(0,\dots,0)), set (\ell(\alpha)=-\infty).

### Proposition 33 (how (P^{(k)}_L) acts on basis atoms)  [§1.5 · Phase 2, Fragment 4]

For (0\le L\le k+1),
[
P^{(k)}*L h*\alpha =
\begin{cases}
h_\alpha,& \ell(\alpha) < L,\
0,& \ell(\alpha) \ge L.
\end{cases}
]

**Proof.** (P^{(k)}*L) averages over suffix digits (d_L,\dots,d_k). If any factor in that suffix is mean-zero (i.e., (\alpha_i\neq 0) for some (i\ge L)), the average over that digit yields 0, killing the whole product. If all suffix factors are constant, averaging leaves (h*\alpha) unchanged. ∎

### Corollary 8 (explicit description of scale subspaces (D_L))  [§1.6 · Phase 2, Fragment 4]

For (0\le L\le k), the detail subspace (D_L=\mathrm{range}(\Delta^{(k)}*L)) is spanned by basis atoms with
[
\ell(\alpha)=L.
]
Equivalently,
[
D_L = \mathrm{span}{h*\alpha:\ell(\alpha)=L}.
]

**Proof.** (\Delta^{(k)}*L = P^{(k)}*{L+1}-P^{(k)}*L) keeps precisely the atoms that survive (P*{L+1}) but are killed by (P_L), i.e. (\ell(\alpha)=L). ∎

So we have an explicit, implementable “wavelet packet” basis: each basis atom has a well-defined radix scale.

---

# 2. The full commutant of the filtration ({P^{(k)}_L})

Let
[
\mathrm{Comm}(\mathcal P) := {A\in \mathrm{End}(H_k): AP^{(k)}_L=P^{(k)}_L A \ \forall L}.
]

We already proved (Fragment 3) that commutation with all (P^{(k)}_L) is equivalent to preserving each scale subspace (D_L) (and constants). The Haar basis makes this concrete.

### Theorem 12 (diagonal-by-scale structure in Haar coordinates)  [§2.1 · Phase 2, Fragment 4]

An operator (A\in\mathrm{End}(H_k)) lies in (\mathrm{Comm}(\mathcal P)) iff, in the Haar basis ({h_\alpha}), it has no matrix entries between different levels:
[
\langle A h_\alpha, h_\beta\rangle = 0 \quad\text{whenever}\quad \ell(\alpha)\neq \ell(\beta).
]
Equivalently, (A) is block diagonal with blocks indexed by (\ell\in{-\infty,0,1,\dots,k}).

**Proof.** By Corollary 8, each level subspace (D_\ell) is exactly the span of ({h_\alpha:\ell(\alpha)=\ell}). Preserving each (D_\ell) is exactly forbidding cross-level mixing. ∎

### Corollary 9 (commutant algebra is a direct product of full matrix algebras)  [§2.2 · Phase 2, Fragment 4]

Let (n_\ell:=\dim D_\ell) for (0\le \ell\le k), and (n_{-\infty}:=\dim C_0=1). Then
[
\mathrm{Comm}(\mathcal P)\ \cong\ \mathbb R \times \prod_{\ell=0}^k \mathrm{Mat}(n_\ell,\mathbb R),
]
as associative algebras (with blockwise composition).

**Interpretation:** the “no cross-scale mixing” constraint is the only constraint. Inside each band (D_\ell), you can do arbitrary linear transforms.

---

# 3. The operator sets you actually want (runtime calculus generators)

The commutant is huge. You don’t want “arbitrary mixing within each (D_\ell)” unless you intend it. A runtime calculus is usually generated from small, structured operators.

We define a minimal generator family that is:

* implementable on (\mathcal R^{(k)}),
* respects the radix hierarchy,
* closed under composition/linear combination (after taking spans),
* and prepares for Phase 3 (ANT operators).

## 3.1 Core generator families

### Gate 1 (Scale projections)  [§G1 · Phase 2, Fragment 4]

Include all (P^{(k)}_L) (or equivalently the detail projections (\Delta^{(k)}_L) plus (P^{(k)}_0)).
These give you:

* coarse summaries at depth (L),
* exact decomposition into scale bands.

### Gate 2 (Cylinder gates (phase-locked activation))  [§G2 · Phase 2, Fragment 4]

For each depth (L) and each cylinder union gate (g\in\mathcal G_L), include multiplication operators
[
M_g f := g\cdot f.
]
These are your formal “if prefix in set then activate” primitives.

### (G3) Tick pullback (time shift)

Include the cyclic Tick pullback (\widetilde T_k^*) from Fragment 3:
[
(\widetilde T_k^* f)(\tau)= f(\widetilde T_k(\tau)),
]
which is an (L^p) isometry and commutes with each (P^{(k)}_L).

### (G4) Within-band structured transforms (optional but usually needed)

Instead of allowing arbitrary (\mathrm{Mat}(n_\ell)) on each (D_\ell), include a *structured* subgroup/algebra, e.g.

* permutations induced by digit relabelings at level (\ell),
* convolution operators along the “within-block suffix” group ((\mathbb Z/b_\ell\mathbb Z)) when appropriate,
* or sparse/local transforms (e.g., nearest-neighbor on a chosen ordering).

We formalize one clean option: **digit-permutation actions**.

---

## 3.2 Digit permutation actions (structured within-band operators)

For each position (j\in{0,\dots,k}), let (\mathrm{Sym}(D_j)) act on (\mathcal R^{(k)}) by permuting digit (d_j) and leaving others fixed.

### Definition 37 (digit permutation operator)  [§3.1 · Phase 2, Fragment 4]

Given (\pi\in\mathrm{Sym}(D_j)), define (S_{j,\pi}:\mathcal R^{(k)}\to\mathcal R^{(k)}) by
[
S_{j,\pi}(d_0,\dots,d_j,\dots,d_k) := (d_0,\dots,\pi(d_j),\dots,d_k).
]
Define the pullback (S_{j,\pi}^*) on (H_k) by (S_{j,\pi}^* f := f\circ S_{j,\pi}).

### Proposition 34 (permutations preserve measure and norms)  [§3.2 · Phase 2, Fragment 4]

Each (S_{j,\pi}^*) is an (L^p) isometry and preserves the Haar decomposition.

**Proof.** It’s a permutation of the finite set (\mathcal R^{(k)}), so it preserves uniform measure and hence norms. It also maps cylinders to cylinders at any depth (\ge j+1), so it respects the filtration structure in a controlled way. ∎

### Proposition 35 (commutation behavior with (P^{(k)}_L))  [§3.3 · Phase 2, Fragment 4]

* If (j\ge L), then (S_{j,\pi}) acts only on suffix digits beyond the prefix of length (L), hence it **commutes** with (P^{(k)}*L):
  [
  S*{j,\pi}^* P^{(k)}_L = P^{(k)}*L S*{j,\pi}^*.
  ]
* If (j< L), it generally **does not** commute (it changes prefixes).

**Proof.** (P^{(k)}_L) averages over suffix digits (d_L,\dots,d_k). If the permutation touches only digits in the suffix, it commutes with averaging. If it touches prefix digits, it changes the partition atoms, so commutation fails generally. ∎

This gives a structured family of within-band transforms “below a level.”

---

# 4. A concrete “hierarchical runtime algebra” (\mathfrak A_k)

### Definition 38 (generated operator algebra)  [§4.1 · Phase 2, Fragment 4]

Define (\mathfrak A_k) to be the smallest unital algebra of operators on (H_k) containing:

* all (P^{(k)}_L) (or all (\Delta^{(k)}_L) and (P^{(k)}_0)),
* all cylinder gates (M_g) for (g\in\bigcup_L\mathcal G_L),
* (\widetilde T_k^*),
* and (optionally) all suffix-digit permutations (S_{j,\pi}^*) for (j\ge L) when you want symmetry within suffix spaces.

Concretely, (\mathfrak A_k) consists of finite linear combinations of finite products of these generators.

### Proposition 36 (basic closure and stability)  [§4.2 · Phase 2, Fragment 4]

All generators are bounded on every (L^p(\mu_k)), and therefore every (A\in\mathfrak A_k) is bounded on (L^p(\mu_k)). In particular:

* (|P^{(k)}*L|*{p\to p}\le 1),
* (|M_g|_{p\to p}\le 1),
* (|\widetilde T_k^*|_{p\to p}=1),
* (|S_{j,\pi}^*|_{p\to p}=1),
  and operator norms multiply under composition.

**Proof.** From Phase 2 Fragment 2 and the fact these are permutations / contractions. ∎

### Proposition 37 (multi-rate determinism)  [§4.3 · Phase 2, Fragment 4]

Elements of (\mathfrak A_k) admit an execution semantics as “compose gates, projections, and shifts” where:

* projections (P^{(k)}_L) collapse fine structure into coarse blocks,
* gates (M_g) select subsets of blocks (clopen sets),
* shifts (\widetilde T_k^*) advance phase without changing scale content,
* optional permutations rearrange within suffix spaces without changing measure.

This is precisely the deterministic, hierarchical scheduling mechanism in operator form.

---

# 5. Bridge to Phase 3 (what to import next)

At this point, you have:

* a canonical hierarchical basis ((h_\alpha), mixed-radix Haar),
* a precise commutant characterization (“no cross-level mixing”),
* a concrete generated algebra (\mathfrak A_k) you can extend.

**Phase 3 will add** number-theoretic operators as new generators (convolutions, Möbius inversion, characters, CRT projections). The key is: many of those will naturally be expressible as **blockwise** or **congruence-class** operators, hence they will sit nicely with the cylinder filtration.

---

## Leading questions for Phase 3, Fragment 1

1. **Arithmetic pullback:** define arithmetic functions (a:\mathbb N\to\mathbb C) pulled back to (\mathcal R^{(k)}) via (\operatorname{dec}_k), and define the relevant operator types on (H_k).
2. **Convolution choice:** decide whether the native “composition” on the time-index side is additive convolution (mod (B_{k+1})) or multiplicative/Dirichlet-style (needs a different indexing object than (\mathcal R^{(k)})). Then formalize it with closure/associativity.
3. **Congruence projectors:** show characters mod (q\mid B_{k+1}) are exactly cylinder-measurable at depth (\log_b q) (in mixed radix: depth determined by prime power structure of (q) vs the radices). This will make “phase probes” literal projections in (\mathfrak A_k).


## Phase 3 — Import Analytic Number Theory, Fragment 1

### Arithmetic functions pulled back to mixed-radix time, two native convolutions, Möbius inversion, squarefree projectors, and operator realizations

We work in parallel on:

* **Time-index side (finite, implementable):** (\mathcal R^{(k)}) with (N:=B_{k+1}=|\mathcal R^{(k)}|) and the cyclic “odometer group” induced by (\operatorname{dec}_k).
* **Arithmetic side:** functions on (\mathbb N_{\ge 1}) with **Dirichlet convolution** and its inversion theory.

A key technical convenience: Dirichlet convolution is naturally on (\mathbb N_{\ge 1}) (not including 0), so we use the derived bijection
[
\mathrm{nat}_k(\tau) := \operatorname{dec}*k(\tau)+1 \in {1,\dots,N},
\qquad
\mathrm{nat}(\tau):=\operatorname{dec}(\tau)+1\in\mathbb N*{\ge1}.
]
This does **not** change Phase 1; it’s an additional lens.

---

# 1. The additive/cyclic convolution native to radix-time (group convolution)

## 1.1 Cyclic group structure on (\mathcal R^{(k)})

Let (N=B_{k+1}). Define **cyclic addition** on (\mathcal R^{(k)}):
[
\tau \boxplus_k \sigma := \operatorname{enc}_k\Big((\operatorname{dec}_k(\tau)+\operatorname{dec}_k(\sigma)) \bmod N\Big),
]
and cyclic inverse/subtraction (\boxminus_k) similarly. Then ((\mathcal R^{(k)},\boxplus_k)\cong(\mathbb Z/N\mathbb Z,+)) via (\operatorname{dec}_k).

**Proposition 38** ((\mathcal R^{(k)},\boxplus_k)) is a finite abelian group; (\operatorname{dec}_k) is a group isomorphism to (\mathbb Z/N\mathbb Z).  [§1.1 · Phase 3, Fragment 1]
*Proof.* Transport the group law through the bijection (\operatorname{dec}_k). ∎

## 1.2 Convolution algebra on signals over (\mathcal R^{(k)})

Let (H_k^\mathbb C := \mathbb C^{\mathcal R^{(k)}}). Define **(normalized) cyclic convolution**
[
(f **k g)(\tau) := \frac{1}{N}\sum*{\sigma\in\mathcal R^{(k)}} f(\sigma), g(\tau \boxminus_k \sigma).
]

**Theorem 13 (closure, associativity, commutativity, identity).**  [§1.2 · Phase 3, Fragment 1]
((H_k^\mathbb C,*_k)) is a commutative associative algebra with identity (\delta_0) (the Kronecker delta at the group identity digit-vector).
*Proof.* This is standard group convolution on a finite abelian group; verify by substitution (\rho=\sigma\boxplus_k \eta). ∎

**Computability.** Naively (O(N^2)). (Later you can diagonalize with additive characters / FFT on (\mathbb Z/N\mathbb Z) when useful.)

---

# 2. Arithmetic functions and Dirichlet convolution (multiplicative composition law)

## 2.1 The Dirichlet algebra

Let (\mathcal A := {a:\mathbb N_{\ge1}\to \mathbb C}). Define **Dirichlet convolution**
[
(a*b)(n) := \sum_{d\mid n} a(d), b(n/d).
]
Define the identity (\varepsilon\in\mathcal A) by (\varepsilon(1)=1) and (\varepsilon(n)=0) for (n>1). Define (\mathbf 1(n)\equiv 1).

**Theorem 14 (Dirichlet algebra).**  [§2.1 · Phase 3, Fragment 1]
((\mathcal A,*)) is a commutative associative unital algebra with identity (\varepsilon).
*Proof.* Finiteness of divisor sums gives closure. Associativity follows from the bijection between factorizations (n=abc) and iterated divisor decompositions:
[
((a*b)*c)(n)=\sum_{d\mid n}\sum_{e\mid n/d} a(d)b(e)c(n/de)=\sum_{de\mid n} a(d)b(e)c(n/de)=(a*(b*c))(n).
]
Commutativity is (d\leftrightarrow n/d). Identity is immediate. ∎

## 2.2 Dirichlet convolution as an operator calculus

For each (a\in\mathcal A), define the **Dirichlet transform operator**
[
(T_a f)(n) := (a*f)(n)=\sum_{d\mid n} a(d), f(n/d).
]

**Proposition 39 (representation).**  [§2.2 · Phase 3, Fragment 1]
(T_a\circ T_b = T_{a*b}) and (T_\varepsilon = I).
*Proof.* Expand:
[
(T_a(T_b f))(n)=\sum_{d\mid n} a(d),(T_b f)(n/d)
=\sum_{d\mid n} a(d)\sum_{e\mid n/d} b(e)f(n/de)
=\sum_{de\mid n} a(d)b(e)f(n/(de)) = (T_{a*b}f)(n).
]
∎

So (a\mapsto T_a) is an algebra homomorphism from ((\mathcal A,*)) into (\mathrm{End}(\mathbb C^{\mathbb N_{\ge1}})). This is the first “ANT operator = computational primitive” statement.

---

# 3. Möbius inversion and squarefree projector

## 3.1 Möbius function and inversion

Let (\mu:\mathbb N_{\ge1}\to{-1,0,1}) be the Möbius function:

* (\mu(1)=1),
* (\mu(n)=(-1)^r) if (n) is a product of (r) distinct primes,
* (\mu(n)=0) if (p^2\mid n) for some prime (p).

**Theorem 20 (Möbius is the Dirichlet inverse of (\mathbf 1)).**
[
\mu * \mathbf 1 = \varepsilon.
]
*Proof.* Standard: ((\mu*\mathbf 1)(n)=\sum_{d\mid n}\mu(d)=0) for (n>1), equals 1 for (n=1). ∎

**Theorem 15 (Möbius inversion).**  [§3.2 · Phase 3, Fragment 1]
If (g=\mathbf 1 * f), i.e.
[
g(n)=\sum_{d\mid n} f(d),
]
then
[
f = \mu * g,\qquad f(n)=\sum_{d\mid n}\mu(d), g(n/d).
]
*Proof.* Apply (\mu*) to both sides and use (\mu*\mathbf 1=\varepsilon). ∎

## 3.2 Squarefree projector

Define (\mu^2(n)\in{0,1}) (squarefree indicator): (\mu^2(n)=1) iff (n) is squarefree.

Define the diagonal operator (S) on arithmetic sequences by
[
(Sf)(n):=\mu^2(n)f(n).
]

**Proposition 40 (idempotence).** (S^2=S).  [§3.3 · Phase 3, Fragment 1]
*Proof.* (\mu^2(n)^2=\mu^2(n)) pointwise. ∎

This is the formal “squarefree filter” primitive: it projects to the squarefree-supported subspace.

---

# 4. Pullback of ANT operators to mixed-radix tensors (finite horizon)

Now connect arithmetic operators to (\mathcal R^{(k)}).

## 4.1 Mixed-radix ↔ arithmetic sequence dictionary

Let (F:\mathcal R^{(k)}\to\mathbb C). Define the corresponding arithmetic sequence (f:{1,\dots,N}\to\mathbb C) by
[
f(n):=F(\operatorname{enc}_k(n-1)),\quad 1\le n\le N.
]
Conversely, (F(\tau)=f(\mathrm{nat}_k(\tau))).

Extend any (f) on ({1,\dots,N}) to (\mathbb N_{\ge1}) by zero outside ([1,N]) when needed.

## 4.2 Dirichlet transform acting on tensors

Given (a\in\mathcal A), define (T_{a}^{(k)}:H_k^\mathbb C\to H_k^\mathbb C) by conjugation:
[
(T_a^{(k)}F)(\tau)
:= (T_a f)(\mathrm{nat}*k(\tau))
= \sum*{d\mid \mathrm{nat}_k(\tau)} a(d), F!\left(\operatorname{enc}_k!\Big(\frac{\mathrm{nat}_k(\tau)}{d}-1\Big)\right).
]
This is **well-defined** on (\mathcal R^{(k)}) because if (n\le N), then (n/d \le n \le N), so the argument stays in ({1,\dots,N}).

**Theorem 23 (closure + composition law on (\mathcal R^{(k)})).**
For all (a,b\in\mathcal A),
[
T_a^{(k)}\circ T_b^{(k)} = T_{a*b}^{(k)},\qquad T_\varepsilon^{(k)}=I.
]
*Proof.* This is exactly Proposition 39 transported through the bijection (F\leftrightarrow f) via (\mathrm{nat}_k). ∎

## 4.3 Möbius inversion and squarefree projection on (\mathcal R^{(k)})

Define the squarefree diagonal operator (S^{(k)}) on tensors by
[
(S^{(k)}F)(\tau):=\mu^2(\mathrm{nat}_k(\tau)), F(\tau).
]
Then ((S^{(k)})^2=S^{(k)}).

Define the Möbius transform (T_\mu^{(k)}). Then:

**Corollary 10 (tensor Möbius inversion).**  [§4.2 · Phase 3, Fragment 1]
If (G = T_{\mathbf 1}^{(k)}F), then (F = T_{\mu}^{(k)}G).
*Proof.* Transport Theorem 15 through (\mathrm{nat}_k). ∎

**Computability.** Each evaluation ((T_a^{(k)}F)(\tau)) is a divisor sum over (\mathrm{nat}_k(\tau)). This is finite and computable; naive divisor enumeration is (O(\sqrt{n})) per point (n), or better with precomputed divisor lists up to (N).

---

# 5. What we have now (and what we intentionally postponed)

You now have **two algebraic compositions** acting on mixed-radix tensors:

1. **Cyclic/time convolution** ((H_k^\mathbb C,*_k)) induced by the odometer group ((\mathcal R^{(k)},\boxplus_k)).
2. **Dirichlet/ANT operator algebra** (a\mapsto T_a^{(k)}) induced by divisor structure on (\mathrm{nat}_k(\tau)).

And you have the core ANT primitives:

* Möbius inversion (T_\mu^{(k)}),
* squarefree projector (S^{(k)}).

We have **not yet** formalized characters/CRT in this fragment (that’s next), because it’s cleaner once we decide exactly which “phase probes” we want: additive characters for (*_k), multiplicative Dirichlet characters for (T_a^{(k)}), or both.

---

## Leading questions for Phase 3, Fragment 2

1. **Characters as probes (two kinds):**

   * Additive characters on (\mathbb Z/N\mathbb Z) that diagonalize (*_k).
   * Dirichlet characters mod (q) (multiplicative) and their orthogonality projectors.
2. **CRT as compositional algebra:** decompose probes/operators along prime-power factors of (q) and of (N=B_{k+1}); show how projections factor.
3. **Filtration compatibility:** characterize when a congruence class mod (q) is cylinder-measurable (especially when (q\mid B_L)), and how these probes interact with (P^{(k)}_L) and the runtime algebra (\mathfrak A_k).


## Phase 3 — Import Analytic Number Theory, Fragment 2

### Characters as probes, CRT factorization, and when congruence structure is cylinder-measurable (filtration compatibility)

We remain on a fixed finite horizon (k\ge 0). Let
[
N:=B_{k+1},\qquad \mathcal R^{(k)}=\prod_{i=0}^{k}D_i,\qquad \operatorname{dec}_k:\mathcal R^{(k)}\to{0,\dots,N-1}.
]
We use the shifted arithmetic index
[
\mathrm{nat}_k(\tau):=\operatorname{dec}*k(\tau)+1\in{1,\dots,N}.
]
Let (\mathcal F*{k,L}) be the sigma-algebra generated by length-(L) cylinders (equivalently: “depends only on the first (L) digits”).

This fragment provides two probe systems:

1. **Additive characters** on (\mathbb Z/N\mathbb Z) (diagonalize cyclic convolution on time).
2. **Dirichlet characters** mod (q) (multiplicative phase probes on arithmetic structure).

Then we prove their **orthogonality/projector identities**, the **CRT factorization**, and the exact condition for these objects to be **cylinder-measurable**.

---

# 1. Additive characters on time: (\mathbb Z/N\mathbb Z)

## 1.1 Characters and Fourier transform

Identify (\mathcal R^{(k)}\cong \mathbb Z/N\mathbb Z) via (\operatorname{dec}_k). For (m\in{0,\dots,N-1}), define the additive character
[
\chi_m(x):=\exp!\Big(\frac{2\pi i m x}{N}\Big),\qquad x\in\mathbb Z/N\mathbb Z,
]
and pull it back to (\mathcal R^{(k)}):
[
\chi_m^{(k)}(\tau):=\chi_m(\operatorname{dec}_k(\tau)).
]

Define the (normalized) Fourier transform for (f:\mathbb Z/N\mathbb Z\to\mathbb C):
[
\widehat f(m):=\frac{1}{N}\sum_{x\in\mathbb Z/N\mathbb Z} f(x),\overline{\chi_m(x)}.
]

## 1.2 Orthogonality

### Proposition 41 (additive orthogonality)  [§1.1 · Phase 3, Fragment 2]

For (m,m'\in{0,\dots,N-1}),
[
\frac{1}{N}\sum_{x\in\mathbb Z/N\mathbb Z}\chi_m(x),\overline{\chi_{m'}(x)}=\delta_{m,m'}.
]
*Proof.* This is the finite geometric series identity. ∎

### Proposition 42 (residue-class projector via additive characters)  [§1.2 · Phase 3, Fragment 2]

Fix a divisor (q\mid N). For (a\in\mathbb Z/q\mathbb Z), define the indicator on (\mathbb Z/N\mathbb Z)
[
\mathbf 1_{x\equiv a\ (q)}.
]
Then for all (x\in\mathbb Z/N\mathbb Z),
[
\mathbf 1_{x\equiv a\ (q)}
=\frac{1}{q}\sum_{t=0}^{q-1}\exp!\Big(\frac{2\pi i t(x-a)}{q}\Big).
]
*Proof.* The inner sum equals (q) if (x\equiv a\pmod q), else 0, by additive orthogonality on (\mathbb Z/q\mathbb Z). ∎

## 1.3 Convolution diagonalization

Let (*_k) be cyclic convolution on (\mathcal R^{(k)}) (equivalently (\mathbb Z/N\mathbb Z)):
[
(f**k g)(x):=\frac{1}{N}\sum*{y} f(y)g(x-y).
]

### Theorem 16 (convolution theorem)  [§1.3 · Phase 3, Fragment 2]

[
\widehat{f*_k g}(m)=\widehat f(m),\widehat g(m)\quad \forall m.
]
*Proof.* Substitute definitions and change variables (z=x-y). ∎

**Meaning:** additive characters are exact “frequency probes” of the time convolution algebra.

---

# 2. Multiplicative probes: Dirichlet characters mod (q)

Fix an integer (q\ge 1). A (Dirichlet) character mod (q) is a completely multiplicative function (\chi:\mathbb Z\to\mathbb C) that is periodic mod (q) and satisfies (\chi(n)=0) whenever (\gcd(n,q)>1). Equivalently, (\chi) is a group character of ((\mathbb Z/q\mathbb Z)^\times), extended by 0 off units.

Let (\mathcal X(q)) denote the set of Dirichlet characters mod (q), and (\varphi(q)=|(\mathbb Z/q\mathbb Z)^\times|).

## 2.1 Orthogonality relations

### Proposition 43 (orthogonality over units)  [§2.1 · Phase 3, Fragment 2]

For (\chi,\psi\in\mathcal X(q)),
[
\sum_{a\in(\mathbb Z/q\mathbb Z)^\times}\chi(a),\overline{\psi(a)}=\varphi(q),\delta_{\chi,\psi}.
]
*Proof.* This is the standard orthogonality of characters of a finite abelian group. ∎

### Proposition 44 (orthogonality over characters gives residue projection on units)  [§2.2 · Phase 3, Fragment 2]

For (a,b\in(\mathbb Z/q\mathbb Z)^\times),
[
\frac{1}{\varphi(q)}\sum_{\chi\in\mathcal X(q)} \chi(a),\overline{\chi(b)}=\mathbf 1_{a\equiv b\ (q)}.
]
If either (a) or (b) is non-unit mod (q), both sides are (0) under the usual extension convention.
*Proof.* Same finite character orthogonality, but summing over the dual group. ∎

## 2.2 Dirichlet-character projectors on sequences

Let (f:\mathbb N_{\ge1}\to\mathbb C). For fixed (\chi\in\mathcal X(q)), define the **twist operator**
[
(M_\chi f)(n):=\chi(n)f(n).
]
This is a diagonal operator; it is the formal “multiplicative phase probe”.

For a residue class (a\in(\mathbb Z/q\mathbb Z)^\times), define the (unit-supported) residue projector on sequences:
[
(\Pi_{q,a} f)(n):=\mathbf 1_{n\equiv a\ (q)}, f(n),
]
where the indicator is 1 only when (\gcd(n,q)=1) and (n\equiv a\pmod q).

### Proposition 45 (character expansion of residue projectors)  [§2.3 · Phase 3, Fragment 2]

For (a\in(\mathbb Z/q\mathbb Z)^\times),
[
\Pi_{q,a}=\frac{1}{\varphi(q)}\sum_{\chi\in\mathcal X(q)} \overline{\chi(a)}, M_\chi.
]
*Proof.* Apply both sides to (f) and use Proposition 44 pointwise in (n \bmod q). ∎

**Meaning:** Dirichlet characters are a complete probe system for congruence classes on the multiplicative (unit) side.

---

# 3. CRT as compositional algebra (factorization of probes and projectors)

## 3.1 Additive CRT (for residues)

Let (q_1,q_2) be coprime divisors of (N). CRT gives an isomorphism
[
\mathbb Z/(q_1q_2)\mathbb Z ;\cong; \mathbb Z/q_1\mathbb Z \times \mathbb Z/q_2\mathbb Z.
]

### Proposition 46 (residue projectors factor)  [§3.1 · Phase 3, Fragment 2]

Let (a) correspond to ((a_1,a_2)) under CRT. Then as indicators on (\mathbb Z/N\mathbb Z),
[
\mathbf 1_{x\equiv a\ (q_1q_2)} = \mathbf 1_{x\equiv a_1\ (q_1)}\cdot \mathbf 1_{x\equiv a_2\ (q_2)}.
]
*Proof.* Congruence mod (q_1q_2) is equivalent to simultaneous congruences mod (q_1) and (q_2). ∎

## 3.2 Multiplicative CRT (characters factor)

For coprime (q_1,q_2), CRT gives
[
(\mathbb Z/(q_1q_2)\mathbb Z)^\times \cong (\mathbb Z/q_1\mathbb Z)^\times \times (\mathbb Z/q_2\mathbb Z)^\times.
]

### Proposition 47 (Dirichlet characters factor)  [§3.2 · Phase 3, Fragment 2]

Every (\chi\in\mathcal X(q_1q_2)) decomposes uniquely as
[
\chi(n)=\chi_1(n)\chi_2(n),
]
with (\chi_i\in\mathcal X(q_i)) (pulled back along reduction mod (q_i)). Conversely, any pair ((\chi_1,\chi_2)) defines a character mod (q_1q_2).
*Proof.* Characters of a direct product group factor as products of characters; extend by 0 off units. ∎

### Corollary 11 (projectors factor)  [§3.3 · Phase 3, Fragment 2]

For (a\in(\mathbb Z/(q_1q_2)\mathbb Z)^\times) corresponding to ((a_1,a_2)),
[
\Pi_{q_1q_2,a} = \Pi_{q_1,a_1},\Pi_{q_2,a_2}.
]

---

# 4. Filtration compatibility: when congruence structure is cylinder-measurable

This is the key bridge back to the mixed-radix cylinder topology.

## 4.1 The depth at which a modulus “appears”

### Definition 39 (radix depth of a modulus)  [§4.1 · Phase 3, Fragment 2]

For a positive integer (q), define
[
\mathrm{depth}(q) := \min{L\in{1,\dots,k+1}: q \mid B_L},
]
if such an (L) exists, and (\mathrm{depth}(q)=\infty) otherwise.

## 4.2 Cylinder measurability of additive residues

### Theorem 17 (additive residue classes are (\mathcal F_{k,L})-measurable iff (q\mid B_L))  [§4.2 · Phase 3, Fragment 2]

Fix (q) with (\mathrm{depth}(q)\le k+1). Then for every residue (a\pmod q), the set
[
E_{q,a}:={\tau\in\mathcal R^{(k)}:\operatorname{dec}*k(\tau)\equiv a\ (\mathrm{mod}\ q)}
]
belongs to (\mathcal F*{k,L}) for every (L\ge \mathrm{depth}(q)). Equivalently, (E_{q,a}) is a union of length-(L) cylinders.

Moreover, if (q\nmid B_L), then there exists some residue (a) such that (E_{q,a}\notin\mathcal F_{k,L}).

*Proof.*

* If (q\mid B_L), then for any (i\ge L), (B_i) is a multiple of (B_L), hence a multiple of (q). Therefore
  [
  \operatorname{dec}*k(\tau)=\sum*{i=0}^{L-1} d_i B_i \pmod q,
  ]
  so (\operatorname{dec}*k(\tau)\bmod q) depends only on the prefix ((d_0,\dots,d*{L-1})). Hence (E_{q,a}) is a union of cylinders of length (L).
* If (q\nmid B_L), then some suffix digit contributes nontrivially mod (q), so within a fixed length-(L) cylinder you can vary suffix digits to obtain different residues mod (q); hence no union of length-(L) cylinders can equal (E_{q,a}) for all (a). ∎

### Corollary 12 (same for (\mathrm{nat}_k))  [§4.3 · Phase 3, Fragment 2]

The sets ({\tau:\mathrm{nat}*k(\tau)\equiv r\ (\mathrm{mod}\ q)}) are (\mathcal F*{k,L})-measurable under the same condition (q\mid B_L), since (\mathrm{nat}_k=\operatorname{dec}_k+1).

## 4.3 Cylinder measurability of Dirichlet characters (multiplicative probes)

### Theorem 18 (Dirichlet characters become cylinder-measurable when the modulus divides some (B_L))  [§4.4 · Phase 3, Fragment 2]

Fix (q) with (\mathrm{depth}(q)\le k+1), and let (\chi\in\mathcal X(q)). Define the pulled-back probe on (\mathcal R^{(k)}):
[
\chi^{(k)}(\tau):=\chi(\mathrm{nat}*k(\tau)).
]
Then (\chi^{(k)}) is (\mathcal F*{k,L})-measurable for all (L\ge \mathrm{depth}(q)).

*Proof.* If (q\mid B_L), then (\mathrm{nat}_k(\tau)\bmod q) depends only on the length-(L) prefix. Both the residue class and the unit/non-unit condition (\gcd(\mathrm{nat}_k(\tau),q)=1) are determined by (\mathrm{nat}_k(\tau)\bmod q). Hence (\chi(\mathrm{nat}*k(\tau))) depends only on the prefix, i.e. is (\mathcal F*{k,L})-measurable. ∎

**Consequence:** when (q\mid B_L), Dirichlet character probes live inside your cylinder filtration at finite depth, and can be realized using cylinder-measurable functions and projectors (hence they integrate into the runtime algebra (\mathfrak A_k) once you admit multiplication by such probes).

---

# 5. Operator realizations on mixed-radix tensors (what becomes “first-class”)

On (H_k^\mathbb C=\mathbb C^{\mathcal R^{(k)}}), you now have explicit operator families:

* **Additive residue projector (time congruence):**
  [
  (M_{E_{q,a}}F)(\tau) := \mathbf 1_{\operatorname{dec}_k(\tau)\equiv a\ (q)},F(\tau),
  ]
  which is a cylinder gate whenever (q\mid B_L) for some (L).

* **Dirichlet character twist (multiplicative phase probe):**
  [
  (M_{\chi^{(k)}}F)(\tau) := \chi(\mathrm{nat}_k(\tau)),F(\tau),
  ]
  cylinder-measurable at depth (\mathrm{depth}(q)) when finite.

* **Residue projector on units via character averaging** (transport of Proposition 45 through (\mathrm{nat}*k)):
  [
  M*{\Pi_{q,a}} = \frac{1}{\varphi(q)}\sum_{\chi\in\mathcal X(q)} \overline{\chi(a)}, M_{\chi^{(k)}}.
  ]

* **Additive residue projector via additive characters** (Proposition 42 pulled back through (\operatorname{dec}_k)).

And CRT guarantees **compositionality** of these constraints across coprime moduli (both additive and multiplicative).

---

## Leading questions for Phase 3, Fragment 3

1. **Squarefree / valuation probes as cylinder objects:** characterize when “(p^2\mid \mathrm{nat}_k(\tau))” becomes cylinder-measurable (depends on whether (p^2\mid B_L) for some (L)), and build explicit projectors for valuation constraints.
2. **Interaction with Dirichlet transforms (T_a^{(k)}):** determine which (T_a^{(k)}) commute with which cylinder projections (P^{(k)}_L), and how character twisting diagonalizes or block-diagonalizes these transforms.
3. **Choose the composition semantics for “programs”:** decide whether you treat “program composition” as (i) additive/time convolution, (ii) Dirichlet composition, or (iii) a two-layer semidirect structure (time-phase × arithmetic-factor), and then prove closure/associativity in that combined algebra.

## Phase 3 — Import Analytic Number Theory, Fragment 3

### Valuation probes, squarefree projector as finite-depth gates (when possible), and covariance/interaction laws with Dirichlet transforms

We stay on a fixed finite horizon (k\ge 0), with
[
N:=B_{k+1},\qquad \mathcal R^{(k)}=\prod_{i=0}^k D_i,\qquad \mathrm{nat}_k(\tau):=\operatorname{dec}_k(\tau)+1\in{1,\dots,N}.
]
We work with complex-valued tensors (H_k^\mathbb C:=\mathbb C^{\mathcal R^{(k)}}), and freely identify (F\in H_k^\mathbb C) with the sequence (f:{1,\dots,N}\to\mathbb C) via (f(n)=F(\operatorname{enc}_k(n-1))).

---

# 1. (p)-adic valuations as first-class probes and projectors

Fix a prime (p). For (n\in\mathbb N_{\ge1}), let (v_p(n)\in\mathbb N\cup{0}) be the usual (p)-adic valuation (largest (e) with (p^e\mid n)).

## 1.1 Divisibility and exact-valuation projectors (on sequences)

### Definition 40 (divisibility projector)  [§1.1 · Phase 3, Fragment 3]

For (e\ge 1), define the diagonal operator on sequences (f:{1,\dots,N}\to\mathbb C):
[
(\Pi_{p^{e}} f)(n) := \mathbf 1_{p^e\mid n}, f(n).
]

### Definition 41 (exact valuation projector)  [§1.2 · Phase 3, Fragment 3]

For (e\ge 0), define
[
(\Pi_{p,=e} f)(n) := \mathbf 1_{v_p(n)=e}, f(n)
= \big(\mathbf 1_{p^e\mid n}-\mathbf 1_{p^{e+1}\mid n}\big) f(n).
]

### Proposition 48 (orthogonal idempotents; partition of unity)  [§1.3 · Phase 3, Fragment 3]

All (\Pi_{p^e}) and (\Pi_{p,=e}) are idempotent and pairwise orthogonal (as diagonal projections). Moreover,
[
\sum_{e\ge 0}\Pi_{p,=e} = I
\quad\text{(finite sum effectively, since }v_p(n)\le \lfloor \log_p N\rfloor \text{ on }1\le n\le N).
]

**Proof.** Pointwise: indicators are (0/1), disjoint for different exact valuations, and ({v_p(n)=e}*{e\ge0}) partitions (\mathbb N*{\ge1}). ∎

## 1.2 Pullback to mixed-radix tensors and cylinder depth

Define pulled-back projectors on (H_k^\mathbb C) by ((\Pi F)(\tau):=(\Pi f)(\mathrm{nat}_k(\tau))).

### Proposition 49 (cylinder measurability criterion)  [§1.4 · Phase 3, Fragment 3]

Fix (q\ge 1). The set
[
E_q:={\tau\in\mathcal R^{(k)} : q \mid \mathrm{nat}*k(\tau)}
]
is (\mathcal F*{k,L})-measurable (a union of length-(L) cylinders) whenever (q\mid B_L).

**Proof.** If (q\mid B_L), then (\mathrm{nat}_k(\tau)\bmod q) depends only on the length-(L) prefix (Phase 3 Fragment 2). Divisibility is the residue condition “(\equiv 0) mod (q)”. ∎

### Corollary 13 (valuation gates at finite depth)  [§1.5 · Phase 3, Fragment 3]

If (p^e \mid B_L), then the projector (\Pi_{p^e}) (pulled back to (\mathcal R^{(k)})) is exactly multiplication by a length-(L) cylinder gate:
[
(\Pi_{p^e}F)(\tau)=\mathbf 1_{E_{p^e}}(\tau),F(\tau),\qquad E_{p^e}\in\mathcal F_{k,L}.
]
Similarly, if both (p^e\mid B_L) and (p^{e+1}\mid B_{L'}) for some (L,L'), then (\Pi_{p,=e}) is a difference of two cylinder gates at depth (\max(L,L')).

---

# 2. Squarefree projector on ({1,\dots,N}) and its factorization

Recall (\mu^2(n)) is the squarefree indicator.

## 2.1 Finite-horizon squarefree projector

### Definition 42  [§2.1 · Phase 3, Fragment 3]

Define (S_{\mathrm{sf}}) on sequences (f:{1,\dots,N}\to\mathbb C) by
[
(S_{\mathrm{sf}} f)(n) := \mu^2(n), f(n).
]
Pull back to tensors: ((S_{\mathrm{sf}}F)(\tau)=\mu^2(\mathrm{nat}_k(\tau))F(\tau)).

### Proposition 50 (idempotence)  [§2.2 · Phase 3, Fragment 3]

(S_{\mathrm{sf}}^2=S_{\mathrm{sf}}).

**Proof.** Pointwise (\mu^2(n)^2=\mu^2(n)). ∎

## 2.2 Product form as “no prime-square divides”

Let (\mathcal P_N := {p \text{ prime} : p^2 \le N}) (finite).

### Theorem 19 (squarefree projector as finite product of divisibility complements)  [§2.3 · Phase 3, Fragment 3]

On ({1,\dots,N}),
[
S_{\mathrm{sf}} ;=; \prod_{p\in\mathcal P_N}\big(I-\Pi_{p^2}\big),
]
(product of commuting diagonal operators).

**Proof.** For each (n\le N), (\mu^2(n)=1) iff (p^2\nmid n) for all primes (p\le\sqrt n), hence for all (p\in\mathcal P_N). Therefore
[
\mu^2(n)=\prod_{p\in\mathcal P_N} (1-\mathbf 1_{p^2\mid n}),
]
and multiplying (f(n)) yields the operator identity. ∎

### Corollary 14 (when squarefree is cylinder-measurable at some depth)  [§2.4 · Phase 3, Fragment 3]

If there exists (L) such that (p^2\mid B_L) for every (p\in\mathcal P_N), then (S_{\mathrm{sf}}) (pulled back to (\mathcal R^{(k)})) is multiplication by an (\mathcal F_{k,L})-measurable gate (a union of length-(L) cylinders).
Otherwise, (S_{\mathrm{sf}}) is still a valid diagonal operator, but it is **not** representable as a single finite-depth cylinder gate in general (because at least one (\Pi_{p^2}) fails to be cylinder-measurable at any depth (\le k+1)).

---

# 3. Dirichlet transforms and their interaction with character twists and valuation layers

Recall the Dirichlet transform operator for an arithmetic kernel (a:\mathbb N_{\ge1}\to\mathbb C):
[
(T_a f)(n)=\sum_{d\mid n} a(d), f(n/d),
]
and its finite-horizon transport (T_a^{(k)}) on tensors via (\mathrm{nat}_k).

## 3.1 Covariance under Dirichlet character twists

Fix a modulus (q) and a Dirichlet character (\chi\in\mathcal X(q)). Define the diagonal twist (M_\chi f(n)=\chi(n)f(n)) (and pull back to tensors as before).

### Theorem 20 (twist–transform covariance)  [§3.1 · Phase 3, Fragment 3]

For any (a) and any Dirichlet character (\chi),
[
M_\chi, T_a ;=; T_{a\cdot \chi}, M_\chi,
]
where ((a\cdot\chi)(d):=a(d)\chi(d)).

**Proof.**
[
(M_\chi T_a f)(n)=\chi(n)\sum_{d\mid n}a(d)f(n/d)
=\sum_{d\mid n} a(d)\chi(d)\chi(n/d)f(n/d)
=(T_{a\cdot\chi}(M_\chi f))(n),
]
using complete multiplicativity (\chi(n)=\chi(d)\chi(n/d)) (and the (0) convention off units handles (\gcd(d,q)>1)). ∎

**Corollary 15 (true commutation criterion).**  [§3.2 · Phase 3, Fragment 3]
(M_\chi) commutes with (T_a) iff (a(d)\chi(d)=a(d)) for all (d) (i.e., (a) is supported where (\chi(d)=1), or more generally (a\cdot\chi=a)).

This is the precise “characters as resonance probes for the transform kernel” statement.

## 3.2 (p)-power kernels give a clean valuation-fiber action

Dirichlet transforms are multiplicative; they align naturally with valuation decompositions.

### Definition 43 (pure (p)-power kernel)  [§3.3 · Phase 3, Fragment 3]

Let (a) be supported only on (p)-powers: (a(d)=0) unless (d=p^j).

### Theorem 21 (valuation-fiber Toeplitz action)  [§3.4 · Phase 3, Fragment 3]

Let (n=p^r m) with (\gcd(m,p)=1). If (a) is supported on (p)-powers, then
[
(T_a f)(p^r m)=\sum_{j=0}^{r} a(p^j), f(p^{r-j} m).
]
Equivalently: for each fixed (p)-free (m), (T_a) acts on the sequence (r\mapsto f(p^r m)) by a finite “lower-triangular convolution” in the valuation coordinate (r).

**Proof.** Divisors (d\mid p^r m) that are (p)-powers are exactly (p^j) for (0\le j\le r), and ((p^r m)/p^j=p^{r-j}m). ∎

**Lean.** Definition 43 and Theorem 21 are formalized in `FdrsFormal/NumberTheory/FactorizationLens/PowerKernel.lean` (`PurePowerKernel`, `valuationFiberAction`).

This is one of the cleanest places where “ANT operator = structured multi-rate update” is literally true: valuations form a discrete hierarchy, and the kernel (a(p^j)) determines cross-level coupling.

---

# 4. Misalignment with the additive/cylinder filtration: a sharp non-commutation statement

Your cylinder filtration (\mathcal F_{k,L}) is *additive/residue* structure (prefix fixes (\operatorname{dec}_k \bmod B_L)). Dirichlet transforms are *multiplicative/divisor* structure.

### Proposition 51 (generic failure of commutation with additive block projections)  [§4.1 · Phase 3, Fragment 3]

Fix (L\ge 1). In general,
[
T_a^{(k)} P^{(k)}_L \neq P^{(k)}_L T_a^{(k)}.
]

**Witness (explicit).** Let (a=\delta_2) (supported only at (d=2)): then
[
(T_{\delta_2} f)(n)=\mathbf 1_{2\mid n}, f(n/2).
]
Take any (L) with (B_L) even (common), and define (f(n):=\mathbf 1_{n\equiv 1 \ (\mathrm{mod}\ B_L)}), which is (\mathcal F_{k,L})-measurable (a union of length-(L) cylinders up to the (\mathrm{nat}*k) shift). Then ((T*{\delta_2}f)(n)) depends on whether (n/2 \equiv 1 \pmod{B_L}), i.e. on (n \pmod{2B_L}), which is strictly finer than (n \pmod{B_L}). Hence (T_{\delta_2}f) is typically **not** (\mathcal F_{k,L})-measurable, so (P^{(k)}*L T*{\delta_2}\neq T_{\delta_2} P^{(k)}_L). ∎

**Meaning:** additive-prefix locality is not preserved by multiplicative divisor operators; the correct compatibility structure for Dirichlet transforms is valuation-based (multiplicative) rather than cylinder-based (additive).

---

## Leading questions for Phase 3, Fragment 4

1. **Two-filtration formalism:** introduce a *multiplicative filtration* (by prime-power divisibility / valuation depth) alongside the additive cylinder filtration, and prove the exact operator classes that are local/commuting with each.
2. **Unified state augmentation:** define an augmented state ((\tau,\upsilon)) where (\upsilon) tracks a finite set of valuations/residue data, so that multiplicative operators become Markovian/local in the augmented space (this is the formal bridge to your “augment state with phase” constraint).
3. **Compositional algebra choice:** construct a combined algebra (e.g., generated by (*_k), (T_a^{(k)}), character twists, and valuation gates) and prove associativity/closure; characterize when it reduces to a semidirect product vs a direct product.

## Phase 3 — Import Analytic Number Theory, Fragment 4

### Dual filtrations, the factorization-lens coordinate system, and a precise “rhythm/program space” decomposition inside an integer

We stay on finite horizon (k\ge 0). Let
[
N:=B_{k+1},\quad \mathcal R^{(k)}=\prod_{i=0}^k D_i,\quad \mathrm{nat}_k(\tau):=\operatorname{dec}_k(\tau)+1\in{1,\dots,N}.
]
We work on sequences (f:{1,\dots,N}\to\mathbb C) and their pullbacks (F(\tau)=f(\mathrm{nat}_k(\tau))) on (H_k^\mathbb C=\mathbb C^{\mathcal R^{(k)}}).

The main point of this fragment:

* The **additive cylinder filtration** (prefix / residue structure) and
* the **multiplicative valuation filtration** (divisor / factorization structure)

are distinct, but there is a clean coordinate system (“factorization lens”) in which Dirichlet operators become *local, fiberwise, and hierarchical*—this is the formal “program space within the integer.”

---

# 1. Two filtrations on ({1,\dots,N}): additive vs multiplicative

## 1.1 Additive (cylinder / residue) filtration

For (L\in{1,\dots,k+1}), define the additive modulus
[
M_L := B_L.
]
A function (f:{1,\dots,N}\to\mathbb C) is **additively (L)-coarse** if it depends only on (n\bmod M_L) (equivalently: its pullback to (\mathcal R^{(k)}) is (\mathcal F_{k,L})-measurable).

Write (\mathcal A_L) for the sigma-algebra on ({1,\dots,N}) generated by residue classes mod (M_L). (Transporting this through (\mathrm{nat}*k) matches (\mathcal F*{k,L}).)

---

## 1.2 Multiplicative (valuation) filtration

Fix a finite set of primes (P). (Natural choice later: all primes appearing in the radix product up to depth (k), but the theory only needs (P) finite.)

For (n\ge 1), define the valuation vector
[
v_P(n):=(v_p(n))*{p\in P}\in \mathbb N^{P}.
]
Define the **(P)-smooth part** and **(P)-free part**:
[
s_P(n):=\prod*{p\in P} p^{v_p(n)},\qquad u_P(n):=\frac{n}{s_P(n)}.
]
So (u_P(n)) is coprime to every (p\in P), and the factorization
[
n = u_P(n), s_P(n)
]
is unique.

### Definition 44 (multiplicative sigma-algebra at depth (E))  [§1.1 · Phase 3, Fragment 4]

Fix a depth vector (E=(E_p)*{p\in P}\in\mathbb N^{P}). Define the truncated valuation
[
v_P^{\le E}(n):=(\min(v_p(n),E_p))*{p\in P}.
]
Let (\mathcal M_E) be the sigma-algebra generated by the map
[
n \longmapsto \big(u_P(n),, v_P^{\le E}(n)\big).
]
Equivalently, (f) is (\mathcal M_E)-measurable iff (f(n)=f(m)) whenever (u_P(n)=u_P(m)) and (v_P^{\le E}(n)=v_P^{\le E}(m)).

This is the multiplicative analogue of “prefix depth”: it is a **finite-depth view of valuations** plus the exact (P)-free unit label.

---

# 2. The rhythm lemma: valuation gates are periodic and hierarchical

For each prime power (p^e), the predicate “(p^e\mid n)” is a strict rhythm: it is periodic with period (p^e) and refines as (e) increases.

### Proposition 52 (periodicity of divisibility)  [§2.1 · Phase 3, Fragment 4]

Fix (p) prime and (e\ge 1). The indicator (g_{p^e}(n):=\mathbf 1_{p^e\mid n}) is periodic mod (p^e):
[
g_{p^e}(n)=g_{p^e}(n+p^e)\quad\forall n.
]
Moreover, (g_{p^{e+1}}\le g_{p^e}) pointwise, and
[
\mathbf 1_{v_p(n)=e}=g_{p^e}(n)-g_{p^{e+1}}(n).
]

**Proof.** (p^e\mid n \iff n\equiv 0\pmod{p^e}) gives periodicity and nesting; the exact-valuation identity is immediate. ∎

**Interpretation:** the (p)-adic valuation is a **multiscale rhythm**: the sets ({n:v_p(n)\ge e}) form a nested tower of periodic gates.

---

# 3. The factorization lens: a coordinate system where Dirichlet operators become local

Dirichlet transforms are multiplicative/divisor-based:
[
(T_a f)(n)=\sum_{d\mid n} a(d), f(n/d).
]
To make “program structure” visible, restrict kernels to (P)-smooth divisors.

## 3.1 (P)-smooth divisor monoid and exponent coordinates

Define the (P)-smooth monoid
[
S_P := \left{\prod_{p\in P} p^{e_p} : e_p\in\mathbb N \right}.
]
Define the exponent encoding
[
\exp_P:; S_P \to \mathbb N^{P},\qquad \exp_P!\Big(\prod_{p\in P} p^{e_p}\Big)=(e_p)_{p\in P}.
]
Divisibility on (S_P) corresponds to coordinatewise order on (\mathbb N^{P}):
[
d\mid s \quad\Longleftrightarrow\quad \exp_P(d)\le \exp_P(s)\ \text{(componentwise)}.
]

## 3.2 Dirichlet convolution becomes multivariate additive convolution on exponents

Let (\mathcal A_P) be the algebra of finitely supported functions (a:S_P\to\mathbb C) (extend by 0 outside (S_P\subset\mathbb N)). Define Dirichlet convolution as usual on (\mathbb N).

### Theorem 22 (exponent convolution isomorphism)  [§3.1 · Phase 3, Fragment 4]

Define (\widetilde a:\mathbb N^{P}\to\mathbb C) by (\widetilde a(e)=a(\prod_{p\in P}p^{e_p})). Then for (a,b\in\mathcal A_P),
[
(a*b)\ \leftrightarrow\ (\widetilde a \star \widetilde b),
]
where (\star) is **multivariate discrete convolution**
[
(\widetilde a \star \widetilde b)(e) := \sum_{0\le u\le e} \widetilde a(u),\widetilde b(e-u),
]
(sum over (u\in\mathbb N^{P}) with componentwise bounds).

**Proof.** For (s\in S_P) with exponent (e=\exp_P(s)),
[
(a*b)(s)=\sum_{d\mid s} a(d)b(s/d).
]
Write (u=\exp_P(d)) and note (d\mid s\iff 0\le u\le e). Also (\exp_P(s/d)=e-u). Substitute. ∎

**This is the first clean “rhythm inside an integer” theorem:** on (P)-smooth structure, Dirichlet composition is literally additive convolution on the valuation lattice (\mathbb N^{P}).

---

# 4. Fiberwise locality of (T_a) for (P)-smooth kernels: the program space

Assume (a\in\mathcal A_P), i.e. (a(d)=0) unless (d\in S_P).

### Theorem 23 (factorization-fiber decomposition)  [§4.1 · Phase 3, Fragment 4]

Fix (n\in{1,\dots,N}) and write (n=u_P(n), s_P(n)). Then
[
(T_a f)(n)=\sum_{d\mid s_P(n)} a(d), f!\left(u_P(n)\cdot \frac{s_P(n)}{d}\right).
]
In particular:

1. (T_a) never mixes different (P)-free parts: if (u_P(m)\neq u_P(n)), then the value (f(m)) cannot influence ((T_a f)(n)).
2. On each fixed fiber (u=u_P(n)), (T_a) acts only on the lattice of (P)-smooth factors of numbers of the form (u\cdot s).

**Proof.** If (a(d)\neq 0) then (d\in S_P). Such a divisor of (n=u\cdot s) must divide (s) (since (\gcd(u,d)=1)). Hence the divisor sum reduces to (d\mid s), and (n/d = u\cdot (s/d)). ∎

### Corollary 16 (explicit valuation-lattice update rule)  [§4.2 · Phase 3, Fragment 4]

Let (e=v_P(n)\in\mathbb N^{P}). Define the fiber function
[
f_u(e') := f!\left(u\cdot \prod_{p\in P}p^{e'_p}\right),
]
whenever the argument lies in ({1,\dots,N}) (otherwise treat as 0). Then on that fiber,
[
(T_a f)*u(e) = \sum*{0\le u\le e}\widetilde a(u), f_u(e-u),
]
i.e. **multivariate convolution on valuation depth**.

**Proof.** Apply Theorem 23 and Theorem 22 with exponent coordinates. ∎

**Meaning (program space):** for (P)-smooth kernels (a), the operator (T_a) is a *local, hierarchical, lower-triangular* update on the valuation lattice, separately for each (P)-free label (u). This is an exact “program execution” semantics on ((u, v_P)).

---

# 5. Markovianity after augmentation: the correct state for multiplicative dynamics

Your earlier constraint was: “Markovian when state is augmented with radix phase.” Here is the precise multiplicative analogue.

### Definition 45 (augmented factorization state)  [§5.1 · Phase 3, Fragment 4]

Define the factorization-lens state map
[
\Lambda_P:{1,\dots,N}\to \mathcal U_P \times \mathbb N^{P},
\qquad
\Lambda_P(n):=\big(u_P(n),, v_P(n)\big),
]
where (\mathcal U_P:={u\in{1,\dots,N}:\gcd(u,\prod_{p\in P}p)=1}).

### Proposition 53 (Dirichlet transforms are local/Markov on (\Lambda_P))  [§5.2 · Phase 3, Fragment 4]

Let (a\in\mathcal A_P). Then the dependence graph of (T_a) is contained in:
[
(u,e)\ \longleftarrow\ (u,e-u') \quad \text{for }u'\in\mathrm{supp}(\widetilde a),\ 0\le u'\le e,
]
i.e. transitions only move **downward** in the valuation lattice and never change (u).

**Proof.** This is exactly Corollary 16. ∎

**Lean.** Proposition 53 is formalized in `FdrsFormal/NumberTheory/FactorizationLens/MarkovProperty.lean` (`markov_on_lens`; `finite_dependency_neighborhood` exhibits the finite dependency neighborhood explicitly). This is *combinatorial* Markov locality of a Dirichlet convolution — distinct from the probabilistic Parry Markov kernel of Phase 13 §13.5.

So if your “environment state” is indexed by ((u,e)), then (T_a) is a structured Markov update (finite dependency neighborhood determined by (\mathrm{supp}(a))).

---

# 6. Squarefree and Möbius in valuation-lattice terms (rhythm filters)

On (P)-smooth numbers, the Möbius and squarefree filters have an especially clean form.

### Proposition 54 (squarefree constraint on the (P)-valuation lattice)  [§6.1 · Phase 3, Fragment 4]

For (s=\prod_{p\in P}p^{e_p}\in S_P),
[
\mu^2(s)=1 \iff e_p\in{0,1}\ \forall p\in P.
]
Hence squarefree projection on (P)-smooth fibers is exactly restriction to the “({0,1}^P)” hypercube inside (\mathbb N^P).

**Proof.** (s) is squarefree iff no exponent exceeds 1. ∎

### Proposition 55 (Möbius on (P)-smooth numbers)  [§6.2 · Phase 3, Fragment 4]

For (s=\prod_{p\in P}p^{e_p}),
[
\mu(s)=
\begin{cases}
(-1)^{\sum_{p} e_p},& e_p\in{0,1}\ \forall p,\
0,& \text{otherwise}.
\end{cases}
]
So Möbius inversion on (P)-smooth fibers is inversion on this valuation-lattice convolution algebra.

**Proof.** Standard characterization of (\mu) by squarefreeness and parity of number of prime factors. ∎

---

# 7. What this gives you: “rhythm in an integer” (formal statement)

You can now point to two *orthogonal* hierarchical structures carried by each integer (n):

1. **Additive rhythm:** residues (n \bmod B_L), i.e. the prefix-cylinder path in mixed radix.
2. **Multiplicative rhythm:** valuation vector (v_P(n)), i.e. the depth in each (p)-adic gate tower ({p^e\mid n}).

And you have proven that an entire, computationally meaningful operator class—Dirichlet transforms with (P)-smooth kernels—acts as **fiberwise multivariate convolution** on the multiplicative rhythm coordinate ((u_P, v_P)). That is a precise “program space inside the integer,” because:

* kernels (a) are compositional by Dirichlet convolution (Theorem 22),
* execution is local on the valuation lattice (Theorem 23 / Corollary 16),
* squarefree/Möbius provide canonical projectors/inverses inside that space.

---

## Leading questions for Phase 4, Fragment 1 (Integers as Programs)

1. **Semantic map:** define a mapping (n \mapsto \llbracket n\rrbracket) into an operator algebra (built from (T_a), valuation gates, character probes, and time-shifts) and prove homomorphism laws under multiplication (under explicit constraints).
2. **Program composition vs multiplication:** decide the “lens” precisely: is the program associated to (n) the kernel (a_n=\delta_n) under Dirichlet composition, or a structured product over prime-power primitives, or a mixed additive×multiplicative operator?
3. **Scheduling:** show how the mixed-radix Tick (additive odometer) schedules evaluation of these multiplicative primitives, i.e. how additive time reveals valuation rhythm events (e.g. triggers at multiples of (p^e)).

## Phase 4 — Integers as Programs, Fragment 1

### Factorization lenses, a semantic map (n \mapsto \llbracket n \rrbracket), composition laws, and “rhythm” as divisibility-gated execution

We fix a finite horizon (k\ge 0) and write
[
N := B_{k+1},\qquad \mathcal R^{(k)}=\prod_{i=0}^{k} D_i,\qquad \mathrm{nat}_k(\tau):=\operatorname{dec}_k(\tau)+1\in{1,\dots,N}.
]
Let (H_k := \mathbb C^{\mathcal R^{(k)}}) (mixed-radix tensors) and identify it with sequences (f:{1,\dots,N}\to\mathbb C) via
[
f(n)=F(\operatorname{enc}_k(n-1)),\quad F(\tau)=f(\mathrm{nat}_k(\tau)).
]

This fragment formalizes the minimal, theorem-grade statement:

* **Programs** are realized as **operators** on (H_k) (or on sequences on ({1,\dots,N})).
* **Integers** map to operators in a way that respects **multiplicative composition**.
* The **mixed-radix clock** schedules these programs via **divisibility rhythms**.

---

# 1. Factorization lenses as explicit state maps

A *lens* is a structured coordinate map on integers that exposes a compositional sub-geometry.

### Definition 46 (prime-set lens)  [§1.1 · Phase 4, Fragment 1]

Fix a finite set of primes (P). For (n\ge 1), define:
[
v_P(n):=(v_p(n))*{p\in P}\in \mathbb N^{P},\qquad
s_P(n):=\prod*{p\in P}p^{v_p(n)},\qquad
u_P(n):=\frac{n}{s_P(n)}.
]
Then (u_P(n)) is coprime to every (p\in P), and (n=u_P(n),s_P(n)) uniquely.

We call (\Lambda_P(n):=(u_P(n),v_P(n))) the **factorization lens state**.

---

# 2. The semantic core: Dirichlet-basis programs (\delta_n)

Let (\delta_n:\mathbb N_{\ge 1}\to\mathbb C) be the Kronecker delta at (n): (\delta_n(n)=1), (\delta_n(m)=0) for (m\neq n).

Recall Dirichlet convolution:
[
(a*b)(m)=\sum_{d\mid m} a(d),b(m/d).
]

### Lemma 4 (multiplication inside the Dirichlet basis)  [§2.1 · Phase 4, Fragment 1]

For all (a,b\ge 1),
[
\delta_a * \delta_b = \delta_{ab}.
]

**Proof.**
[
(\delta_a*\delta_b)(m)=\sum_{d\mid m}\delta_a(d)\delta_b(m/d)
]
is nonzero iff (d=a) and (m/d=b), i.e. iff (m=ab), in which case it equals (1). ∎

This already gives a pure algebraic “integer ↔ program token” in the Dirichlet algebra: ({\delta_n}) is a multiplicative basis mirroring ((\mathbb N_{\ge1},\times)).

---

# 3. The semantic map into operators

## 3.1 Operator space

Work on sequences (f:{1,\dots,N}\to\mathbb C). Extend (f) to (\mathbb N_{\ge1}) by (f(m)=0) for (m>N) (this makes all formulas total without changing values on ({1,\dots,N})).

Define the Dirichlet transform (T_a) for any arithmetic kernel (a):
[
(T_a f)(n)=\sum_{d\mid n} a(d), f(n/d).
]

### Proposition 56 (representation of Dirichlet convolution)  [§3.1 · Phase 4, Fragment 1]

For all (a,b),
[
T_a\circ T_b = T_{a*b},\qquad T_\varepsilon = I.
]

**Proof.** Standard divisor-reindexing (already established in Phase 3 Fragment 1). ∎

## 3.2 Integers as operators: the division-shift program

Define the **integer-program operator** on sequences:
[
(\mathsf S_n f)(m) := (T_{\delta_n} f)(m)
= \sum_{d\mid m}\delta_n(d) f(m/d)
= \mathbf 1_{n\mid m}, f(m/n).
]

Transport to mixed-radix tensors (F\in H_k) by conjugation through (\mathrm{nat}*k):
[
(\llbracket n\rrbracket_k F)(\tau)
:= \mathbf 1*{,n\mid \mathrm{nat}_k(\tau)};
F!\left(\operatorname{enc}_k!\big(\mathrm{nat}_k(\tau)/n - 1\big)\right).
]
This is computable from (\operatorname{dec}_k) and (\operatorname{enc}_k).

### Theorem 24 (monoid homomorphism: multiplication ↔ composition)  [§3.2 · Phase 4, Fragment 1]

For all (a,b\ge 1),
[
\mathsf S_a\circ \mathsf S_b = \mathsf S_{ab},
\qquad\text{equivalently}\qquad
\llbracket a\rrbracket_k \circ \llbracket b\rrbracket_k = \llbracket ab\rrbracket_k.
]

**Proof (sequence form).**
[
(\mathsf S_a(\mathsf S_b f))(m)=\mathbf 1_{a\mid m},(\mathsf S_b f)(m/a)
=\mathbf 1_{a\mid m},\mathbf 1_{b\mid (m/a)}, f(m/(ab))
=\mathbf 1_{ab\mid m}, f(m/(ab))
=(\mathsf S_{ab}f)(m).
]
Transporting through (\mathrm{nat}_k) yields the tensor statement. ∎

### Corollary 17 (prime-power instruction set)  [§3.3 · Phase 4, Fragment 1]

If (n=\prod_{p} p^{e_p}), then
[
\llbracket n\rrbracket_k = \prod_{p} \llbracket p^{e_p}\rrbracket_k,
]
and all (\llbracket p^{e_p}\rrbracket_k) commute (because multiplication is commutative and Theorem 24 forces (\llbracket a\rrbracket_k\llbracket b\rrbracket_k=\llbracket b\rrbracket_k\llbracket a\rrbracket_k)).

This is a fully formal “program decomposes into prime-power micro-instructions.”

---

# 4. The program space inside the integer under a lens (P)

The previous semantics (\llbracket n\rrbracket_k) is global. To make the *internal* structure explicit, restrict to (P)-smooth programs.

### Definition 47 ((P)-smooth program monoid)  [§4.1 · Phase 4, Fragment 1]

Let
[
S_P := \left{\prod_{p\in P}p^{e_p}: e_p\in\mathbb N\right}.
]
Programs (n\in S_P) are those whose prime support is contained in (P).

### Theorem 25 (lens-locality: (P)-smooth programs preserve (u_P) and shift valuations)  [§4.2 · Phase 4, Fragment 1]

Fix (n\in S_P). For any (m\ge 1), write (m=u_P(m),s_P(m)).
If (n\mid m), then:

1. (u_P(m/n)=u_P(m)) (the (P)-free label is invariant),
2. (v_P(m/n)=v_P(m)-v_P(n)) (componentwise subtraction).

Consequently, on the factorization-lens coordinates ((u,e)\in\mathcal U_P\times\mathbb N^{P}), the operator (\mathsf S_n) acts fiberwise as
[
(\mathsf S_n f)(u,e)=\mathbf 1_{v_P(n)\le e}; f(u, e-v_P(n)).
]

**Proof.** Since (n\in S_P), (\gcd(n,u_P(m))=1), so dividing by (n) affects only the (P)-smooth part (s_P(m)). Valuations subtract on division when the divisor is (P)-smooth. ∎

**This is the precise “program space within the integer”:** under lens (\Lambda_P), every (P)-smooth integer (n) is exactly a **translation vector** (v_P(n)) on the valuation lattice (\mathbb N^{P}), acting independently on each (u)-fiber.

---

# 5. Rhythm: execution gating by divisibility events along the mixed-radix clock

The mixed-radix clock enumerates (\mathrm{nat}_k(\tau)\in{1,\dots,N}) in increasing order when applying Tick (T) (or cyclic Tick on (\mathcal R^{(k)})). The “when does a program fire?” question is exactly divisibility.

### Definition 48 (execution set / rhythm of (n))  [§5.1 · Phase 4, Fragment 1]

Define the event set in mixed-radix time:
[
E_n := {\tau\in\mathcal R^{(k)} : n \mid \mathrm{nat}_k(\tau)}.
]
On the integer line ({1,\dots,N}), this corresponds to ({m: n\mid m}), i.e. a pure period-(n) rhythm.

### Proposition 57 (periodicity on the integer line)  [§5.2 · Phase 4, Fragment 1]

Let (g_n(m):=\mathbf 1_{n\mid m}). Then for all (m),
[
g_n(m+n)=g_n(m).
]

**Proof.** (n\mid (m+n)\iff n\mid m). ∎

### Proposition 58 (finite-depth cylinder realization when (n\mid B_L))  [§5.3 · Phase 4, Fragment 1]

If (n\mid B_L) for some (L\le k+1), then (E_n\in\mathcal F_{k,L}); equivalently, the rhythm gate (\mathbf 1_{E_n}) is a union of length-(L) cylinders.

**Proof.** Same as earlier congruence/cylinder measurability: if (n\mid B_L), then (\mathrm{nat}_k(\tau)\bmod n) depends only on the length-(L) prefix, so the residue class “(\equiv 0)” is cylinder-measurable. ∎

So: **the radix clock schedules** the integer-program (\llbracket n\rrbracket_k) by a gate that is *sometimes* representable at finite prefix depth, depending on divisibility of (n) by radix block sizes.

---

# 6. What we have established (without metaphor)

1. The map
   [
   n \longmapsto \llbracket n\rrbracket_k = T^{(k)}*{\delta_n}
   ]
   is a **monoid homomorphism** from ((\mathbb N*{\ge1},\times)) to ((\mathrm{End}(H_k),\circ)).
2. Prime-power factorization of (n) is literally a commuting micro-instruction decomposition of (\llbracket n\rrbracket_k).
3. Under a prime-set lens (P), (P)-smooth programs act as **translations** on the valuation lattice (\mathbb N^{P}), fiberwise in (u_P).
4. The **rhythm** of a program (n) along mixed-radix time is exactly the gate (E_n) (multiples of (n)), with a sharp finite-depth condition (n\mid B_L) for cylinder realizability.

---

## Leading questions for Phase 4, Fragment 2

1. **From basis-programs to compiled programs:** define a class of kernels (a) (finite linear combinations of (\delta_n), or (P)-smooth kernels) and interpret (T_a) as “program superposition/mixture”; prove the exact composition laws and identify normal forms.
2. **Coupling additive time with multiplicative execution:** formalize an “execution operator” (\mathcal E) that uses the time state (\tau) to gate which (\llbracket n\rrbracket_k) applies (e.g., via (E_n)), and prove it is Markov/local in an augmented state.
3. **The integer → program functor (full version):** lift from ((\mathbb N,\times)) to a category of structured programs (labeled prime-power ASTs / valuation vectors) and show equivalence with the operator semantics under explicit commutation assumptions.

## Phase 4 — Integers as Programs, Fragment 2

### Compiled programs as finite Dirichlet kernels, normal forms, divisor-gated execution, and Markov locality in the factorization lens

Fix a finite horizon (k\ge0) and set
[
N:=B_{k+1},\qquad \mathcal R^{(k)}=\prod_{i=0}^k D_i,\qquad \mathrm{nat}_k(\tau):=\operatorname{dec}_k(\tau)+1\in{1,\dots,N}.
]
Let (V) be a complex vector space (or any Banach space; linearity is what matters). We work with “time-indexed memory”
[
\mathsf{Mem}_N(V):={f:{1,\dots,N}\to V},
]
and its mixed-radix pullback (F(\tau)=f(\mathrm{nat}_k(\tau))).

This fragment answers: **what is a compiled program?**
A compiled program is a **kernel** (a) that defines an operator (T_a). Execution at time (n) is *not* imposed; it is selected by the divisor structure (d\mid n). That divisor structure is the “rhythm.”

---

# 1. Finite-horizon program algebra: truncated Dirichlet convolution

Let (\mathcal K_N := {a:{1,\dots,N}\to\mathbb C}). Extend each (a\in\mathcal K_N) to (\mathbb N_{\ge1}) by zero outside ([1,N]) when convenient.

### Definition 49 (truncated Dirichlet product)  [§1.1 · Phase 4, Fragment 2]

For (a,b\in\mathcal K_N), define (a *_N b\in\mathcal K_N) by
[
(a **N b)(n) := \sum*{d\mid n} a(d), b(n/d),\qquad 1\le n\le N.
]
(Notice the sum only uses values (\le n\le N), so it is closed in (\mathcal K_N).)

### Proposition 59 (algebra laws)  [§1.2 · Phase 4, Fragment 2]

((\mathcal K_N,*_N)) is a commutative associative unital algebra with identity (\varepsilon) given by
[
\varepsilon(1)=1,\ \varepsilon(n)=0\ (n>1).
]

**Proof.**

* Closure is immediate from the definition.
* Commutativity: substitute (d\leftrightarrow n/d).
* Associativity: for (n\le N),
  [
  ((a*_N b)**N c)(n)=\sum*{d\mid n}(a**N b)(d)c(n/d)
  =\sum*{d\mid n}\sum_{e\mid d} a(e)b(d/e)c(n/d).
  ]
  Reparameterize by (u=e), (v=d/e), (w=n/d). Then (uvw=n) and every factorization (uvw=n) appears exactly once. This yields
  [
  \sum_{uvw=n} a(u)b(v)c(w) = (a*_N (b*_N c))(n).
  ]
* Identity: ((a**N\varepsilon)(n)=\sum*{d\mid n}a(d)\varepsilon(n/d)=a(n)). ∎

**Interpretation:** (\mathcal K_N) is the finite “compiler target space” for programs-as-kernels.

---

# 2. Program semantics: kernels as operators on memory

### Definition 50 (compiled program operator)  [§2.1 · Phase 4, Fragment 2]

For (a\in\mathcal K_N), define (T_a:\mathsf{Mem}_N(V)\to\mathsf{Mem}*N(V)) by
[
(T_a f)(n) := \sum*{d\mid n} a(d), f(n/d),\qquad 1\le n\le N.
]

### Proposition 60 (representation / homomorphism)  [§2.2 · Phase 4, Fragment 2]

For all (a,b\in\mathcal K_N),
[
T_a\circ T_b = T_{a**N b},\qquad T*\varepsilon = I.
]

**Proof.** For (n\le N),
[
(T_a(T_b f))(n)=\sum_{d\mid n} a(d),(T_b f)(n/d)
=\sum_{d\mid n} a(d)\sum_{e\mid n/d} b(e) f(n/(de))
=\sum_{de\mid n} a(d)b(e)f(n/(de)).
]
Group by (m=de) (equivalently sum over divisors (m\mid n) and then over (d\mid m)):
[
=\sum_{m\mid n}\Big(\sum_{d\mid m}a(d)b(m/d)\Big)f(n/m)
=\sum_{m\mid n}(a**N b)(m),f(n/m)
=(T*{a*_N b}f)(n).
]
Identity is immediate. ∎

So (a\mapsto T_a) is an algebra homomorphism ((\mathcal K_N,*_N)\to \mathrm{End}(\mathsf{Mem}_N(V))).

---

# 3. Normal forms: basis programs, prime-power compilation, and “program space” inside (n)

## 3.1 Basis programs

Let (\delta_m\in\mathcal K_N) be the basis kernel: (\delta_m(m)=1), (0) else.

Then
[
T_{\delta_m} f(n) = \mathbf 1_{m\mid n}, f(n/m).
]
This is exactly the integer-program operator (\mathsf S_m) from Fragment 1.

### Proposition 61 (multiplication = composition on basis programs)  [§3.1 · Phase 4, Fragment 2]

For (ab\le N),
[
\delta_a **N \delta_b = \delta*{ab}
\quad\Longrightarrow\quad
T_{\delta_a}\circ T_{\delta_b}=T_{\delta_{ab}}.
]

**Proof.** Same divisor-uniqueness argument as before; the truncation does not affect it when (ab\le N) because the product index stays in-range. ∎

## 3.2 Compilation as kernel superposition

Any compiled program (a\in\mathcal K_N) is a finite linear combination (a=\sum_{m=1}^N a(m)\delta_m), hence
[
T_a = \sum_{m=1}^N a(m), T_{\delta_m}.
]

**Meaning:** “program space” is literally the coefficient function (m\mapsto a(m)); execution at time (n) selects those coefficients with (m\mid n).

## 3.3 Prime-power microcode and factorization

Define micro-instructions (T_{\delta_{p^e}}). For a fixed integer (n=\prod_p p^{e_p}\le N),
[
T_{\delta_n}=\prod_p T_{\delta_{p^{e_p}}}
]
(commuting product), giving an exact “prime-power microcode” decomposition.

---

# 4. Execution is divisor-gated rhythm (no external scheduler)

### Definition 51 (divisor gate / rhythm)  [§4.1 · Phase 4, Fragment 2]

For (m\le N), define the rhythm predicate on time (n):
[
g_m(n) := \mathbf 1_{m\mid n}.
]

### Theorem 26 (compiled execution law)  [§4.2 · Phase 4, Fragment 2]

For any kernel (a\in\mathcal K_N) and memory (f),
[
(T_a f)(n)=\sum_{m=1}^N a(m), g_m(n), f(n/m),
]
where only divisors (m\mid n) contribute.

**Proof.** Expand (a=\sum_m a(m)\delta_m) and use linearity plus (T_{\delta_m}) form. ∎

**Interpretation:** time (n) “chooses” which sub-programs (m) fire purely by the arithmetic condition (m\mid n). That is the rhythm embedded in (n).

### Corollary 18 (causality / triangularity)  [§4.3 · Phase 4, Fragment 2]

If we order times (1<2<\dots<N), then ((T_a f)(n)) depends only on values (f(t)) with (t\le n) (since (t=n/m \le n)).
So (T_a) is lower-triangular as an operator on the time-line.

---

# 5. Markov locality after augmentation: factorization-lens state space

The additive/cylinder filtration tracks (n\bmod B_L). Dirichlet execution is multiplicative. The correct “local” coordinate system is the factorization lens.

Fix a finite prime set (P). For (n), write
[
n=u_P(n),s_P(n),\qquad s_P(n)=\prod_{p\in P} p^{v_p(n)},\qquad u_P(n)\perp \prod_{p\in P}p.
]

## 5.1 (P)-smooth compiled programs

Say (a\in\mathcal K_N) is **(P)-smooth** if (a(m)=0) unless (m\in S_P:={\prod_{p\in P}p^{e_p}}).

### Theorem 27 (fiberwise locality of (P)-smooth programs)  [§5.1 · Phase 4, Fragment 2]

If (a) is (P)-smooth, then for any (n\le N),
[
(T_a f)(n)=\sum_{d\mid s_P(n)} a(d), f!\Big(u_P(n)\cdot \frac{s_P(n)}{d}\Big).
]
In particular, ((T_a f)(n)) depends only on values of (f) at integers with the **same** (P)-free part (u_P(n)).

**Proof.** If (a(d)\neq 0), then (d\in S_P) and (\gcd(d,u_P(n))=1). Thus any such divisor (d\mid n=u s) must divide (s). Substitute (n/d=u(s/d)). ∎

## 5.2 Lattice neighborhood = “Markov radius”

Let (\widetilde a(e):=a(\prod_{p\in P}p^{e_p})), a finitely supported function on (\mathbb N^P). For each fixed (u), define the fiber memory
[
f_u(e):= f!\Big(u\cdot \prod_{p\in P}p^{e_p}\Big),
]
with the convention (f_u(e)=0) if the argument exceeds (N).

### Corollary 19 (valuation-lattice convolution form)  [§5.2 · Phase 4, Fragment 2]

For (n=u\cdot \prod_{p\in P}p^{e_p}),
[
(T_a f)*u(e)=\sum*{0\le r\le e}\widetilde a(r), f_u(e-r).
]

**Proof.** This is the exponent-coordinate rewrite of Theorem 27 (Dirichlet on (P)-smooth numbers becomes multivariate convolution on (\mathbb N^P)). ∎

**Markov statement:** if (\mathrm{supp}(\widetilde a)\subseteq {r:|r|_\infty\le R}), then ((T_a f)_u(e)) depends only on (f_u(e-r)) within an (R)-neighborhood in the valuation lattice. That is an explicit, finite dependency radius.

---

# 6. Mixed-radix realization of rhythms (when the gate is a cylinder)

Pull back to mixed-radix time (\tau\in\mathcal R^{(k)}) via (n=\mathrm{nat}*k(\tau)). The divisor gate becomes
[
G_m(\tau):=\mathbf 1*{m\mid \mathrm{nat}_k(\tau)}.
]

### Proposition 62 (finite-depth cylinder criterion)  [§6.1 · Phase 4, Fragment 2]

If (m\mid B_L) for some (L\le k+1), then (G_m) is (\mathcal F_{k,L})-measurable; equivalently it is a union of length-(L) cylinders.

**Proof.** (m\mid B_L \Rightarrow \mathrm{nat}_k(\tau)\bmod m) depends only on the first (L) digits, so the residue condition “(\equiv 0)” is cylinder-measurable. ∎

So: when your radix product contains the program modulus (m) by depth (L), the program’s rhythm is not just periodic—it is **prefix-local** in the mixed-radix topology.

---

## Leading questions for Phase 4, Fragment 3

1. **Program categories / functoriality:** define a structured program object (prime-power AST, valuation translation, or kernel with support constraints) and prove equivalence with operator semantics (a\mapsto T_a).
2. **Coupling time Tick and execution operators:** define a two-dimensional state (time (\tau) plus factorization state (\Lambda_P(\mathrm{nat}_k(\tau))) or a tracked valuation register) so execution becomes *locally computable* step-by-step along Tick.
3. **From “memory over time” to “state evolution”:** choose a state space (\mathcal X) and map kernels to endomorphisms of (\mathcal X) driven by divisor rhythms, producing an honest dynamical system (this is the bridge into Phase 6 runtime/complexity).


## Phase 4 — Computation Primitives from ANT, Fragment 4.1

### Instruction set as operators, and the algebra they generate

We work on a finite horizon (N:=B_{k+1}) (implementable), with “memory” as sequences
[
\mathsf{Mem}_N := {f:{1,\dots,N}\to \mathbb C}.
]
(Everything below pulls back to mixed-radix tensors (F(\tau)=f(\mathrm{nat}_k(\tau))) exactly as in Phase 3.)

We will build an instruction set inside the operator algebra (\mathrm{End}(\mathsf{Mem}_N)).

---

# 0. Two primitive operator families

### (A) Diagonal multipliers (gates)

For any (g:{1,\dots,N}\to\mathbb C), define
[
(M_g f)(n):=g(n),f(n).
]
If (g\in{0,1}), then (M_g) is a projection (idempotent gate).

### (B) Dirichlet transforms (compiled kernels)

For any kernel (a:{1,\dots,N}\to\mathbb C), define
[
(T_a f)(n):=\sum_{d\mid n} a(d), f(n/d).
]
These are the “compiled programs” from Phase 4 (Integers as Programs): (T_{\delta_m} f(n)=\mathbf 1_{m\mid n}f(n/m)).

**Key fact (representation law).** For all (a,b),
[
T_a\circ T_b = T_{a*_N b},\qquad (a**N b)(n):=\sum*{d\mid n}a(d)b(n/d).
]

---

# 1. Instruction 1: (\mathrm{Proj}_{q,a}) (residue projection)

Here we use the **multiplicative** residue classes, i.e. on ((\mathbb Z/q\mathbb Z)^\times), because this is the probe system with Fourier basis “characters on ((\mathbb Z/q\mathbb Z)^\times)”.

Fix (q\ge 1) and (a\in(\mathbb Z/q\mathbb Z)^\times). Define the gate
[
g_{q,a}(n):=\mathbf 1_{\gcd(n,q)=1},\mathbf 1_{n\equiv a\ (\mathrm{mod}\ q)}.
]
Define the instruction
[
\mathrm{Proj}*{q,a} := M*{g_{q,a}}.
]

### Proposition 63 (projection algebra for a fixed modulus)  [§1.1 · Phase 4, Fragment 4.1]

For units (a,b\in(\mathbb Z/q\mathbb Z)^\times):

* **Idempotent:** (\mathrm{Proj}*{q,a}^2=\mathrm{Proj}*{q,a}).
* **Orthogonal:** (\mathrm{Proj}*{q,a}\mathrm{Proj}*{q,b}=0) if (a\neq b).
* **Partition of unity on units:**
  [
  \sum_{a\in(\mathbb Z/q\mathbb Z)^\times}\mathrm{Proj}*{q,a} = M*{\mathbf 1_{\gcd(\cdot,q)=1}}.
  ]

*Proof.* Pointwise indicator identities. ∎

### Proposition 64 (character expansion = Fourier probe form)  [§1.2 · Phase 4, Fragment 4.1]

Let (\mathcal X(q)) be the Dirichlet characters mod (q), extended by (0) off units. Then
[
\mathrm{Proj}*{q,a}
=\frac{1}{\varphi(q)}\sum*{\chi\in\mathcal X(q)} \overline{\chi(a)}, M_\chi,
\qquad (M_\chi f)(n):=\chi(n)f(n).
]

*Proof.* Standard orthogonality over ((\mathbb Z/q\mathbb Z)^\times). ∎

**Interpretation:** (\mathrm{Proj}_{q,a}) is a literal “phase selection” instruction, with characters as its spectral basis.

---

# 2. Instruction 2: (\mathrm{MobiusUnmix}) (inversion)

Define two kernels on ({1,\dots,N}):

* (\mathbf 1(d)\equiv 1),
* (\mu(d)) the Möbius function.

Define the operators
[
\mathrm{DivisorSum}:=T_{\mathbf 1},
\qquad
\mathrm{MobiusUnmix}:=T_{\mu}.
]

### Theorem 28 (Möbius inversion as operator inverse)  [§2.1 · Phase 4, Fragment 4.1]

[
\mathrm{MobiusUnmix}\circ \mathrm{DivisorSum} = I
\quad\text{and}\quad
\mathrm{DivisorSum}\circ \mathrm{MobiusUnmix} = I
]
(on (\mathsf{Mem}_N)).

*Proof.* In the kernel algebra, (\mu *_N \mathbf 1 = \varepsilon) and (\mathbf 1 **N \mu=\varepsilon). Transport via (T_a\circ T_b=T*{a*_N b}). ∎

**Interpretation:** “unmixing” is not metaphor: it is exactly inversion in the Dirichlet convolution algebra.

---

# 3. Instruction 3: (\mathrm{SquarefreeProject}) (squarefree projector)

Define the gate
[
g_{\mathrm{sf}}(n):=\mu^2(n)\in{0,1},
\qquad
\mathrm{SquarefreeProject}:=M_{g_{\mathrm{sf}}}.
]

### Proposition 65 (projection + prime-square factorization)  [§3.1 · Phase 4, Fragment 4.1]

* (\mathrm{SquarefreeProject}^2=\mathrm{SquarefreeProject}).
* Let (\Pi_{p^2}:=M_{\mathbf 1_{p^2\mid \cdot}}). Then on ({1,\dots,N}),
  [
  \mathrm{SquarefreeProject}=\prod_{p^2\le N}\big(I-\Pi_{p^2}\big).
  ]

*Proof.* Pointwise identities: (\mu^2(n)=\prod_{p^2\mid n}0) and otherwise 1. ∎

**Interpretation:** squarefree is a *finite* conjunction of periodic “no (p^2)” gates up to the horizon.

---

# 4. Instruction 4: (\mathrm{CRTCompose}) (merge constraints)

Given two constraints ((q_1,a_1)), ((q_2,a_2)) with (\gcd(q_1,q_2)=1), let (a) be the unique class mod (q_1q_2) satisfying CRT:
[
a\equiv a_1\ (\mathrm{mod}\ q_1),\qquad a\equiv a_2\ (\mathrm{mod}\ q_2).
]

Define
[
\mathrm{CRTCompose}\big((q_1,a_1),(q_2,a_2)\big)
:= \mathrm{Proj}*{q_1,a_1},\mathrm{Proj}*{q_2,a_2}.
]

### Theorem 29 (CRT identity)  [§4.1 · Phase 4, Fragment 4.1]

If (\gcd(q_1,q_2)=1), then
[
\mathrm{Proj}*{q_1,a_1},\mathrm{Proj}*{q_2,a_2} = \mathrm{Proj}_{q_1q_2,a}.
]

*Proof.* Pointwise: the product of indicators is the indicator of simultaneous congruences; by CRT this equals a single congruence mod (q_1q_2). Unit conditions also match because (\gcd(n,q_1q_2)=1\iff \gcd(n,q_1)=\gcd(n,q_2)=1). ∎

**Interpretation:** constraint-merge is literally multiplication (intersection) of projectors, and CRT says coprime merges collapse into one projector.

---

# 5. Instruction 5: (\mathrm{SieveFilter}) (progressive admissibility)

A sieve is a growing set of local exclusions. The clean operator form is again a diagonal gate.

### Definition 52 (general sieve filter)  [§5.1 · Phase 4, Fragment 4.1]

Fix a set of primes (P) and for each (p\in P) choose an excluded residue set (A_p\subseteq(\mathbb Z/p\mathbb Z)). Define
[
g_{\mathrm{sieve}}(n):=\prod_{p\in P}\mathbf 1_{n\bmod p \notin A_p}.
]
Then define
[
\mathrm{SieveFilter}:=M_{g_{\mathrm{sieve}}}.
]

### Proposition 66 (idempotence + monotonic refinement)  [§5.2 · Phase 4, Fragment 4.1]

* (\mathrm{SieveFilter}^2=\mathrm{SieveFilter}).
* If (P\subseteq P') and (A_p\subseteq A'*p) for all (p\in P), then
  [
  g*{\mathrm{sieve}'}\le g_{\mathrm{sieve}}\quad\text{pointwise},
  \qquad
  \mathrm{SieveFilter}',\mathrm{SieveFilter}=\mathrm{SieveFilter}'.
  ]

*Proof.* Pointwise indicator algebra. ∎

### Example 1 (squarefree as a sieve)  [§5.3 · Phase 4, Fragment 4.1]

Take (A_p={0}) but applied to the modulus (p^2) (exclude multiples of (p^2)); then (\mathrm{SieveFilter}) becomes (\mathrm{SquarefreeProject}) (Proposition 65).

---

# 6. Closure + key algebraic identities among the instruction set

Let (\mathcal I_N) be the set of operators generated by:

* all (\mathrm{Proj}_{q,a}),
* (\mathrm{SquarefreeProject}),
* (\mathrm{SieveFilter}),
* (\mathrm{DivisorSum}) and (\mathrm{MobiusUnmix}),
* and closed under composition and finite linear combinations.

### Proposition 67 (diagonal subalgebra closure)  [§6.1 · Phase 4, Fragment 4.1]

All projection/gating instructions are diagonal multipliers; hence they form a **commutative** subalgebra:
[
M_{g_1}\circ M_{g_2}=M_{g_1 g_2},\qquad M_{g_1}M_{g_2}=M_{g_2}M_{g_1}.
]
In particular, CRTCompose and sieve refinement live entirely inside this diagonal commutative algebra.

### Proposition 68 (Dirichlet core closure)  [§6.2 · Phase 4, Fragment 4.1]

Dirichlet transforms form a subalgebra:
[
T_a\circ T_b=T_{a*_N b}.
]
In particular, (\mathrm{DivisorSum}) and (\mathrm{MobiusUnmix}) are mutual inverses inside this subalgebra.

### Proposition 69 (spectral interaction law with multiplicative probes)  [§6.3 · Phase 4, Fragment 4.1]

For any Dirichlet character (\chi) mod (q) (extended by 0 off units) and any kernel (a),
[
M_\chi, T_a ;=; T_{a\cdot \chi}, M_\chi,
\qquad (a\cdot\chi)(d):=a(d)\chi(d).
]
Consequently, using the character expansion of (\mathrm{Proj}*{q,a}),
[
\mathrm{Proj}*{q,a}, T_b
=\frac{1}{\varphi(q)}\sum_{\chi\in\mathcal X(q)} \overline{\chi(a)}, T_{b\cdot \chi}, M_\chi.
]
So “project then transform” decomposes into a sum of “twisted transforms,” i.e. a clean spectral normal form.

*Proof.* The covariance identity is the multiplicativity calculation; the second line substitutes the projector expansion. ∎

---

# Acceptance check for Fragment 4.1

You can now point to a minimal operator-level runtime core:

* **Gates (rhythms):** (\mathrm{Proj}_{q,a}), (\mathrm{SquarefreeProject}), (\mathrm{SieveFilter}) are all (M_g) for explicit arithmetic predicates (g(n)).
* **Compilation/composition:** (T_a) is the compiled program operator; composition is Dirichlet convolution; inversion is (\mathrm{MobiusUnmix}).
* **Constraint merge:** (\mathrm{CRTCompose}) is projector multiplication with a CRT collapse law.

This is already a closed, computable instruction set with provable algebraic identities.

---

## Next: Fragment 4.2 (Memory + State as Filtration)

We’ll formalize “block memory per radix cylinder” and prove locality bounds like:

* diagonal predicates (g(n)) with modulus (q\mid B_L) act on only length-(L) cylinders (prefix-local),
* sieve filters with (q)-local constraints touch finitely many cylinder blocks,
* and we’ll state an explicit memory layout: a filtration-indexed store ({x_s}_{s\in\Sigma_L}) updated by these instructions.

## Phase 4 — Computation Primitives from ANT, Fragment 4.2

### Memory + State as Filtration: block memory on radix cylinders, induced operators, and locality guarantees

We fix a finite horizon (k\ge 0). Let the mixed-radix time space be
[
\mathcal R^{(k)}=\prod_{i=0}^{k} D_i,\qquad D_i={0,1,\dots,b_i-1},\qquad N:=|\mathcal R^{(k)}|=B_{k+1}.
]
Let (H_k(V):={F:\mathcal R^{(k)}\to V}) for a vector space (or Banach space) (V).
Let (\mathcal F_{k,L}) be the sigma-algebra generated by length-(L) cylinders (prefixes of length (L)).

This fragment formalizes:

1. **A memory model:** store state per cylinder (block memory) at a chosen depth (L).
2. **Induced operators on block memory:** when an operator is measurable at depth (L), it acts *purely on blocks* (no need to touch finer cells).
3. **Locality:** phase constraints (residue/CRT/sieve gates) touch only the blocks they select.

---

# 1. Cylinder index sets and block memory

## 1.1 Prefix index sets

For each (L\in{0,1,\dots,k+1}), define the prefix set
[
\Sigma_L := \prod_{i=0}^{L-1} D_i,
]
with the convention (\Sigma_0={\varnothing}). Note (|\Sigma_L|=B_L).

For (s=(d_0,\dots,d_{L-1})\in \Sigma_L), define the length-(L) cylinder
[
C(s)\ :=\ {\tau\in\mathcal R^{(k)} : \tau_{0:L}=s}.
]
The family ({C(s):s\in\Sigma_L}) partitions (\mathcal R^{(k)}).

## 1.2 Block memory at depth (L)

**Block memory** at depth (L) is just a function
[
x_L:\Sigma_L\to V.
]
Think: one value per cylinder (C(s)).

We need “lift” (inflate a block state to a full function constant on cylinders) and “restrict” (summarize a full function down to blocks).

### Definition 53 (lift to cylinder-constant functions)  [§1.1 · Phase 4, Fragment 4.2]

Define (U_L: H_L(V)\to H_k(V)) by
[
(U_L x_L)(\tau)\ :=\ x_L(\tau_{0:L}).
]
So (U_L x_L) is constant on each cylinder (C(s)).

### Definition 54 (restriction as conditional expectation / block average)  [§1.2 · Phase 4, Fragment 4.2]

Fix the uniform measure on (\mathcal R^{(k)}). Define (P_L:H_k(V)\to H_k(V)) to be the conditional expectation onto (\mathcal F_{k,L}) (i.e. averaging over suffix digits (d_L,\dots,d_k)). Concretely, for (F\in H_k(V)),
[
(P_L F)(\tau)\ :=\ \frac{1}{|C(\tau_{0:L})|}\sum_{\sigma\in C(\tau_{0:L})} F(\sigma).
]
This depends only on (\tau_{0:L}), hence is cylinder-constant.

Define the *block restriction* (R_L:H_k(V)\to H_L(V)) by picking the cylinder value:
[
(R_L F)(s)\ :=\ (P_L F)(\tau)\quad \text{for any }\tau\in C(s).
]
Well-defined because (P_LF) is constant on (C(s)).

### Proposition 70 (lift/restrict coherence)  [§1.3 · Phase 4, Fragment 4.2]

For all (x_L\in H_L(V)),
[
R_L(U_L x_L)=x_L.
]
For all (F\in H_k(V)),
[
U_L(R_L F)=P_L F.
]

**Proof.** Immediate from definitions: (U_L x_L) is already cylinder-constant, so its conditional expectation at depth (L) is itself; conversely, (P_LF) is cylinder-constant and equals the lift of its cylinder values. ∎

So: **“block memory” is exactly the (\mathcal F_{k,L})-measurable part of a state.**

---

# 2. Hierarchical memory as a filtration-indexed store

Often you want memory at **all** levels, coherently.

### Definition 55 (coherent hierarchical memory)  [§2.1 · Phase 4, Fragment 4.2]

A hierarchical memory is a family ({x_L}*{L=0}^{k+1}) with (x_L:\Sigma_L\to V) such that for each (L<k+1),
[
x_L \ =\ \mathsf{Coarsen}*{L+1\to L}(x_{L+1}),
]
where (\mathsf{Coarsen}) averages children back to the parent:
[
(\mathsf{Coarsen}*{L+1\to L}x*{L+1})(s)\ :=\ \frac{1}{b_L}\sum_{d\in D_L} x_{L+1}(s\mathbin{|}d).
]

### Proposition 71 (equivalence with a single fine state)  [§2.2 · Phase 4, Fragment 4.2]

Given any fine state (F\in H_k(V)), the family (x_L:=R_LF) is coherent.
Conversely, if you also store all Haar “detail” coefficients (Phase 2 Fragment 4 basis), coherence + details reconstruct (F) uniquely.

**Proof.** Coherence is just the tower property of conditional expectations: (P_LP_{L+1}=P_L). Reconstruction with details is the orthogonal decomposition (H_k=C_0\oplus D_0\oplus\cdots\oplus D_k). ∎

**Runtime interpretation:** you can choose *how much* of the tower to store (coarse only, or coarse + selected details) depending on which operators you want to run locally.

---

# 3. Local operators: those measurable at depth (L) act purely on block memory

The key fact is: if an operator respects the (\mathcal F_{k,L}) subspace, then you can update (x_L) without touching finer cells.

## 3.1 Cylinder-measurable gates

Let (g:\mathcal R^{(k)}\to\mathbb C). Define the multiplier (M_g) by
[
(M_g F)(\tau)=g(\tau)F(\tau).
]

### Proposition 72 (depth-(L) gates preserve depth-(L) memory)  [§3.1 · Phase 4, Fragment 4.2]

If (g) is (\mathcal F_{k,L})-measurable (constant on cylinders of length (L)), then

1. (M_g) maps (\mathcal F_{k,L})-measurable functions to (\mathcal F_{k,L})-measurable functions,
2. (M_g) commutes with (P_L):
   [
   P_L M_g = M_g P_L.
   ]

**Proof.**

1. If (F) is constant on each cylinder (C(s)), and (g) is also constant on each cylinder, then their product is constant on each cylinder.
2. On any cylinder (C(s)), (g) is constant with value (g(s)), so averaging (gF) over the cylinder equals (g(s)) times the average of (F) over the cylinder. ∎

### Corollary 20 (induced block operator)  [§3.2 · Phase 4, Fragment 4.2]

If (g\in\mathcal F_{k,L}), define (\bar g:\Sigma_L\to\mathbb C) by (\bar g(s):=g(\tau)) for (\tau\in C(s)). Then the induced operator on block memory is simply
[
(M_g)^{[L]}: H_L(V)\to H_L(V),\qquad ((M_g)^{[L]}x_L)(s)=\bar g(s),x_L(s).
]
Equivalently,
[
R_L(M_g(U_L x_L)) = (M_g)^{[L]}x_L,
]
so you never need to expand to fine resolution to apply the gate.

---

## 3.2 Additive “phase constraints” become cylinder gates at finite depth

From Phase 3 Fragment 2, if a modulus (q\mid B_L), then the residue condition (\mathrm{nat}_k(\tau)\equiv a\pmod q) (and likewise (\operatorname{dec}_k(\tau)\equiv r\pmod q)) depends only on the prefix of length (L).

Thus:

* (\mathrm{Proj}_{q,a}) (residue projection on units, or additive residue classes) is a cylinder-measurable gate at depth (L) whenever (q\mid B_L).
* Dirichlet character twists (\tau\mapsto \chi(\mathrm{nat}_k(\tau))) are cylinder-measurable at depth (L) whenever (q\mid B_L).

So these ANT “phase instructions” are **block-local** updates when the modulus appears in the radix product by depth (L).

---

# 4. Depth calculus: how locality behaves under composition

Define the **cylinder depth** of a gate (g) (when it exists) by
[
\mathrm{depth}(g) := \min{L : g\in\mathcal F_{k,L}}.
]

### Proposition 73 (closure under products and linear combinations)  [§4.1 · Phase 4, Fragment 4.2]

If (g\in\mathcal F_{k,L_1}) and (h\in\mathcal F_{k,L_2}), then:

* (g+h\in \mathcal F_{k,\max(L_1,L_2)}),
* (gh\in \mathcal F_{k,\max(L_1,L_2)}),
  and therefore
  [
  M_g\circ M_h = M_{gh}
  ]
  is block-local at depth (\max(L_1,L_2)).

**Proof.** (\mathcal F_{k,L}) is nested in (L), and pointwise arithmetic preserves measurability at the finer depth. ∎

### Corollary 21 (CRTCompose is depth-max)  [§4.2 · Phase 4, Fragment 4.2]

If (q_1\mid B_{L_1}) and (q_2\mid B_{L_2}), then the CRT-composed gate
[
\mathrm{Proj}*{q_1,a_1}\mathrm{Proj}*{q_2,a_2}
]
is a gate in (\mathcal F_{k,\max(L_1,L_2)}) (and collapses to a single modulus (q_1q_2) gate when (\gcd(q_1,q_2)=1)).

---

# 5. “Touches finitely many cylinders”: locality as sparse block support

Block locality has two layers:

1. **Resolution locality:** an operation can be evaluated at depth (L) (no need for finer state).
2. **Support locality:** it only affects blocks in a subset (S\subseteq \Sigma_L).

### Definition 56 (support of a gate at depth (L))  [§5.1 · Phase 4, Fragment 4.2]

For a depth-(L) gate (g\in\mathcal F_{k,L}), define
[
S(g):={s\in\Sigma_L : \bar g(s)\neq 0}.
]

### Proposition 74 (sparse update on block memory)  [§5.2 · Phase 4, Fragment 4.2]

For any block memory (x_L),
[
((M_g)^{[L]}x_L)(s)=0\ \text{for}\ s\notin S(g),
\qquad
((M_g)^{[L]}x_L)(s)=\bar g(s)x_L(s)\ \text{for}\ s\in S(g).
]
So the update “touches” only the cylinders indexed by (S(g)).

**Proof.** Immediate from the coordinatewise form of ((M_g)^{[L]}). ∎

### Concrete corollary (residue projection sparsity)

If (q\mid B_L) and (g(\tau)=\mathbf 1_{\mathrm{nat}_k(\tau)\equiv a\ (q)}), then (S(g)) is exactly one congruence class of prefixes modulo (q), and
[
|S(g)|=\frac{B_L}{q}
]
(up to the unit restriction if you include (\gcd(\cdot,q)=1)). So a phase constraint reduces active block count by a factor (\approx q).

This is the precise statement you want: **phase constraints yield sparse active cylinders**.

---

# 6. Tick and block memory: induced odometer on prefixes

Let (\widetilde T_k:\mathcal R^{(k)}\to\mathcal R^{(k)}) be cyclic Tick (add (1) mod (N) under (\operatorname{dec}_k)). Define the pullback (\widetilde T_k^*) by ((\widetilde T_k^*F)(\tau)=F(\widetilde T_k(\tau))).

From earlier, (\widetilde T_k^*) commutes with (P_L), hence preserves cylinder-constant functions. Therefore it induces a permutation on (\Sigma_L).

### Proposition 75 (prefix odometer)  [§6.1 · Phase 4, Fragment 4.2]

There exists a permutation (T_L:\Sigma_L\to \Sigma_L) such that for all (x_L),
[
\widetilde T_k^*(U_L x_L)=U_L(x_L\circ T_L).
]
Moreover, under (\operatorname{dec}_k), (T_L) is exactly “add (1)” mod (B_L) in the mixed-radix prefix odometer.

**Proof.** Since (\widetilde T_k^*) preserves (\mathcal F_{k,L})-measurable functions, it maps cylinder-constant functions to cylinder-constant functions, i.e. permutes the partition atoms. The “add 1 mod (B_L)” identification follows by taking (\operatorname{dec}_k(\tau)\bmod B_L), which depends only on the prefix. ∎

So Tick update on block memory is just an index permutation—cheap and exact.

---

# 7. Where Dirichlet transforms fit: nonlocal in cylinders, local in valuations

A crucial honesty point for the runtime design:

* Operators like (\mathrm{Proj}_{q,a}), characters (when (q\mid B_L)), CRTCompose, sieve gates, and Tick are **cylinder-local**: they act at finite prefix depth (L), often sparsely on (S(g)).
* Dirichlet transforms (T_a) (compiled divisor programs) are generally **not** cylinder-local (they respect multiplicative/valuation structure instead).

What you do in a minimal runtime is therefore:

* use **cylinder memory** for additive phase/rhythm gating, scheduling, and prefix-local effects,
* and maintain a **multiplicative (valuation-lattice) memory** (Phase 3 Fragment 4) for executing divisor/Dirichlet dynamics locally.

This is not optional if you want both “prefix locality” and “divisor locality” without exponential blowup.

---

## Leading questions for Fragment 4.3 (Complexity Bounds)

1. Given depth (L), what is the cost of a gate/update as a function of (B_L) and sparsity (|S(g)|)? (Usually (O(|S(g)|)) for sparse gates, (O(B_L)) for full passes.)
2. For CRT merges, how does active support size shrink under independent moduli assumptions? (This is where large-sieve-style “almost independence” heuristics enter.)
3. For valuation-local Dirichlet kernels supported in an (\ell_\infty) ball of radius (R) on (\mathbb N^P), what is the per-fiber update cost as a function of (R), number of primes (|P|), and max valuation depth (\log_p N)?

## Phase 4 — Computation Primitives from ANT, Fragment 4.3

### Complexity bounds in ((q,; \text{radix depth},; \text{sparsity})) and where large-sieve “almost independence” enters

We keep the finite horizon model:

* Mixed-radix time space (\mathcal R^{(k)}) with size (N:=B_{k+1}).
* Cylinder depth (L\in{0,\dots,k+1}) with block count (B_L) and suffix size
  [
  S_L := \frac{N}{B_L}=\prod_{i=L}^{k} b_i.
  ]
* Block memory (x_L:\Sigma_L\to V), (|\Sigma_L|=B_L).

We measure cost in primitive arithmetic ops (add/mul) and comparisons, ignoring constant factors from encoding/decoding.

---

# 1. Baseline costs: applying an operator on full memory vs block memory

Let (F:\mathcal R^{(k)}\to V). A naive full-state pass is (O(N)).

### Proposition 76 (block-lift evaluation cost)  [§1.1 · Phase 4, Fragment 4.3]

If an operator (O) preserves (\mathcal F_{k,L}) (i.e. acts on cylinder-constant functions), then applying (O) to a block state (x_L) costs (O(B_L)) to update all blocks, and (O(|S|)) to update only a sparse active block set (S\subseteq\Sigma_L).

*Reason.* You operate on one representative per block; suffix multiplicity (S_L) never appears.

**Immediate runtime implication:** if you can express constraints/instructions at depth (L), you get a factor-(S_L) savings versus operating at depth (k+1).

---

# 2. Complexity of gate instructions

All of these are diagonal operators (M_g), so the dominant cost is: (i) **compute which blocks are active** and (ii) **multiply/zero out**.

## 2.1 Residue projection (\mathrm{Proj}_{q,a})

Assume we are in the cylinder-local regime: (q\mid B_L). Then the residue class of (\mathrm{nat}*k(\tau)\bmod q) is determined by the prefix (s\in\Sigma_L). Therefore (\mathrm{Proj}*{q,a}) induces a gate on (\Sigma_L).

### Proposition 77 (active block count)  [§2.1 · Phase 4, Fragment 4.3]

Ignoring the unit restriction for the moment, the fraction of prefixes satisfying a fixed residue mod (q) is exactly (1/q). Hence
[
|S(\mathrm{Proj}_{q,a})| = \frac{B_L}{q}.
]
With the unit restriction (\gcd(\cdot,q)=1), the active fraction becomes (\frac{1}{q}\cdot \frac{\varphi(q)}{q}) **if** residues are uniformly distributed among units (exact when you project only on units within a complete residue system; approximately true for many sieve regimes).

### Cost bound

* Updating all blocks: (O(B_L)).
* Updating only active blocks once you have their indices: (O(B_L/q)).

**Index enumeration:** because (q\mid B_L), the active blocks form an arithmetic progression in (\operatorname{dec})-space mod (q); you can enumerate active block indices in (O(B_L/q)) time without scanning all (B_L) blocks.

---

## 2.2 CRTCompose

For coprime moduli (q_1,q_2\mid B_L), CRTCompose collapses:
[
\mathrm{Proj}*{q_1,a_1}\mathrm{Proj}*{q_2,a_2}=\mathrm{Proj}_{q_1q_2,a}.
]

### Cost bound

* If you implement as collapse: update cost (O(B_L/(q_1q_2))).
* If you implement as sequential gates without collapse: (O(B_L/q_1 + B_L/q_2)) (worse).

So CRT is not just algebraic cleanliness; it is an **asymptotic improvement** in sparse-update cost.

---

## 2.3 SieveFilter

A sieve gate is of the form
[
g(n)=\prod_{p\in P}\mathbf 1_{n\bmod p \notin A_p}
\quad\text{or prime-power variants.}
]
Assume each modulus divides (B_L) so the sieve is cylinder-local at depth (L).

### Deterministic cost

If you scan all blocks and test all constraints: (O(B_L\cdot |P|)).

### Sparse progressive cost (incremental refinement)

If you refine the sieve one modulus at a time and maintain the active set (S\subseteq\Sigma_L), then adding a new constraint of modulus (m) costs (O(|S|)) membership tests (or (O(|S|/m)) if you maintain residue-bucket indices).

So:
[
\text{incremental sieve update} ;\approx; O\big(|S|\big)
\quad\text{per added modulus.}
]

---

## 2.4 SquarefreeProject

SquarefreeProject on ({1,\dots,N}) is
[
\mu^2(n)=\prod_{p^2\le N}(1-\mathbf 1_{p^2\mid n}).
]

### Two evaluation modes

1. **Global sieve over integers (1..N):** classic square-sieve costs
   [
   O!\left(N\sum_{p\le \sqrt N}\frac{1}{p^2}\right)=O(N)
   ]
   (since (\sum 1/p^2) converges). Practical implementations are (O(N)) with small constants.
2. **Cylinder-local gate at depth (L):** only possible if every (p^2) up to (\sqrt N) divides (B_L) (rare unless bases are extremely composite). If it holds, cost reduces to (O(B_L)) or sparse (O(|S|)).

**Takeaway:** SquarefreeProject is cheap globally, but not usually prefix-local; it lives more naturally on the integer line or valuation-memory.

---

# 3. Complexity of Dirichlet transforms and Möbius inversion

A compiled program operator is
[
(T_a f)(n)=\sum_{d\mid n} a(d) f(n/d).
]

## 3.1 Naive divisor enumeration cost

Let (\tau(n)) be the divisor-counting function. Computing (T_a f) for all (n\le N) by enumerating divisors costs
[
\sum_{n\le N} O(\tau(n)).
]
A standard average-order fact is:
[
\sum_{n\le N}\tau(n) = N\log N + (2\gamma-1)N + O(\sqrt N).
]
So:
[
\boxed{\text{Full evaluation of }T_a\text{ over }1..N\text{ costs }O(N\log N).}
]

This applies in particular to:

* (\mathrm{DivisorSum}=T_{\mathbf 1}),
* (\mathrm{MobiusUnmix}=T_\mu).

## 3.2 Fast “multiples” form (sieve-like transform)

Rewrite:
[
(T_a f)(n)=\sum_{d\mid n} a(d) f(n/d)
=\sum_{d\le n} a(d),\mathbf 1_{d\mid n},f(n/d).
]
Compute by iterating (d) and updating multiples:

* For each (d\le N), iterate over (m\le N/d), update (n=dm).

This costs:
[
\sum_{d\le N} O(N/d)=O(N\log N).
]
Same asymptotic, usually better constants and cache behavior.

---

# 4. Valuation-local complexity for (P)-smooth kernels (the scalable path)

Assume (a) is (P)-smooth (supported on (S_P={\prod_{p\in P}p^{e_p}})) and has bounded valuation radius:
[
\mathrm{supp}(\widetilde a)\subseteq {r\in\mathbb N^{P}:|r|_\infty\le R}.
]
On each fiber (u) (the (P)-free part), the update is a multivariate convolution:
[
(T_a f)*u(e)=\sum*{0\le r\le e}\widetilde a(r) f_u(e-r).
]

### Proposition 78 (per-fiber update cost)  [§4.1 · Phase 4, Fragment 4.3]

If you store (f_u(e)) only for (e) in some active set (E_u\subseteq\mathbb N^{P}), and (\widetilde a) has support size (|\mathrm{supp}(\widetilde a)|), then computing ((T_a f)_u) on (E_u) costs
[
O\big(|E_u|\cdot |\mathrm{supp}(\widetilde a)|\big).
]
In the radius-(R) regime,
[
|\mathrm{supp}(\widetilde a)| \le (R+1)^{|P|}.
]

### Corollary 22 (global valuation-local cost)  [§4.2 · Phase 4, Fragment 4.3]

Let (\mathcal U) be the set of (P)-free labels (u\le N). Total cost is
[
O!\left(\sum_{u\in\mathcal U} |E_u|\cdot (R+1)^{|P|}\right).
]

**Scaling meaning:** you pay exponentially in (|P|) (number of tracked primes), but only polynomially in the valuation radius (R). This is exactly where you choose a small (P) (or factorize further) to scale.

---

# 5. Where “large sieve” enters: almost-independence of constraints

When you impose many modular constraints (a sieve), the naive model assumes independence:
[
\text{active fraction} \approx \prod_{p\in P}\left(1-\frac{|A_p|}{p}\right)
]
(or prime-power analogues).

This is not always exact; “large sieve” results bound how far reality can deviate from uniformity.

## 5.1 A usable inequality (stated as a tool)

Let (X) be a finite set of integers (or block indices) of size (M). For moduli up to (Q), the (classical) large sieve inequality controls discrepancy of residue counts from uniformity roughly in the form:
[
\sum_{q\le Q}\ \sum_{\substack{a\ (\mathrm{mod}\ q)\(a,q)=1}}
\left|#{n\in X:n\equiv a\ (q)} - \frac{M}{\varphi(q)}\right|^2
\ \le\ (M+Q^2),M.
]
(Exact formulations vary; the key term is the ((M+Q^2)) barrier.)

## 5.2 Consequence for prefix-block sieves

Take (X) to be the set of block indices at depth (L), so (M=B_L), and consider enforcing constraints with moduli (\le Q) where (Q^2\ll B_L).

Then the inequality implies that **on average over moduli up to (Q)**, residue classes behave close to uniform; hence treating different small moduli as “almost independent” is justified at depth (L).

### Practical corollary (rule of thumb)

If you want independence-like shrinkage of active cylinder blocks under many modular constraints, keep the effective modulus scale (Q) below about (B_L^{1/2}). In that regime, support size behaves close to:
[
|S|\approx B_L \cdot \prod_{p\in P}\left(1-\frac{|A_p|}{p}\right).
]
Outside that regime, correlations can dominate and you should expect worse-than-predicted sparsity.

---

# 6. Minimal runtime model + complexity summary

A minimal ANT-derived runtime that matches the earlier fragments has **two coupled memories**:

### (A) Additive / cylinder memory at depth (L)

* Storage: (O(B_L)).
* Supported ops cheaply:

  * Tick: permutation, (O(1)) per step or (O(B_L)) batch.
  * Proj / CRTCompose / SieveFilter (when moduli (\mid B_L)): sparse (O(B_L/q)) and merges (O(B_L/\prod q_i)).
* Use large-sieve regime (Q^2\ll B_L) to justify multiplicative sparsity assumptions when stacking many constraints.

### (B) Multiplicative / valuation-lattice memory (per (u)-fiber)

* Storage: (\sum_{u}|E_u|).
* Supported ops cheaply:

  * (P)-smooth Dirichlet transforms with bounded radius (R): cost (O\left(\sum_u |E_u|(R+1)^{|P|}\right)).

### Bridging mechanism

* Use additive gates (residues/sieves) to select which time blocks or (u)-fibers are active.
* Apply valuation-local updates only on active fibers / lattice points.

---

## Acceptance check for Fragment 4.3

You now have explicit asymptotic costs in:

* **radix depth:** via (B_L) and suffix factor (S_L=N/B_L),
* **modulus size:** via sparse support (B_L/q) and CRT collapse (B_L/\prod q_i),
* **kernel sparsity:** via (|\mathrm{supp}(\widetilde a)|\le (R+1)^{|P|}),
* plus a precise condition where **large-sieve bounds justify treating many constraints as “almost independent”**: (Q^2\ll B_L).

---

### Next step inside Phase 4 (if we continue): “runtime algebra” assembly

We can now formally define the runtime as an operator algebra generated by:

* cylinder-local diagonal gates (Proj/CRT/Sieve/Squarefree when possible),
* Tick permutations,
* valuation-local Dirichlet transforms,
  and prove the full closure and locality properties of this combined system (a semidirect product-style construction).

## Phase 4 — Computation Primitives from ANT, Fragment 4.4

### Minimal runtime model: the generated operator algebra, guarded execution, and a Markov/locality theorem

We continue on the finite horizon (k\ge 0) with (N=B_{k+1}). Memory is either:

* **time-line memory** (f:{1,\dots,N}\to V), or
* **mixed-radix memory** (F:\mathcal R^{(k)}\to V) with (F(\tau)=f(\mathrm{nat}_k(\tau))).

We will assemble the primitives from Fragments 4.1–4.3 into a **minimal runtime** and prove its closure + locality properties.

---

# 1. The runtime algebra (\mathfrak R_N)

Let (\mathrm{End}(\mathsf{Mem}_N(V))) be the algebra of linear operators on (\mathsf{Mem}_N(V)).

## 1.1 Generators

Define three generator families:

### Gate 3 (Diagonal gates (constraints / phase))  [§G1 · Phase 4, Fragment 4.4]

For any predicate/weight (g:{1,\dots,N}\to\mathbb C), define
[
M_g:\ f\mapsto (n\mapsto g(n)f(n)).
]
Special cases include:

* (\mathrm{Proj}*{q,a}=M*{g_{q,a}}) (unit residue projector),
* (\mathrm{SquarefreeProject}=M_{\mu^2}),
* (\mathrm{SieveFilter}=M_{g_{\text{sieve}}}),
* divisibility/valuation gates (M_{\mathbf 1_{p^e\mid \cdot}}).

### Gate 4 (Dirichlet transforms (compiled programs))  [§G2 · Phase 4, Fragment 4.4]

For any kernel (a:{1,\dots,N}\to\mathbb C),
[
T_a:\ f\mapsto \Big(n\mapsto \sum_{d\mid n} a(d),f(n/d)\Big).
]
Special cases include:

* (\mathrm{DivisorSum}=T_{\mathbf 1}),
* (\mathrm{MobiusUnmix}=T_\mu),
* basis programs (\llbracket m\rrbracket = T_{\delta_m}).

### (G3) Time shift / Tick (scheduler primitive)

Let (\mathsf{Shift}) be the cyclic shift on ({1,\dots,N}) (for runtime closure); define:
[
(\mathsf{S}f)(n):=f(n-1 \bmod N),
]
with the convention that indices are taken in (\mathbb Z/N\mathbb Z) and then mapped back to ({1,\dots,N}).

(Equivalently, on mixed-radix, this is the cyclic Tick pullback (\widetilde T_k^*).)

---

## 1.2 Definition (runtime algebra)

Let (\mathfrak R_N\subseteq \mathrm{End}(\mathsf{Mem}_N(V))) be the smallest subalgebra containing all (M_g), all (T_a), and (\mathsf S).

So (\mathfrak R_N) is closed under addition, scalar multiplication, and composition.

---

# 2. Structural laws: normalization and semidirect-product behavior

## 2.1 Diagonal gates form a commutative subalgebra

For any (g,h):
[
M_g M_h = M_{gh} = M_h M_g.
]
If (g) is ({0,1})-valued then (M_g) is a projection: (M_g^2=M_g).

## 2.2 Dirichlet transforms form a convolution subalgebra

For kernels (a,b):
[
T_a T_b = T_{a*_N b},
\qquad
(a**N b)(n)=\sum*{d\mid n} a(d)b(n/d).
]
In particular (T_\mu) and (T_{\mathbf 1}) are mutual inverses.

## 2.3 Shift normalizes diagonal gates

[
\mathsf S, M_g, \mathsf S^{-1} = M_{g\circ \mathsf s^{-1}},
]
where (\mathsf s) is the index permutation (n\mapsto n+1\ (\bmod N)).

**Proof.** Direct computation: ((\mathsf S M_g \mathsf S^{-1}f)(n)=g(n-1)f(n)). ∎

So (\langle \mathsf S\rangle) acts by automorphisms on the diagonal-gate algebra. This is the first clear “scheduler interacts with constraints” law.

## 2.4 Characters normalize Dirichlet transforms (spectral law)

For any Dirichlet character (\chi) (extended by 0 off units):
[
M_\chi, T_a = T_{a\cdot \chi}, M_\chi,
\qquad (a\cdot \chi)(d):=a(d)\chi(d).
]
This is the second normalization law (probe ↔ compiled update).

---

# 3. Guarded execution: the canonical runtime instruction form

A single “guarded instruction” is the composition
[
\boxed{;\mathsf{Instr}(g,a)\ :=\ M_g, T_a;}
]
interpreted as:

1. select admissible times/states via (g) (phase / sieve / residue / valuation gate),
2. apply compiled divisor update (T_a) on those.

This is the minimal form that matches your operator inventory.

### Proposition 79 (closure of guarded instructions)  [§3.1 · Phase 4, Fragment 4.4]

For any (g_1,a_1,g_2,a_2), the product is again in (\mathfrak R_N):
[
\mathsf{Instr}(g_1,a_1),\mathsf{Instr}(g_2,a_2)=M_{g_1},T_{a_1},M_{g_2},T_{a_2}\in \mathfrak R_N.
]
No simplification is claimed in general (because (T_{a_1}) and (M_{g_2}) need not commute), but it is a legal compiled runtime program.

---

# 4. Filtration-local implementation theorem

Now we connect to cylinder memory (Fragment 4.2) and valuation memory (Phase 3 Fragment 4) to prove a *local execution guarantee*.

## 4.1 Cylinder locality of gates

Fix a cylinder depth (L). Suppose (g) is (\mathcal F_{k,L})-measurable when pulled back to (\mathcal R^{(k)}) (equivalently: (g(n)) depends only on (n\bmod B_L), up to the (+1) shift).

Then (M_g) acts on block memory (x_L:\Sigma_L\to V) without refinement:

* cost (O(|S(g)|)) if you update only active blocks,
* cost (O(B_L)) if you scan all blocks.

(We already proved the operator identities (P_LM_g=M_gP_L) and the induced block action.)

## 4.2 Valuation locality of (P)-smooth compiled transforms

Fix a finite prime set (P). Suppose (a) is (P)-smooth and bounded-radius in valuation coordinates:
[
\mathrm{supp}(\widetilde a)\subseteq {r\in\mathbb N^{P}:|r|_\infty\le R}.
]
Then, on the factorization lens state (\Lambda_P(n)=(u_P(n),v_P(n))), (T_a) acts **fiberwise** and only within an (R)-neighborhood in (\mathbb N^{P}) (Phase 3 Fragment 4 / Phase 4 Fragment 4.3).

---

## 4.3 Theorem (locality of one guarded step)

Let (g) be cylinder-local at depth (L), and (a) be (P)-smooth with valuation radius (R). Consider (\mathsf{Instr}(g,a)=M_gT_a).

There exists an implementation of (\mathsf{Instr}(g,a)) that:

1. touches only the active prefix blocks (S(g)\subseteq \Sigma_L) for the gating part, and
2. for the compiled update part, touches only valuation states ((u,e)) that correspond to times (n) lying in the active set selected by (g), and only within (R)-neighbors in each fiber.

Moreover, the total work admits the bound
[
O\Big(|S(g)|;+;\sum_{u\in\mathcal U_{\text{active}}} |E_u|,(R+1)^{|P|}\Big),
]
where (E_u) is the active valuation index set for fiber (u) and (\mathcal U_{\text{active}}) are fibers hit by the gate.

**Proof sketch (formal enough to cite):**

* Cylinder locality gives a block-indexed active set (S(g)) and an induced gate on blocks (Fragment 4.2).
* On the integer line, (g) selects a subset of indices (A\subseteq{1,\dots,N}). (This is computable from the block indices because (q\mid B_L) style conditions make (A) periodic/prefix-decided.)
* For (P)-smooth (a), (T_a) decomposes over fibers (u) and valuation-lattice convolution, and each output (e) depends only on (e-r) with (|r|_\infty\le R). This yields the stated neighborhood bound. ∎

This theorem is the “runtime locality contract” you asked for in Acceptance Checks: the ops are not just abstract—they have a bounded-touch implementation grounded in the filtration + valuation decomposition.

---

# 5. Markov statement (the correct augmented state)

Define an augmented runtime state representation:
[
\boxed{;\mathsf{State} ;=; \Big(\text{prefix }s\in\Sigma_L\Big)\ \times\ \Big(\text{factorization lens registers }(u,e)\Big)\ \times\ \Big(\text{stored values}\Big);}
]

* The prefix (s) evolves by the prefix odometer (T_L) (induced by Tick).
* The factorization register ((u,e)=\Lambda_P(n)) evolves deterministically with (n) (or is recomputed from (n) if you treat it as derived).
* Each instruction (\mathsf{Instr}(g,a)) reads only:

  * the prefix class needed to evaluate (g) at depth (L),
  * and the bounded valuation neighborhood needed to apply (T_a) in the active fibers.

### Corollary 23 (Markov locality)  [§5.1 · Phase 4, Fragment 4.4]

If you treat ((s,(u,e))) and the stored block/valuation memories as the state, then one runtime step depends only on the current state (not on earlier history). Moreover, the dependency neighborhood is finite and parameterized by ((L,R,|P|)).

This is exactly your “Markovian when state is augmented with phase” constraint, now in explicit operator form.

---

## Leading questions for the *next* fragment (transition into Phase 5 cleanly)

1. **Where do variable radices enter this runtime?** They enter by letting the prefix index set (\Sigma_L) and odometer (T_L) become state-dependent—i.e. the partition atoms themselves evolve.
2. **What must be preserved for closure/locality?** You’ll want conditions ensuring: (i) no infinite carry (well-foundedness), (ii) a well-defined induced filtration at each step, and (iii) compatibility of “modulus appears by depth” with evolving (B_L).
3. **Which operators survive unchanged?** Dirichlet/valuation operators live on integer factorization and do not care about the radix chart, but the cylinder-local gate realizations do—this is the hinge that Phase 5 must formalize.

If you want, I’ll now start **Phase 5 — Function-Defined Radices, Fragment 5.1** immediately, using this runtime hinge as the formal motivation.

## Phase 5 — Function-Defined Radices, Fragment 5.1

### Variable-radix odometers as prefix-dependent trees, Tick with variable carry, and computability / no-infinite-carry conditions

We now generalize from fixed bases ((b_i)) to **function-defined / context-dependent radices** while preserving:

* a **discrete hierarchical time** model,
* a **well-founded evaluation index** (ticks are countable and stepwise),
* **composability hooks** for later DP / STOK-style recursion (next fragment).

The correct formal object is: **a rooted tree whose branching factor depends on the prefix**.

---

# 1. Contexted variable-radix spaces as rooted trees

Let (\Omega) be a (computable) context space: this can include “state,” “kernel,” “environment,” etc. For each (\omega\in\Omega), we define a variable-radix digit system.

### Definition 57 (branching function / radix law)  [§1.1 · Phase 5, Fragment 5.1]

A **radix law** is a function
[
b_\omega:\Sigma^\ast\to {2,3,4,\dots},
]
where (\Sigma^\ast) denotes the set of all finite digit words (prefixes). For a prefix (s\in\Sigma^\ast), define the allowed next-digit set
[
D_\omega(s):={0,1,\dots,b_\omega(s)-1}.
]

Interpretation: at prefix (s), the next digit ranges over (D_\omega(s)). This is exactly a rooted tree (T_\omega) whose node (s) has (b_\omega(s)) children.

---

## 1.1 Finite depth space

Fix depth (k\ge 0). Define the **finite variable-radix space**:
[
\mathcal R^{(k)}*\omega
:=
\Big{\tau=(d_0,\dots,d_k)\ :\ d_i\in D*\omega(\tau_{<i})\ \forall i\Big},
]
where (\tau_{<i}:=(d_0,\dots,d_{i-1})) is the length-(i) prefix (with (\tau_{<0}=\varnothing)).

So (\mathcal R^{(k)}*\omega) is the set of root-to-level-(k) paths in (T*\omega).

## 1.2 Infinite depth space (direct-limit object)

Define the **infinite variable-radix space**:
[
\mathcal R^{(\infty)}*\omega
:=
\Big{\tau=(d_0,d_1,\dots)\ :\ d_i\in D*\omega(\tau_{<i})\ \forall i\Big}.
]

This is the boundary/path space of the rooted tree (T_\omega).

---

# 2. Ultrametric topology and cylinders (prefix neighborhoods still work)

All topology is driven by “agreement of prefixes,” independent of whether bases vary.

### Definition 58 (cylinder sets)  [§2.1 · Phase 5, Fragment 5.1]

For any finite prefix (s\in\Sigma^\ast), define the cylinder
[
C_\omega(s):={\tau\in \mathcal R^{(\infty)}*\omega:\ \tau*{<|s|}=s}.
]
(And similarly in (\mathcal R^{(k)}_\omega) when (|s|\le k+1).)

These are the prefix neighborhoods.

### Definition 59 (prefix metric)  [§2.2 · Phase 5, Fragment 5.1]

For (\tau\neq\sigma), let (\ell(\tau,\sigma)) be the length of the longest common prefix:
[
\ell(\tau,\sigma):=\max{m\ge 0:\ \tau_{<m}=\sigma_{<m}}.
]
Fix any (\rho\in(0,1)) (e.g. (\rho=\tfrac12)). Define
[
d(\tau,\sigma):=\rho^{\ell(\tau,\sigma)},\qquad d(\tau,\tau):=0.
]

### Proposition 80 (ultrametric)  [§2.3 · Phase 5, Fragment 5.1]

(d) is an ultrametric on (\mathcal R^{(\infty)}_\omega): for all (\tau,\sigma,\eta),
[
d(\tau,\eta)\le \max{d(\tau,\sigma),d(\sigma,\eta)}.
]

**Proof.** Longest-common-prefix lengths satisfy
[
\ell(\tau,\eta)\ \ge\ \min{\ell(\tau,\sigma),\ell(\sigma,\eta)}.
]
Exponentiating by (\rho^{(\cdot)}) yields the ultrametric inequality. ∎

### Corollary 24 (cylinders are clopen and form a basis)  [§2.4 · Phase 5, Fragment 5.1]

Each (C_\omega(s)) is both open and closed in the metric topology, and the cylinders ({C_\omega(s)}) form a basis.

**Proof.** In an ultrametric, balls are clopen. Here (C_\omega(s)) is exactly the ball of radius (\rho^{|s|}) around any (\tau\in C_\omega(s)). ∎

So the **same ultrametric/cylinder machinery survives** the move to function-defined radices.

---

# 3. Lexicographic order and encoding via subtree sizes

To define Tick rigorously we need a canonical “next” element. Use lexicographic order.

### Definition 60 (lex order)  [§3.1 · Phase 5, Fragment 5.1]

For (\tau,\sigma\in \mathcal R^{(k)}*\omega), define (\tau<*{\mathrm{lex}}\sigma) if at the first index (i) where they differ, (\tau_i<\sigma_i).

This is a total order on (\mathcal R^{(k)}_\omega).

## 3.1 Subtree size recursion

### Definition 61 (completion counts)  [§3.2 · Phase 5, Fragment 5.1]

For any prefix (s) of length (|s|\le k+1), define the number of completions to depth (k):
[
W^{(k)}*\omega(s):=
#{\tau\in\mathcal R^{(k)}*\omega:\ \tau_{<|s|}=s}.
]
Equivalently:

* if (|s|=k+1), then (W^{(k)}_\omega(s)=1),
* if (|s|\le k), then the recursion holds:
  [
  W^{(k)}*\omega(s)=\sum*{d\in D_\omega(s)} W^{(k)}_\omega(s|d).
  ]

### Definition 62 (variable-base rank / decoding)  [§3.3 · Phase 5, Fragment 5.1]

For (\tau=(d_0,\dots,d_k)\in\mathcal R^{(k)}*\omega), define
[
\operatorname{dec}^{(k)}*\omega(\tau)
:=\sum_{i=0}^{k}\ \sum_{d=0}^{d_i-1} W^{(k)}*\omega(\tau*{<i}|d).
]
(Empty sum is 0 when (d_i=0).)

### Theorem 30 (order-isomorphism to an integer interval)  [§3.4 · Phase 5, Fragment 5.1]

Let (M:=W^{(k)}*\omega(\varnothing)=|\mathcal R^{(k)}*\omega|). Then
[
\operatorname{dec}^{(k)}*\omega:\ (\mathcal R^{(k)}*\omega,<_{\mathrm{lex}})\ \longrightarrow\ ({0,1,\dots,M-1},<)
]
is a bijective order-isomorphism.

**Proof (sketch, standard tree ranking).**
Induct on depth. At the root, the space partitions into child-subtrees indexed by (d\in D_\omega(\varnothing)), each with size (W^{(k)}_\omega(d)). The rank adds full subtree sizes for smaller leading digits, then recurses into the chosen subtree. This produces a unique integer in ([0,M-1]) and respects lex order by construction. ∎

**Fixed-base case recovered:** if (b_\omega(s)\equiv b_i) depends only on level (i=|s|), then (W^{(k)}*\omega(\tau*{<i}|d)=\prod_{j=i+1}^k b_j) and this collapses to the usual mixed-radix decoding.

---

# 4. Tick with variable carry (finite depth)

Tick is the successor map in lex order (with optional wrap-around).

### Definition 63 (finite-depth Tick, partial form)  [§4.1 · Phase 5, Fragment 5.1]

Define (\mathrm{Tick}^{(k)}*\omega:\mathcal R^{(k)}*\omega \rightharpoonup \mathcal R^{(k)}*\omega) as:
[
\mathrm{Tick}^{(k)}*\omega(\tau)=\text{the }<*{\mathrm{lex}}\text{-successor of }\tau,
]
undefined only on the maximal element (\tau*{\max}) (the word with each digit maximal given its prefix).

### Definition 64 (finite-depth cyclic Tick)  [§4.2 · Phase 5, Fragment 5.1]

Define the total cyclic Tick (\widetilde{\mathrm{Tick}}^{(k)}*\omega) by
[
\widetilde{\mathrm{Tick}}^{(k)}*\omega(\tau)=
\begin{cases}
\mathrm{Tick}^{(k)}*\omega(\tau),& \tau\neq\tau*{\max},\
\tau_{\min},& \tau=\tau_{\max},
\end{cases}
]
where (\tau_{\min}) is the all-zeros path (always admissible).

## 4.1 Carry algorithm (computational definition)

The successor has an explicit carry procedure:

Given (\tau=(d_0,\dots,d_k)), find the largest index (i) (closest to the right end) such that
[
d_i < b_\omega(\tau_{<i})-1,
]
and for all (j>i), (d_j = b_\omega(\tau_{<j})-1) (they are at their local maxima).
Then define (\tau'=\mathrm{Tick}^{(k)}_\omega(\tau)) by:

* (\tau'*{<i}=\tau*{<i}) (more significant prefix unchanged),
* (d_i' = d_i + 1),
* for (j>i), set (d_j'=0) (reset less significant suffix to minimal digits).

This is well-defined because the base for position (j) depends only on (\tau'_{<j}) (a prefix), which is determined once earlier digits are set.

### Theorem 31 (Tick equals +1 in rank coordinates)  [§4.3 · Phase 5, Fragment 5.1]

Let (M=|\mathcal R^{(k)}*\omega|). For cyclic Tick,
[
\operatorname{dec}^{(k)}*\omega!\big(\widetilde{\mathrm{Tick}}^{(k)}*\omega(\tau)\big)
\equiv \operatorname{dec}^{(k)}*\omega(\tau)+1\pmod M.
]
For partial Tick (non-cyclic), the congruence holds without “(\bmod M)” wherever defined.

**Proof.** Tick is the lex successor, and (\operatorname{dec}^{(k)}_\omega) is an order-isomorphism. The successor in lex order increments rank by 1; wrap-around maps max-rank to 0. ∎

So we retain the key property: **Tick is still “add 1,”** but now “place values” are subtree sizes rather than fixed products.

---

# 5. Infinite depth: no-infinite-carry and well-founded evaluation index

For (\mathcal R^{(\infty)}_\omega), lex order is not a well-order, so we do not use it as “time.” Instead, we use the **odometer successor procedure** and ask when it terminates.

### Definition 65 (maximal path)  [§5.1 · Phase 5, Fragment 5.1]

An infinite path (\tau\in\mathcal R^{(\infty)}*\omega) is **maximal** if for every (i),
[
\tau_i = b*\omega(\tau_{<i})-1.
]
If such a path exists, it is unique (deterministically maximal at each node).

### Definition 66 (infinite Tick, partial)  [§5.2 · Phase 5, Fragment 5.1]

For (\tau\in\mathcal R^{(\infty)}*\omega) that is not maximal, define (\mathrm{Tick}^{(\infty)}*\omega(\tau)) by the same carry algorithm: find the rightmost digit that is not locally maximal, increment it, and reset the suffix to zeros.

### Proposition 81 (no infinite carry)  [§5.3 · Phase 5, Fragment 5.1]

If (\tau) is not maximal, then the carry search terminates in finite time, hence (\mathrm{Tick}^{(\infty)}_\omega(\tau)) is well-defined.

**Proof.** “Not maximal” means: there exists some index (i) with (\tau_i < b_\omega(\tau_{<i})-1). Let (i^\ast) be the **largest** such index. Then all indices (j>i^\ast) are locally maximal, so the algorithm stops at (i^\ast) and performs a finite update. ∎

This is the exact “no infinite carry loop” condition: **the only obstruction is the maximal path.**

### Corollary 25 (well-founded tick index from a start state)  [§5.4 · Phase 5, Fragment 5.1]

Fix any start path (\tau^{(0)}\in\mathcal R^{(\infty)}*\omega) that is not maximal and such that all iterates remain non-maximal. Then the orbit
[
\tau^{(t+1)}=\mathrm{Tick}^{(\infty)}*\omega(\tau^{(t)})
]
is a well-defined sequence indexed by (t\in\mathbb N). Thus “time” is the iteration count (t), i.e. a well-founded discrete index.

(We do **not** claim the orbit is surjective or that lex order is a well-order; only that the Tick dynamics yields a well-defined countable evaluation schedule.)

---

# 6. Computability constraints (what must be assumed)

To keep the system *computable*, we require:

### Assumption 6.1 (effective radix law)

For each (\omega), the function (b_\omega(s)) is computable from ((\omega,s)).

### Proposition 82 (Tick computability)  [§6.2 · Phase 5, Fragment 5.1]

* Finite depth (k): (\widetilde{\mathrm{Tick}}^{(k)}_\omega) is computable in (O(k)) digit operations.
* Infinite depth: (\mathrm{Tick}^{(\infty)}_\omega(\tau)) is computable in (O(i^\ast)) where (i^\ast) is the carry-stop index (finite unless (\tau) is maximal).

**Proof.** The carry algorithm scans digits from the least significant end, evaluating (b_\omega(\tau_{<i})) at each step, and performs a bounded edit once it finds the stop index. ∎

---

# 7. Connection back to the earlier runtime hinge

In Phase 4, cylinder-local gates depended on “modulus appears by depth” (e.g. (q\mid B_L) in fixed-base). In variable radix:

* The **prefix/cylinder filtration still exists** (Section 2).
* The **block counts (B_L)** are replaced by **node-dependent subtree sizes** (W^{(k)}_\omega(s)).
* Therefore, the notion “a modulus is decided by depth (L)” becomes **context/prefix-relative**: a congruence may be decidable on some cylinders but not globally uniform.

This is precisely why Phase 5.2 must state conditions ensuring that compositional operators (convolutions / projections) remain associative / local under the evolving radix law.

---

## Leading questions for Phase 5, Fragment 5.2

1. **Termination & totality (beyond ‘not maximal’):** what structural conditions on (b_\omega) ensure maximal paths are absent, or can be safely handled (e.g. cyclic truncations, absorbing boundaries)?
2. **Compositionality under variable radices:** when does the rank map (\operatorname{dec}^{(k)}_\omega) interact nicely with convolution/projection operators so that “program composition = arithmetic composition” still holds without rewriting everything at each prefix?
3. **DP / STOK recursion viability:** what invariants on (b_\omega(s)) guarantee that the induced time dynamics can be augmented to a Markov state where Bellman-style recursions remain well-posed?

If you want, I’ll proceed immediately with Fragment 5.2 and make those conditions explicit (as theorems / failure modes).

## Phase 5 — Function-Defined Radices, Fragment 5.2

### Stability + compositionality conditions, and when DP / STOK-style recursions remain viable

We continue with the variable-radix law from Fragment 5.1: for each context (\omega\in\Omega),
[
b_\omega:\Sigma^\ast\to{2,3,4,\dots},\qquad D_\omega(s)={0,\dots,b_\omega(s)-1},
]
and the depth-(k) space of admissible digit strings
[
\mathcal R^{(k)}*\omega:={\tau=(d_0,\dots,d_k): d_i\in D*\omega(\tau_{<i})}.
]

This fragment pins down **exact conditions** under which:

1. Tick is **computable / stable** (no ambiguity, no carry loops).
2. The arithmetic operator calculus (convolution, Möbius inversion, residue projectors, etc.) is **composable** when transported onto (\mathcal R^{(k)}_\omega).
3. A Bellman/DP/STOK recursion remains **well-posed** once you augment state appropriately.

---

# 1) Stability of variable-radix Tick: the “prefix-determined” condition

The single most important structural constraint is:

### Definition 67 (prefix-determined radix law)  [§1.1 · Phase 5, Fragment 5.2]

A variable-radix system is **prefix-determined** if, during a Tick update, the admissible digit set at position (i) depends only on the already-fixed prefix (\tau_{<i}) (and a context (\omega) that is held fixed throughout that Tick). Formally: it is exactly the law (b_\omega(\tau_{<i})) from Fragment 5.1, with no dependence on suffix digits or on intermediate carry artifacts.

This is not cosmetic: it is what prevents “carry feedback loops.”

### Theorem 32 (well-defined successor; no carry loops)  [§1.2 · Phase 5, Fragment 5.2]

Fix (k) and (\omega). Under prefix-determinism, the carry/successor algorithm defines a unique (\mathrm{Tick}^{(k)}*\omega(\tau)) (or cyclic (\widetilde{\mathrm{Tick}}^{(k)}*\omega)) for every (\tau\in\mathcal R^{(k)}_\omega) (partial only at the lexicographic maximum in the non-cyclic version), and the computation halts in (O(k)) digit-steps.

**Proof.** The successor algorithm searches from the least significant digit leftward for the first digit that is not locally maximal. Local maximality at index (i) is decidable from (\tau_{<i}) and (d_i) because the bound is (b_\omega(\tau_{<i})-1). Once an index (i) is chosen and (d_i) incremented, all later digits are reset to 0; their admissibility is guaranteed because each later bound depends only on the (now fixed) new prefix. No backtracking is needed, so the process is finite and unique. ∎

### Failure mode (why this condition is necessary)

If the bound at digit (i) depended on suffix digits (or on digits that are being changed during carry), the step “reset suffix to zero” could change earlier admissibility checks, forcing backtracking and possibly non-termination. Prefix-determinism is precisely the condition that removes this circularity.

---

# 2) Compositionality: charts, transported arithmetic, and what breaks when the chart changes

Even with variable radices, at fixed ((\omega,k)) the depth-(k) space is finite and totally ordered by lexicographic order. From Fragment 5.1 we have:

* subtree-size recursion (W_\omega^{(k)}(s)),
* rank map (\operatorname{dec}*\omega^{(k)}:\mathcal R*\omega^{(k)}\to{0,\dots,M-1}), (M:=|\mathcal R_\omega^{(k)}|),
* with Tick corresponding to (+1) in rank coordinates.

## 2.1 The chart is an algebra isomorphism device

### Definition 68 (chart / reindexing isomorphism)  [§2.1 · Phase 5, Fragment 5.2]

Let
[
\mathsf{Seq}*M(V):={f:{0,\dots,M-1}\to V}.
]
Define the pullback and pushforward:
[
(\Phi*{\omega,k} f)(\tau):=f(\operatorname{dec}*\omega^{(k)}(\tau)),
\qquad
(\Psi*{\omega,k} F)(r):=F(\operatorname{enc}*\omega^{(k)}(r)).
]
Then (\Phi*{\omega,k}:\mathsf{Seq}*M(V)\to H_k^\omega(V):=V^{\mathcal R*\omega^{(k)}}) is a bijection with inverse (\Psi_{\omega,k}).

### Theorem 33 (transport principle)  [§2.2 · Phase 5, Fragment 5.2]

Any algebraic operator (A) defined on (\mathsf{Seq}*M(V)) transports to an operator on (H_k^\omega(V)) by conjugation:
[
A^{(\omega,k)} := \Phi*{\omega,k}, A, \Psi_{\omega,k}.
]
If (A) has an identity/composition law (associativity, inverses, etc.), the transported operators have the identical law.

**Proof.** Conjugation by a bijection preserves all algebraic identities:
((AB)^{(\omega,k)}=\Phi A B \Psi = (\Phi A \Psi)(\Phi B \Psi)=A^{(\omega,k)}B^{(\omega,k)}), and similarly for addition, identity, inverses. ∎

**Immediate corollary:** Dirichlet transforms, Möbius inversion, residue projectors, etc. remain associative/invertible **as soon as they are defined on the charted integer line**, because the chart is an isomorphism.

So: **variable radices do not threaten compositionality at fixed ((\omega,k))**. They only change what “index” means.

---

## 2.2 The real hazard: changing (\omega) without recharting

If the radix law changes with state/time, you are composing operators that live on *different* spaces (\mathcal R_{\omega}^{(k)}) (possibly different sizes), or at least different enc/dec charts.

### Definition 69 (rechart map)  [§2.3 · Phase 5, Fragment 5.2]

Suppose (|\mathcal R_{\omega}^{(k)}|=|\mathcal R_{\omega'}^{(k)}|=M). Define the rechart bijection
[
C_{\omega\to\omega'}^{(k)} := \operatorname{enc}*{\omega'}^{(k)}\circ \operatorname{dec}*\omega^{(k)}
:\mathcal R_{\omega}^{(k)}\to \mathcal R_{\omega'}^{(k)}.
]
This is an order-preserving bijection (lex order to lex order via ranks).

### Proposition 83 (coherent composition across changing radices)  [§2.4 · Phase 5, Fragment 5.2]

Let (A) be an operator expressed in the “index algebra” (\mathsf{Seq}*M(V)). Its implementation on (\mathcal R*{\omega}^{(k)}) is (A^{(\omega,k)}). If the radix context changes (\omega\to\omega'), then the coherent way to carry state and operators across is:
[
F' ;=; (C_{\omega\to\omega'}^{(k)})*#,F
\quad\text{(pushforward of state),}
]
and
[
A^{(\omega',k)} ;=; (C*{\omega\to\omega'}^{(k)})*#; A^{(\omega,k)}; (C*{\omega\to\omega'}^{(k)})_#^{-1}.
]
If you do this, all operator identities remain valid across context changes.

**Proof.** This is exactly conjugation transport, with (C) implementing the change-of-chart on the underlying set. ∎

### Failure mode (what breaks if you *don’t* rechart)

If you apply an operator “as if” the chart were unchanged while the radix law has changed, then the same digit string (\tau) corresponds to a different rank (r). Operators whose meaning depends on rank (e.g. “residue mod (q)” on (r), or “multiples of (m)” on (r)) are no longer the same operator. In that case, “composition laws” can appear to fail—not because the arithmetic is wrong, but because you silently changed the coordinate system without transporting semantics.

So compositionality across adaptive radices requires an explicit **rechart protocol**, or a state representation that is chart-invariant (next section).

---

# 3) Conditions for DP / STOK-style recursion viability

DP/Bellman/STOK recursions require a **Markov state** and well-defined step dynamics. Variable radices threaten neither if you formalize the state correctly.

## 3.1 Markovization by augmenting with radix phase/chart state

### Definition 70 (augmented state for variable-radix time)  [§3.1 · Phase 5, Fragment 5.2]

Let (X) be the environment state space (could be finite or measurable). Define the augmented state
[
Z_t := (X_t,\ \omega_t,\ \tau_t),
]
where (\tau_t\in\mathcal R_{\omega_t}^{(k)}) is the current radix-time coordinate, and (\omega_t) determines the radix law (b_{\omega_t}).

Assume:

1. **Prefix-determined Tick** at fixed (\omega_t): (\tau_{t+1}=\widetilde{\mathrm{Tick}}_{\omega_t}^{(k)}(\tau_t)) (or partial Tick with termination).
2. **Context update** is a function of current state/action/observation:
   [
   \omega_{t+1} = \Gamma(\omega_t, X_t, A_t, \tau_t, \xi_t),
   ]
   for some noise (\xi_t).
3. **Environment dynamics**:
   [
   X_{t+1} \sim P(\cdot \mid X_t, A_t, \omega_t, \tau_t).
   ]

### Theorem 34 (Markov property)  [§3.2 · Phase 5, Fragment 5.2]

Under the above assumptions, ({Z_t}) is a Markov process:
[
\mathbb P(Z_{t+1}\in \cdot \mid Z_0,\dots,Z_t, A_0,\dots,A_t) = \mathbb P(Z_{t+1}\in\cdot \mid Z_t, A_t).
]

**Proof.** Each component of (Z_{t+1}) is generated from ((Z_t,A_t)) and fresh noise only: (\tau_{t+1}) is deterministic from ((\omega_t,\tau_t)); (\omega_{t+1}) depends only on current variables; (X_{t+1}) depends only on current variables by assumption. ∎

This is the formal version of “Markovian when state is augmented with phase,” where the phase is ((\omega,\tau)).

---

## 3.2 Bellman recursion: finite horizon and infinite horizon

### Proposition 84 (finite-horizon DP always works)  [§3.3 · Phase 5, Fragment 5.2]

If you define a finite horizon (T) (or partial Tick that terminates at (\tau_{\max})), and rewards (r(Z_t,A_t)) are bounded, then the value functions
[
V_t(z) := \sup_\pi \mathbb E^\pi\Big[\sum_{s=t}^{T-1} r(Z_s,A_s)\ \Big|\ Z_t=z\Big]
]
satisfy the Bellman recursion
[
V_t(z)=\sup_{a}\Big(r(z,a)+\mathbb E[V_{t+1}(Z_{t+1})\mid Z_t=z,A_t=a]\Big),
]
with terminal condition (V_T(\cdot)=0).

**Proof.** Standard dynamic programming for Markov decision processes; the variable-radix structure is absorbed into the augmented state (z=(x,\omega,\tau)). ∎

### Proposition 85 (infinite-horizon contraction condition)  [§3.4 · Phase 5, Fragment 5.2]

If you instead use infinite horizon with discount (\gamma\in(0,1)) and bounded rewards, the Bellman operator is a contraction in sup norm on bounded functions over (Z), hence admits a unique fixed point (V^\star).

**Proof.** Standard discounted MDP result; again, only Markovity is required. ∎

---

## 3.3 What STOK-style recursion additionally needs

STOK feasibility / time-to-termination recursions typically require an absorbing/terminal mechanism (mass drains out of nonterminal set). In this variable-radix setting, the **time coordinate** is not itself the terminal event; you must specify a terminal set (G\subseteq Z) or an absorbing condition.

A sufficient condition template (mirrors what you already use in STOK proofs):

### Condition (T) (absorbing / transience condition)

There exists a measurable terminal set (G\subseteq Z) such that under the induced policy process, (G) is absorbing and reached with probability 1 (or with geometric tail bound). Then the time-to-go value (\nu) and feasibility indicators are well-defined and solve the corresponding Bellman equations.

Variable radices do not change this: they only change the representation of “phase/time” inside (Z). The same transience assumptions carry through once (Z) is the state.

---

# 4) Summary of “preserve or break” conditions

### Preserved (safe) if:

* **Prefix-determinism:** (b_\omega(s)) depends only on prefix and fixed (\omega) during Tick ⇒ Tick is computable and unambiguous.
* **Chart discipline:** arithmetic semantics are defined on rank coordinates and transported via (\operatorname{dec}_\omega^{(k)}) ⇒ operator algebra identities hold.
* **Augmented Markov state:** include (\omega) and (\tau) (and, when needed, valuation registers) ⇒ DP/STOK recursions remain well-posed.

### Breaks / becomes ill-posed if:

* bases depend on suffix/future digits during carry ⇒ Tick may require backtracking or fail to terminate.
* (\omega) changes but you treat digit strings as if rank were unchanged ⇒ you silently changed coordinates and arithmetic operators no longer mean what they did.
* you omit (\omega) (or phase) from state while (\omega) affects transitions/gates ⇒ non-Markov, Bellman recursion invalid.

---

## Leading questions for Phase 5, Fragment 5.3

1. **Chart-invariant semantics:** can we define the “program integer” not as rank (r), but as a function of (\tau) that is invariant under radix-law changes (e.g., valuation lens, residue registers, or an adelic coordinate)?
2. **Local modulus-by-depth under variable branching:** what replaces the simple condition (q\mid B_L)? (Answer will be a *prefix-relative* divisibility condition on subtree sizes (W_\omega^{(k)}(s)) and will produce a nonuniform locality map over (\Sigma_L).)
3. **STOK viability constraints:** formalize exact conditions under which variable radix updates preserve the “absorbing/transient” property needed for (\kappa)/(\nu) recursions when time-phase itself is adaptive.

If you want, I’ll proceed with Fragment 5.3 next and make the “prefix-relative modulus appearance” theorem explicit.

## Phase 5 — Function-Defined Radices, Fragment 5.3

### Chart-invariant semantics, prefix-relative “modulus appears by depth,” and STOK/DP viability as a theorem about augmented state

This fragment makes three things precise:

1. **Chart-invariant time / program semantics:** arithmetic lives on an integer index that does *not* change when the radix law changes.
2. **Modulus-by-depth under adaptive radices:** the fixed condition (q\mid B_L) becomes a *prefix-relative* divisibility condition on cylinder step sizes.
3. **DP / STOK viability:** once you augment the state with the phase/chart register, Bellman/STOK recursions remain well-posed under the same transience/absorption hypotheses.

Throughout, fix a finite horizon (k\ge 0) and let (M_\omega := |\mathcal R_\omega^{(k)}|) (possibly (\omega)-dependent).

---

# 1) Chart-invariant semantics: separate the integer register from its radix representation

The key move: **time is an integer register; radices are a representation layer.**

### Definition 71 (radix chart)  [§1.1 · Phase 5, Fragment 5.3]

A **radix chart** for context (\omega) (at depth (k)) is a bijection
[
\pi_\omega:\ \mathbb Z_{M_\omega}\ \to\ \mathcal R_\omega^{(k)},
]
with computable inverse (\pi_\omega^{-1}). (Here (\mathbb Z_{M_\omega}) is integers mod (M_\omega).)

Interpretation: (\pi_\omega(m)) is “the digit-string representation of counter value (m)” under radix law (\omega).

> In the fixed-base case, (\pi_\omega) is the usual mixed-radix encoding.
> In the variable-base case, (\pi_\omega) can be taken as the lex-rank chart from Phase 5.1 (always exists at finite depth).

### Definition 72 (chart-invariant Tick)  [§1.2 · Phase 5, Fragment 5.3]

Define Tick on the register:
[
m^+ := m+1 \pmod{M_\omega}.
]
Define the represented Tick state:
[
\tau := \pi_\omega(m),\qquad \tau^+ := \pi_\omega(m^+).
]

So the *actual clock* is (m\mapsto m+1); digit strings are a display/phase coordinate that can change with (\omega) by recharting.

### Theorem 35 (semantic stability under radix changes)  [§1.3 · Phase 5, Fragment 5.3]

Suppose at time (t) the context updates (\omega_t\to \omega_{t+1}). If you keep the same integer register (m_{t+1}) and update only by recharting
[
\tau_{t+1} := \pi_{\omega_{t+1}}(m_{t+1}),
]
then **all arithmetic operators defined on the register** (Dirichlet transforms, residue projectors, etc.) are invariant under radix changes. Any two radices differ only by conjugation on the represented space.

**Proof.** Arithmetic operators act on functions of (m\in\mathbb Z_{M}). Changing (\omega) changes (\pi_\omega), i.e. changes coordinates on (\mathcal R), but does not change (m). On represented functions (F(\tau)), the transported operator is (\Phi_\omega A \Phi_\omega^{-1}) with (\Phi_\omega f := f\circ \pi_\omega^{-1}), hence changing (\omega) is conjugation. ∎

**Consequence:** “integer ↔ program” is now literally chart-invariant: it is a mapping on the integer register, not on digits.

---

# 2) Modulus-by-depth becomes prefix-relative: cylinder step sizes

Now we formalize the replacement for the fixed condition (q\mid B_L).

## 2.1 A filtration (cylinders) on (\mathcal R_\omega^{(k)})

Fix a “digit-prefix” notion (the one you use for the ultrametric cylinders). For each (L\le k+1), let (\Sigma_{\omega,L}) index length-(L) cylinders and let (C_\omega(s)\subseteq \mathcal R_\omega^{(k)}) be the cylinder at prefix (s).

Define the induced filtration (\mathcal F_{\omega,L}) as the sigma-algebra generated by these cylinders.

## 2.2 Register-image of a cylinder and its step size

Transport cylinders into the register via the chart:
[
I_\omega(s)\ :=\ \pi_\omega^{-1}(C_\omega(s))\ \subseteq\ \mathbb Z_{M_\omega}.
]

In fixed-base mixed radix, (I_\omega(s)) is exactly an arithmetic progression (a residue class modulo a block size). In general, it need not be.

We therefore isolate the exact structural condition we need for modular locality:

### Definition 73 (arithmetic-cylinder property at depth (L))  [§2.1 · Phase 5, Fragment 5.3]

We say ((\pi_\omega,\mathcal F_{\omega,L})) has the **arithmetic-cylinder property** if for every cylinder index (s\in\Sigma_{\omega,L}) there exist integers (r_\omega(s)) and (\beta_\omega(s)\ge 1) such that
[
I_\omega(s)\ =\ {,m\in\mathbb Z_{M_\omega}:\ m\equiv r_\omega(s)\ (\mathrm{mod}\ \beta_\omega(s)),}.
]
Equivalently, each cylinder is the preimage of a single congruence class on the register (with possibly cylinder-dependent modulus (\beta_\omega(s))).

We call (\beta_\omega(s)) the **local block size** (local step) of that cylinder.

> In fixed-base mixed radix, (\beta_\omega(s)) is constant over all (s) of a given depth: (\beta_\omega(s)=B_L).
> In function-defined radices, (\beta_\omega(s)) can genuinely depend on (s): this is the “prefix-relative” generalization.

### Proposition 86 (prefix-relative modulus appearance)  [§2.2 · Phase 5, Fragment 5.3]

Assume the arithmetic-cylinder property at depth (L). Fix a modulus (q\ge 2). For a cylinder (C_\omega(s)), if
[
q \mid \beta_\omega(s),
]
then **register congruences mod (q) are constant on that cylinder**:
[
m\equiv a\ (\mathrm{mod}\ q)\quad\text{is }\mathcal F_{\omega,L}\text{-measurable when restricted to }C_\omega(s).
]

**Proof.** If (m\in I_\omega(s)), then (m\equiv r_\omega(s)\pmod{\beta_\omega(s)}). If (q\mid \beta_\omega(s)), then (m\equiv r_\omega(s)\pmod q) for all (m\in I_\omega(s)). Thus the residue class mod (q) is constant on (I_\omega(s)), hence constant on (C_\omega(s)). ∎

This is the exact replacement for “(q\mid B_L)”:
[
\boxed{\text{“(q) appears by depth (L)” becomes: }q\mid \beta_\omega(s)\text{ on the relevant cylinder(s).}}
]

## 2.3 When does the arithmetic-cylinder property hold?

You don’t get it for free for arbitrary charts. You get it when your chart is *compatible with the cylinder filtration*.

A sufficient (implementable) condition:

### Condition (AC-L) (filtration-compatible chart)

There exists an integer (\beta_{\omega,L}\ge 1) such that for every cylinder (C_\omega(s)) of depth (L),
[
I_\omega(s)\ \text{is a residue class modulo }\beta_{\omega,L}.
]
Equivalently, all depth-(L) cylinders partition the register into congruence classes mod (\beta_{\omega,L}).

This is exactly the fixed-base situation and can still hold in some adaptive systems (notably when the low-order clock structure is kept uniform while high-order structure adapts).

### Corollary 26 (global modulus-by-depth)  [§2.3 · Phase 5, Fragment 5.3]

Under (AC-L), any modulus (q\mid \beta_{\omega,L}) yields that the predicate (m\equiv a\pmod q) is (\mathcal F_{\omega,L})-measurable (i.e. cylinder-local at depth (L)).

---

# 3) DP / STOK recursion viability under function-defined radices

We now state the minimal theorem that keeps Bellman/STOK recursions valid.

## 3.1 Augmented state space

Let (X_t) be the environment state and (A_t) an action. Define the augmented phase/chart state:
[
Z_t := (X_t,\ \omega_t,\ m_t).
]
We treat the represented radix coordinate as a derived observable:
[
\tau_t := \pi_{\omega_t}(m_t).
]

Assume dynamics:

* register Tick: (m_{t+1}=m_t+1\pmod{M_{\omega_t}}) (or a fixed (M) if you hold depth fixed and enforce equal sizes),
* context update: (\omega_{t+1}=\Gamma(\omega_t,X_t,A_t,m_t,\xi_t)),
* environment update: (X_{t+1}\sim P(\cdot\mid X_t,A_t,\omega_t,m_t)).

### Theorem 36 (Markov property)  [§3.1 · Phase 5, Fragment 5.3]

Under these assumptions, (Z_t) is Markov:
[
\mathbb P(Z_{t+1}\in\cdot\mid Z_0,\dots,Z_t,A_0,\dots,A_t) = \mathbb P(Z_{t+1}\in\cdot\mid Z_t,A_t).
]

**Proof.** Each component of (Z_{t+1}) depends only on ((Z_t,A_t)) plus fresh noise. ∎

This is the rigorous form of “Markovian when state is augmented with radix phase,” with the crucial refinement: the invariant phase is the **integer register** (m), not the digit string (\tau).

## 3.2 Bellman / STOK fixed points

Let (G\subseteq Z) be a terminal/absorbing set (goal/constraint satisfaction, termination, etc.). Define nonterminal set (N:=Z\setminus G).

### Condition (Absorb)

Under the policy class of interest (e.g. your Phase-2 policy), the induced chain on (Z) is absorbing in (G) and (N) is transient:
[
\lim_{t\to\infty}\mathbb P(Z_t\in N\mid Z_0=z)=0,\quad \forall z.
]

### Theorem 37 (STOK/DP recursion viability under variable radices)  [§3.2 · Phase 5, Fragment 5.3]

Under Theorem 36 (Markov) and Condition (Absorb), the standard Bellman recursions for:

* time-to-go (\nu),
* feasibility indicators (\kappa),
* and any bounded cumulative reward value,
  remain well-posed on the augmented space (Z). In particular, the fixed-point equations have the usual least/unique solutions (depending on whether you use undiscounted absorbing or discounted formulations).

**Proof.** Identical to the fixed-radix case, because the proofs only require (i) Markov property on the state space where the operator is defined, and (ii) transience/absorption (or discount) to guarantee convergence/uniqueness. The radix system enters only through the augmented state variables ((\omega,m)), which are already included in (Z). ∎

**Interpretation:** variable radices do not endanger STOK/DP mathematics; *failing to augment the phase* does.

---

# What this fragment locks in

* You now have a clean separation:

  * **Invariant arithmetic time/program index:** (m).
  * **Adaptive representation:** (\tau=\pi_\omega(m)).
* “(q) appears by depth” becomes:

  * **local block size divisibility:** (q\mid \beta_\omega(s)) (prefix-relative).
  * and a **global special case** (AC-L): a single (\beta_{\omega,L}) works for all cylinders at depth (L).

---

## Leading questions for the next fragment

1. **Constructing (\beta_\omega(s)) from the radix law:** give explicit sufficient conditions on (b_\omega) (or on the chart (\pi_\omega)) that guarantee the arithmetic-cylinder property and compute local block sizes efficiently.
2. **Choosing the “right” filtration:** if your operators care about modular structure, pick/engineer a filtration compatible with arithmetic cylinders (AC-L). If your operators care about hierarchical composition, pick the ultrametric filtration that matches factorization/locality. Formalize a dual-filtration runtime.
3. **Phase 6 extraction:** now that we have an instruction algebra (Phase 4) and a chart-invariant clock (Phase 5), we can extract an explicit “ANT ISA” and memory model as a proper abstract machine.

If you want, I’ll make (1) fully explicit next: a theorem that computes (\beta_\omega(s)) (or proves when it’s constant) directly from subtree-size recursions / mixed-radix products.

## Phase 5 — Function-Defined Radices, Fragment 5.4

### Computing local block moduli (\beta_\omega(s)), when cylinders become congruence classes, and the “odometer-compatible chart” condition

In Fragment 5.3 we introduced a strong (but useful) notion: **a modulus is decided by depth** when a modular predicate is measurable w.r.t. a cylinder filtration. For fixed mixed radix this was (q\mid B_L). For adaptive radices we replaced it by **prefix-relative** divisibility (q\mid \beta_\omega(s)).

This fragment makes that concrete: we give **explicit formulas** for (\beta_\omega(s)) and prove exactly when the “arithmetic-cylinder property” holds.

---

# 0. Setup: least-significant-prefix cylinders (the odometer convention)

We keep the convention used in Phase 4.2:

* digits are indexed (i=0,1,\dots,k) with (i=0) **least significant** (the digit Tick touches first);
* a length-(L) prefix is (s=(d_0,\dots,d_{L-1}));
* the cylinder is
  [
  C_\omega(s):={\tau\in\mathcal R_\omega^{(k)}:\tau_{<L}=s}.
  ]

The radix law is prefix-determined:
[
b_\omega:\Sigma^\ast\to{2,3,\dots},\qquad d_i\in{0,\dots,b_\omega(\tau_{<i})-1}.
]

---

# 1. The key structural condition: sibling-uniformity of suffix counts

Let (W_\omega^{(k)}(s)) be the number of completions of a prefix (s) to full length (k+1):
[
W_\omega^{(k)}(s):=#{\tau\in\mathcal R_\omega^{(k)}:\tau_{<|s|}=s}.
]

### Definition 74 (Sibling-uniform suffix counts, SU)  [§1.1 · Phase 5, Fragment 5.4]

We say the radix system is **SU at depth (k)** if for every prefix (s) with (|s|\le k), the completion counts of its children are equal:
[
W_\omega^{(k)}(s|d)\ \text{is independent of }d\in D_\omega(s).
]
Equivalently, there exists (U_\omega^{(k)}(s)) such that
[
W_\omega^{(k)}(s|d)=U_\omega^{(k)}(s)\quad \forall d\in D_\omega(s).
]

### Proposition 87 (SU ⇔ constant block sizes at each node)  [§1.2 · Phase 5, Fragment 5.4]

SU holds iff for all (s) with (|s|\le k),
[
W_\omega^{(k)}(s)=b_\omega(s),W_\omega^{(k)}(s|0).
]

**Proof.** Always (W(s)=\sum_{d\in D(s)}W(s|d)). SU makes the summands equal, giving (W(s)=b(s),W(s|0)). Conversely, if that equality holds for a fixed (0), then all summands must coincide (otherwise the sum would not match). ∎

**Intuition (formal):** SU means “choosing digit (d) at prefix (s) selects one of (b_\omega(s)) blocks of equal size.” That is exactly what makes mixed-radix positional arithmetic work.

---

# 2. Constructing the odometer-compatible chart (\pi_{\omega,k}^{\mathrm{odo}})

We now define a chart in which **least-significant prefixes correspond to congruence classes**. This is the chart you want if you want “modulus-by-depth” and residue projectors to be cylinder-local.

## 2.1 Local block modulus (\beta_\omega(s))

### Definition 75 (local modulus / place value along a prefix)  [§2.1 · Phase 5, Fragment 5.4]

Define (\beta_\omega:\Sigma^\ast\to\mathbb N) inductively:
[
\beta_\omega(\varnothing)=1,\qquad
\beta_\omega(s|d)=\beta_\omega(s)\cdot b_\omega(s).
]
So (\beta_\omega(s)) depends only on the path of prefixes, not on suffix choices.

**Interpretation:** (\beta_\omega(s)) is the “place value” (step size) associated to having fixed the first (|s|) least-significant digits.

## 2.2 Positional decoding (odometer form)

### Definition 76 (odometer decoding)  [§2.2 · Phase 5, Fragment 5.4]

For (\tau=(d_0,\dots,d_k)\in\mathcal R_\omega^{(k)}), define
[
\operatorname{dec}^{\mathrm{odo}}*{\omega,k}(\tau)
:=\sum*{i=0}^{k} d_i,\beta_\omega(\tau_{<i}).
]

This is the natural generalization of mixed-radix evaluation to prefix-dependent bases.

---

# 3. The arithmetic-cylinder theorem

The next theorem is the payoff: it tells you exactly when cylinders become congruence classes.

### Theorem 38 (SU ⇒ arithmetic cylinders with modulus (\beta_\omega(s)))  [§3.1 · Phase 5, Fragment 5.4]

Assume SU at depth (k). Then:

1. (\operatorname{dec}^{\mathrm{odo}}*{\omega,k}) is a bijection
   [
   \operatorname{dec}^{\mathrm{odo}}*{\omega,k}:\ \mathcal R_\omega^{(k)}\ \longrightarrow\ {0,1,\dots,M-1},
   \quad M:=|\mathcal R_\omega^{(k)}|.
   ]

2. For any prefix (s) with (|s|=L), the cylinder (C_\omega(s)) maps to a single congruence class modulo (\beta_\omega(s)):
   [
   \operatorname{dec}^{\mathrm{odo}}*{\omega,k}(\tau)\ \equiv\ \operatorname{dec}^{\mathrm{odo}}*{\omega,L-1}(s)\quad (\mathrm{mod}\ \beta_\omega(s))
   \qquad \forall \tau\in C_\omega(s).
   ]

3. Conversely, for every integer (m\in{0,\dots,M-1}), the least-significant prefix (s) of length (L) extracted by repeated remainder steps satisfies
   [
   m\equiv \operatorname{dec}^{\mathrm{odo}}*{\omega,L-1}(s)\ (\mathrm{mod}\ \beta*\omega(s)),
   ]
   and this (s) is unique.

**Proof (sketch, but complete in structure).**

* **(2)** If (\tau\in C_\omega(s)), then (\tau_{<L}=s). Split the sum:
  [
  \operatorname{dec}^{\mathrm{odo}}*{\omega,k}(\tau)
  =\sum*{i=0}^{L-1} d_i,\beta_\omega(\tau_{<i})
  ;+;\sum_{i=L}^{k} d_i,\beta_\omega(\tau_{<i}).
  ]
  For (i\ge L), (\beta_\omega(\tau_{<i})) includes the product (\beta_\omega(s)) as a factor by construction, hence the second sum is divisible by (\beta_\omega(s)). Therefore the value modulo (\beta_\omega(s)) is determined solely by the first sum, which is exactly (\operatorname{dec}^{\mathrm{odo}}_{\omega,L-1}(s)).

* **(1) and (3)** Under SU, each node (s) partitions the remaining completions into (b_\omega(s)) blocks of equal size. This implies a mixed-radix division algorithm exists: given (m), the digit (d_0) is (m \bmod b_\omega(\varnothing)); the remainder quotient determines the next digit range uniformly because all children have equal completion size; iterate. This produces a unique digit string, and the evaluation formula reconstructs (m). Hence bijection. ∎

### Corollary 27 (prefix-relative modulus appearance)  [§3.2 · Phase 5, Fragment 5.4]

Under SU, for any modulus (q\ge 2), the predicate
[
m\equiv a\ (\mathrm{mod}\ q)
]
is constant on the cylinder (C_\omega(s)) whenever
[
q\mid \beta_\omega(s).
]
This is exactly the prefix-relative replacement of the fixed-base condition (q\mid B_L).

---

# 4. The constant-by-depth special case (recovers the classical theory)

### Proposition 88 (level-only bases ⇒ (\beta_\omega(s)) depends only on depth)  [§4.1 · Phase 5, Fragment 5.4]

If (b_\omega(s)=b_{|s|}) depends only on (|s|), then
[
\beta_\omega(s)=\prod_{i=0}^{L-1} b_i = B_L
\quad \text{for all } |s|=L,
]
and the theory collapses exactly to the fixed mixed-radix system.

---

# 5. What happens when SU fails (and what you do instead)

If SU fails, then different children of a prefix have different suffix sizes. Two consequences are unavoidable:

1. The positional map (\operatorname{dec}^{\mathrm{odo}}_{\omega,k}) generally fails to be a bijection onto a contiguous interval without reweighting blocks (you get “ragged” block structure).
2. Cylinders are no longer congruence classes under any odometer-compatible contiguous chart unless you explicitly **rechart using unequal block weights**, in which case “modulus-by-depth” becomes nonuniform or disappears.

### Practical formal fallback (always valid)

Even without SU, you still have:

* the ultrametric cylinders as a filtration,
* and exact measurability at the finest depth (k+1) (singletons).

So locality becomes: “refine until the predicate is measurable,” but you lose a clean closed-form (q\mid \beta_\omega(s)) test. In the next phase (Phase 6), this is where you choose between:

* enforcing SU-like constraints (engineering the radix law to preserve arithmetic locality), or
* accepting deeper refinements / approximate independence.

---

# 6. Engineering corollary: how the runtime uses (\beta_\omega(s))

Under SU, at any chosen depth (L):

* You store block memory (x_L) on cylinders (C_\omega(s)).
* A modular gate (\mathrm{Proj}*{q,a}) can be applied **block-locally** on those cylinders with (q\mid \beta*\omega(s)).
* The active-set size under a residue constraint shrinks by factor (\approx q) on regions where (\beta_\omega(s)) is a multiple of (q).

This gives you an explicit “locality map”:
[
s \mapsto \beta_\omega(s),
]
which is the computational primitive you were missing in Fragment 5.3.

---

## Leading questions for the next fragment

1. **Dual-filtration runtime (additive + multiplicative):** formalize a runtime that simultaneously maintains (i) cylinder-block memory (using (\beta_\omega(s)) for modular locality) and (ii) valuation-lattice memory (for Dirichlet/divisor locality), and prove a combined locality theorem.
2. **Design constraints on (b_\omega):** characterize the class of adaptive radix laws that preserve SU (or preserve it on selected depths only), and what expressivity you lose/gain.
3. **Phase 6 start:** extract the ISA cleanly: instructions become “(gate on cylinders via (\beta)) ∘ (valuation-local transform)” with explicit storage layout and cost model.

If you want, I’ll take (1) next and make the dual-filtration abstract machine precise (state format + transition operator + closure/locality).

## Phase 5 — Function-Defined Radices, Fragment 5.5

### Dual-filtration abstract machine: cylinder memory + valuation memory, guarded execution, and a combined locality theorem

This fragment formalizes the minimal **runtime state** and **instruction semantics** that simultaneously exploit:

* **additive / prefix locality** (cylinders in the ultrametric mixed-radix space, with local block moduli (\beta_\omega(s))), and
* **multiplicative / divisor locality** (valuation-lattice fibers for (P)-smooth Dirichlet kernels).

It is the first point where the system becomes a precise **abstract machine** rather than a collection of operators.

---

# 0. Fixed horizon and chart discipline

Fix depth (k) and a context (\omega) with SU (Sibling-Uniform) at depth (k) so that the odometer chart exists (Fragment 5.4). Let
[
M := |\mathcal R_\omega^{(k)}|.
]

We maintain an integer register (m\in\mathbb Z_M) as the chart-invariant time. The represented radix coordinate is
[
\tau = \pi_{\omega,k}^{\mathrm{odo}}(m)\in\mathcal R_\omega^{(k)}.
]

At depth (L\le k+1), let (\Sigma_{\omega,L}) index cylinders (C_\omega(s)), and let the local block modulus be
[
\beta_\omega(s) = \prod_{j=0}^{L-1} b_\omega(\tau_{<j}) \quad \text{(along the prefix path)}.
]
(Under SU this is consistent and gives arithmetic cylinders.)

---

# 1. Two filtrations and two memory layers

## 1.1 Cylinder filtration (additive/prefix)

At chosen depth (L), block memory is
[
x_L:\Sigma_{\omega,L}\to V.
]
Interpretation: one state value per cylinder (C_\omega(s)).

## 1.2 Valuation filtration (multiplicative/divisor)

Fix a finite prime set (P). For each integer (n\in{1,\dots,M}), write its (P)-lens decomposition
[
n = u_P(n)\cdot s_P(n),\qquad s_P(n)=\prod_{p\in P} p^{v_p(n)},
]
with (\gcd(u_P(n),\prod_{p\in P}p)=1). Define the valuation vector
[
e(n):=\big(v_p(n)\big)_{p\in P}\in\mathbb N^{P}.
]

Define valuation-fiber memory as a family
[
y:\ \mathcal U \to { \text{functions } \mathbb N^{P}\to V},
\qquad
u\mapsto y_u(\cdot),
]
where (\mathcal U) is the set of (P)-free labels occurring up to horizon. You may store only a finite active set (E_u\subseteq \mathbb N^{P}) per fiber (sparse implementation), but mathematically (y_u) is defined on all relevant exponents.

**Interpretation:** cylinder memory is “hierarchical time-space blocks”; valuation memory is “multiplicative program-space blocks.”

---

# 2. The abstract machine state

### Definition 77 (Dual-Filtration Machine state)  [§2.1 · Phase 5, Fragment 5.5]

A machine state is a tuple
[
\boxed{;\mathsf{State} := (m,\ \omega,\ x_L,\ y);}
]
with:

* (m\in\mathbb Z_M) (time register),
* (\omega) (radix law context),
* (x_L:\Sigma_{\omega,L}\to V) (cylinder blocks),
* (y=(y_u)_{u\in\mathcal U}) valuation-fiber memory.

The represented radix coordinate (\tau=\pi_{\omega,k}^{\mathrm{odo}}(m)) is a derived quantity.

---

# 3. The instruction set in machine form

We restrict to the instruction primitives already justified in Phase 4:

1. **Cylinder gates** (Proj / CRTCompose / SieveFilter and any cylinder-local predicate)
2. **Valuation-local compiled transforms** (Dirichlet kernels supported on (P)-smooth numbers, bounded radius)

and we assemble them as **guarded instructions**.

## 3.1 Cylinder gate instruction

A cylinder gate is specified by a function
[
g:\Sigma_{\omega,L}\to \mathbb C,
]
acting as
[
(\mathsf{Gate}_g x_L)(s) := g(s), x_L(s).
]
Typically (g(s)\in{0,1}) (projection), but weights are allowed.

**Key implementability condition:** A modular constraint “(m \equiv a \pmod q)” is cylinder-local on a cylinder (s) whenever (q\mid\beta_\omega(s)) (Fragment 5.4). This means such constraints induce a computable (g) without scanning finer digits.

## 3.2 Valuation-local transform instruction

A valuation-local compiled kernel is specified by a (P)-smooth kernel (a) with bounded exponent radius:
[
\mathrm{supp}(\widetilde a)\subseteq {r\in\mathbb N^{P}:|r|_\infty\le R}.
]
It acts fiberwise:
[
(\mathsf{ValTrans}_a y)*u(e) := \sum*{0\le r\le e} \widetilde a(r), y_u(e-r).
]
(Exactly the multivariate convolution form from Phase 3/Phase 4.)

## 3.3 Guarded execution (coupling gate + valuation transform)

A guarded instruction couples them:
[
\boxed{;\mathsf{Instr}(g,a)\ :=\ (\mathsf{Gate}_g)\ \text{and}\ (\mathsf{ValTrans}_a)\ \text{applied only on the gated-active region};}
]

To make “only on the gated region” precise, we need the map from cylinders to the integer indices they contain.

---

# 4. Linking layer: which valuation fibers are active under a cylinder gate?

Let (I_\omega(s)\subseteq \mathbb Z_M) be the register-image of cylinder (C_\omega(s)). Under SU and the odometer chart, this is a congruence class modulo (\beta_\omega(s)):
[
I_\omega(s)={m: m\equiv r(s)\ (\mathrm{mod}\ \beta_\omega(s))}.
]

Define the corresponding set of integer times in ({1,\dots,M}) as
[
\mathcal N(s):={n= m+1: m\in I_\omega(s)}.
]

Now define the induced set of valuation indices “hit” by a cylinder:
[
\mathcal A(s):={(u_P(n), e(n)):\ n\in \mathcal N(s)}.
]
This is a subset of (\mathcal U\times\mathbb N^{P}).

Given an active cylinder set (S\subseteq\Sigma_{\omega,L}), define
[
\mathcal A(S) := \bigcup_{s\in S}\mathcal A(s).
]

This is the exact bridge: a cylinder gate selects a union of congruence classes of (m), which selects a subset of integer times (n), which selects a subset of valuation states ((u,e)).

---

# 5. Machine transition semantics

We define a single machine step (one Tick plus one guarded instruction). This is the minimal kernel of the runtime loop.

### Definition 78 (one step of Dual-Filtration Machine)  [§5.1 · Phase 5, Fragment 5.5]

Given ((m,\omega,x_L,y)) and an instruction (\mathsf{Instr}(g,a)):

1. **Gate cylinder memory**
   [
   x_L \leftarrow \mathsf{Gate}_g(x_L).
   ]

2. **Compute active cylinders**
   [
   S_g := {s\in\Sigma_{\omega,L}: g(s)\neq 0}.
   ]

3. **Apply valuation transform only on the active valuation set**
   [
   y_u(e) \leftarrow (\mathsf{ValTrans}_a y)_u(e)\quad \text{for }(u,e)\in \mathcal A(S_g),
   ]
   leaving all other ((u,e)) unchanged (or not updated in sparse storage).

4. **Tick the integer register**
   [
   m \leftarrow m+1 \pmod M.
   ]

(One can also insert a context update (\omega\leftarrow \Gamma(\cdot)) here; we omit it to keep the fragment focused on locality and closure. Adding it is handled by Phase 5.2 Markov augmentation.)

---

# 6. Combined locality theorem

This is the theorem that justifies the machine’s existence as a “local” computation substrate.

### Theorem 39 (combined locality bound)  [§6.1 · Phase 5, Fragment 5.5]

Assume:

* SU at depth (k) so that cylinders correspond to congruence classes modulo (\beta_\omega(s)),
* the gate (g) is depth-(L) (acts on (\Sigma_{\omega,L})),
* the valuation kernel (a) is (P)-smooth and radius-(R) in exponent coordinates.

Then one step of (\mathsf{Instr}(g,a)) can be implemented with work bounded by
[
O\Big(|S_g|\Big)\ +\ O\Big(\sum_{(u,e)\in \mathcal A(S_g)} (R+1)^{|P|}\Big),
]
where:

* the first term is the cylinder-gate update cost (sparse block update),
* the second term is the valuation convolution cost restricted to the valuation indices actually selected by the gate.

Moreover, the valuation update for any fixed ((u,e)) depends only on values (y_u(e-r)) with (|r|_\infty\le R); hence the multiplicative dependency neighborhood is uniformly bounded.

**Proof.**

* Cylinder update is coordinatewise over active blocks: (O(|S_g|)).
* Under (P)-smoothness and bounded radius, each valuation update is a bounded-size sum over (\mathrm{supp}(\widetilde a)\subseteq[0,R]^{|P|}), hence (O((R+1)^{|P|})) per updated ((u,e)).
* Restricting updates to (\mathcal A(S_g)) yields the stated bound. Dependency neighborhood is inherited from the convolution form. ∎

---

# 7. Closure: composing machine programs

A “machine program” is a finite composition of steps with possibly different gates/kernels:
[
\mathsf{Prog} := \mathsf{Step}(g_T,a_T)\circ\cdots\circ \mathsf{Step}(g_1,a_1).
]

### Proposition 89 (closure under composition)  [§7.1 · Phase 5, Fragment 5.5]

The set of machine programs is closed under composition, and each composed program admits a locality bound obtained by summing the per-step locality costs (with active sets tracked stepwise).

**Proof.** Function composition closure is immediate. The complexity bound is additive because each step’s computation depends on its step-local active set. ∎

This is enough to treat “programs” as compiled objects in your runtime sense: a program is a sequence of guarded operator applications plus Tick.

---

# 8. What this fragment establishes (and why it matters)

You now have a mathematically explicit “machine” whose primitives are exactly ANT operators:

* gates = modular/CRT/sieve predicates living on cylinders (additive/prefix filtration),
* transforms = (P)-smooth Dirichlet kernels living on valuation fibers (multiplicative filtration),
* Tick = integer-register increment, with radix digits as a derived, adaptive representation.

And you have a theorem that quantifies “touch locality” in terms of:

* depth (L) and active cylinder set size (|S_g|),
* kernel radius (R) and prime-set size (|P|),
* and the coupling map (\mathcal A(S_g)) (how additive constraints select multiplicative states).

---

## Leading questions for the next fragment

1. **Make (\mathcal A(S_g)) computable without scanning all (n\le M):** derive enumeration methods using congruence classes and factorization constraints (this is where CRT and sieve interact with valuations).
2. **Introduce (\omega)-updates:** define when radix-law changes preserve SU locally, and how recharting affects (\beta_\omega(s)) and the gate semantics.
3. **Bridge to Phase 6 ISA:** compile gates and valuation transforms into a typed instruction set with explicit operands (moduli, residue sets, prime sets, radius, etc.), and give a small-step operational semantics.



---

# Phase 6: Custom Ultrametric Design via Radix Engineering

## Motivation

In Phases 1-5, the ultrametric δ_ω emerges from the radix function ω. Phase 6 makes this relationship explicit and treats it as a **design parameter**: different radix choices induce different ultrametrics, enabling **engineered information distance**.

### Core Insight
The ultrametric is **designed**, not inherited from p-adic structure. By choosing ω appropriately, we can engineer which states are "close" (share long prefixes) and which are "far" (diverge early), independent of their geometric or numerical distance.

---

## 6.1 Radix-Induced Ultrametric Objects

**Definition 79** (Radix-induced ultrametric)  [§6.1.1 · Phase 6]

For a radix function ω: ⋃_{L≥0} Σ_L → ℕ_{≥2}, define the **radix-induced ultrametric** on $\widehat{\mathcal{R}}_\omega$:

$$\delta_\omega(x,y) := \begin{cases}
0 & \text{if } x = y \\
\beta_\omega(s)^{-1} & \text{if } s = \text{lcp}(x,y) \text{ and } x \neq y
\end{cases}$$

where:
- lcp(x,y) is the longest common prefix of x and y
- β_ω(s) = ∏_{i=0}^{|s|-1} ω(s_{<i}) is the odometer weight (from Phase 5)

**Interpretation**: Distance is determined by the first point of disagreement, weighted by the cumulative radix structure up to that point.

---

**Definition 80** (Ultrametric spectrum)  [§6.1.2 · Phase 6]

The **ultrametric spectrum** of a combinatorial space is:

$$\text{Spec}(\widehat{\mathcal{R}}) := \{\delta_\omega : \omega \text{ satisfies SU}\}$$

This is the family of all valid ultrametrics induced by SU-compliant radix functions.

**Novel structure**: Traditional metric spaces have ONE metric. This framework provides a SPECTRUM of metrics on the same combinatorial space, indexed by radix choice.

---

## 6.2 Foundational Ultrametric Properties

**Theorem 40** (SU implies proper ultrametric)  [§6.2.1 · Phase 6]

If ω satisfies sibling uniformity, then δ_ω is a proper ultrametric satisfying:

1. **Identity**: δ_ω(x,y) = 0 ⟺ x = y
2. **Symmetry**: δ_ω(x,y) = δ_ω(y,x)
3. **Strong triangle inequality**: δ_ω(x,z) ≤ max(δ_ω(x,y), δ_ω(y,z))

**Proof.**
(1) and (2) follow immediately from the definition.

For (3): Let s = lcp(x,y), t = lcp(y,z), u = lcp(x,z).

Key observation: u is a prefix of both s and t, since any common prefix of x and z must be common to both pairs (x,y) and (y,z).

Thus |u| ≤ min(|s|, |t|), and since β_ω is monotone increasing in prefix length under SU:

β_ω(u) ≤ min(β_ω(s), β_ω(t))

Taking reciprocals (reversing inequality):

δ_ω(x,z) = β_ω(u)^{-1} ≤ max(β_ω(s)^{-1}, β_ω(t)^{-1}) = max(δ_ω(x,y), δ_ω(y,z))

∎

---

**Proposition 90** (Cylinders are ultrametric balls)  [§6.2.2 · Phase 6]

Under δ_ω, the cylinder U(s) is an ultrametric ball:

$$U(s) = B_{\delta_\omega}\left(x, \beta_\omega(s)^{-1}\right)$$

for any x ∈ U(s).

**Proof.**
Any y ∈ U(s) has lcp(x,y) ⪰ s (extends or equals s), so:

δ_ω(x,y) = β_ω(lcp(x,y))^{-1} ≤ β_ω(s)^{-1}

Conversely, if δ_ω(x,y) < β_ω(s)^{-1}, then β_ω(lcp(x,y))^{-1} < β_ω(s)^{-1}, implying β_ω(lcp(x,y)) > β_ω(s), which means lcp(x,y) ≻ s (strictly extends), thus y ∈ U(s).

∎

**Interpretation:** Cylinders and ultrametric balls are identical objects - one algebraic/combinatorial, the other topological.

---

## 6.3 Metric Comparison and Dominance

**Definition 81** (Metric dominance)  [§6.3.1 · Phase 6]

For two radix functions ω₁, ω₂, we say δ_{ω₁} **dominates** δ_{ω₂} (written δ_{ω₁} ⪰ δ_{ω₂}) if:

$$\forall x,y: \delta_{\omega_1}(x,y) \geq \delta_{\omega_2}(x,y)$$

Equivalently: β_{ω₁}(s) ≤ β_{ω₂}(s) for all prefixes s.

**Interpretation**: ω₁ provides finer resolution (smaller cylinder volumes) than ω₂.

---

**Theorem 41** (Metric spectrum forms a preorder)  [§6.3.2 · Phase 6]

The relation ⪰ on Spec($\widehat{\mathcal{R}}$) satisfies:

- **Reflexivity**: δ_ω ⪰ δ_ω
- **Transitivity**: δ_{ω₁} ⪰ δ_{ω₂} ⪰ δ_{ω₃} ⟹ δ_{ω₁} ⪰ δ_{ω₃}

But not necessarily antisymmetric (distinct ω can induce the same metric).

**Proof.** Follows from properties of ≤ on ℝ and monotonicity of products. ∎

---

## 6.4 The Ultrametric Design Problem (Inverse Problem)

This is the core innovation: treating ultrametric construction as an **engineering design problem**.

**Problem Statement 6.4.1** (Ultrametric design)

**Given:**
- Combinatorial space $\widehat{\mathcal{R}}$
- Desired metric properties 𝒫 (clustering structure, growth rates, locality bounds, etc.)

**Find:** Radix function ω such that δ_ω satisfies 𝒫.

**Variants:**
- **Exact design**: Find ω achieving exact target properties
- **Optimal design**: Find ω minimizing a cost functional subject to constraints
- **Constrained design**: Find ω within allowable class achieving best approximation to 𝒫

---

**Example 6.4.2** (Prescribed cylinder volumes)

**Given:** Desired volume function V: ⋃_L Σ_L → ℝ_{>0} specifying target β_ω values.

**Find:** ω such that β_ω(s) = V(s) for all s.

**Solution:** Under SU, this has a unique solution when V satisfies the consistency condition:

$$\omega(s) = \frac{V(s \| d)}{V(s)}$$

must be constant over all siblings d ∈ D_s.

**Consistency condition:** V(s∥d) / V(s) independent of digit d.

**Verification:** If consistent, then β_ω(s) = V(s) by construction. ∎

---

**Example 6.4.3** (Prescribed asymptotic growth rate)

**Given:** Desired asymptotic behavior β_ω(s) ~ f(|s|) for some growth function f.

**Solutions:**

1. **Exponential growth**: f(L) = c^L
   - Achieved by constant radix: ω(s) = c for all s
   - Result: Standard p-adic-like structure

2. **Polynomial growth**: f(L) = L^α
   - Requires variable radices: ω(s) ~ |s|^{α-1}
   - Result: Subexponential ultrametric

3. **Factorial growth**: f(L) = L!
   - Achieved by: ω(s) = |s| + 1
   - Result: Super-exponential refinement

---

**Example 6.4.4** (Context-dependent spatial resolution)

**Given:** Partition of prefix space into "critical" and "coarse" regions based on domain knowledge.

**Objective:** Fine ultrametric resolution on critical regions, coarse elsewhere.

**Construction:**
$$\omega(s) = \begin{cases}
\omega_{\text{fine}} & s \in \text{Critical} \\
\omega_{\text{coarse}} & s \in \text{Coarse}
\end{cases}$$

with ω_fine ≫ ω_coarse.

**Result:** β_ω(s) is much smaller in critical regions → δ_ω provides finer distance resolution where computationally important.

**Application:** Biological systems where certain pathways require fine temporal resolution, others can be coarse-grained.

---

**Example 6.4.5** (DNA sequence ultrametric respecting biological structure)

Design ultrametric for DNA sequences that reflects codon-level significance:

```rust
ω(sequence) = match |sequence| {
    k if k < 3 => 4,           // Incomplete codon - uniform
    k if k % 3 == 0 => 64,     // Codon boundary - coarse
    _ => 4,                     // Mid-codon - fine
}
```

**Resulting ultrametric:**
- Sequences differing mid-codon: distance = 4^{-m} (relatively close)
- Sequences differing at codon boundary: distance = 64^{-m} (farther)

**Biological interpretation:** Codon-level changes are more significant (often change amino acid) than point mutations within codons (often synonymous).

**Advantage over uniform metric:** Ultrametric reflects functional distance, not just edit distance.

---

## 6.5 Observer Complex with Multi-Metric Structure

**Definition 82** (Multi-metric observer complex)  [§6.5.1 · Phase 6]

An observer complex with custom ultrametrics is:

$$\mathcal{O} := (A, B; \sigma; \omega_A, \omega_B, \omega_I)$$

where:
- ω_A defines δ_{ω_A} on ℛ_A (timeline A's ultrametric)
- ω_B defines δ_{ω_B} on ℛ_B (timeline B's ultrametric)
- ω_I defines δ_{ω_I} on ℛ_I (interpreter/composite ultrametric)

**Key property:** Each timeline measures information distance differently.

---

**Definition 83** (Metric projection)  [§6.5.2 · Phase 6]

The projection π_B: ℛ_I → ℛ_B induces a **pullback metric** on ℛ_I:

$$\pi_B^*(\delta_{\omega_B})(x,y) := \delta_{\omega_B}(\pi_B(x), \pi_B(y))$$

**Observation:** Generally π_B*(δ_{ω_B}) ≠ δ_{ω_I}

**Interpretation:** The pullback measures distance in B's coordinate system, while δ_{ω_I} is the intrinsic composite metric. The discrepancy represents information not captured by B alone.

---

**Theorem 42** (Residual as metric discrepancy)  [§6.5.3 · Phase 6]

The residual payload at step n can be characterized as:

$$\text{payload}(n) = \log\left(\frac{\delta_{\omega_I}(\tau_n, \tau_{n+1})}{\pi_B^*\delta_{\omega_B}(\tau_n, \tau_{n+1})}\right)$$

where τ_n is the interpreter state at step n.

**Interpretation:** The payload measures how much "distance information" is lost when projecting from the composite metric to B's metric.

**Proof sketch:** The ratio compares intrinsic I-distance to projected B-distance. Logarithm converts multiplicative discrepancy to additive payload. ∎

---

## 6.6 Realizability and Classification

**Theorem 43** (Realizability criterion for ultrametrics)  [§6.6.1 · Phase 6]

An ultrametric δ on ∏_{i=0}^∞ D_i is realizable as δ = δ_ω for some SU radix function ω if and only if:

1. **Cylinder correspondence**: Every ultrametric ball is a finite union of cylinders
2. **Monotone refinement**: U(s) ⊆ U(t) ⟹ rad(U(s)) ≤ rad(U(t))
3. **Finite branching**: Each cylinder has finitely many immediate sub-cylinders

**Proof sketch.**
(→) For δ_ω, these properties hold by construction from SU.

(←) Given δ satisfying these conditions:
- Construct ω by assigning radices equal to branching factors at each cylinder
- Cylinder correspondence ensures this is well-defined
- Monotone refinement ensures β_ω matches ball radii
- SU follows from uniform ball radii for siblings

∎

**Erratum and corrected statement** (Phase 14 pass; machine-checked in
`Realizability/MetricRealizability.lean`). As stated above, the three conditions
are **insufficient** for `δ = δ_ω`, in two independent ways:

1. *"Finite union of cylinders" is too weak*: three sibling subtrees at
   pairwise-unequal distances satisfy (1)–(3) while breaking the first-difference
   form — balls can sit strictly between cylinder levels. The corrected condition
   (C1) takes the single-cylinder form, **every open ball is a prefix cylinder** —
   which is exactly what the necessity direction actually proves
   (`ball_is_cylinder`), and exactly the gauge keystone's shape (Theorem 83).
2. *Monotone refinement does not pin the radii*: the schedule `rad = 1/(2n+1)` on
   the binary product satisfies (C1) — a fortiori (1)–(3) — but is not `δ_ω` for
   any SU `ω`, whose radii are forced to be reciprocal place values
   (`conditions_insufficient`, machine-checked). The conditions pin the *tree*
   (the dendrogram); `δ = δ_ω` additionally pins the *gauge*.

**Theorem 43 (corrected).** An ultrametric `δ` on `∏ᵢ Dᵢ` (each `Dᵢ` finite, with
at least two elements) is realizable as `δ = δ_ω` for an SU radix law `ω` — the
position-only law `ω(s) = |D_{|s|}|`, unique by `radixLaw_unique` — **iff**

- **(C1)** every open ball is a prefix cylinder, and
- **(C4)** every depth-`n` cylinder has diameter exactly `(∏_{j<n} |D_j|)⁻¹`
  (the canonical reciprocal place value, as a least upper bound).

Both directions are machine-checked (`theorem43`). The proof factors as the
erratum predicts: **(C1) alone forces the first-difference (gauge) form** — the
extraction (`dist_eq_of_lcpLenD_eq`, `dist_anti_of_lcpLenD_lt`, `dist_local`): a
ball of radius `δ(x,z)` is a cylinder, so it separates partners by lcp depth,
making the distance a strictly-refining function of the shared prefix (the
classical ultrametric ↔ dendrogram correspondence — Theorem 43-general); **(C4)
then pins the gauge** to the canonical product schedule (Theorem 43-SU).
Realizability is stated intrinsically (the Definition 79 formula on `δ`'s own
space, tied to the constructed law by `suRealizable_iff_prefixWeight`); strict
monotone refinement and vanishing radii are consequences of (C1), not assumptions.

---

**Corollary 28** (Non-realizable ultrametrics)  [§6.6.2 · Phase 6]

Ultrametrics with the following properties are NOT realizable via SU radix functions:
- Continuous branching (uncountable immediate sub-cylinders)
- Refinement inversion (finer cylinders have larger ball radii)
- Non-uniform sibling structure (siblings have different branching factors)

---

## 6.7 Computational Properties Under Custom Metrics

**Theorem 44** (Locality bounds under designed metrics)  [§6.7.1 · Phase 6]

For an L-local operator T (in the combinatorial sense of operating on depth-L cylinders), the Lipschitz constant under δ_ω is:

$$\text{Lip}_{\delta_\omega}(T) = \max_{|s|=L} \beta_\omega(s)$$

**Implication:** By designing ω to make β_ω(s) small on computationally relevant cylinders, we can enforce strong locality (low Lipschitz constant) where needed.

**Proof.** L-local operator cannot distinguish points within same depth-L cylinder. Maximum sensitivity is when operating on cylinders with largest β_ω. ∎

---

**Example 6.7.2** (Cache-optimized ultrametric)

Design ω such that:
$$\beta_\omega(s) = 2^{-\text{cache\_cost}(s)}$$

where cache_cost(s) is the measured cache miss rate for accessing cylinder U(s).

**Result:** δ_ω-locality directly corresponds to cache efficiency. Algorithms that are δ_ω-local are automatically cache-optimized.

---

## 6.Summary: Phase 6 Proved Results

**Proposition 91** (SU ⟹ proper ultrametric). If ω satisfies sibling uniformity, then δ_ω satisfies identity, symmetry, and strong triangle inequality.  [P6.1 · Phase 6]

**Proposition 92** (Cylinders are balls). U(s) = B_{δ_ω}(x, β_ω(s)^{-1}) for any x ∈ U(s).  [P6.2 · Phase 6]

**Proposition 93** (Spectrum forms preorder). Ultrametric dominance ⪰ is reflexive and transitive on Spec($\widehat{\mathcal{R}}$).  [P6.3 · Phase 6]

**Proposition 94** (Volume prescription). Given consistent volume function V, there exists unique ω with β_ω = V.  [P6.4 · Phase 6]

**Proposition 95** (Multi-metric observers). Observer complex (A, B; σ) extends to (A, B; σ; ω_A, ω_B, ω_I) with independent metrics.  [P6.5 · Phase 6]

**Proposition 96** (Realizability criterion). Ultrametric δ is realizable as δ_ω iff it has cylinder correspondence, monotone refinement, and finite branching.  [P6.6 · Phase 6]

**Proposition 97** (Custom locality). L-local operators have Lipschitz constant max_{|s|=L} β_ω(s) under δ_ω.  [P6.7 · Phase 6]

---

# Phase 7: Context-Dependent Radix Systems

## Motivation

Phase 5 introduced variable radices b_i = ω(s_{<i}). Phase 7 generalizes: **the radix function itself can depend on external context that evolves over time**.

### Core Insights

1. **ω need not be stored** - can be computed on-demand, adaptive, stochastic
2. **External determination** - sizing oracle can be separate from state structure
3. **Lazy materialization** - structure discovered only when needed
4. **Stateful evolution** - context changes induce radix changes

These enable:
- Learned/adaptive ω functions
- Resource-constrained lazy allocation
- Multi-agent negotiated structure
- Environmental coupling

---

## 7.1 Context Spaces and Extended Radix Oracles

**Definition 84** (Context space)  [§7.1.1 · Phase 7]

A **context space** is a set 𝒞 equipped with (optionally):
- A partial order ⪯_𝒞 (refinement/information ordering)
- A measurable structure (for stochastic contexts)
- Composition operations (for multi-agent contexts)

No specific structure required; 𝒞 is an abstract parameter space.

**Examples:**
- **Trivial**: 𝒞 = {*} (reduces to fixed ω)
- **Finite modes**: 𝒞 = {mode₁, ..., mode_k} (discrete state machine)
- **State-dependent**: 𝒞 = ℤ_M (system register value)
- **Continuous parameter**: 𝒞 = [0,1]^n (real-valued parameters)
- **Multi-agent**: 𝒞 = ∏_{i=1}^N 𝒞_i (product of agent contexts)

---

**Definition 85** (Extended radix oracle)  [§7.1.2 · Phase 7]

An **extended radix oracle** is a function:

$$\Omega: \left(\bigcup_{L \geq 0} \Sigma_L\right) \times \mathcal{C} \to \mathbb{N}_{\geq 2}$$

We write ω_c(s) := Ω(s, c) for the radix at prefix s under context c.

**Interpretation:** The radix depends on BOTH structural position (prefix s) AND external context (state c).

---

**Definition 86** (Contextual sibling uniformity - CSU)  [§7.1.3 · Phase 7]

Ω satisfies **contextual sibling uniformity** if:

$$\forall c \in \mathcal{C}, \forall s \in \Sigma_L, \forall d, e \in D_L: \quad \omega_c(s \| d) = \omega_c(s \| e)$$

**Interpretation:** Within any fixed context c, siblings have the same radix. Standard SU holds at each "snapshot" of context.

**Critical property:** This allows context to change over time while preserving odometer properties at each instant.

---

**Definition 87** (Context-indexed mixed-radix family)  [§7.1.4 · Phase 7]

Given Ω satisfying CSU, define the **family of mixed-radix spaces:**

$$\{\mathcal{R}_c : c \in \mathcal{C}\}$$

where ℛ_c is the mixed-radix space with radix function ω_c.

Each ℛ_c has:
- **Odometer weight**: β_c(s) = ∏_{i=0}^{|s|-1} ω_c(s_{<i})
- **Ultrametric**: δ_c(x,y) = β_c(lcp(x,y))^{-1}
- **Cylinder structure**: U_c(s) = {x : π_L(x) = s} (same combinatorially, different metric scale)

---

## 7.2 Context Evolution and Stateful Systems

**Definition 88** (Context dynamics)  [§7.2.1 · Phase 7]

A **context evolution rule** is a function:

$$\Gamma: \mathcal{C} \times \mathcal{E} \to \mathcal{C}$$

where ℰ is an **event space** (system observations, time steps, external inputs, measurements, etc.).

**Interpretation:** c_{t+1} = Γ(c_t, e_t) updates context based on event e_t.

---

**Definition 89** (Stateful context-dependent system)  [§7.2.2 · Phase 7]

A **stateful radix system** is a tuple:

$$\mathcal{S} := (\Omega, \mathcal{C}, c_0, \Gamma, \mathcal{E})$$

where:
- Ω is an extended radix oracle
- 𝒞 is a context space
- c₀ ∈ 𝒞 is the initial context
- Γ: 𝒞 × ℰ → 𝒞 is the context evolution rule
- ℰ is the event space

**Evolution protocol:**
```
At time t:
  Observe event e_t ∈ ℰ
  Update context: c_{t+1} = Γ(c_t, e_t)
  Radix becomes: ω_{c_{t+1}}
  Continue with new radix law
```

---

**Definition 90** (Trace of a stateful system)  [§7.2.3 · Phase 7]

A **trace** of 𝒮 under event sequence (e₀, e₁, ...) ∈ ℰ* (or ℰ^ℕ) is the context sequence:

$$c_0, c_1, c_2, \ldots \quad \text{where } c_{t+1} = \Gamma(c_t, e_t)$$

The induced **radix history** is:
$$\omega_{c_0}, \omega_{c_1}, \omega_{c_2}, \ldots$$

**Interpretation:** The radix function evolves over time as context changes. The structure itself is dynamic.

---

**Theorem 45** (Context-switching preserves SU)  [§7.2.4 · Phase 7]

If Ω satisfies CSU and Γ is arbitrary, then ω_{c_t} satisfies standard SU for each t.

**Proof.** CSU holds for each fixed c_t by definition. Γ changes which context snapshot we're viewing but doesn't violate the pointwise SU property within that context. ∎

**Implication:** Can have time-varying radix while maintaining all Phase 5 properties (odometer bijection, cylinder structure, etc.) at each time step.

---

## 7.3 Semantic Modes and Implementation Equivalences

**Definition 91** (Operational semantic modes)  [§7.3.1 · Phase 7]

A context-dependent system 𝒮 can operate in different **semantic modes** corresponding to different computational models:

1. **Random access mode**: State at any time t can reference state at any time t' (full directed graph)
2. **Streaming mode**: State at time t depends only on finite window t-k, ..., t (bounded causal)
3. **Purely sequential mode**: State at time t depends only on t-1 (Markov property)

**Critical observation:** The mode is a constraint on the **computation graph**, not on the algebraic structure. The same 𝒮 can support all modes depending on how it's used.

---

**Definition 92** (Lazy vs eager realization)  [§7.3.2 · Phase 7]

For a context-dependent system 𝒮:

**Eager realization:** All cylinders at depth ≤ L are pre-allocated for all contexts in some finite reachable set 𝒞_reach ⊆ 𝒞.

**Lazy realization:** Cylinders are materialized only when accessed:

$$\text{Materialized}(t) := \{U_c(s) : s \text{ accessed by time } t, c \in \{c_0, \ldots, c_t\}\}$$

**Trade-off:**
- Eager: Higher memory, O(1) access
- Lazy: Lower memory, possible allocation cost on first access

---

**Theorem 46** (Lazy-eager semantic equivalence)  [§7.3.3 · Phase 7]

For any finite trace and deterministic access pattern, lazy and eager realization produce **identical observable behavior** (same values at accessed locations).

**Proof.** Both modes compute ω_c(s) on-demand when U_c(s) is first accessed. Pre-allocation only affects unaccessed cylinders. Since computation results depend only on accessed values, observable behaviors coincide. ∎

**Implication:** Implementation can choose lazy or eager based on resource constraints without changing semantics. This is a true **representation independence** theorem.

---

## 7.4 Structural Invariants Under Context Change

**Definition 93** (Structure-preserving context transition)  [§7.4.1 · Phase 7]

A context transition c → c' is **structure-preserving at depth L** if:

$$\forall s \in \Sigma_L: \beta_c(s) = \beta_{c'}(s)$$

**Interpretation:** Cylinder volumes at depth L are unchanged; only structure at depth > L may differ.

---

**Theorem 47** (Depth-L operators preserved)  [§7.4.2 · Phase 7]

If transition c → c' is structure-preserving at depth L, then:

1. All L-local gates remain valid (cylinder boundaries unchanged)
2. Ultrametric δ_c agrees with δ_{c'} on Σ_L-indexed points
3. Projection operators P_L commute with context switch

**Proof.**
(1) Gates depend only on Σ_L partition, which is combinatorial (independent of metric scale).

(2) For any x,y with |lcp(x,y)| ≤ L: δ_c(x,y) = β_c(lcp(x,y))^{-1} = β_{c'}(lcp(x,y))^{-1} = δ_{c'}(x,y) by assumption.

(3) P_L averages over suffix within each depth-L cylinder. Since cylinder structure is preserved, P_L commutes.

∎

**Implication:** Can change radix law for depth > L without invalidating depth-L computations.

---

**Definition 94** (Monotone context refinement)  [§7.4.3 · Phase 7]

A context transition c → c' is **monotone refining** if:

$$\forall s: \beta_{c'}(s) \leq \beta_c(s)$$

**Interpretation:** Context c' provides finer (or equal) resolution everywhere.

---

**Proposition 98** (Metric dominance under refinement)  [§7.4.4 · Phase 7]

If c → c' is monotone refining, then:

$$\delta_{c'}(x,y) \geq \delta_c(x,y) \quad \forall x,y$$

**Proof.** δ_{c'}(x,y) = β_{c'}(s)^{-1} ≥ β_c(s)^{-1} = δ_c(x,y) where s = lcp(x,y). ∎

**Interpretation:** Refining context increases ultrametric distances (finer resolution).

---

## 7.5 Multi-Context Observer Composition

**Definition 95** (Multi-context observer complex)  [§7.5.1 · Phase 7]

A **multi-context observer complex** is:

$$\mathcal{O} := (A, B; \sigma; \Omega_A, \Omega_B, \Omega_I; \mathcal{C}_A, \mathcal{C}_B, \mathcal{C}_I)$$

where:
- Ω_A, Ω_B, Ω_I are extended radix oracles for timelines A, B, and interpreter I
- 𝒞_A, 𝒞_B, 𝒞_I are respective context spaces
- σ: ℕ × 𝒞_I → {A, B} may depend on interpreter context

---

**Definition 96** (Context-dependent schedule)  [§7.5.2 · Phase 7]

A **context-dependent schedule** is:

$$\sigma: \mathbb{N} \times \mathcal{C}_I \to \{A, B\}$$

At interpreter step n with context c_I, execute timeline σ(n, c_I).

**Generalization:** Fixed schedule σ(n) is special case where schedule is context-independent.

---

**Definition 97** (Context coupling maps)  [§7.5.3 · Phase 7]

A **context coupling** consists of maps:

$$\phi_A: \mathcal{C}_I \to \mathcal{C}_A, \quad \phi_B: \mathcal{C}_I \to \mathcal{C}_B$$

**Projection rule:** Interpreter context c_I induces component contexts:

$$\omega_A(s) = \Omega_A(s, \phi_A(c_I)), \quad \omega_B(s) = \Omega_B(s, \phi_B(c_I))$$

**Interpretation:** Component timelines inherit structure from interpreter's current context.

---

**Theorem 48** (Independent context evolution)  [§7.5.4 · Phase 7]

If Γ_A, Γ_B, Γ_I evolve independently (no coupling), then:

$$\text{Trace}(\mathcal{O}) = \text{Trace}_I \times \text{Trace}_A \times \text{Trace}_B$$

is the Cartesian product of independent traces.

**Proof.** Context updates factor: Γ(c_I, c_A, c_B, e) = (Γ_I(c_I, e), Γ_A(c_A, e), Γ_B(c_B, e)). Evolution is component-wise independent. ∎

---

**Definition 98** (Coupled context evolution)  [§7.5.5 · Phase 7]

For coupled contexts, define **joint evolution:**

$$\Gamma: \mathcal{C}_I \times \mathcal{C}_A \times \mathcal{C}_B \times \mathcal{E} \to \mathcal{C}_I \times \mathcal{C}_A \times \mathcal{C}_B$$

**Example (payload feedback):**
$$c_{A,t+1} = \Gamma_A(c_{A,t}, \text{payload}_B(c_{I,t}))$$

Timeline A's context is updated based on the residual payload from B's projection.

**Interpretation:** Information that B cannot represent influences A's adaptive structure.

---

## 7.6 Well-Formedness and Computability Conditions

**Definition 99** (Computable oracle)  [§7.6.1 · Phase 7]

Ω is **computable** if there exists an algorithm that, given finite representations of (s, c), halts and returns Ω(s, c) ∈ ℕ_{≥2}.

---

**Definition 100** (Finitely-supported oracle)  [§7.6.2 · Phase 7]

Ω is **finitely-supported** if for each c, the function ω_c has finite description (e.g., finite lookup table, closed-form expression, finite automaton).

---

**Proposition 99** (Finite-depth realizability)  [§7.6.3 · Phase 7]

If:
1. Ω is computable
2. 𝒞 is finite or countable
3. Depth L is finite
4. Reachable context set 𝒞_reach ⊆ 𝒞 is finite

Then the cylinder structure at depth L is finitely realizable (admits finite data structure).

**Proof.** At depth L, there are at most Σ_{k=0}^L ∏_{i=0}^{k-1} max_c ω_c(s_{<i}) cylinders across all contexts. For finite 𝒞_reach and computable Ω, all radix values are computable and bounded, hence admits finite tabular representation. ∎

---

**Definition 101** (Stable oracle)  [§7.6.4 · Phase 7]

Ω is **stable** under context evolution Γ if:

$$\sup_{c \in \mathcal{C}, s \in \Sigma, e \in \mathcal{E}} |\omega_c(s) - \omega_{\Gamma(c,e)}(s)| < \infty$$

**Interpretation:** Radix changes are bounded; no infinite jumps in resolution on single context transition.

---

## 7.7 Independence and Determinism Conditions

**Definition 102** (Context-independent prefix)  [§7.7.1 · Phase 7]

A prefix s is **context-independent** if:

$$\forall c, c' \in \mathcal{C}: \omega_c(s) = \omega_{c'}(s)$$

**Example application:** Early structural digits might be fixed (context-independent), while later digits adapt to context (context-dependent).

---

**Definition 103** (Deterministic context system)  [§7.7.2 · Phase 7]

(Ω, 𝒞, Γ) is **deterministic** if Γ is a function and:

$$\forall c, e: \Gamma(c, e) \text{ is uniquely determined}$$

---

**Definition 104** (Stochastic context system)  [§7.7.3 · Phase 7]

A **stochastic context system** replaces Γ with a transition kernel:

$$\Gamma: \mathcal{C} \times \mathcal{E} \to \Delta(\mathcal{C})$$

where Δ(𝒞) is the space of probability distributions on 𝒞.

**Trace becomes stochastic process:** (c_t)_{t≥0} is a Markov chain on 𝒞.

---

**Theorem 49** (Stochastic SU preservation)  [§7.7.4 · Phase 7]

If Ω satisfies CSU, then for any stochastic Γ, the random radix function ω_{c_t} satisfies SU almost surely at each time t.

**Proof.** CSU is a pointwise property of Ω at each c. Regardless of which c_t is sampled from Γ, CSU holds at that c_t. Hence SU holds almost surely (in fact, surely). ∎

---

## 7.8 Abstract Embedding and Oracle Equivalence

**Definition 105** (Oracle embedding)  [§7.8.1 · Phase 7]

An **oracle embedding** ι: Ω ↪ Ω' is a pair of injective maps:

$$\iota_\Sigma: \Sigma \hookrightarrow \Sigma', \quad \iota_{\mathcal{C}}: \mathcal{C} \hookrightarrow \mathcal{C}'$$

such that:
$$\Omega(s, c) = \Omega'(\iota_\Sigma(s), \iota_{\mathcal{C}}(c))$$

**Interpretation:** Ω is a restriction or subsystem of Ω'.

---

**Definition 106** (Oracle equivalence)  [§7.8.2 · Phase 7]

Two oracles Ω₁, Ω₂ are **semantically equivalent** (written Ω₁ ≅ Ω₂) if there exist bijections:

$$\phi_\Sigma: \Sigma_1 \to \Sigma_2, \quad \phi_{\mathcal{C}}: \mathcal{C}_1 \to \mathcal{C}_2$$

such that:
$$\Omega_1(s, c) = \Omega_2(\phi_\Sigma(s), \phi_{\mathcal{C}}(c))$$

**Interpretation:** Oracles differ only by relabeling; represent the same abstract structure.

---

**Theorem 50** (Equivalence preserves all structural properties)  [§7.8.3 · Phase 7]

If Ω₁ ≅ Ω₂, then:
- CSU for Ω₁ ⟺ CSU for Ω₂
- Computability is preserved
- All locality theorems, composition laws, and operator properties transfer

**Proof.** Structural properties (CSU, locality bounds, composition rules) are defined in terms of the abstract operations and relations, which are invariant under relabeling bijections. ∎

---

## 7.Summary: Phase 7 Proved Results

**Proposition 100** (Context-switching preserves SU). If Ω satisfies CSU, then ω_c satisfies standard SU for each c ∈ 𝒞.  [P7.1 · Phase 7]

**Proposition 101** (Lazy-eager equivalence). For finite traces with deterministic access patterns, lazy and eager realization are observationally equivalent.  [P7.2 · Phase 7]

**Proposition 102** (Structure-preserving transitions). If c → c' preserves structure at depth L, then all L-local operators remain valid under the context change.  [P7.3 · Phase 7]

**Proposition 103** (Refinement induces metric dominance). Monotone refining context transitions yield metric dominance: δ_{c'} ≥ δ_c.  [P7.4 · Phase 7]

**Proposition 104** (Independent factorization). Observer complex with uncoupled context evolution has product trace structure.  [P7.5 · Phase 7]

**Proposition 105** (Finite realizability). Computable Ω on finite 𝒞_reach admits finite representation at any finite depth L.  [P7.6 · Phase 7]

**Proposition 106** (Stochastic SU preservation). CSU oracle with stochastic Γ preserves SU almost surely.  [P7.7 · Phase 7]

**Proposition 107** (Oracle equivalence invariance). Semantically equivalent oracles preserve all structural and computational properties.  [P7.8 · Phase 7]

---

# Phase 8: Multi-Timeline Routing and Composition

## Motivation

Extend single-timeline and two-timeline observer formalisms to handle:
- **Multiple concurrent timelines** with arbitrary connectivity topology
- **Overflow routing** - overflow in one timeline triggers events in others
- **Injection at junction cylinders** - structured cross-timeline coupling
- **Spawn/terminate dynamics** - dynamic timeline creation and destruction
- **Composite timing bounds** - provable latency across routed systems

### Core Insight

> **Interrupts, I/O events, and async signals are not external disruptions - they are parallel timelines with structured overflow routing at junction points.**

This reconceptualizes asynchronous computation: instead of "interrupts disturbing sequential flow," we have "multiple timelines ticking independently, coupled via algebraic routing rules."

---

## 8.1 Timeline Graphs and Junction Points

**Definition 107** (Timeline identifier space)  [§8.1.1 · Phase 8]

A **timeline identifier space** is a set 𝒯 of timeline identifiers. May be:

- **Finite**: 𝒯 = {T₁, ..., T_n} (static system with n timelines)
- **Countable**: 𝒯 = ℕ (dynamic spawning allowed)

Each T ∈ 𝒯 has:
- **Radix oracle**: Ω_T: Σ × 𝒞_T → ℕ_{≥2}
- **Context space**: 𝒞_T
- **State space**: ℛ_T (mixed-radix space induced by Ω_T)

---

**Definition 108** (Timeline graph structure)  [§8.1.2 · Phase 8]

A **timeline graph** is a tuple:

$$\mathcal{G} := (\mathcal{T}, \mathcal{J}, \rho)$$

where:
- 𝒯 is the timeline identifier space
- 𝒥 ⊆ 𝒯 × Σ* × 𝒯 × Σ* is the set of **junctions** (potential coupling points)
- ρ is the **routing function** specifying actual transfers

A junction (A, s_A, B, s_B) ∈ 𝒥 connects:
- **Source**: timeline A at cylinder prefix s_A
- **Target**: timeline B at cylinder prefix s_B

---

**Definition 109** (Junction point types)  [§8.1.3 · Phase 8]

A **junction point** is a triple (T, s, dir) where:
- T ∈ 𝒯 is a timeline
- s ∈ Σ*_T is a cylinder prefix in T's mixed-radix space
- dir ∈ {OUT, IN} specifies direction

**Notation:**
- **(A, s_A)^OUT**: source/outflow point (overflow exits here)
- **(B, s_B)^IN**: target/inflow point (injection enters here)

---

**Definition 110** (Active cylinder in timeline)  [§8.1.4 · Phase 8]

A cylinder U_T(s) in timeline T is **active** at global time t if the timeline's current state τ_T(t) satisfies:

$$\pi_{|s|}(\tau_T(t)) = s$$

**Interpretation:** The timeline is currently executing within that cylinder.

---

## 8.2 Routing Function and Transfer Semantics

**Definition 111** (Event space for timeline graphs)  [§8.2.1 · Phase 8]

The **event space** is:

$$\mathcal{E} := \{(\text{TICK}, T), (\text{OVERFLOW}, T, s), (\text{INJECT}, T, s, \text{payload})\}_{T \in \mathcal{T}, s \in \Sigma^*}$$

**Event types:**
- **TICK**: Timeline advances one local step
- **OVERFLOW**: Timeline's cylinder at prefix s overflows (carry propagates beyond s)
- **INJECT**: External payload arrives at timeline's cylinder s

---

**Definition 112** (Routing function)  [§8.2.2 · Phase 8]

A **routing function** is:

$$\rho: \mathcal{T} \times \Sigma^* \times \mathcal{E}_{\text{trigger}} \times \mathcal{C}_{\text{global}} \to \mathcal{P}(\mathcal{T} \times \Sigma^* \times \text{TransferType} \times \text{PayloadTransform})$$

**Given:**
- Source timeline A
- Source cylinder prefix s_A
- Triggering event e
- Current global context c

**Returns:** Set of target specifications (B, s_B, τ, φ) where:
- B is target timeline
- s_B is target cylinder
- τ is transfer type
- φ is payload transformation

**Notation:** ρ(A, s_A, e, c) = {(B₁, s_{B₁}, τ₁, φ₁), ..., (B_k, s_{B_k}, τ_k, φ_k)}

---

**Definition 113** (Transfer types)  [§8.2.3 · Phase 8]

The **transfer type** τ specifies residue flow semantics:

1. **TOTAL**: Complete transfer with source reset
   $$\text{residue}_A \to \text{residue}_B, \quad \text{state}_A \leftarrow 0$$

2. **PARTIAL(π)**: Projected transfer with remainder retention
   $$\pi(\text{residue}_A) \to \text{residue}_B, \quad \text{state}_A \leftarrow (1-\pi)(\text{residue}_A)$$

3. **COPY**: Duplication without source modification
   $$\text{residue}_A \to \text{residue}_B, \quad \text{state}_A \text{ unchanged}$$

4. **SPAWN(Ω_new, τ₀)**: Create new timeline with initial configuration
   $$\text{create } T_{\text{new}} \text{ with oracle } \Omega_{\text{new}} \text{ and initial state } \tau_0$$

5. **TERMINATE**: Destroy source timeline with final residue transfer
   $$\text{residue}_A \to \text{residue}_B, \quad \text{destroy timeline } A$$

---

**Definition 114** (Payload transform)  [§8.2.4 · Phase 8]

A **payload transform** is a function:

$$\phi: \text{Residue}_A \times \mathcal{C}_A \to \text{Payload}_B$$

converting source-timeline residue to target-timeline compatible payload.

**Examples:**
- **Identity**: φ(res, c) = res
- **Projection**: φ(res, c) = π_k(res) (first k components)
- **Context-dependent**: φ(res, c) = f(res, c) (arbitrary computable function)

---

**Definition 115** (Static routing table)  [§8.2.5 · Phase 8]

Routing is **static** if it factors through a finite table independent of context:

$$\rho(A, s_A, e, c) = \text{TABLE}[A][s_A][e]$$

**Importance:** Static routing enables:
- Compile-time verification
- O(1) routing lookup at runtime
- Provable timing bounds (Theorem 53)

---

## 8.3 Injection Semantics and Locality

**Definition 116** (Injection operation)  [§8.3.1 · Phase 8]

Given target timeline B at cylinder s_B with incoming payload p:

$$\text{Inject}(B, s_B, p): \text{state}_B \leftarrow \text{Inject}_{s_B}(\text{state}_B, p)$$

where Inject_{s_B} is a cylinder-local state update function.

---

**Definition 117** (Injection locality)  [§8.3.2 · Phase 8]

Injection at (B, s_B) is **L-local** if:

$$\text{Inject}_{s_B} \text{ modifies only digits at positions } i \geq |s_B| - L$$

**Interpretation:** Injection affects at most L digit positions beyond the junction depth.

**Importance:** Locality of injection preserves computational bounds and enables compositional reasoning.

---

**Definition 118** (Injection queue for asynchrony)  [§8.3.3 · Phase 8]

For asynchronous systems, each timeline T maintains an **injection queue:**

$$Q_T: \text{Queue}(\Sigma^* \times \text{Payload})$$

**Protocol:**
- **Enqueue** when routed: Q_T.push(s_B, p)
- **Process** on timeline tick: (s, p) ← Q_T.pop(); Inject(T, s, p)

**Bounded queues:** System is well-behaved if |Q_T| ≤ Q_max for all T.

---

**Theorem 51** (Injection preserves CSU)  [§8.3.4 · Phase 8]

If:
1. Timeline B satisfies CSU under Ω_B
2. Injection Inject_{s_B} is cylinder-local

Then B continues to satisfy CSU after injection.

**Proof.** CSU is a property of the radix oracle Ω_B, which is not modified by state updates. Cylinder-locality ensures injection doesn't alter the combinatorial prefix structure that defines CSU. ∎

---

## 8.4 Routing Graph Properties and Deadlock Analysis

**Definition 119** (Routing dependency graph)  [§8.4.1 · Phase 8]

The **routing graph** G_ρ = (V, E) induced by ρ is:

- **Vertices**: V = {(T, s) : T ∈ 𝒯, s ∈ Σ*_T} (all possible junction points)
- **Edges**: E = {((A, s_A), (B, s_B)) : ∃τ,φ. (B, s_B, τ, φ) ∈ ρ(A, s_A, _, _)}

**Interpretation:** Edge from (A, s_A) to (B, s_B) means overflow/event at A can route to B.

---

**Definition 120** (Acyclic routing)  [§8.4.2 · Phase 8]

Routing is **acyclic** if G_ρ is a directed acyclic graph (DAG).

**Interpretation:** No circular event dependencies.

---

**Theorem 52** (Acyclic routing implies deadlock-freedom)  [§8.4.3 · Phase 8]

If:
1. Routing is acyclic
2. All timelines satisfy liveness (make progress if not waiting)
3. All injection queues are bounded

Then the system is **deadlock-free**.

**Proof.**
Suppose deadlock occurs: some set S ⊆ 𝒯 of timelines are mutually waiting.

Each T ∈ S waits for injection from some T' ∈ S. This creates a waiting cycle, which corresponds to a cycle in G_ρ.

Contradiction with acyclicity assumption. ∎

**Implication:** Acyclicity is checkable at compile time from routing specification (Proposition 109).

---

**Definition 121** (Routing depth)  [§8.4.4 · Phase 8]

The **routing depth** of junction point (T, s) is:

$$\text{depth}_\rho(T, s) := \text{length of longest path from any source to } (T, s) \text{ in } G_\rho$$

For source points (no incoming edges): depth_ρ(T, s) = 0.

---

**Proposition 108** (Finite routing depth)  [§8.4.5 · Phase 8]

If routing is acyclic and G_ρ is finite, then:

$$\max_{(T,s) \in V} \text{depth}_\rho(T, s) < \infty$$

**Proof.** DAG on finite vertex set has finite longest path by graph theory. ∎

---

## 8.5 Composite Timing and Complexity Bounds

**Definition 122** (Local timeline operation cost)  [§8.5.1 · Phase 8]

For timeline T at cylinder depth L with radix function ω_T:

$$\text{Cost}_T(L) := \sum_{i=0}^{L-1} f(\omega_T(s_{<i}))$$

where f is a cost model (e.g., f(b) = log b for digit operations, f(b) = b for memory access).

---

**Definition 123** (Routing operation overhead)  [§8.5.2 · Phase 8]

For routing step from (A, s_A) to target set {(B_i, s_{B_i})}:

$$\text{Cost}_\rho(A, s_A) := |\rho(A, s_A, \_, \_)| \cdot \text{Cost}_{\text{lookup}} + \sum_i \text{Cost}_{\phi_i}$$

where:
- |ρ(...)| is fanout (number of targets)
- Cost_lookup is routing table access cost
- Cost_{φ_i} is payload transformation cost for target i

---

**Theorem 53** (Composite timing bound - Main Result)  [§8.5.3 · Phase 8]

For an event originating at (A, s_A) with routing depth D:

$$\text{Total latency} \leq \sum_{k=0}^{D} \left( \max_{(T,s) \in \text{layer}_k} \left[\text{Cost}_T(|s|) + \text{Cost}_\rho(T, s)\right] \right)$$

where layer_k = {(T, s) : depth_ρ(T, s) = k}.

**Proof.**
Event propagates through routing layers 0, 1, ..., D sequentially.

At layer k, multiple timelines may process in parallel. Worst-case latency is the maximum over all junction points in that layer.

Layer latencies compose additively (sequential propagation).

Bound obtained by summing maximum cost over each layer. ∎

**Significance:** This theorem provides **compile-time provable worst-case latency** for arbitrary multi-timeline systems with static routing.

---

**Corollary 29** (Static routing compile-time bound)  [§8.5.4 · Phase 8]

If:
1. Routing is static (table-based, context-independent)
2. All Ω_T are static or have bounded range
3. Routing graph G_ρ is finite

Then **total latency bound is computable at compile time**.

**Proof.** All parameters in Theorem 53 are statically determined:
- Routing depth D is computable from G_ρ
- Cost_T(|s|) is computable from ω_T
- Cost_ρ is determined by routing table structure

∎

**Critical implication:** Enables **formal verification of real-time systems** before deployment.

---

## 8.6 Spawn and Terminate Dynamics

**Definition 124** (Timeline lifecycle states)  [§8.6.1 · Phase 8]

A timeline T has **lifecycle status:**

$$\text{Lifecycle}_T \in \{\text{DORMANT}, \text{ACTIVE}, \text{TERMINATED}\}$$

**State transitions:**
- DORMANT →^SPAWN ACTIVE (timeline created)
- ACTIVE →^TERMINATE TERMINATED (timeline destroyed)

---

**Definition 125** (Spawn operation)  [§8.6.2 · Phase 8]

**Spawn**(A, s_A, Ω_new, τ₀) executed at timeline A, cylinder s_A creates new timeline:

1. Allocate fresh identifier: T_new ∈ 𝒯 ∖ {T : lifecycle_T = ACTIVE}
2. Initialize radix oracle: Ω_{T_new} ← Ω_new
3. Initialize state: τ_{T_new} ← τ₀
4. Set lifecycle: lifecycle_{T_new} ← ACTIVE
5. Register routing edges: add (A, s_A) → (T_new, ...) and return edges to G_ρ

**Interpretation:** Timeline creation at runtime, with overflow from A providing initial state for T_new.

---

**Definition 126** (Terminate operation)  [§8.6.3 · Phase 8]

**Terminate**(T, final_residue) destroys timeline T:

1. Compute routing: ρ(T, ROOT, TERMINATE, c_global) determines final residue destinations
2. Inject final_residue into target timelines
3. Set lifecycle: lifecycle_T ← TERMINATED
4. Remove from active routing graph

**Interpretation:** Timeline destruction with cleanup - final state is not lost but routed to continuation points.

---

**Definition 127** (Bounded spawn system)  [§8.6.4 · Phase 8]

A system has **bounded spawn** if there exists N_max such that:

$$|\{T \in \mathcal{T} : \text{lifecycle}_T = \text{ACTIVE}\}| \leq N_{\max}$$

at all times.

**Interpretation:** Finite bound on concurrent timelines (prevents unbounded resource usage).

---

**Theorem 54** (Bounded spawn preserves global timing bounds)  [§8.6.5 · Phase 8]

If:
1. System has bounded spawn with limit N_max
2. Each timeline has bounded per-cylinder cost C_max
3. Routing is acyclic with maximum depth D_max

Then **global worst-case latency** satisfies:

$$\text{Total latency} \leq N_{\max} \cdot D_{\max} \cdot C_{\max}$$

**Proof.**
At most N_max timelines can be active simultaneously.

Any event propagates through at most D_max routing layers (acyclicity).

Each layer processes at most N_max timelines, each with cost ≤ C_max.

Product bound N_max · D_max · C_max follows. ∎

**Significance:** Dynamic timeline creation doesn't break timing guarantees if spawn count is bounded.

---

## 8.7 Multicast and Synchronization Patterns

**Definition 128** (Multicast routing)  [§8.7.1 · Phase 8]

Routing at (A, s_A) is **multicast** if:

$$|\rho(A, s_A, e, c)| > 1$$

The same triggering event routes to multiple distinct targets.

**Example:** Timer overflow broadcasts to CPU, LED controller, and network module simultaneously.

---

**Definition 129** (Synchronization point)  [§8.7.2 · Phase 8]

A junction (T, s) is a **synchronization point** if it has multiple incoming edges:

$$|\{(A, s_A) : ((A, s_A), (T, s)) \in E_{G_\rho}\}| > 1$$

**Interpretation:** Timeline T at cylinder s waits for events from multiple source timelines.

---

**Definition 130** (Join semantics)  [§8.7.3 · Phase 8]

At synchronization point (T, s) with k sources {(A₁, s₁), ..., (A_k, s_k)}:

- **ALL-join (barrier)**: Inject executes only when ALL sources have delivered
- **ANY-join (race)**: Inject executes when FIRST source delivers
- **COLLECT-join (accumulate)**: Inject combines payloads: Inject(T, s, combine(p₁, ..., p_k))

**Example:**
```
Barrier: Task waits for CPU + DMA + Network all ready
Race: Interrupt handler triggered by any of multiple sources
Collect: Aggregate sensor readings from multiple timelines
```

---

**Theorem 55** (Multicast-join duality)  [§8.7.4 · Phase 8]

For every multicast at routing depth d with k targets, there exists a potential synchronization at depth d' > d with k sources, if the routing graph paths reconverge.

**Proof.** Multicast creates k divergent paths from source. If any subset of these paths later converge to a common junction point, that point becomes a synchronization with multiple incoming edges. Path depth increases by traversal length. ∎

---

## 8.8 Compile-Time Verification Infrastructure

**Definition 131** (Routing specification language)  [§8.8.1 · Phase 8]

A **routing specification** is a declarative set:

$$\text{Spec} := \{(A, s_A, \text{trigger}, B, s_B, \tau, \phi)\}$$

enumerating all routing rules.

**Syntax example:**
```
route (CPU, SYSCALL_0x80, OVERFLOW) -> (KERNEL, ENTRY_0x1000, TOTAL, extract_args);
route (TIMER, MAX_TICK, OVERFLOW) -> (CPU, TIMER_ISR, COPY, id);
route (DMA, COMPLETE, SIGNAL) -> (CPU, DMA_ISR, PARTIAL(low_bytes), truncate);
```

---

**Definition 132** (Compiled routing table)  [§8.8.2 · Phase 8]

The **compiled routing table** from Spec is:

$$\text{TABLE}[A][s_A][\text{trigger}] := \{(B, s_B, \tau, \phi) : (A, s_A, \text{trigger}, B, s_B, \tau, \phi) \in \text{Spec}\}$$

**Runtime:** Single array lookup determines all targets.

---

**Proposition 109** (Compile-time decidable properties)  [§8.8.3 · Phase 8]

From routing specification Spec, the following are **decidable at compile time:**

1. **Acyclicity**: Is G_ρ a DAG? (cycle detection algorithm)
2. **Bounded fanout**: Is max_{A,s} |ρ(A, s, _, _)| < ∞? (scan specification)
3. **Bounded depth**: Is max_{T,s} depth_ρ(T, s) < ∞? (longest path algorithm)
4. **Reachability**: Can source (A, s_A) reach target (B, s_B)? (graph traversal)
5. **Deadlock freedom**: Are there cycles in wait-for dependencies? (cycle detection)

**Proof.** All questions reduce to standard graph algorithms on finite G_ρ constructed from Spec. All are polynomial-time decidable. ∎

**Engineering consequence:** Routing correctness is **statically verifiable** before runtime.

---

**Definition 133** (Verified routing specification)  [§8.8.4 · Phase 8]

A routing specification is **verified** if compile-time analysis confirms:
- ✓ Acyclicity (guarantees deadlock-freedom)
- ✓ Bounded fanout (guarantees finite resource usage per event)
- ✓ Bounded depth (guarantees finite worst-case latency)
- ✓ Type compatibility (payload transforms preserve types)

---

## 8.9 Integration with Observer Complex

**Definition 134** (Routed observer complex)  [§8.9.1 · Phase 8]

A **routed observer complex** generalizes the two-timeline observer to arbitrary timeline graphs:

$$\mathcal{O}_\rho := (\mathcal{T}, \{\Omega_T\}_{T \in \mathcal{T}}, \{\mathcal{C}_T\}_{T \in \mathcal{T}}, \rho, \{\Gamma_T\}_{T \in \mathcal{T}})$$

**Components:**
- Timeline set 𝒯 with individual radix oracles Ω_T and context spaces 𝒞_T
- Routing function ρ coupling them
- Context evolution rules Γ_T for each timeline

**Generalization:** Two-timeline observer (A, B; σ) embeds as special case (Theorem 56).

---

**Theorem 56** (Observer complex as special case of routing)  [§8.9.2 · Phase 8]

The classical two-timeline observer complex (A, B; σ) is equivalent to a routed observer complex with:

- 𝒯 = {A, B, I} (interpreter timeline)
- ρ(I, step_k, TICK, _) = {(σ(k), ROOT, COPY, id)} where σ(k) ∈ {A, B}
- Static schedule σ determines which timeline I routes to at each step

**Proof.** Interpreter I ticks through schedule σ. At each tick k, routing sends execution to exactly one constituent timeline (A or B) determined by σ(k). Return edges route back to I for next schedule step. Structure matches observer complex definition. ∎

---

**Theorem 57** (Residual payload as junction accumulation)  [§8.9.3 · Phase 8]

In a routed observer complex, the residual payload from A to B is:

$$\text{payload}_{A \to B}(t) = \sum_{(A, s_A, B, s_B) \in \mathcal{J}} \text{undelivered}(A, s_A, t)$$

where undelivered(A, s_A, t) is the residue at A-to-B junction s_A not yet processed by B at time t.

**Proof.** Payload exists when A generates overflow but injection queue at B hasn't processed it yet. Sum over all A-to-B junctions gives total undelivered payload. ∎

**Interpretation:** Residual is precisely the "in-flight" information between timelines.

---

## 8.10 Concrete Examples

### Example 2: Multi-Timeline RTOS Architecture  [§8.10.1 · Phase 8]

**System design:**
```
Timeline FLIGHT: ω = 1000 (1ms resolution), depth 3
Timeline SENSORS: ω adaptive (100-1000 based on data rate), depth 2
Timeline RADIO: ω = 100 (10ms resolution), depth 4
Timeline LOGGER: ω = 10 (100ms resolution), depth 2
```

**Routing specification:**
```
(SENSORS, IMU_READY, OVERFLOW) -> (FLIGHT, IMU_UPDATE, COPY, latest_reading)
(RADIO, RX_COMPLETE, SIGNAL) -> (FLIGHT, CMD_UPDATE, COPY, extract_control)
(RADIO, RX_COMPLETE, SIGNAL) -> (SENSORS, CALIBRATE, PARTIAL(cal_data), extract_cal)
(FLIGHT, LOG_REQUEST, EVENT) -> (LOGGER, APPEND, COPY, format_log)
```

**Timing analysis:**
- Routing depth D = 2 (longest path: RADIO → FLIGHT → LOGGER)
- From Theorem 53: Total latency ≤ Σ_layers max_per_layer(Cost_T + Cost_ρ)
- All parameters known at compile time → provable <5ms worst case

**Comparison to traditional RTOS:** No shared clock needed, heterogeneous rates native, formally verified timing.

---

### Example 3: Interrupt as Timeline Injection  [§8.10.2 · Phase 8]

**Traditional interrupt model:**
```
CPU executing normally
→ GPIO pin changes (async)
→ Save context
→ Jump to ISR
→ Execute handler
→ Restore context
→ Resume
```

**Multi-timeline model:**
```
CPU: Timeline with ω_CPU at cylinder c_current
GPIO: Timeline with ω_GPIO (event-driven, mostly dormant)

GPIO event occurs:
  - GPIO timeline ticks
  - Overflow generates residue (pin state)
  - Routing: ρ(GPIO, ANY, CPU, ISR_ENTRY) with COPY transfer
  - Injection: CPU receives payload at ISR_ENTRY cylinder
  - CPU processes injection (ISR code)
  - CPU continues with modified state
```

**Advantages:**
- No special "interrupt context" switching overhead
- Timing is just routing latency (provable via Theorem 53)
- Compositional: can add new interrupt sources without global analysis
- Deadlock-free if routing graph is acyclic (checkable)

---

### Example 4: Dynamic Task Spawning  [§8.10.3 · Phase 8]

**Scenario:** Main timeline creates worker tasks dynamically.

**Routing rules:**
```
(MAIN, FORK_POINT, CREATE_TASK) -> SPAWN(ω_worker, τ_initial)
  - Creates new timeline T_worker
  - Initializes with ω_worker and state τ_initial
  - Adds routing: (T_worker, DONE, MAIN, JOIN_POINT, TERMINATE, φ_result)

When worker completes:
  - (T_worker, DONE, SIGNAL) triggers TERMINATE transfer
  - Final residue routed to (MAIN, JOIN_POINT)
  - T_worker destroyed, resources reclaimed
```

**Bounded spawn:** If system limits to max 8 concurrent workers:
- N_max = 1 + 8 = 9 total timelines
- Theorem 54 gives global bound: Latency ≤ 9 · D_max · C_max

---

## 8.Summary: Phase 8 Proved Results

**Proposition 110** (Injection preserves CSU). Cylinder-local injection into CSU timeline maintains CSU property.  [P8.1 · Phase 8]

**Proposition 111** (Acyclic routing ⟹ deadlock-free). Acyclic routing with liveness and bounded queues prevents deadlock.  [P8.2 · Phase 8]

**Proposition 112** (Finite depth under acyclicity). Finite acyclic routing graph has bounded routing depth.  [P8.3 · Phase 8]

**Proposition 113** (Composite timing bound). Total latency bounded by sum over layers of per-layer maximum costs.  [P8.4 · Phase 8]

**Proposition 114** (Static routing compile-time bound). Static routing with bounded parameters yields compile-time computable latency bound.  [P8.5 · Phase 8]

**Proposition 115** (Bounded spawn timing preservation). Bounded spawn count preserves global timing bounds.  [P8.6 · Phase 8]

**Proposition 116** (Multicast-join duality). Multicast fanout has dual synchronization join if paths reconverge.  [P8.7 · Phase 8]

**Proposition 117** (Observer complex embedding). Classical two-timeline observer complex embeds in routed multi-timeline framework.  [P8.8 · Phase 8]

**Proposition 118** (Compile-time verification). Routing properties (acyclicity, fanout, depth, deadlock) are decidable from specification.  [P8.9 · Phase 8]

**Proposition 119** (Residual as undelivered accumulation). Payload equals sum of undelivered residue at junctions.  [P8.10 · Phase 8]

---

## Cross-Phase Integration

### Dependency Chain Summary

```
Phase 5 (Variable ω, SU condition)
    ├─→ Phase 6 (Custom δ_ω design)
    │       ↓
    ├─→ Phase 7 (Context-dependent Ω(s,c))
    │       ↓
    └─→ Phase 8 (Multi-timeline routing ρ)
```

### Key Theorems Building on Each Other

- **P5.4** (Odometer bijection under SU) enables **P6.1** (ultrametric properties)
- **P6.7** (Locality under custom metrics) enables **P8.5** (compile-time bounds)
- **P7.2** (Lazy-eager equivalence) enables efficient **P8** implementations
- **P8.2** (Deadlock-freedom) relies on graph structure from **P8.9** (decidability)

---

## Applications Enabled by Phases 6-8

### 1. Formally Verified Real-Time Systems
- **Phase 6**: Design ω for cache-optimal locality
- **Phase 7**: Context-adaptive task priorities via Ω(s, system_state)
- **Phase 8**: Interrupt handling via timeline routing, compile-time timing proofs

**Target:** Safety-critical embedded systems (aviation, automotive, medical)

---

### 2. Adaptive Database Structures
- **Phase 6**: Ultrametric reflects query access costs, not key distance
- **Phase 7**: Index structure adapts via context evolution Γ based on workload
- **Phase 8**: Query routing through multi-index timelines

**Target:** High-performance OLTP/OLAP systems

---

### 3. Heterogeneous Distributed Coordination
- **Phase 6**: Each subsystem has its own metric (production rate, quality constraints)
- **Phase 7**: Subsystem structure adapts to resource availability
- **Phase 8**: Observer complex handles incommensurable production timelines

**Target:** Manufacturing, supply chain, IoT coordination

---

### 4. Molecular/Biological Computing
- **Phase 6**: Ultrametric reflects chemical significance (codon structure, functional domains)
- **Phase 7**: Structure adapts to thermodynamic context (ATP, pH, temperature)
- **Phase 8**: Reaction pathways as timelines with chemical routing

**Target:** Synthetic biology, DNA computing, cellular simulation

---

## Novel Contributions Summary

### What Phase 6 Adds:
- **Ultrametric design as inverse problem** (given desired properties, find ω)
- **Spectrum of metrics on same space** (Spec($\widehat{\mathcal{R}}$) as design space)
- **Realizability characterization** (which ultrametrics are achievable)

### What Phase 7 Adds:
- **Context-dependent radix oracle** Ω(s, c) (structure depends on external state)
- **Lazy materialization equivalence** (representation independence)
- **Stateful evolution** (structure changes over time via Γ)

### What Phase 8 Adds:
- **Multi-timeline routing** as computational primitive (not special case)
- **Interrupts as parallel timelines** (not external disruptions)
- **Compile-time verification** of timing and deadlock properties
- **Spawn/terminate dynamics** (dynamic timeline creation/destruction)

---

## Theoretical Novelty Assessment

### Existing in Literature:
- p-adic ultrametrics (fixed p, single metric)
- Mixed-radix number systems (fixed sequences, engineering applications)
- Process algebras (concurrent composition, no hierarchy)
- Symbolic dynamics (shift spaces, uniform structure)

### Novel Here:
1. **Engineered ultrametrics via variable radix** (not in p-adic theory)
2. **Context-dependent adaptive structure** (not in standard mixed-radix)
3. **Multi-timeline overflow routing as primitive** (not in process algebras)
4. **Complete substrate-independent framework** combining all three

**Assessment:** Individual concepts have precedents; this **synthesis and application domain are novel**.

---

## Open Research Questions

### From Phase 6:
1. **Optimal ultrametric design:** Given locality objectives, algorithmically find optimal ω
2. **Complete realizability classification:** Characterize Spec($\widehat{\mathcal{R}}$) fully
3. **Metric learning:** Learn ω from example distance judgments
4. **Multi-metric stability:** When do different δ_ω interfere/cooperate?

### From Phase 7:
1. **Optimal context design:** Find (Ω, 𝒞, Γ) achieving performance/resource objectives
2. **Oracle learning:** Learn Ω from experience or observation
3. **Multi-agent negotiation:** Game-theoretic context composition
4. **Physical realizability:** Which (Ω, 𝒞, Γ) can be implemented in specific substrates?

### From Phase 8:
1. **Optimal routing synthesis:** Given timing constraints, find minimal routing graph
2. **Dynamic routing:** Allow ρ to evolve while preserving bounds
3. **Fault-tolerant routing:** Handle timeline failures without global deadlock
4. **Distributed implementation:** Map abstract routing to physical network topology
5. **Probabilistic routing:** Stochastic ρ with expected-time analysis

---

## Relation to Original Motivation

### Substrate-Independent Polycompute

The complete framework (Phases 1-8) provides:

**Mathematical Foundation:**
- Algebraic/combinatorial (not geometric) → no physics dependency
- Discrete (not continuous) → directly computational
- Compositional (operators form algebras) → modular design

**Computational Semantics:**
- Random access, streaming, or oracle-driven modes
- Lazy or eager materialization (representation-independent)
- Compile-time verification (timing, deadlock, resource bounds)

**Heterogeneous Composition:**
- Incommensurable timelines (no forced common clock)
- Residual payloads (explicit information that doesn't translate)
- Multi-metric structure (each subsystem has its own δ_ω)

**Applicable To:**
- Molecular computing (DNA transcription, protein folding timelines)
- Silicon (CPU, DMA, peripherals as timelines)
- Biological systems (metabolic pathways, regulatory networks)
- Economic systems (agents with incomparable utilities)
- AI architectures (hierarchical options, multi-timescale learning)

---

## Conceptual Clarifications

### Cylinders Are Algebraic, Not Geometric

**What cylinders ARE:**
- Finite prefix constraint sets (combinatorial)
- Clopen sets in ultrametric topology (topological)
- Boolean lattice elements (algebraic)
- Information neighborhoods (information-theoretic)

**What cylinders are NOT:**
- Smooth manifolds
- Riemannian objects with curvature
- Requiring calculus or differential structure

**Correct analogy:** p-adic integers ℤ_p (discrete, algebraic, ultrametric) NOT Euclidean space ℝ^n (continuous, metric, geometric).

---

### Three Operational Modes of Same Algebra

The cylinder/prefix formalism supports multiple computational interpretations:

| Mode | Time Model | Memory Access | Structure Discovery | Use Case |
|------|-----------|---------------|---------------------|----------|
| **Random Access** | Absolute coordinates | Full DAG | Pre-allocated | General computation |
| **Eternal Advance** | Causal stream | Forward-only | Pre-defined or lazy | Streaming systems |
| **External Oracle** | Either/both | On-demand | Fully dynamic | Adaptive systems |

**Same mathematical structure, different execution strategies.**

---

## Implementation Roadmap

### Rust Implementation Extensions (Building on Phases 1-5 MVP)

1. **Context-dependent oracle** (Phase 7):
   ```rust
   trait ExtendedRadixOracle<C> {
       fn radix(&self, prefix: &[usize], context: &C) -> usize;
   }
   ```

2. **Multi-timeline orchestrator** (Phase 8):
   ```rust
   struct MultiTimeline<T> {
       timelines: HashMap<TimelineId, DualMachineState<T>>,
       routing: RoutingTable,
       injection_queues: HashMap<TimelineId, Vec<Injection<T>>>,
   }
   ```

3. **Compile-time routing verification** (Phase 8):
   ```rust
   const ROUTING_SPEC: RoutingSpec = routing_spec! {
       (CPU, SYSCALL, OVERFLOW) => (KERNEL, ENTRY, TOTAL, extract_args);
       // ... compiled at build time
   };

   // Macro performs compile-time acyclicity check
   ```

### Killer Application Prototype: Formally Verified RTOS

**Target hardware:** ARM Cortex-M4 (STM32F4 dev board)

**Tasks (timelines):**
- Flight control: 1ms period, ω = 1000
- Navigation: 10ms period, ω = 100
- Radio: 20ms period, ω = 50
- Telemetry: 1s period, ω = 10

**Routing:**
- IMU interrupt → flight control (COPY transfer)
- Radio RX → flight + navigation (multicast)
- Flight urgent → radio TX (spawn response timeline)

**Deliverable:**
- Working unikernel binary
- Coq/Lean proof of <1ms worst-case for critical path
- Oscilloscope measurements validating mathematical proof
- Comparison to FreeRTOS showing formal guarantees

**Timeline:** 6-12 months for full prototype with verification

---

## Future Phases (Identified, Not Yet Formalized)

### Phase 9: Optimal Structure Design (Tentative)
- Algorithms for finding optimal ω, Ω, ρ given objectives
- Machine learning approaches to structure discovery
- Multi-objective optimization (latency vs resource vs locality)

### Phase 10: Physical Realizability (Tentative)
- Mapping abstract timelines to physical substrates
- Thermodynamic constraints on molecular implementations
- Error models and fault tolerance
- Measurement and observability theory

---

## Conclusion: What Phases 6-8 Achieve

**Theoretical contributions:**
- Formalized custom ultrametric design (Phase 6)
- Formalized context-dependent adaptive structure (Phase 7)
- Formalized multi-timeline asynchronous composition (Phase 8)

**Computational capabilities:**
- Engineer information locality via radix choice
- Adapt structure to runtime conditions
- Compose heterogeneous timelines with provable properties

**Practical impact:**
- Enables formally verified RTOS with heterogeneous periods
- Enables adaptive data structures with provable performance
- Provides substrate-independent framework for polycompute

**Mathematical rigor:**
- 24 theorems across three phases (P6.1-P6.7, P7.1-P7.8, P8.1-P8.10)
- All with proofs (varying rigor - some sketched, some complete)
- Builds systematically on Phase 1-5 foundations

**Status:** Theory is coherent and novel. Ready for:
- Rigorous proof formalization (Coq/Lean)
- Rust implementation (extending current MVP)
- Experimental validation (RTOS prototype)
- Publication (foundational CS venues)

---

**End of Phases 6-8 Extension**
**Document Version:** 1.0
**Integration Status:** Ready to append to fdrs.md after Phase 5
**Next:** Implement in code, validate experimentally, publish formally

---

## Phase 9 — Extended Base Support: Base-0 (Wall) and Base-1 (Wire)

### Motivation

The original FDRS formalism assumes all radices b_i ≥ 2. This phase extends the base domain to include:

- **Base-0 (Wall/Barrier):** Uninstantiated positions with no representable digit. These form a "sea of base-0" within which the active radix sequence lives.
- **Base-1 (Wire):** Positions with exactly one representable digit (0). Carry propagates through without being absorbed.

This extension enables:
- Dynamic growth of the radix sequence ("awakening" positions)
- Transparent carry routing through wire segments
- Barriers that partition the state space

---

## 9.1 Extended Base Domain

### Definition 135 (Extended radix sequence)  [§9.1.1 · Phase 9]

A **generalized radix sequence** is b = (b_i)_{i≥0} with b_i ∈ ℕ := {0, 1, 2, 3, ...}.

### Definition 136 (Extended digit alphabets)  [§9.1.2 · Phase 9]

The digit alphabet at position i is:
```
D_i := { ∅,                   if b_i = 0  (no representable symbol)
       { {0},                 if b_i = 1  (forced single value)
       { {0, 1, ..., b_i-1},  if b_i ≥ 2  (standard case)
```

### Definition 137 (Active and capacity index sets)  [§9.1.3 · Phase 9]

For a generalized radix sequence b:
- **Active index set:** I_active := {i ≥ 0 : b_i ≥ 1}
- **Capacity index set:** I_capacity := {i ≥ 0 : b_i ≥ 2}

### Definition 138 (Effective base)  [§9.1.4 · Phase 9]

Define the effective base function:
```
b̃_i := max(b_i, 1)
```

This ensures place value products remain well-defined and monotone.

---

## 9.2 Extended Place Values

### Definition 139 (Generalized cumulative radix products)  [§9.2.1 · Phase 9]

For m ≥ 0, define:
```
B_m := ∏_{i=0}^{m-1} b̃_i = ∏_{i=0}^{m-1} max(b_i, 1)
```
with B_0 := 1.

### Proposition 120 (Monotonicity preserved)  [§9.2.2 · Phase 9]

For all m ≥ 0: B_m ≥ 1 and B_{m+1} ≥ B_m.

**Proof.** Since b̃_i ≥ 1 for all i, all products are ≥ 1. Also B_{m+1} = B_m · b̃_m ≥ B_m · 1 = B_m. ∎

### Proposition 121 (Recovery of original)  [§9.2.3 · Phase 9]

When all b_i ≥ 2, this definition coincides with the original B_m = ∏_{i<m} b_i.

---

## 9.3 Extended Encode/Decode

### Definition 140 (Representable subspace)  [§9.3.1 · Phase 9]

The **representable subspace** is:
```
R^{(k)}_rep := ∏_{i ∈ I_active, i ≤ k} D_i
```

### Definition 141 (Extended decode)  [§9.3.2 · Phase 9]

For τ ∈ R^{(k)}_rep, decode is:
```
dec_k(τ) := Σ_{i ∈ I_capacity, i ≤ k} d_i · B_i
```

Note: Wire positions (b_i = 1) have d_i = 0, contributing 0 to the sum.

### Definition 142 (Extended encode)  [§9.3.3 · Phase 9]

For n in the capacity range, encode produces digits:
- Wall positions: placeholder 0 (or ⊥)
- Wire positions: forced 0
- Standard positions: standard division algorithm

### Proposition 122 (Bijection on representable subspace)  [§9.3.4 · Phase 9]

decode is a bijection from R^{(k)}_rep to {0, 1, ..., C-1} where:
```
C := ∏_{i ∈ I_capacity, i ≤ k} b_i
```
is the **capacity** of the radix system.

---

## 9.4 Extended Tick Semantics

### Definition 143 (Tick with extended bases)  [§9.4.1 · Phase 9]

For τ in the representable subspace, Tick(τ) follows:

1. **Base-0 (Wall):** Carry cannot enter. If carry reaches a wall, the clock **wraps** (all prior positions reset to 0).

2. **Base-1 (Wire):** Carry propagates through unchanged. Digit stays 0.

3. **Base-≥2 (Standard):** Normal carry absorption. If d_i + 1 ≥ b_i, reset to 0 and propagate carry.

### Theorem 58 (Wire transparency)  [§9.4.2 · Phase 9]

Let W be a contiguous run of base-1 positions between capacity positions. Inserting W does not change the decoded successor relationship:
```
dec(Tick(τ)) = (dec(τ) + 1) mod C
```
where C is the capacity.

**Proof.** Base-1 positions contribute factor 1 to both place values and capacity. Carry propagates through as if they didn't exist for state purposes. ∎

### Theorem 59 (Barrier wrap)  [§9.4.3 · Phase 9]

When carry reaches a base-0 position at index j, all positions i < j reset to 0 and the operation returns with wrap=true.

**Proof.** By Definition 143, base-0 is impenetrable. The only valid behavior is to wrap the active segment. ∎

---

## 9.5 Cylinder Sets with Extended Bases

### Proposition 123 (Sigma-algebra contribution by base type)  [§9.5.1 · Phase 9]

At position i:
- Base-0: Contributes trivial σ-algebra {∅, Ω}
- Base-1: Contributes trivial σ-algebra {∅, {0}}
- Base-≥2: Contributes full finite σ-algebra on b_i atoms

### Proposition 124 (Extended β_ω(s))  [§9.5.2 · Phase 9]

For prefix s of length |s| = L:
```
β_ω(s) := ∏_{i=0}^{L-1} b̃_ω(s_{<i})
```

Base-1 and base-0 positions contribute factor 1.

### Proposition 125 (Arithmetic-cylinder property extension)  [§9.5.3 · Phase 9]

The condition "q | β_ω(s)" reduces to:
```
q divides ∏_{i<L, b_ω(s_{<i}) ≥ 2} b_ω(s_{<i})
```

Only capacity positions contribute to divisibility conditions.

---

## 9.6 Instantiation (Stub)

### Definition 144 (Instantiation API)  [§9.6.1 · Phase 9]

The operation `instantiate(position, new_base)` converts a base-0 position to base new_base ≥ 1:
- Updates the radix sequence
- Initializes the digit to 0
- Recomputes block sizes

### Remark 9.6.2 (Triggering mechanism)

The **when** and **why** of instantiation is deferred to the context-dependent radix law:
```
b_{ω,c}: Σ* × C → {0, 1, 2, ...}
```

When context c evolves such that b_{ω,c}(s) changes from 0 to k≥1, position |s| awakens. This mechanism integrates with Phase 7 (context-dependent radix).

---

## 9.7 Implementation Summary

### Rust Types

```rust
pub enum ExtendedBase {
    Wall,           // Base-0
    Wire,           // Base-1
    Standard(usize) // Base ≥ 2
}

pub struct ExtendedMixedRadix {
    bases: Vec<ExtendedBase>,
    blocks: Vec<usize>,        // Using effective bases
    representable_size: usize,
}
```

### Key Properties Verified by Tests

1. **Wire transparency:** decode(Tick(τ)) = (decode(τ) + 1) mod C regardless of wire count
2. **Barrier wrap:** Carry hitting base-0 causes wrap of active segment
3. **Capacity invariance:** Wire insertion doesn't change capacity
4. **Monotone blocks:** B_{m+1} ≥ B_m always
5. **Bijection:** encode/decode are mutual inverses on representable subspace

### Files

- `src/radix/extended.rs` — ExtendedBase, ExtendedMixedRadix types
- `src/radix/extended_codec.rs` — Extended encode/decode
- `src/radix/extended_tick.rs` — Extended Tick with wire/barrier semantics
- `src/radix/instantiate.rs` — Instantiation API (stub for triggering logic)

---

## 9.8 Spatial Thermometer Encoding

The algebraic digit `d ∈ {0, ..., b-1}` is abstract. A **spatial thermometer encoding** physicalizes it as a one-hot token sliding along a chain of cells, with a movable wall that truncates the chain to set the active radix.

### Definition 145 (Spatial digit capacity)  [§9.8.1 · Phase 9]

A **spatial digit** with capacity M is a one-hot token on a chain of M cells:

```
SpatialDigit(M) := { tokenPos ∈ {0, ..., M-1} }
```

This is isomorphic to `Fin M` and, when restricted to the active zone `[0, b)`, to `ExtendedDigit b`.

### Definition 146 (Spatial tick)  [§9.8.2 · Phase 9]

Given a spatial digit with token at position `p` in the active zone `[0, b)` where `1 ≤ b ≤ M`:

- **No carry:** If `p + 1 < b`, advance the token to `p + 1`. Return carry = false.
- **Carry (wrap):** If `p + 1 = b`, wrap the token to position 0. Return carry = true.

This is the 1-Lipschitz spatial analogue of the algebraic digit increment.

### Definition 147 (Spatial radix wall)  [§9.8.3 · Phase 9]

A **radix wall** at position `b ≤ M` restricts the active zone to `[0, b)`:

- `b = 0` → **Wall** (Base-0): no active cells, digit is uninhabited.
- `b = 1` → **Wire** (Base-1): one cell, token fixed at 0.
- `b ≥ 2` → **Standard**: full digit with `b` states.

Moving the wall implements `instantiate` (Definition 144): setting `b` from 0 to `k ≥ 1` awakens the position.

### Theorem 60 (Spatial-algebraic isomorphism)  [§9.8.4 · Phase 9]

Let `proj : SpatialDigit(M) → ExtendedDigit(b)` project the token position into the active zone. The following diagram commutes:

```
SpatialDigit(M) --spatialTick--> SpatialDigit(M) × Bool
      |                                |
    proj                          proj × id
      |                                |
      v                                v
ExtendedDigit(b) --algebraicTick--> ExtendedDigit(b) × Bool
```

**Proof.** Case split on whether the token wraps. In both cases, the projected position undergoes the same increment-or-wrap as the algebraic tick. ∎

---

## 9.9 Carry-Route Unification (Fractal Unification)

Standard arithmetic views carry propagation as a recursive digit-by-digit process: tick digit 0, if it wraps then tick digit 1, etc. Phase 8 views inter-timeline communication as event routing: OVERFLOW at timeline A triggers INJECT at timeline B. This section proves these are the same mechanism.

### Definition 148 (Carry event classification)  [§9.9.1 · Phase 9]

The Boolean carry output of a single-digit `spatialTick` is classified as a **carry event**:

- `carry = true` → `CarryEvent.OVERFLOW` (digit wrapped, must route carry)
- `carry = false` → `CarryEvent.QUIESCENT` (digit absorbed the tick)

This bridges the arithmetic carry flag to the Phase 8 event vocabulary (Definition 111).

### Definition 149 (Carry-as-route)  [§9.9.2 · Phase 9]

The **odometer routing rule**: when `SpatialDigit i` produces an OVERFLOW, route an INJECT payload to `SpatialDigit (i+1)`. This is a deterministic, acyclic routing table with exactly one rule per position:

```
carryRouteDecision(OVERFLOW) = true    (propagate to next digit)
carryRouteDecision(QUIESCENT) = false  (stop)
```

The transfer type is always `TransferType.TOTAL` (Definition 113): the source digit resets to 0 and emits one unit of carry as residue.

### Definition 150 (Unified spatial tick)  [§9.9.3 · Phase 9]

The **event-driven cylinder tick**: instead of recursive arithmetic, apply `spatialTick` to digit 0, classify the carry via `classifyCarry`, consult `carryRouteDecision`, and propagate if routed. The routing is deterministic and sequential: at most one event is live at any time.

### Theorem 61 (Fractal unification — carry is overflow route)  [§9.9.4 · Phase 9]

For any spatial cylinder `C` with `k` digits:

```
recursiveCarryTick(C, pos, carry_in) = unifiedSpatialTick(C, pos, carry_in)
```

That is, applying standard recursive carry propagation to a cylinder is strictly equal to applying the queue-based event routing tick.

**Proof.** By well-founded induction on `k - pos`. The key lemma is `carryRouteDecision_eq_carry`: `carryRouteDecision(classifyCarry(c)) = c` for all `c : Bool`. At each step, both functions apply `spatialTick` to the same digit, construct the same updated cylinder, and recurse with the same carry flag — one passes it directly, the other routes it through classification and decision, but the round-trip is the identity. ∎

**Interpretation.** Each digit position is a timeline. Arithmetic carry is an OVERFLOW event routed between adjacent timelines. Addition is local routing.

---

**End of Phase 9: Extended Base Support**
**Status:** Implemented and tested (44 new tests, all passing)

---

## Phase 10 - Base-Zero Sea Dynamics (Deterministic)

### Motivation

Phase 9 introduced base-0 walls and base-1 wires as extended radix states. Phase 10 adds an explicit **deterministic substrate dynamics** in which:

- base-0 is representational potential,
- base-1 is instantiated occupancy,
- arithmetic structure emerges from controlled creation and reversion events.

This phase is deterministic only. Stochastic variants are deferred.

---

## 10.1 Substrate Model

### Definition 151 (Base-zero sea)  [§10.1.1 · Phase 10]

A **base-zero sea** is a countable graph `Sea = (V, E)` together with an occupancy map
```
σ : V -> {0, 1}
```
where:

- `σ(v) = 0` means `v` is uninstantiated base-zero potential,
- `σ(v) = 1` means `v` is an instantiated base-one site.

### Definition 152 (Observation windows and radix walls)  [§10.1.2 · Phase 10]

An **observation profile** is a finite family of ordered windows
```
W_0, W_1, ..., W_{k-1},   W_i = (v_{i,0}, ..., v_{i,M_i-1})
```
with associated wall positions `b_i` satisfying `0 <= b_i <= M_i`.

Each window induces:

- **Wall** if `b_i = 0`,
- **Wire** if `b_i = 1`,
- **Standard digit** if `b_i >= 2`.

### Definition 153 (Legacy thread)  [§10.1.3 · Phase 10]

For each window `W_i`, a **legacy thread** `L_i(t)` at step `t` is the ordered list of currently instantiated active sites in `[0, b_i)`, ordered by instantiation time.

Its length
```
ell_i(t) := |L_i(t)|
```
is the local persistent occupancy depth.

### Definition 154 (Deterministic creation step)  [§10.1.4 · Phase 10]

A **creation selector** is a deterministic function
```
CreateTarget : State x Nat -> Option V
```
such that when `CreateTarget(state, t) = some v`:

- `σ(v) = 0`,
- `v` is adjacent to the current active frontier (1-Lipschitz locality),
- updating sets `σ(v) := 1`.

If `CreateTarget` returns `none`, no creation occurs.

---

## 10.2 Deterministic Reversion Dynamics

### Definition 155 (Consumption target rule)  [§10.2.1 · Phase 10]

A **consumption target rule** is a deterministic function
```
ConsumeTarget : (L_i(t), t) -> Option Nat
```
selecting which thread index to revert (if any), e.g.:

- `Oldest`,
- `Newest`,
- `Index(k)`,
- `Pattern(f)` (deterministic index pattern).

### Definition 156 (Consumption schedule)  [§10.2.2 · Phase 10]

A **consumption schedule** is a deterministic trigger
```
ConsumeSchedule : Nat -> Bool
```
where `ConsumeSchedule(t) = true` means a consumption attempt occurs at step `t`.

### Definition 157 (Unified deterministic sea tick)  [§10.2.3 · Phase 10]

Given `(CreateTarget, ConsumeTarget, ConsumeSchedule)`, one global step
```
SeaTick : State x Nat -> State
```
performs, in order:

1. deterministic creation (Definition 154),
2. if `ConsumeSchedule(t) = true`, deterministic reversion using Definition 155.

Reversion sets the chosen instantiated site back to `σ(v) := 0`.

---

## 10.3 Structural Properties

### Proposition 126 (Deterministic totality)  [§10.3.1 · Phase 10]

For fixed `(CreateTarget, ConsumeTarget, ConsumeSchedule)`, `SeaTick` is a deterministic state transition relation:
```
State_{t+1} = SeaTick(State_t, t)
```
with unique successor for each `t`.

### Proposition 127 (Closure and validity invariants)  [§10.3.2 · Phase 10]

If `State_t` is valid, then `State_{t+1}` is valid, where validity means:

- occupancy remains boolean (`σ(v) in {0,1}`),
- each `L_i(t)` contains only active-window instantiated sites,
- `L_i(t)` order is consistent with instantiation history after creation/reversion updates.

### Proposition 128 (Legacy-length balance law)  [§10.3.3 · Phase 10]

For each window `i`, there exist deterministic bits `c_i(t), r_i(t) in {0,1}` such that:
```
ell_i(t+1) = ell_i(t) + c_i(t) - r_i(t)
```
with bounds:
```
0 <= ell_i(t) <= b_i.
```

### Theorem 62 (Deterministic sea dynamics is a well-defined transition system)  [§10.3.4 · Phase 10]

The tuple
```
(State, SeaTick, Valid)
```
forms a well-defined deterministic transition system preserving validity at every step.

**Proof.** Combine Proposition 126 (unique successor) and Proposition 127 (invariant preservation). Proposition 128 gives the explicit per-window conservation/update law. ∎

---

## 10.4 Projection to Extended Arithmetic

### Definition 158 (Window-to-digit projection)  [§10.4.1 · Phase 10]

Fix an observation profile `(W_i, b_i)_{i<k}`. The projection
```
Pi : State -> SpatialCylinder
```
maps each window `W_i` to a spatial digit state by reading its active occupancy pattern and interpreting it as token position / wrap state in the corresponding Phase 9 cylinder.

### Definition 159 (Phase-9 constraint profile)  [§10.4.2 · Phase 10]

The **Phase-9 constraint profile** is the deterministic parameter choice:

1. fixed windows and fixed walls `(W_i, b_i)`,
2. carry routing policy = nearest-right overflow routing,
3. `ConsumeSchedule(t) = false` for all `t` (consumption disabled),
4. creation restricted to the active carry front.

### Theorem 63 (Phase 9 is a special case of Phase 10)  [§10.4.3 · Phase 10]

Under Definition 159, the projected Phase 10 update equals the Phase 9 unified event-driven tick:
```
Pi(SeaTick(state, t)) = unifiedSpatialTick(Pi(state), pos, carry_in)
```
for corresponding `(pos, carry_in)` encoding.

Hence:

- Theorem 61 (carry = overflow route) is recovered as a direct special case.
- Phase 9 arithmetic cylinders are deterministic emergent instances of Phase 10 sea dynamics.

**Proof.** With consumption disabled, only deterministic frontier creation remains. Under fixed walls and nearest-right overflow policy, each projected window step is exactly the same local increment-or-wrap and carry routing used in Definitions 148-150. Therefore projection commutes with update, yielding equality with `unifiedSpatialTick`; invoke Theorem 61 for recursive/event-route equivalence. ∎

---

## 10.5 Scope Note

This phase formalizes deterministic creation/reversion only. A stochastic extension may be built later by randomizing schedule or target selection, but is intentionally excluded from Phase 10.

---

## 10.6 Coupled Digit Modules in the Sea

### Definition 160 (Digit module in a base-zero sea)  [§10.6.1 · Phase 10]

A **digit module** is a deterministic subsystem
```
M_i = (V_i, N_i, I_i, D_i, C_i)
```
where:

- `V_i subseteq V` is the module vertex set in the sea graph,
- `N_i` is its internal adjacency relation (inherited from `E`),
- `I_i` is a local injection rule (creation / activation),
- `D_i` is a local conversion-decay rule (reversion / consumption),
- `C_i` is a coupling interface for transfer to/from other modules.

Modules need not be linearly ordered, contiguous, or connected.

### Definition 161 (Sustainment and resistance functional)  [§10.6.2 · Phase 10]

Fix horizon `H >= 1`. For module `M_i`, define cumulative inflow and decay:
```
In_i(t, H)  := sum_{tau=t}^{t+H-1} injected_i(tau) + coupled_in_i(tau)
Out_i(t, H) := sum_{tau=t}^{t+H-1} decayed_i(tau) + coupled_out_i(tau).
```
The **resistance functional** is
```
R_i(t, H) := In_i(t, H) - Out_i(t, H).
```
A module is **sustained on horizon H at time t** if:

1. `R_i(t, H) >= 0`, and
2. at least one observational state class of `M_i` persists through the horizon.

### Proposition 129 (Deterministic persistence criterion)  [§10.6.3 · Phase 10]

If `R_i(t, H) < 0` and no external replenishing coupling enters `M_i`, then sustained occupancy cannot increase on `[t, t+H)`.
Conversely, if `R_i(t, H) >= 0` and deterministic update invariants hold, persistence is admissible.

---

## 10.7 Emergent Base from Sustainment

### Definition 162 (Emergent effective base)  [§10.7.1 · Phase 10]

Let `Obs_i(t, H)` be the set of distinguishable sustained observational states of module `M_i` over horizon `H`.
Define the **emergent effective base**:
```
b_i^eff(t, H) := |Obs_i(t, H)|.
```

Interpretation:

- `b_i^eff = 0` means no sustained digit state (wall-like regime),
- `b_i^eff = 1` means exactly one sustained state (wire-like regime),
- `b_i^eff >= 2` means a genuine multi-state digit.

So base is not primitive; it is a sustained-activation capacity against decay.

### Proposition 130 (Resistance-base monotonicity under fixed observation resolution)  [§10.7.2 · Phase 10]

Under fixed observation granularity, increasing net resistance (larger admissible `R_i`) cannot decrease `b_i^eff` unless state classes collapse by coupling/identification.

---

## 10.8 Arbitrary Coupling and Nonlinear Digit Topologies

### Definition 163 (Coupled-digit sea network)  [§10.8.1 · Phase 10]

A **coupled-digit sea network** is a directed module graph
```
Gamma = (M, K)
```
where nodes are digit modules `M_i` (Definition 160) and
```
K_{i -> j}
```
is a deterministic coupling transfer map between modules.

This allows:

- multiple disconnected digit spaces,
- asynchronous creation/decay rates,
- nonlocal couplings between arbitrarily chosen digit modules.

All updates remain deterministic if each `I_i, D_i, K_{i -> j}` is deterministic.

---

## 10.9 Linear Mixed-Radix as Special Case

### Theorem 64 (Classical mixed-radix line as a single-lineage special case)  [§10.9.1 · Phase 10]

*(Faithful, formalized form. This supersedes the earlier prose statement, whose Lean placeholder `classicalMixedRadixLine` had a vacuous conclusion (`… → True` plus a restated hypothesis); the genuine projection-equivalence below is now machine-checked, 0 sorries.)*

The abstract coupled-digit network (`CoupledDigitNetwork`, Definition 163) carries no dynamic digit state, so it admits no step to project. We therefore bundle the chain constraints with the data the abstract layer lacks — per-module active radix `b i`, cell-chain capacity `M i` (with `1 ≤ b i ≤ M i`), and a digit-vector state `digits i` — into a **linear-chain machine** `LinearChain`, mirroring how `SeaState` carries the occupancy that `seaTick` advances. Its step `linearChainStep` is a single mixed-radix `+1`: increment-or-overflow with nearest-right carry (`chainIncrement`). The projection `Π_chain` (`chainToCylinder`) sends each module's digit to a one-hot Phase 9 spatial token position — the analogue of `windowToDigitProjection` (Theorem 63).

**Theorem.** Under input active-zone validity (`∀ i, digits i < b i`), the projected chain step equals the Phase 9 unified spatial tick:
```
Π_chain (linearChainStep lc) = (unifiedSpatialTick … (Π_chain lc) … 0 true).1
```
That is, the abstract increment-or-overflow on the coupled-digit chain **commutes with the projection** into the proven spatial-tick (odometer) semantics. Output validity and the `cylinderValid` premise are *derived*, not assumed.

**Lean.** `linearChain_projectsTo_odometer` (`FdrsFormal/Modes/BaseZeroSea/LinearChain.lean`).

**Proof.** Induct on `n − pos` (`unifiedSpatialTick_tokenPos_eq`): when the cylinder projects the digit vector, the spatial tick's token positions track `chainIncrement` position-by-position. The carry step is closed by the route-decision identity `carryRouteDecision_eq_carry` (Theorem 61, carry = overflow routing), the advance case collapsing via `unifiedSpatialTick_false`; validity is preserved by `linearChainStep_valid` (the analogue of `cylinderValid_update`). This is exactly Theorem 63 (`phase9_specialCase`) one layer up. ∎

This single-lineage odometer is the bridge into Phase 13, where its place value `B_L` is generalized to the *generated* gauge `q_n` (§13.2) and its overflow rate `1/B_L` to the carry frequency `1/q_n` (§13.4).

---

**End of Phase 10: Base-Zero Sea Dynamics (Deterministic)**
**Status:** Extended specification with deterministic coupled-digit sustainment framework

---

## Phase 11 - Digit-Conditional Signal Analysis

### Motivation

Phases 2–4 established multiresolution analysis on mixed-radix function spaces: block projections `P_L`, detail operators `Δ_L`, the contrast basis, and Vilenkin–Fourier analysis. These tools completely characterize signals that are periodic or Vilenkin-measurable — functions whose structure aligns with the product filtration `F_0 ⊂ F_1 ⊂ ...` generated by the standard radix sequence.

Experiments 76–77 revealed a signal class that lives strictly *between* Vilenkin-measurable signals and noise. These **digit-conditional signals** have structure that depends on the *value* of a digit at one position to determine the relevant partition at another position. A simple example: in a base-`(6,6)` space on `I = {0,...,35}`, the signal `f(n) = 1` if `(n mod 6) mod 2 = 0` and `0` otherwise partitions `I` into groups of 2 within each coset of 6 — a structure invisible to the uniform refinement `6 → 36` but captured by a heterogeneous radix tree with branching `6 → 2`.

Phase 11 formalizes this signal class by introducing **non-stationary radix trees** — position-dependent branching structures that generalize the fixed-radix refinement of earlier phases. The phase establishes an orthogonal decomposition theorem, proves a sharp ceiling on Fourier/Vilenkin correlation, quantifies the representation gap between uniform and tree-adapted partitions, and connects tree projections back to the FDRS filtration infrastructure, proving that the Vilenkin/MRA framework of Phase 2 is a homogeneous special case.

---

## 11.1 Non-Stationary Radix Trees

### Definition 164 (Non-stationary radix tree)  [§11.1.1 · Phase 11]

Let `I` be a finite set with `N = |I|`. A **non-stationary radix tree** `T` on `I` is a finite rooted tree where:

1. The root node represents all of `I`.
2. Each internal node `v` has `r(v) ≥ 2` children.
3. Each node `v` is associated with a subset `I_v ⊆ I` (its **cell**).
4. Children of `v` partition `I_v`: if `v` has children `c_1, ..., c_{r(v)}` then `I_{c_j}` are pairwise disjoint and `⋃_j I_{c_j} = I_v`.
5. Each leaf `ℓ` has `|I_ℓ| ≥ 1`.

The tree is **position-modular** if for every internal node `v` with children `c_1, ..., c_{r(v)}`, the partition of `I_v` into `I_{c_j}` is given by position-modular grouping: elements of `I_v` (listed in canonical order) are assigned to child `j = (position within I_v) mod r(v)`.

### Definition 165 (Depth and heterogeneity)  [§11.1.2 · Phase 11]

For a non-stationary radix tree `T`:

- The **depth** of `T` is the maximum root-to-leaf path length.
- `T` is **homogeneous** if every internal node at the same depth has the same branching factor: there exist `r_0, r_1, ...` such that every node at depth `d` has `r(v) = r_d` children.
- `T` is **heterogeneous** if it is not homogeneous.

A depth-1 tree with branching `r` at the root partitions `I` into `r` equal groups. A depth-2 tree with branching `b_0` at the root and `r_j` at the `j`-th child of the root partitions `I` first into `b_0` groups, then each group `j` into `r_j` sub-groups.

### Proposition 131 (Leaf count identity)  [§11.1.3 · Phase 11]

For any non-stationary radix tree `T` on `I`:
```
|Leaves(T)| = 1 + Σ_{v internal} (r(v) - 1).
```

**Proof.** By induction on the tree structure. A single-node tree has 1 leaf and 0 internal nodes, so `|Leaves| = 1 = 1 + 0`. Replacing a leaf by an internal node with `r` children adds `r - 1` leaves and 1 internal node contributing `(r - 1)` to the sum. ∎

### Proposition 132 (Homogeneous recovery)  [§11.1.4 · Phase 11]

A non-stationary radix tree `T` of depth `d` on `I` with `|I| = N` is homogeneous with branching factors `(r_0, ..., r_{d-1})` if and only if it induces the same partition as the standard cylinder refinement of a mixed-radix system with radix sequence `(r_0, ..., r_{d-1})`.

In particular, `|Leaves(T)| = r_0 · r_1 · ... · r_{d-1}` and `|I_ℓ| = N / ∏ r_i` for every leaf `ℓ`.

**Proof.** The forward direction follows from the position-modular grouping rule applied uniformly at each depth. The converse: if `T` induces the cylinder partition of `(r_0, ..., r_{d-1})`, then by the unique factorization of the partition structure, every depth-`d` node has branching `r_d`. ∎

---

## 11.2 Orthogonal Layer Decomposition

### Definition 166 (Tree-adapted signal)  [§11.2.1 · Phase 11]

Let `T` be a non-stationary radix tree on `I` with `|I| = N`. A signal `f : I → ℝ` is **`T`-adapted** (or tree-adapted) if `f` is constant on each leaf cell of `T`:
```
∀ leaves ℓ of T, ∀ n, m ∈ I_ℓ : f(n) = f(m).
```

The space of `T`-adapted signals is denoted `H_T ⊆ ℝ^I`. Its dimension equals `|Leaves(T)|`.

### Definition 167 (Node projection and layer)  [§11.2.2 · Phase 11]

For each node `v` of `T` with children `c_1, ..., c_{r(v)}`, define:

- **Node projection** `P_v : ℝ^I → ℝ^I` as the averaging operator over `I_v`:
  ```
  (P_v f)(n) = (1/|I_v|) · Σ_{m ∈ I_v} f(m)    if n ∈ I_v
  (P_v f)(n) = 0                                    if n ∉ I_v
  ```

- **Node layer** `g_v : ℝ^I → ℝ^I` as the detail within `v` relative to its parent:
  ```
  g_v(f) = Σ_j [ (mean of f on I_{c_j}) · 1_{I_{c_j}} ] - (mean of f on I_v) · 1_{I_v}
  ```
  where `1_S` is the indicator function of set `S`.

The layer `g_v(f)` captures the variation *within* node `v` that is visible at the child level but not at the parent level — analogous to the detail operator `Δ_L` (Definition 23) but adapted to the tree structure.

### Lemma 5 (Within-node layer properties)  [§11.2.3 · Phase 11]

For each internal node `v` with children `c_1, ..., c_{r(v)}`:

1. **Mean-zero on `I_v`**: `Σ_{n ∈ I_v} g_v(f)(n) = 0`.
2. **Block-constant on children**: `g_v(f)` is constant on each `I_{c_j}`.
3. **Supported on `I_v`**: `g_v(f)(n) = 0` for `n ∉ I_v`.
4. **Dimension**: The space `{g_v(f) : f ∈ ℝ^I}` has dimension `r(v) - 1`.

**Proof.** (1) The sum of child means weighted by child sizes equals the parent mean times `|I_v|`, so the indicator-weighted sum minus the parent-mean indicator sums to zero. (2) By construction `g_v(f)` assigns a single value (child mean minus parent mean) to each child cell. (3) Both terms are supported on `I_v`. (4) The child means lie in `ℝ^{r(v)}` subject to one linear constraint (weighted average = parent mean), giving `r(v) - 1` free parameters. ∎

### Theorem 65 (Orthogonal decomposition)  [§11.2.4 · Phase 11]

Let `T` be a non-stationary radix tree on `I` and `f : I → ℝ` be `T`-adapted. Then:

1. **Decomposition**: `f = μ · 1_I + Σ_{v internal} g_v(f)` where `μ = (1/N) Σ_n f(n)`.
2. **Orthogonality**: For distinct internal nodes `v ≠ w`, `⟨g_v(f), g_w(f)⟩ = 0` (standard inner product on `ℝ^I`).
3. **Parseval**: `‖f - μ‖² = Σ_{v internal} ‖g_v(f)‖²`.

**Proof.** (1) The telescoping argument: starting from the root mean `μ`, each internal node `v` refines the approximation from the `v`-level mean to the child-level means. Since `f` is `T`-adapted (constant on leaves), the sum of all layers recovers `f` exactly.

(2) If `v` and `w` are not in an ancestor-descendant relationship, their supports `I_v` and `I_w` are disjoint (since `T` is a tree), so `⟨g_v, g_w⟩ = 0`. If `v` is an ancestor of `w`, then `g_v` is constant on `I_w` (since `I_w ⊆ I_{c_j}` for some child `c_j` of `v`) while `g_w` has mean zero on `I_w` (Lemma 5.1), so `⟨g_v, g_w⟩ = (g_v|_{I_w}) · Σ_{I_w} g_w = 0`.

(3) Expand `‖f - μ‖² = ‖Σ g_v‖²` and use orthogonality. ∎

### Corollary 30 (Exact adapted signals)  [§11.2.5 · Phase 11]

If `f ∈ H_T`, then the orthogonal decomposition of Theorem 65 reconstructs `f` exactly. The decomposition is unique: if `f = μ' · 1_I + Σ_v g'_v` with `g'_v` satisfying the layer properties (Lemma 5), then `μ' = μ` and `g'_v = g_v(f)` for all internal `v`.

**Proof.** Existence is Theorem 65(1). Uniqueness: take inner products with indicator functions of each child cell to recover child means, then subtract to get layers. ∎

---

## 11.3 The Digit-Conditional Signal Class

### Definition 168 (Signal taxonomy)  [§11.3.1 · Phase 11]

Fix a base sequence `b = (b_0, ..., b_{k-1})` with `N = ∏ b_i` and let `I = {0, ..., N-1}`. Define the following nested signal classes:

1. **Constant signals** `C`: `f` is constant on `I`. Dimension 1.
2. **Periodic signals** `Per`: `f(n)` depends only on `n mod b_0`. Dimension `b_0`.
3. **Vilenkin-measurable signals** `Vil`: `f` is measurable with respect to the product filtration `F_k`. Equivalently, `f ∈ V_k` (Definition 19, block-constant subspace at depth `k`). Dimension `N`.
4. **Digit-conditional signals** `DC`: `f` is `T`-adapted for some non-stationary radix tree `T` on `I`. The class `DC` is the union `⋃_T H_T` over all valid trees.
5. **All signals**: `ℝ^I`. Dimension `N`.

The inclusions are: `C ⊆ Per ⊆ Vil ⊆ DC ⊆ ℝ^I`.

### Proposition 133 (Strict class hierarchy)  [§11.3.2 · Phase 11]

For `N ≥ 6` with at least two distinct prime factors in the radix sequence, each inclusion in the taxonomy (Definition 168) is strict: `C ⊊ Per ⊊ Vil ⊊ DC ⊊ ℝ^I`.

**Proof.** `C ⊊ Per`: any non-constant `b_0`-periodic signal separates. `Per ⊊ Vil`: a signal depending on digit 1 but not digit 0 is Vilenkin-measurable but not periodic. `Vil ⊊ DC`: a signal constant on the tree with root branching `b_0 = 6` and heterogeneous child branching `(2, 3, 2, 3, 2, 3)` is digit-conditional but not Vilenkin-measurable (requires position-dependent sub-partitioning invisible to the uniform filtration). `DC ⊊ ℝ^I`: a generic signal in `ℝ^N` requires `N` parameters (one per point); any tree-adapted signal has dimension `|Leaves(T)| < N` for `T` with depth ≥ 1. ∎

---

## 11.4 Fourier Ceiling Theorem

### Definition 169 (Root-periodic energy fraction)  [§11.4.1 · Phase 11]

For a `T`-adapted signal `f` with tree `T` having root branching `r_0`, define the **root-periodic energy fraction**:
```
α(f, T) = ‖g_root(f)‖² / ‖f - μ‖²
```
where `g_root(f)` is the root layer (Definition 167) and `μ` is the global mean. When `f = μ` (constant), define `α = 1` by convention.

This measures the fraction of signal energy that lives in the first (root-level) layer — the only layer visible to standard Fourier/Vilenkin analysis at depth 1.

### Theorem 66 (Fourier ceiling)  [§11.4.2 · Phase 11]

Let `f` be a non-constant `T`-adapted signal with `α = α(f, T)`. Then for any Fourier/Vilenkin character `χ` of the ambient product space:
```
|⟨f, χ⟩|² / ‖f‖² ≤ α.
```
In words: no single Fourier mode can capture more than fraction `α` of the signal energy. For heterogeneous trees with deep structure, `α` can be arbitrarily small.

**Proof.** The Fourier characters `χ` are products of additive characters of `ℤ/b_i` (Proposition 41). Any such character is constant on cylinder sets of the product filtration. By Theorem 65, `f - μ = g_root + Σ_{v ≠ root} g_v`. The non-root layers `g_v` (for `v` below the root) have mean zero on each root-level coset, so `⟨g_v, χ⟩ = 0` for any depth-1 character. Only the root layer contributes: `|⟨f - μ, χ⟩|² = |⟨g_root, χ⟩|² ≤ ‖g_root‖² = α · ‖f - μ‖²` by Cauchy–Schwarz and Parseval. ∎

### Proposition 134 (Homogeneous ceiling trivial)  [§11.4.3 · Phase 11]

If `T` is homogeneous (all branching factors equal at each depth), then `α(f, T) = 1` for any signal `f` whose energy lies entirely in the root layer. In particular, for a periodic signal adapted to a depth-1 homogeneous tree, the Fourier ceiling is tight: there exists a character achieving correlation `1`.

**Proof.** A depth-1 homogeneous tree has only the root layer, so `‖g_root‖² = ‖f - μ‖²` and `α = 1`. The Fourier transform of a periodic signal on `ℤ/b_0` has at least one mode with full energy by the Parseval identity for finite groups. ∎

---

## 11.5 Representation Gap

### Definition 170 (Minimum uniform cells)  [§11.5.1 · Phase 11]

For a signal `f : I → ℝ`, define `U(f)` as the minimum number of uniform (equal-size) partition cells needed to represent `f` as a piecewise-constant function:
```
U(f) = min { k : ∃ partition of I into k equal-size cells s.t. f is constant on each cell }.
```
If no uniform partition represents `f` exactly, set `U(f) = N`.

### Definition 171 (Representation gap)  [§11.5.2 · Phase 11]

For a `T`-adapted signal `f`, the **representation gap** is:
```
Gap(f, T) = U(f) / |Leaves(T)|.
```
This measures how many more uniform cells are needed compared to tree-adapted cells. For a tree that is *tight* for `f` (it separates every leaf cell), `Gap ≥ 1`; in general the robust, hypothesis-honest facts are the collapse `Gap ≤ 1` when the tree is uniform-adapted and the strict `Gap > 1` achievable under heterogeneity (Proposition 135).

### Proposition 135 (Representation gap: collapse and strict gap)  [§11.5.3 · Phase 11]

The bare claim "`Gap(f, T) ≥ 1` for every `T`-adapted `f`" is **false**: a constant `f` is adapted to any tree, so a 5-leaf tree gives `Gap = 1/5`. The inequality silently needs `f` to separate every leaf cell (the tree is *tight* for `f`) — a hypothesis the bare form omits. The two hypothesis-honest facts, both machine-checked and axiom-clean, are:

1. **Collapse (zero penalty).** If `f` is constant on the equal-size cells of the uniform tree with `|Leaves(T)|` cells, then `Gap(f, T) ≤ 1`: the uniform partition loses nothing. This is the empirical `adv-over-uniform = 0.0000` at `Gap = 1` made into a theorem (`representationGap_le_one_of_uniform`).

2. **Heterogeneity strictly pays.** Some heterogeneous tree with an adapted signal has `Gap > 1`: on `Fin 4`, `f = ![0,0,1,2]` adapted to `node [leaf 2 0, node [leaf 1 2, leaf 1 3]]` has `U(f) = 4` over `3` leaves, so `Gap = 4/3` (`representationGap_gt_one_example`).

**Proof.** (1) `U(f) ≤ |Leaves(T)|` since the uniform partition of that size already resolves `f`, so `Gap = U(f)/|Leaves(T)| ≤ 1`. (2) The only equipartitions of `{0,1,2,3}` are into `1, 2, 4` cells; `f` is non-constant (rules out `1`) and differs across the second block `{2,3}` (rules out `2`), so `U(f) = 4` while the tree has `3` leaves. The classical tight-tree `Gap ≥ 1` (a uniform partition resolving `f` must refine a tight tree's leaves) remains true but is subsumed by (1)–(2) and not separately formalized. ∎

### Theorem 67 (Depth-2 gap formula)  [§11.5.4 · Phase 11]

For a depth-2 tree `T` with root branching `b_0` and child branching factors `r_1, ..., r_{b_0}`:
```
Gap = b_0 · lcm(r_1, ..., r_{b_0}) / Σ_j r_j.
```
Here `lcm` denotes the least common multiple, `Σ_j r_j = |Leaves(T)|`, and `b_0 · lcm(r_j)` is the minimum uniform cell count because a uniform partition must subdivide each root coset into `lcm(r_j)` equal parts.

**Proof.** The tree has `Σ_j r_j` leaves. Leaf cell sizes are `N/(b_0 · r_j)`. A uniform partition must use cells of size `N/(b_0 · lcm(r_j))` (the smallest common refinement), giving `b_0 · lcm(r_j)` cells. The ratio is `b_0 · lcm(r_j) / Σ_j r_j`. ∎

### Corollary 31 (Compensated heterogeneity)  [§11.5.5 · Phase 11]

`Gap(f, T) = 1` for a depth-2 tree if and only if all child branching factors are equal: `r_1 = r_2 = ... = r_{b_0}`. In this case `lcm(r_j) = r_1` and `Σ_j r_j = b_0 · r_1`, so `Gap = b_0 · r_1 / (b_0 · r_1) = 1`.

**Proof.** Direct substitution into Theorem 67. `lcm(r_j) = r` when all `r_j = r`, giving `Gap = b_0 · r / (b_0 · r) = 1`. Conversely, if any `r_j ≠ r_k`, then `lcm(r_j) > max(r_j) ≥ (Σ r_j)/b_0`, making `Gap > 1`. ∎

---

## 11.6 Tree Projection as Generalized Block Projection

### Definition 172 (Tree block projection)  [§11.6.1 · Phase 11]

For a non-stationary radix tree `T` on `I`, the **tree block projection** `P_T : ℝ^I → ℝ^I` is defined by:
```
(P_T f)(n) = (1/|I_ℓ|) · Σ_{m ∈ I_ℓ} f(m)
```
where `ℓ = leaf(n)` is the unique leaf of `T` containing `n`. This averages `f` over the leaf cell containing each point.

### Proposition 136 (Projection properties)  [§11.6.2 · Phase 11]

The tree block projection `P_T` satisfies:

1. **Idempotency**: `P_T ∘ P_T = P_T` (it is a projection).
2. **Self-adjointness**: `⟨P_T f, g⟩ = ⟨f, P_T g⟩` (orthogonal projection).
3. **Contraction**: `‖P_T f‖ ≤ ‖f‖` in `L^2`.
4. **Tower property**: If `T'` is a refinement of `T` (every leaf of `T'` is contained in some leaf of `T`), then `P_T ∘ P_{T'} = P_T`.
5. **Image**: `Im(P_T) = H_T` (the space of `T`-adapted signals).

**Proof.** (1) `P_T f` is `T`-adapted (constant on leaves), so `P_T(P_T f) = P_T f`. (2) Expand inner products using the leaf partition; the averaging is symmetric. (3) Jensen's inequality: averaging cannot increase `L^2` norm. (4) If `T'` refines `T`, averaging over `T'`-leaves then `T`-leaves is the same as averaging over `T`-leaves directly. (5) `P_T f ∈ H_T` by construction; conversely, any `T`-adapted `f` satisfies `P_T f = f`. ∎

### Theorem 68 (Connection to FDRS filtration)  [§11.6.3 · Phase 11]

Let `b = (b_0, ..., b_{k-1})` be a base sequence and `T_K` the homogeneous radix tree of depth `K` with branching factors `(b_0, ..., b_{K-1})`. Then:

1. `P_{T_K} = P_K`, the block projection of Definition 22 at depth `K`.
2. The filtration `F_0 ⊂ F_1 ⊂ ... ⊂ F_k` (Definition 17) equals the tower `H_{T_0} ⊂ H_{T_1} ⊂ ... ⊂ H_{T_k}` where `T_d` is the depth-`d` homogeneous tree.
3. The detail operator `Δ_K = P_K - P_{K-1}` (Definition 23) equals the sum of root-level layers `Σ_{v at depth K-1} g_v` where `g_v` are the depth-`(K-1)` node layers of `T_K`.

**Proof.** (1) By Proposition 132, the leaf partition of `T_K` equals the cylinder partition at depth `K`, so the averaging operators coincide. (2) `H_{T_d}` consists of functions constant on depth-`d` cylinders, which is exactly `V_d` (Definition 19). (3) The detail operator removes the depth-`(K-1)` average and retains the depth-`K` refinement, which is exactly what the node layers at depth `K-1` compute. ∎

---

## 11.7 Detection Power

### Definition 173 (F-statistic for radix selection)  [§11.7.1 · Phase 11]

Given a signal `f` and a candidate non-stationary radix tree `T`, define the **F-statistic** for tree selection:
```
F(f, T) = [SS_between / (|Leaves(T)| - 1)] / [SS_within / (N - |Leaves(T)|)]
```
where:
- `SS_between = Σ_ℓ |I_ℓ| · (mean(f on I_ℓ) - μ)²` is the between-leaf sum of squares,
- `SS_within = Σ_ℓ Σ_{n ∈ I_ℓ} (f(n) - mean(f on I_ℓ))²` is the within-leaf sum of squares,
- `μ` is the global mean of `f`.

This is the one-way ANOVA F-statistic treating leaves as groups. Under the null hypothesis that `f` has no tree structure (i.e., `f` is noise), `F` follows an `F`-distribution with `(|Leaves| - 1, N - |Leaves|)` degrees of freedom.

### Proposition 137 (Detection power scaling)  [§11.7.2 · Phase 11]

For a digit-conditional signal with signal-to-noise ratio `SNR` in Gaussian noise, the minimum detectable effect size `ε₅₀` (at 50% detection power and significance level 0.05) scales as:
```
ε₅₀ ~ √(b₀ / M)
```
where `b₀` is the root branching factor and `M = N / b₀` is the number of samples per root-level coset. As `M → ∞`, arbitrarily weak digit-conditional structure becomes detectable.

**Proof.** The F-statistic has `b₀ - 1` numerator degrees of freedom and `N - b₀ = b₀(M - 1)` denominator degrees of freedom. The non-centrality parameter is `λ = M · b₀ · ε² / σ²` where `ε` is the effect size. For 50% power, `λ ≈ b₀`, giving `ε₅₀ ≈ σ · √(b₀/M)`. ∎

---

## 11.8 Digit-Conditional Complexity

### Definition 174 (DCC)  [§11.8.1 · Phase 11]

The **digit-conditional complexity** `DCC(f, ε)` of a signal `f` at tolerance `ε > 0` is:
```
DCC(f, ε) = min { |Leaves(T)| : T is a non-stationary radix tree with R²(f, T) ≥ 1 - ε }
```
where `R²(f, T) = ‖P_T f - μ‖² / ‖f - μ‖²` is the fraction of variance explained by the tree projection (Definition 172).

### Proposition 138 (DCC characterizes taxonomy)  [§11.8.2 · Phase 11]

The DCC provides a quantitative characterization of the signal taxonomy (Definition 168):

1. `DCC(f, 0) = 1` iff `f` is constant.
2. `DCC(f, 0) ≤ b_0` iff `f` is periodic (depth-1 adapted).
3. `DCC(f, 0) < N` iff `f` is digit-conditional (adapted to some tree with fewer than `N` leaves).
4. `DCC(f, 0) = N` iff `f` is a generic signal requiring full pointwise specification.

For `ε > 0`, DCC measures the effective complexity: how many tree cells suffice to explain `(1-ε)` of the signal variance.

**Proof.** (1) Constant `f` has `f = μ`, so `P_T f = μ` for any tree and `R² = 1` with 1 leaf (the root as a leaf). (2) A periodic signal is constant on root-level cosets; the depth-1 tree with branching `b_0` captures it exactly with `b_0` leaves. (3) By definition, digit-conditional signals are tree-adapted for some `T` with `|Leaves| < N`. (4) A generic signal in `ℝ^N` has full rank; any tree with fewer than `N` leaves projects into a strict subspace, losing some variance. ∎

---

## 11.9 Capstone

### Theorem 69 (Vilenkin is special case)  [§11.9.1 · Phase 11]

The Phase 2 multiresolution analysis (Definitions 17–23, Theorem 7) is the homogeneous special case of Phase 11:

1. **Trees**: Homogeneous radix trees of depth `d` with branching `(b_0, ..., b_{d-1})` are exactly the standard cylinder partitions (Proposition 132).
2. **Projections**: `P_{T_d} = P_d` for the depth-`d` block projection (Theorem 68).
3. **Filtration**: `H_{T_0} ⊂ H_{T_1} ⊂ ...` recovers `F_0 ⊂ F_1 ⊂ ...` (Theorem 68).
4. **Fourier ceiling**: `α = 1` for Vilenkin signals (Proposition 134), recovering full Fourier analysis.
5. **Representation gap**: `Gap = 1` for homogeneous trees (Corollary 31), meaning uniform partitions suffice.
6. **DCC**: `DCC(f, 0) = ∏_{i<d} b_i` for a signal adapted to depth `d`, matching the Vilenkin dimension formula.

Phase 11 therefore strictly extends the Phase 2 framework to heterogeneous, digit-conditional signal structure while preserving full backward compatibility.

**Proof.** Each item follows from the referenced result:
(1) Proposition 132. (2)-(3) Theorem 68. (4) Proposition 134. (5) Corollary 31. (6) By Proposition 138(2)-(3), the DCC of a depth-`d` Vilenkin signal equals the number of depth-`d` cylinder cells, which is `∏ b_i`. ∎

---

**End of Phase 11: Digit-Conditional Signal Analysis**
**Status:** Extended specification with non-stationary radix tree formalization

---

## Phase 12 — Unit Complement Structure

### Additive complement-to-unity on the closed unit interval

Throughout FDRS, normalized quantities arise naturally: energy fractions $(\alpha(f,T) \in [0,1])$ (Definition 169), variance-explained ratios $(R^2(f,T))$ (Definition 174), cylinder measures $(\mu(C))$, and gate functions $(g : \mathcal R \to [0,1])$ (Proposition 24). The **unit complement** provides a uniform structural framework for reasoning about these quantities and their residuals.

---

## 12.1 Unit complement

### Definition 175 (unit complement)  [§12.1.1 · Phase 12]

For $(x \in [0,1])$, define the **unit complement** as:
$[
\operatorname{comp}(x) := 1 - x.
]$
The defining law is the **complement sum**: $(x + \operatorname{comp}(x) = 1)$.

### Definition 176 (unit pair and parts)  [§12.1.2 · Phase 12]

For $(x \in [0,1])$, define:

1. The **unit pair**: $(\operatorname{pair}(x) = (x,\; 1-x))$.
2. The **lesser part**: $(\operatorname{lesser}(x) = \min(x,\; 1-x))$.
3. The **greater part**: $(\operatorname{greater}(x) = \max(x,\; 1-x))$.

### Proposition 139 (complement properties)  [§12.1.3 · Phase 12]

The unit complement satisfies:

1. **Closure**: If $(x \in [0,1])$, then $(\operatorname{comp}(x) \in [0,1])$.
2. **Complement sum**: $(x + \operatorname{comp}(x) = 1)$ for all $(x \in \mathbb R)$.
3. **Involution**: $(\operatorname{comp}(\operatorname{comp}(x)) = x)$.
4. **Fixed point**: $(\operatorname{comp}(x) = x)$ if and only if $(x = 1/2)$.

**Proof.**
(1) If $(0 \le x \le 1)$, then $(0 \le 1 - x \le 1)$.
(2) $(x + (1 - x) = 1)$ by additive cancellation.
(3) $(1 - (1 - x) = x)$ by additive cancellation.
(4) $(1 - x = x)$ iff $(1 = 2x)$ iff $(x = 1/2)$. ∎

### Proposition 140 (ordering split)  [§12.1.4 · Phase 12]

For $(x \in [0,1])$:

1. If $(x < 1/2)$, then $(x < \operatorname{comp}(x))$: the lesser part is $(x)$ itself.
2. If $(x = 1/2)$, then $(x = \operatorname{comp}(x))$: the pair degenerates.
3. If $(x > 1/2)$, then $(x > \operatorname{comp}(x))$: the greater part is $(x)$ itself.
4. In all cases: $(\operatorname{lesser}(x) + \operatorname{greater}(x) = 1)$.

**Proof.** Items (1)–(3) follow from comparing $(x)$ with $(1-x)$ given the relation to $(1/2)$. Item (4): $(\min(x, 1-x) + \max(x, 1-x) = x + (1-x) = 1)$ since $(\min + \max = \text{sum})$ for linearly ordered pairs. ∎

---

### Remark (structural role in FDRS)

The unit complement structure provides a foundational framework for reasoning about normalized FDRS quantities and their residuals:

- **Energy fractions**: When $(\alpha(f,T))$ measures the root-periodic energy fraction (Definition 169), its complement $(1 - \alpha)$ measures the energy distributed across deeper tree layers. The Fourier ceiling theorem (Theorem 66) bounds individual Fourier correlations by $(\sqrt\alpha)$, while $(1 - \alpha)$ quantifies the irreducible heterogeneity that resists Vilenkin analysis.

- **Variance decomposition**: The $(R^2)$ statistic (Definition 174) and its complement $(1 - R^2)$ partition total signal variance into explained and unexplained components. The DCC tolerance parameter $(\varepsilon)$ controls the acceptable unexplained fraction: $(R^2 \ge 1 - \varepsilon)$ is precisely a complement-sum constraint.

- **Measure duality**: For any cylinder set $(C)$ with $(\mu(C) = p)$, the complement set has measure $(1 - p)$. The lesser/greater part decomposition gives a canonical orientation: the minority partition (lesser part) and majority partition (greater part).

- **Self-pairing threshold**: The unique fixed point at $(1/2)$ marks the threshold where a quantity and its complement are balanced — the maximum-entropy point for binary decompositions. This is structurally analogous to the midpoint of a radix digit range, connecting unit-complement reasoning to the existing cylinder partition framework.

## 12.2 Irrational unit-carry decomposition

### Definition 177 (fit count, completion residue, overflow carry)  [§12.2.1 · Phase 12]

For $(a \in (0,1))$, define:

1. The **fit count**: $(N(a) := \lfloor 1/a \rfloor)$ — how many full copies of $(a)$ fit inside the unit interval.
2. The **completion residue**: $(\rho(a) := 1 - N(a) \cdot a)$ — the gap between the maximal non-overflowing stack and unity.
3. The **overflow carry**: $(\omega(a) := (N(a)+1) \cdot a - 1)$ — the spill past unity from one additional copy.

The last copy of $(a)$ splits into $(\rho(a))$ (completing the unit) and $(\omega(a))$ (carrying forward), satisfying $(\rho(a) + \omega(a) = a)$.

### Proposition 141 (basic carry arithmetic)  [§12.2.2 · Phase 12]

For $(a \in (0,1))$:

1. **Stack fits**: $(N(a) \cdot a \le 1)$.
2. **Overflow**: $((N(a)+1) \cdot a > 1)$.
3. **At least one fits**: $(N(a) \ge 1)$ for $(a \in (0,1))$.
4. **Carry sum law**: $(\omega(a) = a - \rho(a))$.
5. **Stack equation**: $(N(a) \cdot a + \rho(a) = 1)$.
6. **Overflow equation**: $((N(a)+1) \cdot a = 1 + \omega(a))$.

**Proof.** (1) From $(\lfloor 1/a \rfloor \le 1/a)$. (2) From $(\lfloor 1/a \rfloor + 1 > 1/a)$. (3) Since $(a < 1)$ implies $(1/a > 1)$, so $(\lfloor 1/a \rfloor \ge 1)$. Items (4)–(6) are algebraic rearrangements of the definitions. ∎

### Proposition 142 (irrational sharpening)  [§12.2.3 · Phase 12]

For irrational $(a \in (0,1))$:

1. **Strict stack inequality**: $(N(a) \cdot a < 1)$. (If equality held, $(a = 1/N(a))$ would be rational.)
2. **Positive residue**: $(0 < \rho(a))$.
3. **Residue bound**: $(\rho(a) < a)$.
4. **Positive carry**: $(0 < \omega(a))$.
5. **Carry bound**: $(\omega(a) < a)$.

**Proof.** (1) Suppose $(N(a) \cdot a = 1)$. Then $(a = 1/N(a) \in \mathbb{Q})$, contradicting irrationality. (2) Follows from (1): $(\rho(a) = 1 - N(a) \cdot a > 0)$. (3) From Proposition 141(2): $((N(a)+1) \cdot a > 1)$ gives $(N(a) \cdot a > 1 - a)$, so $(\rho(a) = 1 - N(a) \cdot a < a)$. (4) Immediate from Proposition 141(2). (5) From the carry sum law $(\omega(a) = a - \rho(a) < a)$ since $(\rho(a) > 0)$. ∎

### Proposition 143 (greater/lesser part specialization)  [§12.2.4 · Phase 12]

Let $(x \in (0,1))$ be irrational, with greater part $(g = \operatorname{greater}(x))$ and lesser part $(\ell = \operatorname{lesser}(x))$.

1. **Greater part fit count**: $(N(g) = 1)$. Since $(1/2 < g < 1)$, we have $(1 < 1/g < 2)$.
2. **Residue equals lesser part**: $(\rho(g) = \ell)$. The gap after one copy of $(g)$ is exactly the lesser part.
3. **Carry formula**: $(\omega(g) = 2g - 1)$.
4. **Lesser part fit count**: $(N(\ell) \ge 2)$. Since $(0 < \ell < 1/2)$, we have $(1/\ell > 2)$.

**Proof.** (1) Since $(g > 1/2)$ and $(g < 1)$, we have $(1 < 1/g < 2)$, so $(\lfloor 1/g \rfloor = 1)$. (2) $(\rho(g) = 1 - 1 \cdot g = 1 - g = \ell)$, using $(\ell + g = 1)$. (3) $(\omega(g) = (1+1) \cdot g - 1 = 2g - 1)$. (4) Since $(\ell < 1/2)$, we have $(1/\ell > 2)$, so $(\lfloor 1/\ell \rfloor \ge 2)$. ∎

---

**End of Phase 12: Unit Complement Structure and Carry Decomposition**
**Status:** Foundational primitives for normalized quantity reasoning and irrational carry dynamics

---

## Phase 13 — Generated (Continued-Fraction) Timelines

### Motivation

Phases 1–12 develop the mixed-radix line whose place values `B_L = ∏ b_i` are a *given* product of bases. Phase 5 (function-defined radices `b_ω(prefix)`) and Phase 7 (context-dependent radix) already let the base at position `i` depend on the prefix seen so far; Phase 9/10 give the odometer its spatial, carry-routed dynamics; Phase 12 (§12.2) isolates the irrational unit-carry primitive `N(a) = ⌊1/a⌋` — which is exactly one step of a continued-fraction (Gauss-map) expansion.

Phase 13 follows that primitive to its conclusion: the **generated timeline**, where the place-value sequence is not supplied as a product of bases but is *generated* by a constrained-alphabet (subshift) transfer rule. The canonical instance is the **continued fraction / Ostrowski numeration**: a point is an infinite sequence of partial quotients, and the place value at depth `n` is the convergent denominator `q_n` (Fibonacci for the golden mean `φ = [1;1,1,…]`, Pell for `√2 = [1;2,2,…]`). This is the *irrational* radix line — the one whose base product would stagnate on base-1 "wires" yet whose cylinders still shrink to a point, because the gauge `q_n` keeps growing via the `+ q_{n-1}` recurrence.

The phase tells one story, and the sub-section order is that story:

1. **§13.1** the fixed-radix baseline: coupling two ordinary radix lines through a least-significant-unit (LSU) mediator, where place values and overflow rates *factor as products*;
2. **§13.2–13.3** generalize the place value from a base product to the generated gauge `q_n`, and rebuild the ultrametric on it (`ball = cylinder` survives);
3. **§13.4** the hinge: the overflow-rate (carry-frequency) law `1/B_L` generalizes to `1/q_n` — **but the product law of §13.1 breaks**;
4. **§13.5** equips the golden-mean gauge with its measure of maximal entropy (the Parry measure), built as a genuine Markov chain;
5. **§13.6** exhibits the engine that forced the product law to break: the density-free homographic/bihomographic arithmetic that combines two generated streams exactly, in `ℤ`, most-significant-digit first.

Everything in this phase is machine-checked in Lean (0 `sorry`, no added axioms beyond Mathlib's `propext`/`Classical.choice`/`Quot.sound`); each numbered result cites its Lean name for direct verification.

### Formalization map

| Sub-section | Lean module (under `FdrsFormal/`) |
|---|---|
| §13.1 | `Integration/ThreeLineMediator/Definition.lean`, `…/CoupledSystem.lean` |
| §13.2 | `Modes/VariableRadix/SubshiftWeight.lean` |
| §13.3 | `Modes/VariableRadix/SubshiftMetric.lean` |
| §13.4 | `Modes/VariableRadix/CarryFrequency.lean` |
| §13.5 | `Modes/VariableRadix/SubshiftParry.lean` |
| §13.6 | `Modes/VariableRadix/{HomographicCarry,Bihomographic,BihomographicSound,BihomographicDriver,HyperGosper}.lean` |

The single-lineage bridge from Phase 10's coupled-digit network into this phase is the strengthened **Theorem 64** (§10.9.1, `Modes/BaseZeroSea/LinearChain.lean`): the chain step projects onto the Phase 9 spatial odometer. Phase 13 picks up where that odometer's place value is replaced by the generated gauge.

---

## 13.1 The least-significant-unit mediator and overflow rate (fixed radix)

Two independent radix lines A and B each advance by a 1-Lipschitz tick — their **least significant unit** (LSU), the smallest meaningful advance. The LSUs are *incommensurable* (one tick on A need not equal one tick on B in any metric), but both are `+1` in `ℤ`, so they are comparable through carry mechanics. A **mediator** line C makes that comparison observable.

### Definition 178 (Product radix and the observer-line mediator)  [§13.1.1 · Phase 13]

For radix sequences `b₁, b₂`, the **product radix** is `(productRadix b₁ b₂) i = b₁ i · b₂ i`. An **observer line** is a radix sequence together with its odometer; a **line mediator** of observer lines A, B is a line C with maps `toA, toB, fromAB` forming a bijection `R̂_C ≅ R̂_A × R̂_B` (as sets, via the mod/div encoding `c_i = a_i + b₁(i)·b_i`) together with the place-value and overflow factoring laws below. The **product mediator** instantiates C with the product radix.

**Lean.** `productRadix`, `ObserverLine`, `LineMediator`, `productMediator` (`ThreeLineMediator/Definition.lean`).

### Proposition 144 (Mediator ≅ A × B: the round-trip identities)  [§13.1.2 · Phase 13]

The projections `projectA x = (x mod b₁)`, `projectB x = (x div b₁)` and the constructor `combine a b = a + b₁·b` satisfy `projectA (combine a b) = a`, `projectB (combine a b) = b`, and `combine (projectA x) (projectB x) = x`. Hence the mediator space is exactly the set-theoretic product of the source spaces.

**Lean.** `projectA_combine`, `projectB_combine`, `combine_project`.

**Proof.** Each is the digit-wise Euclidean identity `n = (n mod m) + m·(n div m)` with `m = b₁ i`, discharged by `Nat.mod_add_div` / `Nat.add_mul_div_left`. ∎

**Remark (no truncated CRT).** This bijection is on the *completed* (full-depth) space. The analogous identity on truncated length-`L` prefix values **fails**: for `b₁=(3,5)`, `b₂=(2,7)`, `x=(4,13)`, `L=2` one gets `82 ≠ 85`, because cross-digit carry patterns differ between the product and component systems. The Lean source therefore deliberately omits a product-radix prefix-CRT lemma. Do not assert one.

### Theorem 70 (Place value and overflow rate factor under the product mediator)  [§13.1.3 · Phase 13]

Define the **overflow rate** `overflowRate b L = 1 / B_L` — the fraction of states whose tick carries past depth `L`, a purely combinatorial reciprocal place value. Then under the product mediator,
```
placeValue (productRadix b₁ b₂) L = placeValue b₁ L · placeValue b₂ L
overflowRate (productRadix b₁ b₂) L = overflowRate b₁ L · overflowRate b₂ L
```
and `overflowRate` is positive and antitone in depth (deeper carry is rarer).

**Lean.** `placeValue_product`, `overflowRate_product`, `overflowRate_pos`, `overflowRate_antitone`.

**Proof.** `placeValue_product` is induction on `L` (`B_{L+1} = b·B_L`, multiply through). The overflow product is then `1/(B₁B₂) = (1/B₁)(1/B₂)` (`field_simp`). Positivity and antitonicity follow from `placeValue.pos` / `placeValue.mono`. ∎

This **product law** is the structural payload of fixed-radix coupling: comparing two lines reduces to multiplying reciprocal place values, no real-valued metric presupposed. §13.4 shows precisely how much of it survives the passage to a generated gauge.

### Definition 179 (Coupling, the coupled system, and manifest instantiation)  [§13.1.4 · Phase 13]

A **coupling** of A, B is a latency `latency ≥ 1` — the number of A-ticks per B-emission; this latency, *not* the radix, defines what "one mediator unit" means (`lsuWeight = latency`). A **coupled system** bundles lines A (finer), B (coarser), a coupling, an **independent** mediator radix, and an **instantiation mode**: `preInitialized` (all positions present, filled with 0 — the completed space `R̂`) or `manifestOnOverflow` (positions are null `∅` until carry first reaches them; the first carry writes `0`, the additive identity — manifestation, not counting).

**Lean.** `Coupling`, `CoupledSystem`, `InstantiationMode`, `ManifestSpace`, `tickDigit` (`ThreeLineMediator/CoupledSystem.lean`).

### Proposition 145 (Independence of coupling and radix; manifestation absorbs carry)  [§13.1.5 · Phase 13]

(i) The A:B tick ratio is exactly the latency at every count: `aTicksFor n = latency · bEmissionsFor n`. (ii) The two structural parameters are orthogonal — equal latency forces equal A-tick counts regardless of radix (`lsu_independent_of_radix`), and equal mediator radix forces equal capacity regardless of coupling (`radix_independent_of_coupling`). (iii) Ticking a null slot yields `(some 0, false)`: **manifestation absorbs the carry** — a created position halts propagation rather than overflowing.

**Lean.** `tick_ratio`, `lsu_independent_of_radix`, `radix_independent_of_coupling`, `tickDigit_none`.

### Proposition 146 (Overflow-rate ratio and the discrete → real comparison)  [§13.1.6 · Phase 13]

The overflow-rate ratio of two lines is the reciprocal place-value ratio, `overflowRatio b₁ b₂ L = B₂(L) / B₁(L)`; for constant radices `a, c` it is the exact power `(c/a)^L`. Chaining these ratios as `L → ∞` is the discrete mechanism by which real-valued line-speed comparisons are recovered without presupposing the continuum.

**Lean.** `overflowRatio_eq`, `overflowRatio_constant`. The construction extends to prefix-dependent laws via `productLaw` (Phase 5/7 context dependence).

---

## 13.2 The generated (continued-fraction) gauge

We now replace the supplied base product `B_L` by a gauge *generated* from a constrained alphabet — the place value of the irrational radix line.

### Definition 180 (Subshift / transfer-matrix prefix gauge)  [§13.2.1 · Phase 13]

For a `d`-state alphabet constraint with prefix-indexed transition weights `M`, the **subshift weight** carries a state-vector through the prefix (`weightVec`, one `stepVec` contraction per symbol) and contracts against a boundary vector. It generalizes the free per-path place value `β_ω` (`prefixWeight`) of Phase 5 to a per-path *transfer product*, using only a `Finset` contraction — no `Matrix` type class.

**Lean.** `subshiftWeight`, `stepVec`, `weightVec`, `freeTransition` (`SubshiftWeight.lean`).

### Theorem 71 (Defensive perimeter: the free `d = 1` gauge recovers the place value)  [§13.2.2 · Phase 13]

Over the free (complete, single-state) transition, the subshift gauge equals the Phase 5 place value exactly: `subshiftWeight (freeTransition ω) 1 1 s = prefixWeight ω s`.

**Lean.** `subshiftWeight_free_eq_prefixWeight` (via `weightVec_free_const`).

**Proof.** Induction on `s`: the free fold multiplies the carried scalar by `ω.radix` at each head shift, so a constant start `x` yields `x · β_ω(s)`; take `x = 1`. ∎

**Consequence.** Every existing result built on `prefixWeight` — the induced ultrametric, `ball = cylinder`, the Group-G block convergence — is the `d = 1` instance and is left untouched as the generalization is built out. This is why the generalization is safe.

### Definition 181 (The convergent-pair ledger)  [§13.2.3 · Phase 13]

`RemainderState` carries the last two continued-fraction convergents `(p_{k-1}, p_k ; q_{k-1}, q_k)` — the `SL₂(ℤ)` transition state. One discovered partial quotient acts by the convergent recurrence `x_{k+1} = a·x_k + x_{k-1}` (`step`, i.e. right-multiply by `[[a,1],[1,0]]`); `init = (1,0,0,1)` starts a fractional CF `[0; a₁, a₂, …]`. The **gauge** is the denominator `q_k`; the defining quantity is the cross-determinant `det = p_k q_{k-1} − p_{k-1} q_k`.

**Lean.** `RemainderState`, `step`, `init`, `steps`, `gauge`, `det` (`SubshiftWeight.lean`).

### Theorem 72 (The bracket invariant)  [§13.2.4 · Phase 13]

For any discovered-quotient sequence, the cross-determinant is `±1`: `|p_k q_{k-1} − p_{k-1} q_k| = 1`. Hence the convergent bracket gap is exactly `1/(q_{k-1} q_k)`.

**Lean.** `bracket_invariant` (via `det_step`, `det_steps`, `init_det`).

**Proof.** Each `step` multiplies the determinant by `−1` (the factor `[[a,1],[1,0]]` has determinant `−1`); with `init.det = −1`, after `k` steps `det = (−1)^{k+1}`, so `|det| = 1`. Pure integer algebra — the exact, general form of the periodic `|Q| = 1` check. ∎

### Theorem 73 (Gauge growth: `q_k > 0` and `q_k → ∞`, even for `φ`)  [§13.2.5 · Phase 13]

For continued-fraction quotients (all `≥ 1`): the denominator is a positive integer (`q_k ≥ 1`) and grows without bound, `|as| + 1 ≤ 2·q_k`; consequently for every `ε > 0` there is a depth beyond which `1/q_k < ε`. This holds **even for the all-1 sequence** `φ`, where the base product `β = ∏ radix` stagnates: the `+ q_{k-1}` Fibonacci term keeps `q_k` growing, so the cylinders `1/q_k` still shrink to a point.

**Lean.** `steps_qCur_pos`, `steps_qCur_unbounded`, `gauge_inv_lt`.

**Proof.** A combined invariant (`steps_invariant`, by reverse induction on the quotient list) gives `0 ≤ q_{k-1} ≤ q_k`, `q_k ≥ 1`, and `|as|+1 ≤ q_{k-1}+q_k`; positivity and the linear lower bound follow, and `1/q_k → 0` is the Archimedean consequence. ∎

---

## 13.3 The continued-fraction ultrametric

### Definition 182 (Admissible point, prefix, and the gauge at depth)  [§13.3.1 · Phase 13]

A point of the generated timeline is an infinite quotient sequence `x : ℕ → ℕ` with every `x i ≥ 1` (`Admissible`). Its length-`n` prefix is `pre x n`, and the **gauge at depth `n`** is `gaugeAt x n = q_n`, the convergent denominator of that prefix. It is positive, monotone (non-decreasing) in depth, and `1/q_n → 0`.

**Lean.** `Admissible`, `pre`, `gaugeAt`, `gaugeAt_pos`, `gaugeAt_monotone`, `gaugeAt_inv_lt` (`SubshiftMetric.lean`).

### Definition 183 (The gauge-induced continued-fraction distance)  [§13.3.2 · Phase 13]

For distinct points let `ℓ = lcpLen x y` be the longest-common-prefix length (first index of disagreement). The **CF distance** is `cfDist x y = 1/q_ℓ` (and `0` when `x = y`) — the subshift analogue of the Phase 1/6 cylinder ultrametric, with the generated gauge `q_ℓ` in place of the base product `β`.

**Lean.** `lcpLen`, `cfDist`.

### Theorem 74 (`cfDist` is a genuine ultrametric)  [§13.3.3 · Phase 13]

On admissible points, `cfDist` satisfies `cfDist x x = 0`, non-negativity, symmetry, identity of indiscernibles (`cfDist x y = 0 ↔ x = y`), and the **strong triangle inequality** `cfDist x z ≤ max (cfDist x y) (cfDist y z)`.

**Lean.** `cfDist_self`, `cfDist_nonneg`, `cfDist_comm`, `cfDist_eq_zero_iff`, `cfDist_triangle`.

**Proof.** The strong triangle is the gauge made geometric: `lcpLen x z ≥ min(lcpLen x y, lcpLen y z)` (a shared prefix of `x,y` and of `y,z` is a shared prefix of `x,z`), and `gaugeAt` monotone turns the longer common prefix into the smaller `1/q`. Symmetry uses that both endpoints read the same gauge on their common prefix; identity of indiscernibles uses `q_ℓ > 0`. ∎

### Theorem 75 (`ball = cylinder`)  [§13.3.4 · Phase 13]

Every open ball about an admissible point is exactly a combinatorial cylinder: choosing `n` minimal with `1/q_n < r`,
```
{ y | cfDist x y < r } = { y | pre y n = pre x n }.
```

**Lean.** `ball_eq_cylinder`.

**Proof.** `→`: `cfDist x y < r` forces the common prefix to reach depth `n` (else `1/q` at a shallower depth would be `≥ r` by minimality of `n`). `←`: agreement to depth `n` makes `lcpLen ≥ n`, so `1/q_{lcp} ≤ 1/q_n < r` by gauge monotonicity. This is the translation layer between the analytic metric and the combinatorial cylinders that the measure and routing layers consume. ∎

---

## 13.4 Carry frequency on the generated timeline

This is the hinge of the phase. The fixed-radix overflow rate `1/B_L` (§13.1) generalizes to the generated gauge — the carry-frequency *law* survives, the *product law* does not.

### Definition 184 (Carry frequency of a generated timeline)  [§13.4.1 · Phase 13]

`cfOverflowRate x L = 1 / q_L` — the reciprocal of the gauge, the continued-fraction analogue of `overflowRate b L = 1/B_L`, with the convergent denominator `q_L` (admissible-configuration count) in place of the fixed place value. Rational and exact; no measure, no density.

**Lean.** `cfOverflowRate` (`CarryFrequency.lean`).

### Theorem 76 (`cfOverflowRate` is positive, antitone, and vanishing)  [§13.4.2 · Phase 13]

For admissible `x`: `cfOverflowRate x L > 0`; it is antitone in depth (deeper carry is rarer); and it **vanishes** — beyond some depth it drops below any `ε > 0`.

**Lean.** `cfOverflowRate_pos`, `cfOverflowRate_antitone`, `cfOverflowRate_vanishes` (via `gaugeAt_pos`, `gaugeAt_monotone`, `gaugeAt_inv_lt`).

**Proof.** The three properties mirror `overflowRate_pos`/`_antitone` exactly, with gauge facts replacing place-value facts; vanishing is `gaugeAt_inv_lt` (Theorem 73) — the strict-positivity payoff the fixed-radix `overflowRate` attains only when `B_L → ∞`, which here holds even for `φ`. ∎

**Remark (the product law breaks).** Theorem 70's `overflowRate_product` (`B_C = B_A · B_B`) has **no analogue** here: continued-fraction combination is not a radix product, so the place value of a combined output stream is not the product of the inputs' place values. The bridge from §13.1 holds at the level of the carry-frequency law (reciprocal place value), **not** the product structure. §13.6 is the reason: combining two generated streams is genuinely more than digit-aligned carry.

---

## 13.5 The Parry measure on the golden-mean shift

The generated gauge of §13.2–13.4 is combinatorial. §13.5 equips its canonical instance — the golden-mean (Zeckendorf) shift — with its measure of maximal entropy, the **Parry measure**, built as a genuine Markov chain so the integration engine cannot leak probability mass.

### Definition 185 (Parry transition kernel of the golden-mean shift)  [§13.5.1 · Phase 13]

The golden-mean shift on `{0,1}` ("no two consecutive 1s", transition matrix `[[1,1],[1,0]]`, place values the Fibonacci numbers). Its **Parry kernel** is `goldenP`: from state `0`, go to `0` with probability `1/φ` and to `1` with `1/φ²`; from state `1`, go to `0` with probability `1` (a `1` must be followed by a `0`). Packaged as a `ProbabilityTheory.Kernel`.

**Lean.** `goldenP`, `goldenKernel` (`SubshiftParry.lean`); `φ = Real.goldenRatio`, characterized purely by `goldenRatio_sq`.

### Theorem 77 (Mass conservation and the Markov kernel)  [§13.5.2 · Phase 13]

Each row of `goldenP` sums to `1`, and `goldenKernel` is a Markov kernel (`IsMarkovKernel`).

**Lean.** `goldenP_sum_one`, `goldenP_nonneg`, `instIsMarkovKernel…`.

**Proof.** The non-trivial state-`0` row is exactly the golden identity `1/φ + 1/φ² = 1`, equivalent to `φ² = φ + 1` (`goldenRatio_sq`) and proved *exactly* — no real-analysis limits — using `φ⁻¹ = φ − 1`. The Markov instance is then discharged by the per-state `PMF`. The Perron eigenpair `[[1,1],[1,0]]·(φ,1)ᵀ = φ·(φ,1)ᵀ` is implicit in the probabilities `p_{ij} = A_{ij} r_j /(λ r_i)`; Mathlib's Perron–Frobenius is not invoked. ∎

### Definition 186 (Parry stationary law)  [§13.5.3 · Phase 13]

`goldenStat = π ∝ (φ², 1)`, normalized by `φ² + 1` — for the symmetric golden-mean matrix this is `l_i r_i`, the unique `goldenP`-invariant law.

**Lean.** `goldenStat`, `goldenStat_sum_one`.

### Theorem 78 (Stationarity)  [§13.5.4 · Phase 13]

`π · goldenP = π`: the stationary law is invariant, so the path measure built from it is the genuine shift-invariant Parry measure.

**Lean.** `goldenStat_stationary`.

**Proof.** Each coordinate of `π · P = π` reduces, after clearing the denominator `φ² + 1`, to the golden identity `φ² = φ + 1` (a `linear_combination` of `goldenRatio_sq`). ∎

### Definition 187 (Parry path measure via Ionescu–Tulcea)  [§13.5.5 · Phase 13]

Injecting the homogeneous chain into the history-dependent family `goldenFam n` (the next state depends only on the current one), the **Parry path measure** on `ℕ → Fin 2` is the stationary law pushed through the Ionescu–Tulcea trajectory kernel: `parryMeasure = parryInit.bind parryTraj`. It is a probability measure on the canonical product σ-algebra.

**Lean.** `goldenFam`, `parryTraj` (`Kernel.traj`), `parryInit`, `parryMeasure`; `IsProbabilityMeasure parryMeasure`.

### Theorem 79 (Lévy upward convergence — "Group G" — on the golden timeline)  [§13.5.6 · Phase 13]

For every integrable, strongly-measurable `f`, the block conditional expectations over the coordinate filtration converge to `f` in `L¹` under the Parry measure: `E[f | ℱ_L] → f`.

**Lean.** `parry_condExp_tendsto` (via `iSup_piLE_eq_pi`).

**Proof.** The coordinate filtration exhausts the product σ-algebra (`⨆_L ℱ_L = pi`, the lone obligation), after which the statement is Mathlib's classical martingale (Lévy upward) convergence `tendsto_eLpNorm_condExp`. The integration engine thus runs natively on the generated golden-mean timeline — no bespoke metric or topology, just the canonical `pi` σ-algebra. ∎

---

## 13.6 Density-free continued-fraction arithmetic

Finally, the engine that combines generated streams — and the reason §13.4's product law had to break. It is *density-free*: exact `ℤ` arithmetic, most-significant-digit first, emitting an output digit only once it is *forced*.

### Definition 188 (Homographic emission — single stream)  [§13.6.1 · Phase 13]

The dual of the absorbing `step` (Definition 181): `emit q` applies the homographic map `v ↦ 1/(v − q)` (left-multiply the `SL₂(ℤ)` ledger by `[[0,1],[1,-q]]`), writing one output partial quotient. The candidate digit is `emitDigit = ⌊h_cur / q_cur⌋`; `emitReady` fires when that floor agrees at both ends of the unread input range `[1, ∞)`, so the next output is forced regardless of the input tail.

**Lean.** `RemainderState.emit`, `emitDigit`, `emitReady` (`HomographicCarry.lean`).

### Theorem 80 (Exactness and channel independence)  [§13.6.2 · Phase 13]

Emission preserves `|det| = 1` (combined with `init`, the engine stays unimodular forever — exact integer arithmetic, no rounding), and the absorb and emit channels **commute**: `emit q (step r a) = step (emit q r) a`.

**Lean.** `emit_det_natAbs`, `emit_step_comm`.

**Proof.** `emit` flips the determinant (`emit_det`), so `|det|` is preserved; commutation is a four-field polynomial identity closed by `ring`. Channel independence is the defining property of an exact-real streaming transducer: reads and writes interleave freely. ∎

### Definition 189 (The bihomographic tensor — two-stream mediator, Timeline C)  [§13.6.3 · Phase 13]

Gosper's rank-3 tensor `z = (a·xy + b·x + c·y + d)/(e·xy + f·x + g·y + h)`, a flat 8-field `ℤ` structure (`BihTensor`) absorbing two input streams (`absorbX`, `absorbY`) and emitting one (`emit`). `emitDigit = a.fdiv e` (floor division at the `(∞,∞)` corner); `emitReady` requires positive corner-denominators and that the candidate digit trap all **four corners** `(x,y) ∈ {1,∞}²`.

**Lean.** `BihTensor`, `absorbX`, `absorbY`, `emit`, `emitDigit`, `emitReady` (`Bihomographic.lean`).

### Theorem 81 (Channel commutations)  [§13.6.4 · Phase 13]

The two input reads and the output write pairwise commute: `absorbX_absorbY_comm`, `emit_absorbX_comm`, `emit_absorbY_comm`. The mediator is therefore an asynchronous, non-blocking transducer — A, B, C interleave freely.

**Lean.** `absorbX_absorbY_comm`, `emit_absorbX_comm`, `emit_absorbY_comm`.

**Proof.** Each is a polynomial identity on the 8 fields closed by `ring` (the flat structure is used precisely so `ring` sees through it, where a `Matrix` product would hide a `Finset.sum`). ∎

### Theorem 82 (Emission soundness — the four-corner trap)  [§13.6.5 · Phase 13]

If the integer floor `k` agrees at all four corners (eight integer inequalities on the tensor coefficients), then for **every** input tail `x, y ≥ 1` the true output value `N/D` is trapped in `[k, k+1)`. Emitting `k` therefore never hallucinates a digit, whatever the unread tails of A and B. Moreover a `true` from the executable `emitReady` discharges exactly these hypotheses, so every digit the driver physically emits carries its own correctness proof.

**Lean.** `emit_traps`, `emitReady_traps` (via `bilinear_ge_const`) (`BihomographicSound.lean`).

**Proof.** The kernel is a no-limits bilinear bound: over any ordered ring, `α·xy + β·x + γ·y + δ ≥ α + β + γ + δ` on the quadrant `x, y ≥ 1` whenever the three leading corner-coefficients `α`, `α+β`, `α+γ` are non-negative — via the identity `αxy+βx+γy+δ = α(x−1)(y−1) + (α+β)(x−1) + (α+γ)(y−1) + (α+β+γ+δ)`. Applying it to `N − k·D` and to `(k+1)·D − N` gives the two-sided trap. The infinite corners are leading-coefficient sign conditions, never limits; `ℚ` suffices, and `x, y` are inert order-carriers (`nlinarith`). ∎

### Definition 190 (The two-stream driver)  [§13.6.6 · Phase 13]

`run` is the Gosper scheduler over the verified tensor: emit when `emitReady` (the digit is forced, certified by Theorem 82), else absorb the next quotient, alternating A/B with a fuel bound. With `addTensor` (`z = x + y`) and `mulTensor` (`z = x·y`) it computes irrational arithmetic exactly in `ℤ`.

**Lean.** `run`, `addTensor`, `mulTensor` (`BihomographicDriver.lean`).

**Worked evaluations (executable `#eval`).** `φ + φ = 2φ = 1+√5 = [3;4,4,…]`; `φ·φ = φ+1 = [2;1,1,…]`; `√2 + √2 = [2;1,4,1,4,…]`. And the honest case: `√2·√2 = 2` sits exactly on a floor boundary — undecidable from finite input — so the engine **safely emits nothing** (`[]`) rather than guess; this is Theorem 82 preventing a hallucinated digit, not a failure.

### Definition 191 (The hyper-Gosper clock)  [§13.6.7 · Phase 13]

Coupling `N` streams through a single flat tensor would need `2^(N+1)` integers. Instead `coupleAll` arranges verified rank-3 nodes into a **tournament-bracket binary tree** (`pairUp` a layer, `coupleTree` cascade): every node stays at 8 integers, only discrete emitted streams travel the wires, and per-node certification (Theorem 82) composes up the tree. Linear node count, log-depth latency, no exponential state.

**Lean.** `coupleAll`, `coupleTree`, `pairUp` (`HyperGosper.lean`). Evaluations: `3φ = [4;1,5,…]`, `4φ = [6;2,…]`, `8φ = [12;1,…]`, each node still 8 integers.

**Remark (honest scope).** Two limitations are stated in the source and are *not* theorems here: (i) the "thermodynamic limit" intuition — that coarsening up an infinite tree converges to the Gauss/Parry invariant measure — is a **conjecture**, and the link to the commutant/multiresolution algebra is an analogy; (ii) composing finite-fuel `run`s truncates intermediate streams, so deep trees lose tail precision (the bracket's log depth mitigates but does not remove this). This file builds the coupler; the limit theorem is future work.

---

**End of Phase 13: Generated (Continued-Fraction) Timelines**
**Status:** Machine-verified in Lean (0 sorries; axioms `propext`/`Classical.choice`/`Quot.sound` only). The generated gauge `q_n` generalizes the place value `B_L`; the ultrametric and carry-frequency law transfer (`ball = cylinder`, `cfOverflowRate = 1/q_n`), the product law does not; the golden-mean instance carries an exact Parry measure with Lévy convergence; and the density-free homographic/bihomographic engine combines generated streams exactly, emitting only certified digits.

---

## Phase 14 — The Synthetic Place Complex (Coupled Radix Networks)

Phases 5–13 built mixed-radix structure along a line: one timeline, one gauge, one
odometer — with Phase 13 generalizing the gauge from a base product to a generated
quantity, and the adelic complex running two such engines side by side under
scheduler confluence. Phase 14 is the network regime: digit fibers determined by
*other* chains' states (Phase 7's oracle with chain-valued context), histories that
are partial orders rather than words, and conservation that crosses interfaces. Its
organizing discovery is a triple migration:

> **In the network regime, every global scalar dies, and every law survives by
> becoming indexed and glued.** Value (the global decode) dies with sibling
> uniformity and survives as gauge-graded observables; conservation (the product
> formula) dies with separability and survives as a family of interface balances;
> geometry (a scalar depth) dies with concurrency and survives as the
> observer-indexed gauge family glued by sup.

The coupled radix complex is accordingly not a generalized adele but a **networked
transport object** — a gauge-indexed transport geometry. Design record:
`docs/synthetic-place/00-thesis.md`, `01-build-roadmap.md`, `02-phase14-design.md`,
`03-digit-coupling.md` (the digit-coupling layer, §14.8–14.9), `04-network-config.md`
(the SU7 network arc — the radix-complex machine these statics serve).

### 14.1 Designed gauges and the refinement ultrametric

**Definition 192 (prefix gauge)**:
A *prefix gauge* on words over a digit alphabet `D` is a pair `(Adm, g)`: a
prefix-closed admissibility predicate `Adm ⊆ D*` and a weight `g : D* → ℕ` with
`g(s) ≥ 1` on admissible words and `g(s) ≤ g(s·d)` along admissible extensions. A
point is admissible when all its prefixes are; the induced distance is the
first-disagreement reciprocal `δ_g(x,y) = g(lcp(x,y))⁻¹` (and `0` for equal points).

**Theorem 83 (gauge ⇒ ultrametric; ball = cylinder)**:
For any prefix gauge, `δ_g` is an ultrametric on admissible points (strong triangle
inequality); if moreover the gauge is unbounded along the centre, every open ball is
exactly a combinatorial cylinder. The structure (product law, subshift, completion
count, nested chain) enters only through the two gauge laws.

*Lean:* `FdrsFormal/Modes/SyntheticPlace/GaugeUltrametric.lean`.

**Proposition 147 (the corpus instances)**:
The product gauge `g = β_ω` of any radix law is a prefix gauge (unbounded, via
`2^{|s|} ≤ β_ω(s)`), and its induced distance carries Definition 79's formula
`β_ω(lcp)⁻¹`. The generated CF gauge `g(s) = q(s)` of Phase 13 is a prefix gauge on
quotient-admissible words, and its induced distance **equals** `cfDist`
(Definition 180). Both prior ultrametrics are instances of Theorem 83.

### 14.2 Cross-timeline composition and the ragged regime

**Definition 193 (coupled fiber law; coupled completion counts)**:
A *coupled fiber law* is a pair `fiberA : Σ* → ℕ≥2`, `fiberB : Σ* × Σ* → ℕ≥2`, where
B's fiber reads its own prefix *and* A's prefix including A's current digit — the
Definition 85 oracle `Ω(s, c)` with the context `c` instantiated as another chain's
state. The *coupled completion count* `W_k(s_A, s_B)` counts admissible pair-paths of
depth `k` (Definition 61, coupled).

**Theorem 84 (level-only coupling preserves SU)**:
If both fibers depend only on prefix lengths, the coupled completion counts depend
only on lengths; all pair-siblings have equal counts (the Definition 74 regime — the
coupled echo of Theorem 70).

**Proposition 148 (the ragged witness, machine-checked)**:
There is a coupled fiber law with two A-siblings of different completion counts
(`4 ≠ 6` at depth 1, `16 ≠ 36` at depth 2; kernel-checked). Coupling generically
destroys sibling uniformity: no rank chart, no odometer, and the pair-fiber of a
single node is jagged — the coupled tree is not a radix law at all (Phase 5.4 §5,
realized).

**Theorem 85 (geometry survives raggedness)**:
The path place-value of a coupled chain is a prefix gauge on pair digits; hence the
coupled chain carries a genuine ultrametric with ball = cylinder *even in the ragged
regime*. Refinement geometry survives the death of the odometer.

*Lean (14.2):* `FdrsFormal/Modes/SyntheticPlace/Composition.lean`.

### 14.3 The admissibility trap (the third certificate)

**Definition 194 (transfer structure; uncertainty ledger; trap gate)**:
A *transfer structure* is a finite state set `Q` with total transition
`step : Q × D → Q`, Boolean admissibility gate `allowed`, and observation
`obs : Q → O`. The engine's ledger is the *uncertainty set* `S ⊆ Q` of states
consistent with what has been observed; the *trap gate* `ready S` holds when the
admissible one-step image of `S` carries exactly one observation.

**Theorem 86 (admissibility-trap soundness)**:
If the candidate set is a singleton `{o}`, then every admissible tail from every
state of `S` observes `o` after one step. A finite Boolean check certifies a
universally quantified forcing — the third emission certificate, with admissibility
playing the role order plays at the Archimedean place (Theorem 82) and congruence
plays at the p-adic places. The fuel driver emits only when forced; on the
golden-mean structure the certificate is Zeckendorf's forced zero (`ready {1}`
fires, candidate `0`; from `0` the engine must refine), the engine-side face of the
deterministic Parry kernel row (Theorem 77).

*Lean:* `FdrsFormal/Modes/SyntheticPlace/AdmissibilityTrap.lean`.

### 14.4 Zoom-out restriction

**Definition 195 (depth-decided observables)**:
An observable `f` on digit streams is *decided at depth `n`* when it is constant on
every depth-`n` cylinder.

**Theorem 87 (indistinguishability below the gauge; strict hierarchy)**:
A depth-`n` observable cannot separate points closer than `(g(pre_n x))⁻¹`:
separating by a depth-`n` view costs at least the depth-`n` gauge reciprocal in
distance (Theorem 44's Lipschitz bound, gauge-general and decode-free — valid in the
ragged regime). The depth hierarchy of decided observables is monotone and strict at
every genuine branch (Proposition 133's shape). The SU-regime modulus-by-depth
(Corollary 27) is the decode-bearing special case and is not rebuilt.

*Lean:* `FdrsFormal/Modes/SyntheticPlace/Restriction.lean`.

### 14.5 Conservation: partition, balance, rigidity

**Definition 196 (completion mass and observed flux)**:
The *completion mass* `mass_n(q)` is the number of admissible runs of horizon `n`
from `q`; the *observed flux* `flux_n(q, o)` is the mass flowing through admissible
first steps whose next observation is `o`.

**Theorem 88 (the partition law; zero leak)**:
`mass_{n+1}(S) = Σ_o flux_n(S, o)` over the candidate observations — the continuity
equation of refinement: mass is partitioned by the emitted symbol, never created or
destroyed. When the trap fires (`candidates = {o}`), the **entire** mass flows
through the emitted symbol: certified emission is conditioning on a sure event —
exact transport, zero leak. On the golden structure the masses are the Fibonacci
numbers (the counting shadow of `fib(n+2) ≤ qₙ`), kernel-checked.

*Lean:* `FdrsFormal/Modes/SyntheticPlace/Conservation.lean`.

**Definition 197 (the coupled interface machine; balance)**:
The coupled step of Definition 193 run as a two-place machine with a declared
ledger: an A-half-step appends an A-digit and *issues* the grant
`fiberB(s_B, s_A·a)` into the interface; a B-half-step *consumes* the pending grant
by choosing a digit below it. A configuration is *balanced* when
`issued = consumed + pending`.

**Theorem 89 (the interface balance law)**:
Every reachable configuration is balanced, for **arbitrary** coupling — Proposition
128's shape per step, Theorem 57's shape in sum: the residual is exactly the
undelivered in-flight payload; nothing is created or destroyed anonymously. No
reachable configuration has `consumed > issued` (the obstruction reading).

*Lean:* `FdrsFormal/Modes/SyntheticPlace/InterfaceBalance.lean`.

**Definition 198 (place-local transfer rules)**:
A charge `Φ` on configurations is *place-locally exact* when its increment at an
A-half-step is a function of `(s_A, a)` alone and at a B-half-step of `(s_B, b)`
alone — neither rule sees the other place or the interface.

**Theorem 90 (conservation rigidity: factorization, no-go, boundary)**:
(i) *Factorization*: every place-locally exact charge satisfies
`Φ = Φ₀ + f(s_A) + g(s_B)` on reachables — it is additively separable and cannot
measure the coupling. (ii) *No-go*: for a bilateral coupling (the grant reads both
opening digits) the carry charge `issued` admits **no** place-local transfer rule —
the four corner runs carry ledgers `5, 6, 6, 5`, violating the rectangle identity
forced by (i) (kernel-checked). (iii) *Boundary*: for B-blind couplings (the grant
ignores B's own prefix) the carry charge **is** place-locally exact. The classical
product formula is the ultimate separable charge — possible exactly because
classical places are mutually blind; the Phase 13 product-law breakage (§13.4) is
the same fact seen from the engine side. The conserved quantity of a genuine
coupling lives on the interface, not in the places: Definition 197's register is
necessary, not a convenience.

**Proposition 149 (witnesses on both sides of the boundary)**:
Proposition 148's ragged fiber is B-blind — hence place-locally accountable, *inside*
the boundary: raggedness does not obstruct local accounting; bilaterality does. The
bilateral witness sits outside. The boundary is real and crossed.

*Lean (Defs 198, Thm 90, Prop 149):*
`FdrsFormal/Modes/SyntheticPlace/ConservationRigidity.lean`.

### 14.6 Network geometry: the scalar no-go and the observer gluing

**Definition 199 (schedules, trace equivalence, projections)**:
A network *schedule* is a finite word of events `(place, digit)`; *trace
equivalence* identifies schedules up to adjacent swaps of events at different places
(Mazurkiewicz, for the place-disjointness independence); the *projection* `π_v`
extracts place `v`'s digits in order; `u` is a *trace-prefix* of `w` when some
completion of `u` is trace-equivalent to `w`. Projections are schedule-invariant:
trace-equivalent schedules have identical projection tuples.

**Theorem 91 (the scalar trace-gauge no-go, machine-checked)**:
No distance on schedules can simultaneously satisfy the triangle inequality, call
two schedules `(g u)⁻¹`-close whenever `u` is a common trace-prefix of both (for any
gauge unbounded along each of two places' own pure lines — no positivity or
swap-invariance assumed), and keep root-divergent pure runs uniformly separated.
Witness: `a^n` and `b^m` are both trace-prefixes of `a^n · b^m` (the block commute),
so the bridge run is close to both while they stay far from each other — even the
ordinary triangle inequality fails. Depth earned at one place masks blindness at
another: **a scalar refinement metric cannot price concurrency.**

*Lean:* `FdrsFormal/Modes/SyntheticPlace/TraceGeometry.lean`.

**Definition 200 (the observer-glued network distance)**:
For a family of prefix gauges `G_v` indexed by the places and network points given
by per-place stream tuples, `netDist(x, y) = max_v δ_{G_v}(x_v, y_v)` — *you are
only as close as your most-disagreeing observer.*

**Theorem 92 (the glued network ultrametric)**:
`netDist` is an ultrametric on admissible tuples; with one place it equals the
Theorem 83 distance exactly (the sequential theory is the one-observer case); with
per-place unbounded gauges every ball is a **cylinder profile** — a per-place depth
vector, the network's refinement domain; every observable of the projection tuple is
schedule-invariant; and a place-`v` observable decided at depth `n` cannot separate
network points closer than `(g_v(pre_n x_v))⁻¹` — each observer's information flows
at its own gauge speed (Theorem 87, transported through the gluing).

*Lean:* `FdrsFormal/Modes/SyntheticPlace/NetworkGauge.lean`.

### 14.7 Honest scope and open frontiers

"Balance sheaf" and "gauge sheaf" are structural vocabulary — indexed families with
additive/sup gluing; no sheaf axioms are formalized. "No product formula" has the
exact scope of Theorem 90: separable charges cannot measure coupling, and the
bilateral witness refutes place-local accounting of the carry; the full
accountability iff ("place-local ⟺ rectangle identity on reachables") is open.
Liveness is absent throughout: every certificate is sound, none is yet guaranteed to
fire. Coupled-place stream determinacy (the conditional Kahn diamond) is open. The
bridge from infinite network runs to total stream tuples needs an unformalized
fairness hypothesis. Minimality of the sup-gluing is posed, not claimed. Trace
theory background is classical (Mazurkiewicz); the corpus contributes the
FDRS-shaped statements and the verified artifact.

### 14.8 Digit coupling — the six axes (the SU6 layer)

*(Addendum, 2026-07-02: assigns Phase-14 numbering to the digit-coupling layer built
2026-06-10/11 — design record `03-digit-coupling.md` — and to the non-abelian arc of
2026-06-29/30, §14.10. The `03` ledger's "Phase 14 numbering for SU6 awaits the next
corpus pass" is hereby discharged.)*

Every coupling rule between FDRS lines is a point in a six-axis space — **topology**
(which digits couple), **window** (what the receiver sees of the source), **message**
(what crosses: a commutative-monoid currency), **distribution** (route/split vs
mirror), **activation** (overflow, trigger, manifestation), and **grading** (exact vs
frustrated) — with the ordinary number line at the origin: path topology, blind
window, unit mass, route-to-next, overflow activation, exact grading. The base
primitive is the *window-coupled step*: one source tick emits a message (its carry
content), and the receiver's fiber is gated by the pair (message, window-reading of
the source). This section records the grading, currency, and window axes; §14.9 the
within-digit (nested) topology.

**Definition 201 (coupling graph; size as an edge cocycle)**:
A *coupling graph* on places `V` is an edge type with `src, tgt : Edge → V` and a
positive ratio `ratio : Edge → ℚ` — how many source-increments one target-increment
is worth (its reciprocal is the carry frequency: the two readings of size,
composition and activity, are reciprocal currencies of one **edge** datum). A
traversal step crosses an edge forward (factor `ratio`) or backward (factor
`ratio⁻¹`); `walkFactor` is the product along a walk; the complex is **gradable**
when a global positive magnitude `w` exists with `w(tgt) = ratio · w(src)` on every
edge. Size is not a node property; it is a multiplicative cocycle on the coupling
graph.

*Lean:* `FdrsFormal/Modes/SyntheticPlace/Grading.lean` (`CouplingGraph`, `Step`,
`walkFactor`, `Gradable`).

**Theorem 93 (the holonomy dichotomy — the full iff)**:
In a gradable complex every closed walk has size factor `1` (`gradable_holonomy`);
conversely, a base-connected complex with trivial loop holonomy is gradable — the
potential is defined by walk transport, well-defined by the walk-reversal toolkit
(`gradable_of_trivial_holonomy`). *Direction is not geometry — it is exactness of the
size cocycle.*

**Proposition 150 (witnesses on both sides)**:
`chainGraph_gradable` — the standard number line is the graded case: path topology
has no loops and the witness potential is exactly the place value (`chainPotential`
= `B_i`); "most significant digit" is well-defined *because* chains are trees.
`frustratedTriangle_not_gradable` — three digits, each overflowing into the next at
ratio `2` around a loop (loop factor `8 ≠ 1`): the dynamics and every per-edge
balance remain perfectly well-defined, yet **no global bigger/smaller exists** — a
Penrose staircase of digits. **Frustration** thereby joins raggedness (Proposition
148: kills the rank chart) and bilaterality (Theorem 90: kills separable
conservation) as the **third obstruction to number-hood**; a coupling complex is "a
number" exactly when it clears all three, and each failure leaves a survivor
(geometry, balance, per-edge ratios).

**Definition 202 (currency; transport vs trigger)**:
A per-interface *currency register* over a commutative monoid `M` carries the
declared ledger (`issued`, `consumed`, `pending : Option M`) with `issue`/`consume`
transitions and reachability relative to a declared grant set. Overflow distribution
has two species that must never be conflated: **transport** (route/split — the carry
is conserved mass; distributed weights sum) and **trigger** (mirror — every coupled
digit generates its own tick; the carry is *copied like information*).

*Lean:* `FdrsFormal/Modes/SyntheticPlace/CurrencyBalance.lean` (`CurrencyConfig`,
`CurrencyReachable`).

**Theorem 94 (currency-generic interface balance)**:
`issued = consumed + pending` on every reachable register, generically over **any**
commutative monoid (`currencyReachable_balanced`) — SU4b's law never used
subtraction, order, or grant size. Instantiations: `mass_balance` (transport,
`M = ℕ`) and `trigger_balance` (each overflow issues one event-token): **mirrors
conserve too — in the event currency.** Every coupling edge declares its currency;
conservation holds in the declared currency; currencies never convert without a
declared morphism.

**Definition 203 (windows; the length window; grant uniformity)**:
The *window* of a coupling is what the grant may read of the partner: nothing
(blind) ⊂ the partner's clock (`LengthWindow`: the grant factors through the
partner's prefix *length*) ⊂ the partner's content (the full prefix — SU1's
`CoupledFiber`). A coupling is *grant-uniform* (`GrantUniform`) when the grant
agrees across co-reachable configurations with the same source prefix — i.e. the
books never depend on partner data that varies while the source's own view is fixed.

*Lean:* `FdrsFormal/Modes/SyntheticPlace/WindowAccountability.lean`,
`WindowBoundary.lean`.

**Theorem 95 (the shared clock; clock windows are accountable)**:
Strict alternation is a shared clock: on every reachable configuration
`|s_A| = |s_B|` with the interface empty and `|s_A| = |s_B| + 1` with a grant
pending (`reachable_length`). Consequently a length-window coupling is place-locally
accountable (`issued_placeLocal_of_lengthWindow`): reading the partner's *time*
costs nothing, because synchrony already shares it. The accountability boundary thus
refines to: blind ⊂ clock — accountable; content — not (Theorem 90 ii).

**Theorem 96 (the window boundary, CLOSED for the alternating machine)**:
The carry charge is place-locally accountable **iff** the coupling is grant-uniform
(`issued_placeLocal_iff_grantUniform`). The calibrated points fall out as
corollaries: clock windows are uniform (`grantUniform_of_lengthWindow`, subsuming
Theorem 95), the bilateral content window is not (`jointFiber_not_grantUniform`).
*Scope:* strict alternation only — under free network scheduling the boundary
reopens, and its correct restatement (accountable ⟺ the window factors through
schedule-deducible data) is an open item of the SU7 arc (`04-network-config.md` §3).

### 14.9 Nested charts and dilation (within-digit coupling)

**Definition 204 (the exact splice)**:
One digit of an outer radix line is *implemented by an inner chain*: `refineBase`
splices a `k`-stage inner line `c` into position `p` of the outer line `b`, under
the recorded **exactness** decision `b p = ∏_{j<k} c j` — the outer fiber equals the
inner mass on the nose (lossless chart; lossy/quotient charts are the sea's regime
and remain a declared variant).

*Lean:* `FdrsFormal/Modes/SyntheticPlace/NestedChain.lean`, `NestedDilation.lean`.

**Theorem 97 (synthetic fractions; the gauge half of dilation)**:
Below the spliced block nothing changes (`refined_potential_below`); **inside the
block the gauge is composite** `B_p · C_j` — the inner states sit at resolutions
strictly between `B_p` and `B_{p+1}`, so a *synthetic fraction* is exactly a
position inside one outer unit whose denominator is the inner gauge scaled by the
outer place value (`refined_potential_inside`); at the top of the block and beyond,
the refined gauge **rejoins the outer gauge exactly** (`refined_potential_top`,
`refined_potential_above`) — the chart is gauge-lossless: the outer line cannot
tell, by resolution, that one of its digits is secretly a whole structure; and
crossing the block multiplies resolution by exactly `b p`
(`nested_dilation_gauge`). *The gauge is the clock; coupling re-clocks.*

**Theorem 98 (dilation, dynamic half — exact nesting is conservative)**:
The exact splice never leaves Mode 0: the refined sequence is a bona fide radix line
(`refineBase_ge_two`), its place values agree with the composite gauge
(`chainPlace_refine_below/inside/above`), the **re-blocking identity** holds — the
outer digit is the inner decode of the block digits (`refined_digit_reblock`) — and
one outer unit is exactly a `B_p`-fold inner tick (`dilation_tick`). **Exact nesting
buys resolution, never arithmetic**: both lines enumerate the same `ℕ`, and the
chart between them is value-preserving.

### 14.10 The non-abelian arc: group grading and the certified SE(2) engine

The grading axis of §14.8 is `ℚ`-valued — abelian by accident of the instance, not
by necessity of the idea. This arc (built 2026-06-29/30) re-derives the axis over an
**arbitrary group**: the walk factor becomes an *ordered* product, and order matters
exactly when the group does. It then carries the emission-certificate family into
the non-commutative regime, where the value space (rotation) has **no global order
and no floor**.

**Definition 205 (group-valued coupling graph)**:
A `GroupGraph V G` (`[Group G]`) carries `ratio : Edge → G`; `walkFactor` is the
**ordered** product of step factors (`ratio` forward, `ratio⁻¹` backward);
`Gradable` demands a potential `w : V → G` with `w(tgt) = ratio · w(src)`.

*Lean:* `FdrsFormal/Modes/SyntheticPlace/GroupGrading.lean` (`GroupGraph`,
`walkFactor`, `Gradable`).

**Theorem 99 (group holonomy dichotomy — gain-graph balance)**:
`gradable_holonomy` and `gradable_of_trivial_holonomy` combine to the full iff for
base-connected complexes: **`group_gradable_iff_trivial_holonomy`** — a global
`G`-valued magnitude exists iff every closed walk has factor `1`. Chains are
gradable over *any* group (`chainGraph_gradable`, potential = the ordered
`chainPotential`): the abelian/non-abelian distinction is invisible to trees — it is
a **cycle** property. *Attribution:* this is Zaslavsky's balance criterion for gain
graphs (1989), classical; the corpus contributes the placement (size/order as
cocycles on the coupling graph) and the machine-checked artifact.

**Proposition 151 (non-abelian frustrated witnesses, discrete and continuous)**:
`frustratedTriangle : GroupGraph (Fin 3) (DihedralGroup 3)` — loop factor `≠ 1`
(`frustrated_loop_factor_ne_one`), hence `frustratedTriangle_not_gradable`
(discrete). `frustratedSE2 : GroupGraph (Fin 3) SE2` — three genuine rigid motions
of the plane composing around a loop to a nontrivial slide
(`frustratedSE2_holonomy_ne_one`, `frustratedSE2_not_gradable`): a real rigid-motion
cycle that does not close (continuous). *Lean:* `GroupGrading.lean`, `SE2Pose.lean`.

**Definition 206 (sector emission — the floor-free trap)**:
On the circle `ℤ/(M · cellWidth)` with `M` sectors: `sector` reads the cyclic sector
of a position; `emitSector` emits the sector index **only when the entire
uncertainty window lies in one sector**, and refuses otherwise. The digit *wraps*
(`wall_wraps` — the base-0 wall): there is no global order and no floor to take.

*Lean:* `FdrsFormal/Modes/SyntheticPlace/CircleEmit.lean`.

**Theorem 100 (sector-trap soundness — the fourth certificate)**:
`emitSector_sound`: every value of the uncertainty window observes the emitted
sector — the faithful wrap-analogue of the Archimedean four-corner trap, with cyclic
sectors in place of floor intervals. The emission-certificate family is now four:
**order** (the Archimedean place, Theorem 82), **congruence** (the p-adic places,
`padic_emit_traps`), **admissibility** (synthetic places, Theorem 86), and **sector**
(the circle — the rotation half of SE(2)). Executable demos: `emit_demo`,
`refuse_demo`.

**Definition 207 (exact SE2 motions; pose regions; tractable engines)**:
`SE2` is the genuine rigid-motion group (rotation `Circle` × translation `ℂ`, the
non-commutative semidirect law); a *pose region* is `PoseRegion := Set SE2`, with
`predict` (the group's own set-product) and `update` (intersection). A
`TractablePose R` is an engine over representable regions `R` with sound
predict/update; the generic machinery is `Box K` and affine motions `Aff K` over
**any** ordered ring `K` — exactly the typeclass of the bihomographic trap.

*Lean:* `SE2Pose.lean`, `SE2Engine.lean`, `SE2Tight.lean`.

**Theorem 101 (the certified non-commutative engine: soundness and the tight traps)**:
At the set level the predict→update loop is sound through non-commutative
composition (`predict_sound`, `update_sound`, `run_sound`) — soundness is free; the
work is tractability. The generic engine supplies it exactly: `Aff.comp_apply`
(exact affine composition, no error), `Aff.bbox_sound` (**the tight four-corner
trap**: every box point maps into the bbox of the actual slanted image),
`bilinear_ge`/`bilinear_le` and `coupling_ge`/`coupling_le` (**the bounded-region
bihomographic trap**: the Gosper bilinear form over a box is trapped by its four
corners — Theorem 82's kernel with `[1,∞]` tails replaced by box edges, certifying
the rotation × translation coupling itself), and exact rational rotations (the
Pythagorean `(3,4,5)`: `cos = 3/5, sin = 4/5`) — genuine fine rotations over `ℚ`,
no floats.

**Theorem 102 (the tight tractable engine)**:
`tightTractable_run_sound`: the `PoseBox` engine — rotation box × translation box;
predict = tight bbox transported through the coordinate bridges (`rc_mul`,
`tc_mul`), update = exact intersection — is sound at every step against the true
pose. *Honest seam (open):* the coordinate bridges identify the generic `K × K` box
engine with `Circle ⋉ ℂ` pointwise; the full engine-level identification, with
`CircleEmit`'s certified sector feeding the heading channel, is the remaining wire.

### 14.11 Addendum honest scope

Potentials on graphs are classical discrete gauge theory, and Theorem 99 is
Zaslavsky's gain-graph balance — the contribution is placement, the FDRS reading,
and the verified witnesses. The three obstructions to number-hood are a
classification of *observed* failure modes, never a completeness claim; *causal
frustration* is a recorded **candidate** fourth (`04-network-config.md` §2, clause
3: magnitude may be frustrated, causality must not be). The window-boundary iff
(Theorem 96) is alternation-relative — do not cite it for free schedulers. Currency
laws hold per declared currency only. The SE(2) identification seam and
`CircleEmit`'s probe status are as stated in Theorem 102 / Definition 206. These
statics serve the **SU7 network arc** — `Config` + `complexStep`, the coupled radix
network as a verified abstract machine (`04-network-config.md`) — whose
formalization begins with the SU7.0 probe (`NetworkConfig.lean`: the 2-node/1-edge
network machine recovers the SU4b interface machine).

---

**End of Phase 14: The Synthetic Place Complex**
**Status:** Machine-verified in Lean (0 sorries; axioms `propext`/`Classical.choice`/`Quot.sound` only). The designed gauge generalizes both the place-value product `β_ω` and the generated gauge `q_n` into one keystone (ultrametric + ball = cylinder); coupling realizes the ragged regime concretely while geometry survives it; emission gains its third certificate (admissibility) with exact mass transport; conservation migrates from separable node charges — impossible under bilateral coupling, by machine-checked rigidity — to interface balance laws; and network geometry, refused to every scalar gauge by the trace no-go, is carried by the observer-glued family. Value, conservation, and geometry each survive the network regime by becoming indexed and glued.
**Addendum status (2026-07-02, §14.8–14.11):** the digit-coupling layer lands the three-obstruction picture (raggedness · bilaterality · frustration) with the holonomy dichotomy proven as a full iff and witnessed on both sides; conservation becomes currency-generic (mirrors conserve in the event currency); the window boundary is closed for the alternating machine (accountable ⟺ grant-uniform); exact nesting is conservative (resolution, never arithmetic); and the non-abelian arc lifts grading to arbitrary groups (gain-graph balance, machine-checked, with dihedral and SE(2) frustrated witnesses) and extends certified emission to the floor-free sector trap and the tight SE(2) pose engine. Next: the SU7 network machine.
