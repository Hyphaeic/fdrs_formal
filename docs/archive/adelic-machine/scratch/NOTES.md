# Scratch research notes — derivations behind the design

*Raw working for the claims in `03`/`04`. Builder's cheat-sheet. Everything here is
elementary and checkable by hand or by `adelic_validation.py`.*

---

## 1. The p-adic homographic recurrence (derivation)

Value `y = (a x + b)/(c x + d)`, written `M = [[a,b],[c,d]]` acting on `x`.

**Absorb (read a Hensel digit `α`).** A p-adic read is `x = α + p·x'`, `x' ∈ ℤ_p`.
Substitute:
```
 y = (a(α+p x') + b)/(c(α+p x') + d) = ((a p) x' + (a α + b)) / ((c p) x' + (c α + d))
```
so `absorb α :  M ↦ [[a p, a α + b],[c p, c α + d]] = M · [[p, α],[0,1]]`.

**Emit (write a Hensel digit `β`).** Output `y = β + p·y'`, so `y' = (y − β)/p`:
```
 y' = ((a x + b) − β(c x + d)) / (p(c x + d)) = ((a−βc) x + (b−βd)) / ((p c) x + (p d))
```
so `emit β :  M ↦ [[a − β c, b − β d],[p c, p d]]`.

**Determinant bookkeeping.**
```
 det(absorb α (M)) = (a p)(c α + d) − (a α + b)(c p) = p(ac α + ad − ac α − bc) = p·det(M)
 det(emit   β (M)) = (a−βc)(p d) − (b−βd)(p c) = p(ad − βcd − bc + βcd) = p·det(M)
```
**So every step multiplies `det` by `p`** ⟹ `v_p(det) = #steps`, `det = ±pᵏ·det₀`.
This is the within-place exactness invariant at `p` — **not** `|det|=1` (that is the
`∞` invariant). Proof template in corpus: `det_step`/`det_steps` (SubshiftWeight,
✅), same induction shape.

Contrast `∞` (CF): read `x = a + 1/x'` ⟹ `M·[[a,1],[1,0]]`, `det ↦ −det`,
`|det|=1`. The p-adic read is a **shift** (no inversion) and is **non-unimodular**.

---

## 2. Readiness: when is the output digit `β` forced? (congruence, no order)

The next Hensel digit `β = y mod p` is determined regardless of the unread tail
`x ∈ ℤ_p` iff:

1. **unit denominator on the disk:** `c x + d ∈ ℤ_p^×` for all `x ∈ ℤ_p`.
   `c x + d ≡ 0 (mod p)` is solvable for `x` iff `c ≢ 0 (mod p)` (then
   `x ≡ −d/c`), or `c ≡ d ≡ 0`. So *not* solvable — unit for all `x` — iff
   **`c ≡ 0 (mod p)` and `d ≢ 0 (mod p)`** (then `c x + d ≡ d`, a unit).
2. **constant residue across the `p` corners:** `y mod p = (a x + b)(c x + d)^{−1}
   mod p` is the same for all `x ∈ {0,…,p−1}` (the `p` residue-disks of the tail).

Both are **divisibility/congruence** conditions on the integer entries — decidable
(`omega`/`decide`), **no `<`, no floor**. This is the p-adic `emitReady`; its
soundness is `residue_depends_on_prefix` specialized to base `p`.

> NB: condition (2) on the *initial* `M` is restrictive (forces `a ≡ 0 (mod p)`
> too, i.e. `M` already ≈ constant mod `p`). The point is that one **absorbs input
> digits first** — each `absorb` refines `x mod pⁿ` and drives the ledger toward
> the pinned state. The certificate `residue_depends_on_prefix` says the output
> digit stabilizes after **finitely many** absorbs. Demo B exhibits exactly this:
> output digit `aᵢ` frozen once input known `mod p^{i+1}`.

**Bihomographic (two inputs, Axis I at `p`):** the `BihTensor` 8-field algebra is
pure `ℤ` (transfers ✅); the four order-corners `{1,∞}²` become the `p²`
congruence-corners `(ℤ/p)²`; `ready` checks the candidate agrees across them with
unit denominators. Soundness = bilinear congruence analogue of `bilinear_ge_const`
(a divisibility identity, not `nlinarith`).

---

## 3. Product formula = unique factorization (for rationals)

For `x = ∏_p p^{eₚ}` (a rational, `eₚ = vₚ(x) ∈ ℤ`, finitely many nonzero):
```
 |x|_∞ = ∏_p p^{eₚ}   (= the rational's magnitude, eₚ can be ±)
 |x|_p = p^{−eₚ}
 ∏_v |x|_v = (∏_p p^{eₚ}) · ∏_p p^{−eₚ} = 1.                  ✓
```
So the product formula **is** unique factorization rephrased. For the machine, the
content is not the theorem but: *can finite emitted prefixes certify it exactly?*
The non-Archimedean `eₚ` are read finitely (`residue_depends_on_prefix` ✅); the
Archimedean magnitude is only a CF *convergent* at finite depth — hence the
finite-precision asymmetry and the `gauge_bound` conjecture (`04` §3.3).

---

## 4. Multiplicative composes, additive doesn't (the axis choice)

`|x y|_v = |x|_v |y|_v` at **every** `v` (valuations are homomorphisms) ⟹ the
product formula composes under `×` placewise, idele norm conserved (Demo D, all
places `OK`). For `+`: only `|x+y|_p ≤ max(|x|_p,|y|_p)` at finite places, nothing
at `∞`, and `x+y` may gain new places ⟹ no local product-formula law. Build the
**multiplicative** axis first (`mulTensor` per place); additive is the boundary.

---

## 5. The script

`adelic_validation.py` — exact arithmetic (`fractions.Fraction`, integers), no
floats. Demos:

- **A** product formula `∏_v|x|_v=1` on sample rationals → all `OK`.
- **B** p-adic homographic emission forced by finite input prefix → `aᵢ` frozen at
  `mod p^{i+1}`.
- **C** two emission paradigms (order floor vs congruence residue) on one quantity.
- **D** multiplicative coupling composes / additive doesn't.

Recommended next scratch (gates M4, `04` §5): item 4 (gauge-bound tabulation —
the make-or-break check), item 5 (`S`-integral soundness from emitted valuations),
item 6 (idele combination through the tensor).
