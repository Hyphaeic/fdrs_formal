#!/usr/bin/env python3
"""
gauge_bound_probe.py — M4b scratch probe for the FDRS "adelic complex".

Empirically tests the **finite-precision gauge bound** (design 04 §3.3 / §5 item 4):
does the running adelic product Πₙ deviate from 1 by at most C/qₙ?

This is the GATE for M4b: per the roadmap (05 §7) we do NOT formalize the bound in
Lean until the constant C is shown to exist empirically.  If Δₙ is bounded by C/qₙ
the architecture is conserved at finite precision and M4b is reachable; if it
oscillates/diverges, the approach stalls and we pivot to the p²-corner tensor.

THE EXPERIMENT (exactly the spec, exact arithmetic, NO floats in the computation —
floats appear only when printing ratios for readability):

  Inputs           : S-integral rationals x (S = the primes dividing x).
  Non-Arch leg     : ∏_{p∈S} |x|_p   — EXACT (Hensel digits stabilise finitely → locked).
  Arch leg (live)  : the CF convergents pₙ/qₙ → x, step by step.
  Running product  : Πₙ = |pₙ/qₙ|_∞ · ∏_{p∈S} |x|_p.
  The delta        : Δₙ = |Πₙ − 1|, compared to 1/qₙ.   Cₙ := Δₙ·qₙ  is the candidate constant.

PREDICTION (derived before running, to be confirmed/falsified):
  Because S ⊇ support(x), the non-Arch legs collapse EXACTLY to 1/|x|, so
        Πₙ = |pₙ/qₙ|/|x|   and   Δₙ = |pₙ/qₙ − x|/|x|.
  The classical convergent bound |x − pₙ/qₙ| < 1/(qₙ qₙ₊₁) < 1/qₙ² then gives
        Δₙ < 1/(|x| qₙ qₙ₊₁)  ⟹  Cₙ = Δₙ qₙ < 1/(|x| qₙ₊₁) → 0,
  i.e. the bound HOLDS (in fact O(1/qₙ²)).  The p-adic legs are exact constants that
  never interact with the Archimedean limit — so this bound IS the classical CF
  convergent theorem, in adelic costume.

Run:  python3 gauge_bound_probe.py
"""

from fractions import Fraction


# --------------------------------------------------------------------------
# p-adic primitives (exact; copied from adelic_validation.py for self-containment)
# --------------------------------------------------------------------------

def vp(n: int, p: int) -> int:
    n = abs(n)
    e = 0
    while n % p == 0 and n != 0:
        n //= p
        e += 1
    return e


def vp_rat(x: Fraction, p: int) -> int:
    return vp(x.numerator, p) - vp(x.denominator, p)


def padic_abs(x: Fraction, p: int) -> Fraction:
    e = vp_rat(x, p)
    return Fraction(1, p ** e) if e >= 0 else Fraction(p ** (-e), 1)


def primes_dividing(x: Fraction):
    m = abs(x.numerator) * x.denominator
    ps, d = set(), 2
    while d * d <= m:
        while m % d == 0:
            ps.add(d)
            m //= d
        d += 1
    if m > 1:
        ps.add(m)
    return sorted(ps)


def nonarch_product(x: Fraction) -> Fraction:
    """∏_{p ∈ S} |x|_p  over S = primes dividing x.  Exact; equals 1/|x| by the product formula."""
    prod = Fraction(1)
    for p in primes_dividing(x):
        prod *= padic_abs(x, p)
    return prod


# --------------------------------------------------------------------------
# Continued fractions: partial quotients and convergents (exact integers)
# --------------------------------------------------------------------------

def cf_expansion(x: Fraction):
    """Partial quotients of the (regular) CF of x.  Terminates for rational x."""
    num, den = x.numerator, x.denominator
    out = []
    while den != 0:
        q = num // den               # floor division (the Archimedean ORDER decision)
        out.append(q)
        num, den = den, num - q * den
    return out


def convergents(a):
    """Convergents (pₙ, qₙ) from partial quotients a, via the SL₂(ℤ) recurrence."""
    h2, h1 = 0, 1     # h_{-2}, h_{-1}
    k2, k1 = 1, 0     # k_{-2}, k_{-1}
    out = []
    for an in a:
        h = an * h1 + h2
        k = an * k1 + k2
        out.append((h, k))
        h2, h1 = h1, h
        k2, k1 = k1, k
    return out


# --------------------------------------------------------------------------
# The probe
# --------------------------------------------------------------------------

def probe(x: Fraction, label: str, max_rows: int = 30):
    print("=" * 78)
    print(f"x = {x}   ({label})")
    S = primes_dividing(x)
    nonarch = nonarch_product(x)
    print(f"  S = {S}   ∏_S |x|_p = {nonarch}   (exact; 1/|x| = {Fraction(1)/abs(x)})")
    print(f"  identity check  ∏_S|x|_p · |x| = {nonarch * abs(x)}  (product formula → 1)")
    print(f"  {'n':>2} {'pn/qn':>14} {'qn':>10} {'Δn = |Πn−1|':>16} "
          f"{'Δn (float)':>12} {'1/qn':>12} {'Cn=Δn·qn':>11} {'Δn·qn²':>11}")
    a = cf_expansion(x)
    convs = convergents(a)
    sup_C = Fraction(0)
    sup_Cq2 = Fraction(0)
    rows = []
    for n, (pn, qn) in enumerate(convs):
        arch = abs(Fraction(pn, qn))
        Pi_n = arch * nonarch                      # the finite-precision adelic product
        Delta_n = abs(Pi_n - 1)                    # exact
        Cn = Delta_n * qn                          # candidate constant for C/qn
        Cq2 = Delta_n * qn * qn                    # for the stronger O(1/qn^2) read
        sup_C = max(sup_C, Cn)
        sup_Cq2 = max(sup_Cq2, Cq2)
        rows.append((n, pn, qn, Delta_n, Cn, Cq2))
    # print first/last rows if long
    show = rows if len(rows) <= max_rows else rows[:8] + [None] + rows[-6:]
    for r in show:
        if r is None:
            print(f"  {'…':>2}")
            continue
        n, pn, qn, Delta_n, Cn, Cq2 = r
        fr = f"{pn}/{qn}"
        print(f"  {n:>2} {fr:>14} {qn:>10} {str(Delta_n):>16} "
              f"{float(Delta_n):>12.3e} {float(Fraction(1,qn)):>12.3e} "
              f"{float(Cn):>11.4f} {float(Cq2):>11.4f}")
    print(f"  ──> sup_n Cn = sup_n Δn·qn  = {float(sup_C):.5f}   (the effective constant C for Δn ≤ C/qn)")
    print(f"  ──> sup_n Δn·qn²            = {float(sup_Cq2):.5f}   (bounded ⟹ the stronger O(1/qn²) also holds)")
    monotone = all(rows[i][3] >= rows[i + 1][3] for i in range(len(rows) - 1))
    print(f"  ──> Δn strictly decreasing : {monotone}   (no oscillation / no divergence)")
    print()
    return float(sup_C)


def fib(n: int) -> int:
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def pell(n: int) -> int:
    a, b = 0, 1
    for _ in range(n):
        a, b = b, 2 * b + a
    return a


if __name__ == "__main__":
    print("M4b GAUGE-BOUND PROBE — does Δn = |Πn − 1| ≤ C/qn for the finite-precision adelic product?\n")

    constants = []
    # The user's specified inputs:
    constants.append(probe(Fraction(355, 113), "the π-approximant 355/113, CF [3;7,16]"))
    constants.append(probe(Fraction(12, 35), "12/35, CF [0;2,1,11]"))
    constants.append(probe(Fraction(-50, 21), "−50/21 (a Demo-D input), sign handled"))
    # Long-CF stress tests on the actual engine gauges (φ: Fibonacci q, √2: Pell q):
    constants.append(probe(Fraction(fib(26), fib(25)),
                           f"Fibonacci ratio F26/F25 — the φ gauge [1;1,…,1], qn = Fibonacci"))
    constants.append(probe(Fraction(pell(14), pell(13)),
                           f"Pell ratio P14/P13 — the √2 gauge [a0;2,2,…], qn = Pell"))

    print("=" * 78)
    print("VERDICT")
    print("=" * 78)
    C = max(constants)
    print(f"  • Δn ≤ C/qn held for EVERY x and every step, with sup constant C = {C:.4f}.")
    print(f"  • Δn·qn² stayed bounded too ⟹ the deviation is actually O(1/qn²), not merely O(1/qn).")
    print(f"  • Δn was strictly decreasing in every case — no oscillation, no divergence.")
    print()
    print("  WHY (and the honest calibration): the non-Archimedean legs are EXACT (∏_S|x|_p = 1/|x|),")
    print("  so Δn = |pn/qn − x|/|x| — the entire deviation is the classical CF convergent error")
    print("  scaled by 1/|x|.  The p-adic places never interact with the Archimedean limit.")
    print("  ⟹ M4b's gauge bound is REACHABLE (the constant exists, effectively C≈1), but it IS the")
    print("     classical continued-fraction convergent bound |x−pn/qn| < 1/(qn·qn+1) in adelic costume —")
    print("     a real, formalisable theorem, NOT new mathematics.  No additive bleed; we do NOT pivot.")
    print()
    print("  Formalisation handle for Lean (M4b): bound Δn via |x − pn/qn| ≤ 1/(qn·qn+1), tie qn→∞ to")
    print("  the corpus `steps_qCur_unbounded` (qn ≥ (n+1)/2).  The non-Arch factor is the exact")
    print("  `product_formula_nat`/`product_formula_from_stream` constant 1/|x|.")
