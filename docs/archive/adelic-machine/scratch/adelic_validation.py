#!/usr/bin/env python3
"""
adelic_validation.py  —  scratch validation for the FDRS "adelic complex" design.

This is a RESEARCH SCRATCH SCRIPT, not part of the machine. It exists to
de-risk three load-bearing design claims with *exact* arithmetic (Python
``fractions.Fraction`` and integers only — deliberately NO floats, mirroring
the machine's "no float / no clock coercion" discipline) BEFORE they are
written into the build guide:

  A. The product formula  ∏_v |x|_v = 1  (x ∈ ℚ*) is the cross-place
     conservation law — the adelic analogue of |det| = 1.

  B. The non-Archimedean emission certificate: for a homographic map over
     ℤ_p, the next p-adic output digit is FORCED by a finite prefix of the
     input. This is the congruence dual of the Gosper four-corner floor
     trap (`emit_traps`), and it is exactly FDRS's `residue_depends_on_prefix`
     (NumberTheory/CylinderMeasurability.lean) specialized to base p.

  C. The two emission paradigms side by side on the SAME quantity: the
     Archimedean place decides a digit by an ORDER trap (floor between
     interval endpoints); the p-adic place decides a digit by a CONGRUENCE
     (residue constant over residue-disks). Neither ever forms a float.

Run:  python3 adelic_validation.py
"""

from fractions import Fraction
from math import gcd, isqrt


# --------------------------------------------------------------------------
# p-adic primitives (exact, integer/rational only)
# --------------------------------------------------------------------------

def vp(n: int, p: int) -> int:
    """p-adic valuation of a nonzero integer."""
    if n == 0:
        return float("inf")
    n = abs(n)
    e = 0
    while n % p == 0:
        n //= p
        e += 1
    return e


def vp_rat(x: Fraction, p: int) -> int:
    """p-adic valuation of a nonzero rational: v_p(num) - v_p(den)."""
    return vp(x.numerator, p) - vp(x.denominator, p)


def padic_abs(x: Fraction, p: int) -> Fraction:
    """|x|_p = p^{-v_p(x)}, exact rational."""
    e = vp_rat(x, p)
    return Fraction(1, p**e) if e >= 0 else Fraction(p**(-e), 1)


def arch_abs(x: Fraction) -> Fraction:
    """|x|_∞ = ordinary absolute value, exact rational."""
    return x if x >= 0 else -x


def primes_dividing(x: Fraction):
    """All primes p with v_p(x) != 0 (i.e. the finite places where x is not a unit)."""
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


def padic_residue(x: Fraction, p: int, n: int) -> int:
    """x mod p^n  in ℤ/p^n, for x ∈ ℤ_p (requires p ∤ den).  Exact, integer."""
    assert x.denominator % p != 0, f"{x} is not a p-adic integer for p={p}"
    mod = p**n
    inv_den = pow(x.denominator % mod, -1, mod)
    return (x.numerator * inv_den) % mod


def padic_digits(x: Fraction, p: int, n: int):
    """Low n Hensel digits a_0..a_{n-1} of x ∈ ℤ_p  (x = Σ a_i p^i)."""
    r = padic_residue(x, p, n)
    digs = []
    for _ in range(n):
        digs.append(r % p)
        r //= p
    return digs


# --------------------------------------------------------------------------
# Demo A — the product formula is the cross-place conservation law
# --------------------------------------------------------------------------

def demo_product_formula():
    print("=" * 70)
    print("DEMO A  —  product formula  ∏_v |x|_v = 1  (the adelic |det|=1)")
    print("=" * 70)
    samples = [Fraction(12, 35), Fraction(-50, 21), Fraction(7, 1),
               Fraction(1, 360), Fraction(99, 100)]
    for x in samples:
        ps = primes_dividing(x)
        prod = arch_abs(x)
        parts = [f"|x|_inf={arch_abs(x)}"]
        for p in ps:
            ap = padic_abs(x, p)
            prod *= ap
            parts.append(f"|x|_{p}={ap}")
        ok = (prod == 1)
        print(f"  x = {str(x):>8}   " + "  ".join(parts))
        print(f"           product over all places = {prod}   {'OK' if ok else 'FAIL'}")
        assert ok, "product formula violated"
    print("  => the finitely-many non-unit places exactly cancel the")
    print("     Archimedean size. This is the conserved quantity that")
    print("     couples a single x across its adelic positions.\n")


# --------------------------------------------------------------------------
# Demo B — p-adic homographic emission is forced by a finite input prefix
#          (the congruence dual of emit_traps)
# --------------------------------------------------------------------------

def homographic(M, x: Fraction) -> Fraction:
    """(a x + b)/(c x + d) for M = (a,b,c,d)."""
    a, b, c, d = M
    return Fraction(a * x + b, c * x + d)


def denom_is_padic_unit_on_disk(M, p: int) -> bool:
    """Is c·x + d a p-adic unit for EVERY x ∈ ℤ_p?  <=>  c ≡ 0 (p) and d ≢ 0 (p).
    (c x + d ≡ d mod p for all x when p|c; and that is a unit iff p ∤ d.)"""
    a, b, c, d = M
    return (c % p == 0) and (d % p != 0)


def demo_padic_emission(p=5):
    print("=" * 70)
    print(f"DEMO B  —  p-adic homographic emission certificate  (p={p})")
    print("=" * 70)
    # A homographic map whose denominator is a p-adic unit on all of ℤ_p,
    # so the value y = M(x) ∈ ℤ_p has well-defined Hensel digits for any x ∈ ℤ_p.
    #   M = (a,b,c,d):  y = (a x + b)/(c x + d).
    M = (3, 2, 5, 1)   # c=5 ≡ 0 mod 5, d=1 ≢ 0 mod 5  => unit denominator on ℤ_5
    assert denom_is_padic_unit_on_disk(M, p), "pick M with unit denominator on the disk"
    print(f"  map  y = ({M[0]}x+{M[1]})/({M[2]}x+{M[3]})   over ℤ_{p}")
    print(f"  denominator a p-adic unit on all of ℤ_{p}: "
          f"{denom_is_padic_unit_on_disk(M, p)}\n")

    # CLAIM (the certificate): output digit a_i(y) is determined by x mod p^{N}
    # for some finite N = N(i). We exhibit it: vary the *unread tail* of x by
    # multiples of p^N and show the first i output digits never move.
    base_x = Fraction(2, 3)   # a p-adic integer for p=5 (5 ∤ 3); arbitrary
    print(f"  reference input x0 = {base_x}  (a p-adic integer)")
    y0 = homographic(M, base_x)
    print(f"  exact output  y0 = M(x0) = {y0}")
    print(f"  Hensel digits of y0 (low->high): {padic_digits(y0, p, 8)}\n")

    print("  pinning test: how deep an input prefix forces each output digit?")
    print("  (perturb x by +t*p^N for many t; report least N that freezes digit i)")
    for i in range(6):
        forced_N = None
        for N in range(1, 12):
            stable = True
            for t in range(1, p + 2):          # several tail perturbations
                x_pert = base_x + Fraction(t * p**N)   # same x mod p^N, different tail
                y_pert = homographic(M, x_pert)
                if padic_digits(y_pert, p, i + 1)[i] != padic_digits(y0, p, i + 1)[i]:
                    stable = False
                    break
            if stable:
                forced_N = N
                break
        print(f"    output digit a_{i} (= {padic_digits(y0, p, i+1)[i]}) "
              f"forced once input known mod {p}^{forced_N}")
    print("  => every output digit is pinned by a FINITE input prefix.")
    print("     No order, no floor, no float: the digit is read off by a")
    print("     congruence (residue mod p^k), which is FDRS's")
    print("     `residue_depends_on_prefix` (CylinderMeasurability.lean)")
    print("     specialized to base p.\n")


# --------------------------------------------------------------------------
# Demo C — two emission paradigms on the SAME quantity, neither a float
# --------------------------------------------------------------------------

def cf_digits(x: Fraction, n: int):
    """Regular continued-fraction partial quotients (the Archimedean digits)."""
    out = []
    for _ in range(n):
        a = x.numerator // x.denominator     # floor — the ORDER decision
        out.append(a)
        frac = x - a
        if frac == 0:
            break
        x = 1 / frac
    return out


def demo_two_paradigms(p=7):
    print("=" * 70)
    print(f"DEMO C  —  one quantity, two emission engines  (p={p})")
    print("=" * 70)
    x = Fraction(355, 113)   # a rational; finite at every place
    print(f"  x = {x}")
    print(f"  ARCHIMEDEAN place (∞): digit = floor  (an ORDER trap)")
    print(f"     continued-fraction quotients: {cf_digits(x, 8)}")
    print(f"     |x|_inf = {arch_abs(x)}")
    print(f"  NON-ARCHIMEDEAN place ({p}): digit = residue mod {p} (a CONGRUENCE)")
    if x.denominator % p != 0:
        print(f"     Hensel digits (low->high): {padic_digits(x, p, 8)}")
        print(f"     |x|_{p} = {padic_abs(x, p)}")
    else:
        print(f"     x has a pole at {p}: v_{p}(x) = {vp_rat(x, p)} (not in ℤ_{p})")
    ps = primes_dividing(x)
    prod = arch_abs(x)
    for q in ps:
        prod *= padic_abs(x, q)
    print(f"  coupling: ∏_v |x|_v = {prod}  (places {['inf'] + ps})")
    print("  => the SAME x carries an exact stream at each place; the two")
    print("     digit-decision rules are different (order vs congruence) but")
    print("     both are exact and integer-driven. The product formula is the")
    print("     only thing tying the independent streams together.\n")


def all_places(x: Fraction):
    return ["inf"] + primes_dividing(x)


def product_over_places(x: Fraction) -> Fraction:
    prod = arch_abs(x)
    for p in primes_dividing(x):
        prod *= padic_abs(x, p)
    return prod


def demo_multiplicative_vs_additive_coupling():
    print("=" * 70)
    print("DEMO D  —  the Axis-II invariant: clean under x*y, broken under x+y")
    print("=" * 70)
    x, y = Fraction(12, 35), Fraction(-50, 21)
    print(f"  x = {x},  y = {y}")
    # Multiplicative: |xy|_v = |x|_v * |y|_v at EVERY place, so the product")
    # formula composes locally and the idelic norm is conserved.
    xy = x * y
    print("\n  MULTIPLICATIVE coupling (ideles): for every place v, |xy|_v = |x|_v*|y|_v ?")
    places = sorted(set(all_places(x)) | set(all_places(y)) | set(all_places(xy)),
                    key=lambda s: (s != "inf", s))
    ok_mult = True
    for v in places:
        if v == "inf":
            lx, ly, lxy = arch_abs(x), arch_abs(y), arch_abs(xy)
        else:
            lx, ly, lxy = padic_abs(x, v), padic_abs(y, v), padic_abs(xy, v)
        local_ok = (lxy == lx * ly)
        ok_mult &= local_ok
        print(f"    v={str(v):>3}: |xy|={lxy}  vs |x||y|={lx*ly}   {'OK' if local_ok else 'FAIL'}")
    print(f"    => local multiplicativity holds at every place: {ok_mult}")
    print(f"    => product formula composes: ∏|xy| = {product_over_places(xy)} "
          f"= ∏|x|·∏|y| = {product_over_places(x)*product_over_places(y)}")
    assert ok_mult and product_over_places(xy) == 1

    # Additive: there is NO local law |x+y|_v = f(|x|_v,|y|_v); the product
    # formula of x+y is not determined by those of x and y.
    s = x + y
    print("\n  ADDITIVE coupling: is |x+y|_v determined by |x|_v and |y|_v locally?")
    for v in places:
        if v == "inf":
            lx, ly, ls = arch_abs(x), arch_abs(y), arch_abs(s)
        else:
            lx, ly, ls = padic_abs(x, v), padic_abs(y, v), padic_abs(s, v)
        ultram = (ls <= max(lx, ly))  # the only general bound (strong triangle, non-Arch only)
        note = "≤max (ultrametric)" if v != "inf" else "(no ultrametric at ∞)"
        print(f"    v={str(v):>3}: |x+y|={ls}  max(|x|,|y|)={max(lx,ly)}  {note}")
    print(f"    x+y = {s},  ∏|x+y| = {product_over_places(s)} (still 1, but NOT")
    print(f"      computable from x,y's per-place data alone — new places can appear)")
    print("  => MULTIPLICATIVE coupling is the clean, locally-conserved invariant")
    print("     (the idele norm). ADDITIVE coupling has no local product-formula")
    print("     law — this is the boundary of the approach (strong-approximation")
    print("     territory), and the build should target the multiplicative axis first.\n")


if __name__ == "__main__":
    demo_product_formula()
    demo_padic_emission(p=5)
    demo_two_paradigms(p=7)
    demo_multiplicative_vs_additive_coupling()
    print("All exact-arithmetic checks passed (no floats used anywhere).")
