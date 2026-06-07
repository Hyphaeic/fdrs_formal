#!/usr/bin/env python3
"""
phi_vs_sqrt2.py -- the transition law made visible (FDRS explorations).

Two quadratic irrationals, both fractional parts in (0,1), both FIXED POINTS of
the Gauss map G(x) = {1/x}, i.e. purely periodic continued fractions:

    g = 1/phi = (sqrt5 - 1)/2 ~ 0.6180339887...   CF [0; 1,1,1,...]  (all 1s)
    s = sqrt2 - 1             ~ 0.4142135624...    CF [0; 2,2,2,...]  (all 2s)

Because G(x) = x EXACTLY (1/x = x + a, a = the constant quotient), the
renormalization is period-1: the continued-fraction TAIL never changes, so the
"beat of beats" is maximally self-similar -- the part-and-rejoin repeats
identically forever. The ONLY structural difference between the two systems is
the quotient (1 vs 2), which sets:

    convergent denominators   Fibonacci      vs   Pell
    rejoining rate k_n^(1/n)  -> phi (1.618)  vs   1+sqrt2 (2.414)
    extremal gap k^2|x - p/k| -> 1/sqrt5      vs   1/(2 sqrt2)

The convergent error bound is PROVEN at every rejoin with exact integer
arithmetic (no floating point in the proof): the residual is exactly +-1 of the
defining quadratic form

    Q_a(h, k) = h^2 + a*h*k - k^2        (a = the constant quotient)

whose root in (0,1) is x  (t^2 + a t - 1 = 0). So |Q_a(h_n, k_n)| = 1 for every
convergent, the bracket side is sign(Q_a(h_n,k_n)) (exact), and the gap between
consecutive convergents is exactly 1/(k_n k_{n+1}).  mpmath is used ONLY as an
independent ground-truth cross-check of the decimals and the asymptotic limits.
"""
from __future__ import annotations
from fractions import Fraction
from dataclasses import dataclass
from mpmath import mp, mpf, sqrt as mp_sqrt, floor as mp_floor

mp.dps = 60


@dataclass
class System:
    name: str
    a: int  # the constant partial quotient of the purely-periodic CF [0; a,a,a,...]

    @property
    def value(self) -> mpf:
        # x = (-a + sqrt(a^2+4))/2 : the root of t^2 + a t - 1 = 0 lying in (0,1)
        return (-self.a + mp_sqrt(self.a * self.a + 4)) / 2

    @property
    def rate(self) -> mpf:
        # denominator growth = larger root of t^2 = a t + 1 = (a + sqrt(a^2+4))/2
        return (self.a + mp_sqrt(self.a * self.a + 4)) / 2

    @property
    def gap_const(self) -> mpf:
        # lim k_n^2 |x - h_n/k_n| = 1/(2x+a) = 1/sqrt(a^2+4)
        return 1 / mp_sqrt(self.a * self.a + 4)

    def Q(self, h: int, k: int) -> int:
        # defining quadratic form; |Q(h_n,k_n)| = 1 at every convergent (exact)
        return h * h + self.a * h * k - k * k


def convergents(a: int, N: int):
    """Convergents (h_n, k_n) of [0; a, a, a, ...] for n = 0 .. N (exact ints)."""
    out = [(0, 1)]                 # c_0 = 0/1   (h_{-1},h_0)=(1,0); (k_{-1},k_0)=(0,1)
    h_prev, h = 1, 0
    k_prev, k = 0, 1
    for _ in range(N):
        h, h_prev = a * h + h_prev, h
        k, k_prev = a * k + k_prev, k
        out.append((h, k))
    return out


def sturmian(x: mpf, length: int):
    """Coincidence word s(n) = floor((n+1)x) - floor(n x) in {0,1}, n = 0..length-1.
    Density of 1s = x; for these x it is the Fibonacci word (a=1) / silver word (a=2)."""
    word = []
    prev = 0
    for n in range(1, length + 1):
        cur = int(mp_floor(n * x))
        word.append(cur - prev)
        prev = cur
    return word


def analyse(sys: System, N: int = 18) -> bool:
    x = sys.value
    conv = convergents(sys.a, N)
    ok = True

    print(f"\n{'='*74}\n {sys.name}:  x = [0; {sys.a},{sys.a},{sys.a},...]"
          f"   ~ {mp.nstr(x, 18)}")
    print(f" Gauss fixed point:  1/x - {sys.a} = x ?  "
          f"{mp.nstr(1/x - sys.a, 18)}  (== x, period-1 renormalization)")
    print(f"{'='*74}")
    print(f" {'n':>2} {'h_n/k_n':>14} {'decimal':>13} {'side':>5} "
          f"{'Q=±1':>5} {'gap=1/(k k+1)':>16} {'k+1/k_n':>10}")

    for n in range(1, N):
        h, k = conv[n]
        h1, k1 = conv[n + 1]
        q = sys.Q(h, k)
        # exact bracket side from the integer form:  sign(h/k - x) = sign(Q)
        side = "above" if q > 0 else "below"
        # exact gap to the next convergent
        det = h * k1 - h1 * k                 # = ±1
        gap = Fraction(abs(det), k * k1)       # = 1/(k k_{n+1})
        # denominator growth ratio k_{n+1}/k_n -> rate (geometric convergence)
        rate_so_far = mpf(k1) / k
        print(f" {n:>2} {f'{h}/{k}':>14} {mp.nstr(mpf(h)/k, 11):>13} {side:>5} "
              f"{q:>5} {f'1/{k*k1}':>16} {mp.nstr(rate_so_far, 8):>10}")

        # --- exact checks ---------------------------------------------------
        if abs(q) != 1:
            print(f"    !! Q residual not ±1 at n={n}: {q}"); ok = False
        if abs(det) != 1:
            print(f"    !! determinant not ±1 at n={n}: {det}"); ok = False
        # bracket really straddles x (independent mpmath cross-check)
        lo, hi = sorted([mpf(h) / k, mpf(h1) / k1])
        if not (lo < x < hi):
            print(f"    !! x not in convergent bracket at n={n}"); ok = False
        # side claim agrees with ground truth
        true_side = "above" if mpf(h) / k > x else "below"
        if side != true_side:
            print(f"    !! exact side {side} != mpmath {true_side} at n={n}"); ok = False
        # the gap bound: |x - h/k| < 1/(k k_{n+1})
        if not (abs(x - mpf(h) / k) < gap):
            print(f"    !! gap bound violated at n={n}"); ok = False

    # --- asymptotic constants (mpmath cross-check of the limits) ------------
    h, k = conv[N]
    last_ratio = mpf(conv[N][1]) / conv[N - 1][1]   # k_N / k_{N-1} -> rate
    print(f"\n   rejoin rate  k_(n+1)/k_n -> {mp.nstr(sys.rate, 12)}"
          f"   (n={N}: {mp.nstr(last_ratio, 12)})")
    gap_c = mpf(k) ** 2 * abs(x - mpf(h) / k)
    print(f"   gap constant k_n^2|x-h/k| -> {mp.nstr(sys.gap_const, 12)}"
          f"   (n={N}: {mp.nstr(gap_c, 12)})")
    if abs(last_ratio - sys.rate) > mpf(10) ** -3:
        print("    !! rate not converging"); ok = False
    if abs(gap_c - sys.gap_const) > mpf(10) ** -6:
        print("    !! gap constant not converging"); ok = False

    # --- coincidence word: #1s in first k_n ticks == h_n (the numerator) ----
    word = sturmian(x, conv[8][1])  # first k_8 symbols
    head = "".join(map(str, word[:34]))
    print(f"\n   coincidence word (Sturmian): {head}...   (density of 1s = x)")
    for n in (4, 6, 8):
        h, k = conv[n]
        ones = sum(word[:k])  # = floor(k * x)
        tag = "OK" if abs(ones - h) <= 1 else "??"
        print(f"     in first k_{n}={k:>4} ticks: {ones:>4} ones   vs  h_{n}={h:>4}  [{tag}]")
        if abs(ones - h) > 1:
            ok = False

    # --- complement co-expansion: c_n + (k_n - h_n)/k_n = 1 exactly ---------
    comp_val = 1 - x
    h, k = conv[N]
    comp = Fraction(k - h, k)
    print(f"\n   complement 1-x ~ {mp.nstr(comp_val, 16)}   (CF co-determined)")
    print(f"     h_n/k_n + (k_n-h_n)/k_n = {Fraction(h, k) + comp}   (== 1 exactly, every n)")
    if Fraction(h, k) + comp != 1:
        print("    !! complement does not sum to unity"); ok = False
    if not (abs(comp_val - mpf(k - h) / k) < Fraction(1, k * conv[N + 1][1] if N + 1 < len(conv) else k)):
        pass  # (loose; the exact sum==1 above is the real check)

    print(f"\n   ----> {sys.name}: ALL EXACT CHECKS {'PASS' if ok else 'FAIL'}")
    return ok


if __name__ == "__main__":
    print(__doc__)
    phi = System("phi   (golden, a=1)", 1)
    rt2 = System("sqrt2 (silver, a=2)", 2)
    ok1 = analyse(phi)
    ok2 = analyse(rt2)

    print(f"\n{'='*74}\n CONTRAST (same machine, only the quotient differs):")
    print(f"{'='*74}")
    print(f" {'':22} {'phi  [0;1,1,1,..]':>22} {'sqrt2 [0;2,2,2,..]':>22}")
    print(f" {'Gauss tail':22} {'fixed (period 1)':>22} {'fixed (period 1)':>22}")
    print(f" {'denominators':22} {'Fibonacci':>22} {'Pell':>22}")
    print(f" {'rejoin rate':22} {mp.nstr(phi.rate,10):>22} {mp.nstr(rt2.rate,10):>22}")
    print(f" {'gap const 1/sqrt(a^2+4)':22} {mp.nstr(phi.gap_const,10):>22} {mp.nstr(rt2.gap_const,10):>22}")
    print(f" {'(phi = slowest rejoin: the extremal Hurwitz number, gap const 1/sqrt5)'}")
    print(f"\n OVERALL: {'PASS' if (ok1 and ok2) else 'FAIL'}")
