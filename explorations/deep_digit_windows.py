#!/usr/bin/env python3
"""
Double-check: can we put a 'window at the head' and read very deep digits of pi
WITHOUT preserving the entire left-hand side?

Answer: yes -- but only in base 2^k (hex), via BBP digit extraction, and it is
NOT free. Reaching depth n still costs ~n modular exponentiations; the win is
O(log n) MEMORY (no left-hand side stored) + random access + parallelism.

This is the OPPOSITE regime from pi_spigot_fdrs.py:
  * Rabinowitz-Wagon (base 10, odometer): the head digit depends on the ENTIRE
    tail through the carry chain -> cannot be windowed, must stream.
  * BBP (base 16, congruence): each digit position is an independent modular
    probe -> windowing / deep random access is the native mode.

In FDRS terms these are the two aspects: the additive odometer (carry-coupled,
sequential) vs. the congruence/cylinder side (modular, position-independent).
"""
from __future__ import annotations
import time


def bbp_pi_hex(n: int, ndigits: int = 1) -> str:
    """
    Hex digits of pi beginning at 0-indexed fractional position `n`, via the
    Bailey-Borwein-Plouffe formula. O(log n) memory, ~O(n log n) time.

    pi = sum_{k>=0} 16^-k * (4/(8k+1) - 2/(8k+4) - 1/(8k+5) - 1/(8k+6))
    """
    def series(j: int) -> float:
        # fractional part of sum_{k=0}^{inf} 16^(n-k) / (8k+j)
        total = 0.0
        # left part k = 0..n : reduce 16^(n-k) mod (8k+j) (this is the whole trick)
        for k in range(n + 1):
            denom = 8 * k + j
            total += pow(16, n - k, denom) / denom
            total -= int(total)            # keep only the fractional part
        # right part k > n : terms shrink geometrically, a handful suffice
        k = n + 1
        while True:
            term = 16.0 ** (n - k) / (8 * k + j)
            if term < 1e-17:
                break
            total += term
            k += 1
        return total - int(total)

    x = 4.0 * series(1) - 2.0 * series(4) - series(5) - series(6)
    x -= int(x)
    if x < 0:
        x += 1.0
    out = []
    for _ in range(ndigits):
        x *= 16.0
        d = int(x)
        out.append("0123456789ABCDEF"[d])
        x -= d
    return "".join(out)


def bbp_modexp_count(n: int) -> int:
    """How many modular exponentiations a depth-n probe costs (the honest price)."""
    return 4 * (n + 1)  # one modexp per k per the 4 series sums


def pi_hex_via_mpmath(n_hex: int) -> str:
    """Ground-truth: first n_hex hex fractional digits of pi using mpmath."""
    from mpmath import mp
    mp.dps = int(n_hex * 1.21) + 30
    frac = mp.pi - 3
    s = []
    for _ in range(n_hex):
        frac *= 16
        d = int(frac)
        s.append("0123456789ABCDEF"[d])
        frac -= d
    return "".join(s)


def hex_digit_via_mpmath(pos: int) -> str:
    """Single hex fractional digit of pi at 0-indexed position `pos`."""
    from mpmath import mp
    mp.dps = int((pos + 4) * 1.21) + 30
    frac = mp.pi - 3
    for _ in range(pos):
        frac *= 16
        frac -= int(frac)
    frac *= 16
    return "0123456789ABCDEF"[int(frac)]


if __name__ == "__main__":
    print("Deep-digit windowing double-check (BBP, base 16)")
    print("-" * 66)

    # ---- 1. Shallow correctness: BBP random-access == ground-truth expansion.
    truth = pi_hex_via_mpmath(40)
    got = "".join(bbp_pi_hex(n, 1) for n in range(40))
    print(f"pi hex (mpmath) : {truth}")
    print(f"pi hex (BBP)    : {got}")
    print(f"shallow match   : {got == truth}")
    print()

    # ---- 2. Deep random access: jump straight to deep positions, O(log n) memory.
    print("Deep windows -- each computed directly, NO preceding digits stored:")
    for pos in (1_000, 100_000, 1_000_000):
        t0 = time.time()
        win = bbp_pi_hex(pos, 6)         # a 6-hex-digit window at depth `pos`
        dt = time.time() - t0
        ref = hex_digit_via_mpmath(pos)  # cross-check just the leading digit
        ok = win[0] == ref
        print(f"  pos {pos:>9,}: window={win}  leading-vs-mpmath={ref} "
              f"match={ok}  modexps~{bbp_modexp_count(pos):,}  time={dt:.2f}s")
    print()
    print("Note: memory is O(log n) (a few ints), but total work ~ n modexps --")
    print("      'deep' is still genuinely expensive; it is space + parallel + ")
    print("      random-access that you win, not the arithmetic.")
