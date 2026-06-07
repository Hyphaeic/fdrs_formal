#!/usr/bin/env python3
"""
Rabinowitz-Wagon pi spigot, expressed as an FDRS "walls + carry-routing" odometer.

GOLDEN MODEL for the FPGA datapath (exploration option (a)). The point is not
speed; it is that every operation maps directly onto the FDRS Phase-9/10 fabric,
so the eventual RTL is a transcription, not a redesign:

  * Each array position i is a CELL with a WALL at d_i = 2*i + 1 (the Phase-9
    radix wall). It holds a token A[i] with 0 <= A[i] < d_i. Position 0 is the
    decimal HEAD (its "wall" is the output base, 10).
  * One decimal step = INJECT (x10) into every cell, then a CARRY WAVE sweeps
    right-to-left (least- to most-significant): each cell keeps the residue
    x % d_i and ROUTES the overflow x // d_i to its left neighbour. That is
    exactly Phase-9 Theorem 61: carry == overflow event routed to cell i-1.
  * The head emits a decimal predigit; a small FINALITY BUFFER holds 9s/0s
    until an incoming carry resolves them. The "held 9s" folklore == prefix
    finality (a digit is final once no carry can reach back to it).

No floating point and no big-number multiply: every cell does one small-int
mul + one divmod, which is a fixed-width carry chain in hardware.

Run directly to self-verify against the known digits of pi.
"""

from __future__ import annotations

# First 120 digits of pi (no decimal point) for the self-test.
KNOWN_PI = (
    "3141592653589793238462643383279502884197"
    "1693993751058209749445923078164062862089"
    "9862803482534211706798214808651328230664"
)


def wall(i: int) -> int:
    """Phase-9 wall (radix) at cell i (0-indexed): d_i = 2i + 1."""
    return 2 * i + 1


def spigot_pi(n_digits: int):
    """
    Stream the first `n_digits` decimal digits of pi.

    Returns (digits, trace) where digits is a list[int] and trace records, per
    emitted-step, the carry-out of the head (q) so we can inspect the carry/
    finality topology later. Cells = mixed-radix odometer; the inner sweep is
    the carry wave / overflow routing.
    """
    # Guard digits: the last digit(s) of any spigot run are unreliable (the tail
    # truncation + an unflushed finality buffer can be off by one). Compute a few
    # extra and trim -- the requested digits then all sit in the safe zone.
    guard = 8
    n_total = n_digits + guard

    # Cell count. Each decimal digit consumes ~log10(pi-series radix) of depth;
    # the classic bound is floor(10*n/3) + a little headroom for the tail.
    n_cells = (10 * n_total) // 3 + 10

    # Every cell initialised to the series constant 2 (pi = 2 + 1/3(2 + 2/5(2 + ...))).
    A = [2] * n_cells

    digits: list[int] = []
    trace: list[int] = []
    held = 0           # finality buffer: number of held 9s awaiting resolution
    predigit = 0       # most recent not-yet-final digit
    started = False    # drop the initial (spurious) predigit

    for _ in range(n_total + 1):  # one warm-up step before the first real digit
        # 1+2. INJECT x10 and run the CARRY WAVE from the deepest cell inward.
        carry = 0
        for i in range(n_cells - 1, 0, -1):
            x = 10 * A[i] + carry * (i + 1)   # inject x10; absorb carry from cell i+1
            d = wall(i)                        # wall at this cell = 2i+1
            A[i] = x % d                       # residue STAYS (token under the wall)
            carry = x // d                     # overflow ROUTED to cell i-1
        # HEAD cell (i = 0): the wall here is the output base 10.
        x = 10 * A[0] + carry
        A[0] = x % 10
        q = x // 10
        trace.append(q)

        # 3. FINALITY BUFFER. q is the freshly produced decimal value at the head.
        if q == 9:
            # Cannot commit yet: a later carry might turn this 9 into a 0-with-carry.
            held += 1
        elif q == 10:
            # Carry resolved upward: the held 9s all roll over to 0s, predigit +1.
            digits.append(predigit + 1)
            digits.extend([0] * held)
            held = 0
            predigit = 0
        else:
            # q in 0..8: the previous predigit (and any held 9s) are now FINAL.
            if started:
                digits.append(predigit)
            digits.extend([9] * held)
            held = 0
            predigit = q
            started = True

    digits.append(predigit)
    return digits[:n_digits], trace


def _selftest() -> bool:
    n = len(KNOWN_PI)
    digits, _ = spigot_pi(n)
    got = "".join(str(d) for d in digits)
    ok = got == KNOWN_PI
    print(f"  requested digits : {n}")
    print(f"  got              : {got[:60]}...")
    print(f"  known pi         : {KNOWN_PI[:60]}...")
    if ok:
        print(f"  RESULT           : PASS ({n}/{n} digits match)")
    else:
        # find first mismatch
        k = next((j for j in range(min(len(got), n)) if got[j] != KNOWN_PI[j]), None)
        print(f"  RESULT           : FAIL (first mismatch at index {k})")
        if k is not None:
            print(f"                     got '{got[k:k+10]}' vs '{KNOWN_PI[k:k+10]}'")
    return ok


if __name__ == "__main__":
    print("Rabinowitz-Wagon pi spigot as an FDRS walls/carry-routing odometer")
    print("-" * 66)
    _selftest()
