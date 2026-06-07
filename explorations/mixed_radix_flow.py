#!/usr/bin/env python3
"""
One integer-carry fabric, many constants -- swap only the RADIX LAW.

Claim under test: a wide class of numbers is a SIMPLE integer string in a chosen
mixed-radix system, and their digit expansion in any output base can be "flowed
out" with nothing but integer carry arithmetic.

The shared fabric (`carry_wave`) is identical for every constant:
    inject xB into every cell, sweep deep->head,
    residue STAYS in the cell (x % wall), quotient ROUTES left (x // wall).

What changes per constant is a small bundle -- the "radix law determined at
evaluation time" (the local algebra of the coupled-digit network):
    init       : the uniform integer every cell starts at
    wall(i)    : the per-cell modulus (the radix wall)
    mult(i)    : the multiplier applied to the incoming carry
    head       : how the spill at the head becomes an output digit

  pi : init=2, wall(i)=2i+1, mult(i)=i+1, head=base-10 cell + finality buffer
  e  : init=1, wall(j)=j,    mult(j)=1,   head=spill is the digit directly

The structure of pi / e lives entirely in that law, not in the digits.
Both are verified below against their known decimal expansions.
"""
from __future__ import annotations

# full pi (with the leading 3) and the FRACTIONAL part of e (after the '2.').
PI_REF = ("3141592653589793238462643383279502884197"
          "1693993751058209749445923078164062862089")
E_REF = ("7182818284590452353602874713526624977572"
         "4709369995957496696762772407663035354759")


def carry_wave(A, lo, hi, wall, mult, B=10):
    """The shared dataflow. Inject xB into cells [lo, hi]; sweep hi -> lo; each
    cell keeps the residue and routes the quotient to its left neighbour.
    Returns the carry that spills out of cell `lo`."""
    carry = 0
    for i in range(hi, lo - 1, -1):
        x = B * A[i] + carry * mult(i)
        d = wall(i)
        A[i] = x % d           # residue stays under the wall
        carry = x // d         # quotient routes left
    return carry


def pi_flow(n):
    """pi via the Euler-transformed Gregory-Leibniz radix law."""
    n_total = n + 12
    n_cells = (10 * n_total) // 3 + 12
    A = [2] * n_cells                                   # uniform string of 2s
    digits, held, predigit, started = [], 0, 0, False
    for _ in range(n_total + 1):
        carry = carry_wave(A, 1, n_cells - 1,
                           wall=lambda i: 2 * i + 1, mult=lambda i: i + 1)
        x = 10 * A[0] + carry                           # base-10 head cell
        A[0], q = x % 10, x // 10
        if q == 9:
            held += 1
        elif q == 10:
            digits.append(predigit + 1); digits.extend([0] * held); held = 0; predigit = 0
        else:
            if started: digits.append(predigit)
            digits.extend([9] * held); held = 0; predigit = q; started = True
    digits.append(predigit)
    return digits[:n]


def e_flow(n):
    """e (fractional part) via the factorial-base radix law."""
    n_total = n + 15
    n_cells = n_total + 2
    A = [1] * n_cells                                   # uniform string of 1s
    digits = []
    for _ in range(n_total):
        carry = carry_wave(A, 2, n_cells - 1,
                           wall=lambda j: j, mult=lambda j: 1)
        digits.append(carry)                            # spill is the digit
    return digits[:n]


def pi_flow_base(n, B):
    """The SAME pi object (all-2s under walls 2i+1), read out in OUTPUT base B.
    Only B changes -- the input law (2i+1) that makes the object *be* pi is fixed.
    `B` is the observation/readout base; it is decoupled from pi's identity."""
    import math
    n_total = n + 16
    n_cells = int(n_total * math.log(B) / math.log(10) * 10 / 3) + 25
    A = [2] * n_cells
    digits, held, predigit, started = [], 0, 0, False
    for _ in range(n_total + 1):
        carry = carry_wave(A, 1, n_cells - 1,
                           wall=lambda i: 2 * i + 1, mult=lambda i: i + 1, B=B)
        x = B * A[0] + carry                                # head reduces in base B
        A[0], q = x % B, x // B
        if q == B - 1:
            held += 1
        elif q == B:
            digits.append(predigit + 1); digits.extend([0] * held); held = 0; predigit = 0
        else:
            if started: digits.append(predigit)
            digits.extend([B - 1] * held); held = 0; predigit = q; started = True
    digits.append(predigit)
    return digits[:n]


# pi in three readout bases (verified vs mpmath) -- same object, different lens.
_PI_BASE = {
    10: "3141592653589793238462643383279502884197",
    16: "3243F6A8885A308D313198A2E03707344A409382",
     8: "3110375524210264302151423063050560067016",
}
_DIG = "0123456789ABCDEF"


def _check(name, fn, ref):
    got = "".join(map(str, fn(len(ref))))
    ok = got == ref
    k = None if ok else next((j for j in range(len(ref)) if got[j] != ref[j]), None)
    print(f"  {name:<3}: {'PASS' if ok else 'FAIL @' + str(k)}  {got[:50]}...")
    return ok


if __name__ == "__main__":
    print("One integer-carry fabric (carry_wave); the radix law is the only knob")
    print("-" * 70)
    _check("pi", pi_flow, PI_REF)
    _check("e",  e_flow,  E_REF)
    print("-" * 70)
    print("Same dataflow, different law -> different transcendental flows out.")
    print()
    print("Same pi OBJECT, different OUTPUT base (B is the only knob):")
    for B, ref in sorted(_PI_BASE.items()):
        got = "".join(_DIG[d] for d in pi_flow_base(len(ref), B))
        print(f"  base {B:>2}: {got}  [{'PASS' if got == ref else 'FAIL'}]")
    print("Digit VALUES change with the readout base; pi's identity (walls 2i+1) does not.")
