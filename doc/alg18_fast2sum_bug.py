#!/usr/bin/env python3
"""Algorithm 18 of doc/old-triplewors.pdf (Section 8.4) does NOT achieve its
claimed relative error  delta2 = u^3 + 260u^4  in binary64.

Algorithm 18 -- 3Prod^fast_{2,3}(b0, b1, (1), i1, i2), 20 flops -- computes
b_bar * i_bar for a double word b_bar = (b0,b1) and a triple word
i_bar = (1, i1, i2) whose head is 1.  Its second line is

    b'0, b'1 <- Fast2Sum(b1, z01+)        with (z01+, z01-) = 2Prod(b0, i1)

and Remark 10 justifies the Fast2Sum by: "if the condition to be errorless is
false, it means that b1 is very small, so that the global error will be small
anyway".

That is not so.  The condition fails exactly when |b1| < |z01+|, and the
worst case is |b1| ~ ulp(z01+): b1 is then ABSORBED by the addition, and what
is lost is ~ u|z01+| ~ u * 41u^2 = 41u^3 -- not O(u^4).  Since |i1| <= 41u^2
holds along Algorithm 13 (i_bar = 2 - 3Prod(b_bar, x_bar) is within 35u^2 of
1), such inputs are legal.

Below: a search over legal (i1, b1) reaching 32u^3, i.e. 32x the claimed
bound; replacing that single Fast2Sum by a 2Sum (one extra operation) drops
the error to ~1e-29 u^3.  Theorem 12 of the old paper, and Theorem 9 of
doc/paper3.pdf (11.5u^3 + 1465u^4), rest on delta2, so the fix matters.
"""
from fractions import Fraction as F
import random

u = F(2) ** -53

def two_prod(a, b):
    p = a * b
    return p, float(F(a) * F(b) - F(p))

def fast2sum(a, b):
    s = a + b; z = s - a; return s, b - z

def two_sum(a, b):
    s = a + b; ap = s - b; bp = s - ap; return s, (a - ap) + (b - bp)

def vecsum3(x0, x1, x2):
    s1, e1 = two_sum(x1, x2); s0, e0 = two_sum(x0, s1); return s0, e0, e1

def alg18(b0, b1, i1, i2, use_2sum=False):
    """Algorithm 18; use_2sum=True is the proposed one-operation fix."""
    z01p, z01m = two_prod(b0, i1)
    bp0, bp1 = (two_sum if use_2sum else fast2sum)(b1, z01p)
    z31 = z01m + b1 * i1
    z3 = z31 + b0 * i2
    s3 = bp1 + z3
    e0, e1, e2 = vecsum3(b0, bp0, s3)
    y1, y2 = fast2sum(e1, e2)
    return e0, y1, y2

def rel_err(b0, b1, i1, i2, use_2sum=False):
    y = alg18(b0, b1, i1, i2, use_2sum)
    exact = (F(b0) + F(b1)) * (1 + F(i1) + F(i2))
    comp = F(y[0]) + F(y[1]) + F(y[2])
    return float(abs(comp - exact) / abs(exact) / u ** 3)

if __name__ == "__main__":
    b0, i2 = 1.0, 0.0
    # the documented witness
    i1 = float.fromhex("0x1.2c554c0fcea8ap-101")   # |i1| <= 41u^2
    b1 = float.fromhex("0x1.0000a7e4e5e5ap-154")   # |b1| <= u, absorbed window
    print("witness:  i1 = %s   b1 = %s" % (i1.hex(), b1.hex()))
    print("  Algorithm 18 as printed : %6.1f u^3   (claimed: 1 u^3 + 260u^4)"
          % rel_err(b0, b1, i1, i2))
    print("  with a 2Sum instead     : %.2g u^3" % rel_err(b0, b1, i1, i2, True))
    random.seed(7)
    worst = 0.0
    for _ in range(200000):
        j1 = float(F(random.uniform(0.5, 1.0)) * 41 * u * u) * random.choice([1, -1])
        c1 = float(abs(F(j1)) * 2 ** random.uniform(-8, 2) * F(2) ** -53) \
             * random.choice([1, -1])
        if abs(c1) > float(u):
            continue
        worst = max(worst, rel_err(b0, c1, j1, i2))
    print("  worst over 200000 random legal inputs: %.1f u^3" % worst)
