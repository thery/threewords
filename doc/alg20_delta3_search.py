#!/usr/bin/env python3
"""Is the old paper's  delta3 <= 3u^3  for Algorithm 20 actually violated?

Our Rocq proof of [ThreeProdOneTW_error] only certifies 8u^3.  That is an
UPPER bound, so it does not by itself contradict the paper: it may simply be
loose.  This script measures the true error of Algorithm 20 in binary64
(p = 53, u = 2^-53) with an exact rational reference, over random and
adversarially-constructed triple-word inputs, and reports the largest
relative error found, in units of u^3.

Algorithm 20 (old paper, Section 9) -- 3Prod^fast_{3,3}(x0,x1,x2, (1),y1,y2):

    z01+, z01- <- 2Prod(x0, y1)
    b'0, b'1   <- Fast2SumS(x1, z01+)
    z31 <- RN(z01- + x1 y1)          (FMA)
    z3  <- RN(z31 + x0 y2)           (FMA)
    s3' <- RN(b'1 + z3)
    s3  <- RN(s3' + x2)
    e0, e1, e2 <- VecSum(x0, b'0, s3)
    y0 <- e0 ; y1, y2 <- Fast2SumS(e1, e2)

Every block is error free, so the value of the result is exactly
x0 + b'0 + s3 -- that is what we compare with the exact product.
"""

from fractions import Fraction as F
import random

P = 53
U = F(1, 2 ** P)                       # u = 2^-53


def RN(x):
    """Round a Fraction to the nearest binary64, ties to even."""
    return float(x)


def fast2sum(a, b):
    """Exact, provided |b| <= |a|."""
    s = RN(F(a) + F(b))
    return s, RN(F(a) + F(b) - F(s))


def fast2sum_s(a, b):
    """The sorted Fast2Sum: error free unconditionally."""
    return fast2sum(a, b) if abs(b) <= abs(a) else fast2sum(b, a)


def alg20(x0, x1, x2, y1, y2):
    """Returns (exact value of the result, the intermediate quantities)."""
    z01p = RN(F(x0) * F(y1))
    z01m = RN(F(x0) * F(y1) - F(z01p))
    b0, b1 = fast2sum_s(x1, z01p)
    z31 = RN(F(z01m) + F(x1) * F(y1))
    z3 = RN(F(z31) + F(x0) * F(y2))
    s3p = RN(F(b1) + F(z3))
    s3 = RN(F(s3p) + F(x2))
    # VecSum and the final Fast2SumS are error free: the value is the sum.
    return F(x0) + F(b0) + F(s3), (z01p, z01m, b0, b1, z31, z3, s3p, s3)


def rel_err_u3(x0, x1, x2, y1, y2):
    val, aux = alg20(x0, x1, x2, y1, y2)
    exact = (F(x0) + F(x1) + F(x2)) * (1 + F(y1) + F(y2))
    if exact == 0:
        return None, aux
    return abs(val - exact) / abs(exact) / U ** 3, aux


def rnd_sig(bits=P):
    """A random 53-bit significand in [2^52, 2^53)."""
    return random.getrandbits(bits - 1) | (1 << (bits - 1))


def random_tw_input():
    """x = (x0,x1,x2) a P-nonoverlapping TW, y = (1,y1,y2) with |y-1|<=40u^2.

    x0 in [1,2), so ulp(x0) = 2^-52 and the constraints are
    |x1| < 2^-52, |x2| < ulp(x1), |y1| < 2^-52, |y2| < ulp(y1).
    """
    x0 = float(F(rnd_sig(), 2 ** (P - 1)))                    # [1, 2)
    # |x1| < ulp(x0) = 2^-52; put it in [2^-53, 2^-52).
    x1 = float(F(rnd_sig() * random.choice((1, -1)), 2 ** 105))
    # |x2| < ulp(x1) = 2^-105; put it in [2^-106, 2^-105).
    x2 = float(F(rnd_sig() * random.choice((1, -1)), 2 ** 158))
    # |y1| <= 40u^2 = 40 * 2^-106; scale it in [2^-106, 32 * 2^-106).
    e = random.randrange(0, 5)
    y1 = float(F(rnd_sig() * random.choice((1, -1)), 2 ** (158 - e)))
    y2 = float(F(rnd_sig() * random.choice((1, -1)), 2 ** (211 - e)))
    if abs(F(y1) + F(y2)) > 40 * U ** 2:
        return None
    return x0, x1, x2, y1, y2


def search(n=200000, seed=1):
    random.seed(seed)
    best, arg = F(0), None
    for _ in range(n):
        inp = random_tw_input()
        if inp is None:
            continue
        r, _ = rel_err_u3(*inp)
        if r is not None and r > best:
            best, arg = r, inp
    return best, arg


def targeted(n=200000, seed=2):
    """Push the two roundings that reach u^3 -- s3' = RN(b'1+z3) and
    s3 = RN(s3'+x2) -- towards their half-ulp maxima at the same time.

    |b'1| is maximal when x1 + z01+ falls halfway between two floats, and
    |x2| is maximal just under ulp(x1); we bias the search that way.
    """
    random.seed(seed)
    best, arg = F(0), None
    for _ in range(n):
        x0 = 1.0                                   # bottom of the binade
        m1 = rnd_sig()
        x1 = float(F(m1, 2 ** 105))                # [2^-53, 2^-52)
        # x2 just below ulp(x1) = 2^-105, i.e. in [2^-106, 2^-105).
        x2 = float(F(rnd_sig() * random.choice((1, -1)), 2 ** 158))
        # y1 near the 40u^2 ceiling, and tuned so that x1 + y1 is close to a
        # tie on the 2^-105 grid (that maximises |b'1|).
        half = F(1, 2 ** 106)
        base = F(random.randrange(1, 32), 2 ** 106)
        y1 = float(base + half * F(random.randrange(0, 2 ** 20), 2 ** 20))
        y2 = float(F(rnd_sig() * random.choice((1, -1)), 2 ** 211))
        if abs(F(y1) + F(y2)) > 40 * U ** 2 or abs(F(y1)) >= F(1, 2 ** 52):
            continue
        r, _ = rel_err_u3(x0, x1, x2, y1, y2)
        if r is not None and r > best:
            best, arg = r, (x0, x1, x2, y1, y2)
    return best, arg


if __name__ == "__main__":
    for name, fn in (("random", search), ("targeted", targeted)):
        best, arg = fn()
        print(f"{name:9s} max relative error = {float(best):.4f} u^3")
        if arg:
            print("           x =", [a.hex() for a in arg[:3]])
            print("           y = (1,", arg[3].hex(), ",", arg[4].hex(), ")")
