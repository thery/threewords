#!/usr/bin/env python3
"""Trying (so far WITHOUT success) to break the old paper's  delta3 <= 3u^3.

Algorithm 20 (old paper, Section 9) is 3Prod^fast_{3,3}(x0,x1,x2,(1),y1,y2),
the triple-word product with a head-1 second argument that Algorithm 14 (3Div)
uses for its last multiplication.  Section 9 describes its error analysis as
"that of Algorithm 18 with an additional 2u^3", i.e. delta3 <= 3u^3 + 264u^4.
Our Rocq bound [ThreeProdOneTW_error] only certifies 8u^3 + 1330u^4, so the
question is whether the paper is wrong or our bound is loose.

STATUS: the paper is NOT refuted.  The largest relative error we have reached
on inputs that really satisfy the hypotheses is about 2.5u^3, below 3u^3.

WHAT WENT WRONG THE FIRST TIME, and why the check below matters.  A directed
search does reach 6u^3 -- with

    x = (1, -0x1.fffffffffffffp-53, -0x1.ffffffffffffap-106)
    y = (1, -0x1.0p-104, -0x1.f8p-153)

both roundings landing on a tie (|b'1| = 2u^2, eta3 = -2u^3, eta4 = -4u^3) --
but that y is NOT a triple word: |y2| = 2^-152 exceeds ulp(y1) = 2^-156 by
four binades.  [check_hypotheses] rejects it.  Any candidate must satisfy

    |x1| < ulp(x0),  |x2| < ulp(x1),  |y1| < ulp(1),  |y2| < ulp(y1),
    |y1 + y2| <= 40u^2,

and the last two together are what keep the two ties from firing at once: to
put b'1 + z3 in the binade above 2^-105 one needs z3 to have the sign of b'1
and a magnitude of a few 2^-158, and z3 = RN(RN(x1 y1) + y2) is then pinned by
|y2| < ulp(y1).

WHERE OUR 8u^3 IS LOOSE (the three steps to tighten, in doc/thm10.md):
  * |x2| <= 4u^2|x0| should be 2u^2|x0|: |x1| < ulp(x0) puts x1 at least one
    binade down, so ulp(x1) <= u * ulp(x0);
  * |b'1| <= 2u^2|x0| is attained only when b'0 reaches ulp(x0) exactly;
  * eta4 <= u|s3' + x2| should be the half-ulp of s3' + x2, which is smaller
    whenever that sum stays in the binade below.
"""


from fractions import Fraction as F
import math

P = 53
U = F(1, 2 ** P)
U3 = U ** 3

# The 6u^3 candidate -- REJECTED by check_hypotheses (y is not a TW).
WITNESS = (
    1.0,
    float.fromhex("-0x1.fffffffffffffp-53"),
    float.fromhex("-0x1.ffffffffffffap-106"),
    float.fromhex("-0x1.0000000000000p-104"),
    float.fromhex("-0x1.f800000000000p-153"),
)


def fast2sum(a, b):
    """Error free provided |b| <= |a|; the residual is computed exactly."""
    s = a + b
    return s, float(F(a) + F(b) - F(s))


def fast2sum_s(a, b):
    """Fast2SumS: Fast2Sum preceded by the test that sorts its arguments."""
    return fast2sum(a, b) if abs(b) <= abs(a) else fast2sum(b, a)


def alg20(x0, x1, x2, y1, y2):
    """Returns the exact value of the result and the interesting internals.

    Every block (2Prod, the two sorted Fast2Sums, VecSum) is error free, so
    the value of the returned triple word is exactly x0 + b'0 + s3.
    """
    prod = F(x0) * F(y1)
    z01p = float(prod)                      # 2Prod(x0, y1)
    z01m = float(prod - F(z01p))
    b0, b1 = fast2sum_s(x1, z01p)           # Fast2SumS(x1, z01+)
    z31 = float(F(z01m) + F(x1) * F(y1))    # FMA
    z3 = float(F(z31) + F(x0) * F(y2))      # FMA
    s3p = float(F(b1) + F(z3))              # Algorithm 18's s3
    s3 = float(F(s3p) + F(x2))              # the one new line
    eta3 = F(s3p) - (F(b1) + F(z3))
    eta4 = F(s3) - (F(s3p) + F(x2))
    return F(x0) + F(b0) + F(s3), dict(b0=b0, b1=b1, z3=z3, s3p=s3p, s3=s3,
                                       eta3=eta3, eta4=eta4)


def rel_err_u3(x0, x1, x2, y1, y2):
    val, aux = alg20(x0, x1, x2, y1, y2)
    exact = (F(x0) + F(x1) + F(x2)) * (1 + F(y1) + F(y2))
    return (val - exact) / abs(exact) / U3, aux


def check_hypotheses(x0, x1, x2, y1, y2):
    """x P-nonoverlapping TW, y = (1,y1,y2) TW with |y - 1| <= 40u^2."""
    return dict(
        x_tw=abs(x1) < math.ulp(abs(x0)) and abs(x2) < math.ulp(abs(x1)),
        y_tw=abs(y1) < math.ulp(1.0) and abs(y2) < math.ulp(abs(y1)),
        y_near_1=abs(F(y1) + F(y2)) <= 40 * U ** 2,
    )


def search():
    """Directed search, with the hypotheses ENFORCED on every candidate."""
    best = (F(0), None, None)
    x0 = 1.0
    for sgn in (1, -1):
        for w in range(2, 21):                    # y1 = sgn * w * 2^-105
            y1 = float(F(sgn * w, 2 ** 105))
            x1 = float(F(sgn * (2 ** 53 + 1 - w), 2 ** 105))
            if abs(x1) >= 2.0 ** -52:
                continue
            step = math.ulp(math.ulp(abs(y1)) / 2)     # y2's granularity
            n = int(F(math.ulp(abs(y1))) / F(step))
            for k in range(-n + 1, n):            # y2 = k * step, |y2| < ulp(y1)
                y2 = float(F(k) * F(step))
                for i in range(1, 96):            # x2 just below ulp(x1)
                    x2 = float(F(sgn * (2 ** 53 - i), 2 ** 158))
                    inp = (x0, x1, x2, y1, y2)
                    if not all(check_hypotheses(*inp).values()):
                        continue
                    e, _ = rel_err_u3(*inp)
                    if abs(e) > best[0]:
                        best = (abs(e), inp, None)
    return best


def report(inp):
    x0, x1, x2, y1, y2 = inp
    e, aux = rel_err_u3(*inp)
    h = check_hypotheses(*inp)
    print("  x = (", x0.hex(), ",", x1.hex(), ",", x2.hex(), ")")
    print("  y = ( 1 ,", y1.hex(), ",", y2.hex(), ")")
    print("  hypotheses:", h)
    print(f"  |b'1| = {float(F(aux['b1']) / U ** 2):+.4f} u^2"
          f"   (the algorithm's maximum)")
    print(f"  eta3  = {float(aux['eta3'] / U3):+.4f} u^3")
    print(f"  eta4  = {float(aux['eta4'] / U3):+.4f} u^3")
    print(f"  relative error = {float(e):+.6f} u^3"
          f"     [old paper: <= 3 u^3, our Rocq bound: <= 8 u^3]")
    if not all(h.values()):
        print("  *** HYPOTHESES VIOLATED -- not a counterexample ***")


if __name__ == "__main__":
    print("The 6u^3 candidate (rejected -- y is not a triple word):")
    report(WITNESS)
    print("\nDirected search with the hypotheses enforced ...")
    best, inp, _ = search()
    print(f"  search maximum = {float(best):.6f} u^3")
    if inp:
        report(inp)
