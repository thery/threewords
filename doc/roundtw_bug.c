/* roundtw_bug.c
 *
 * Demonstrates that Algorithm 7 (RoundTW) of the triple-word paper, as printed,
 * returns an INCORRECT result when x0+x1 is a midpoint.  Uses IEEE-754 binary64
 * (p = 53, u = 2^-53), so the counterexample is the direct analogue of the
 * p = 4 example (1, u, u^2).
 *
 * Build:  cc -O0 -frounding-math roundtw_bug.c -lm -o roundtw_bug
 * Run:    ./roundtw_bug
 */
#include <stdio.h>
#include <fenv.h>
#include <math.h>

#pragma STDC FENV_ACCESS ON

/* Correctly-rounded (round-to-nearest, ties-to-even) FP operations. */
static double RN(double a, double b){ fesetround(FE_TONEAREST); return a + b; }
static double RU(double a, double b){ fesetround(FE_UPWARD);    double r = a + b;
                                      fesetround(FE_TONEAREST); return r; }
static double RD(double a, double b){ fesetround(FE_DOWNWARD);  double r = a + b;
                                      fesetround(FE_TONEAREST); return r; }

/* RoundTW, parameterised by the polarity of the (star) test.
 *   printed_version = 1 : first branch on  RN(-(3/2u-2u^2)x0) != x1   (as printed)
 *   printed_version = 0 : first branch on  RN(-(3/2u-2u^2)x0) == x1   (proposed fix)
 */
static double RoundTW(double x0, double x1, double x2, int printed_version)
{
    const double u = ldexp(1.0, -53);           /* u = 2^-p, p = 53          */

    /* --- test 1: is x0 + 2*x1 exact?  (Fast2Sum error test, |x0| >= |2x1|) */
    double two_x1 = 2.0 * x1;                    /* exact (multiply by 2)     */
    double s = RN(x0, two_x1);
    double z = RN(s, -x0);                       /* z = s - x0                */
    double e = RN(two_x1, -z);                   /* e = 2x1 - z ; ==0 iff exact*/
    int inexact = (e != 0.0);

    /* --- test (star): RN( -(3/2 u - 2 u^2) * x0 ) vs x1 ------------------- */
    fesetround(FE_TONEAREST);
    double k    = 1.5 * u - 2.0 * u * u;         /* the constant 3/2 u - 2u^2 */
    double star = -(k) * x0;                     /* RN(-(3/2u-2u^2) x0)       */
    int star_ne_x1 = (star != x1);

    int first_condition = printed_version ? (inexact || star_ne_x1)
                                          : (inexact || !star_ne_x1);

    if (first_condition) {
        return RN(x0, x1);                       /* RN(x0+x1)                 */
    } else if (x2 > 0) {
        return RU(x0, x1);                       /* RU(x0+x1)                 */
    } else if (x2 < 0) {
        return RD(x0, x1);                       /* RD(x0+x1)                 */
    } else {
        return RN(x0, x1);
    }
}

int main(void)
{
    /* Triple word  x_bar = (1, u, u^2),  u = 2^-53.
     * Valid TW:  |x1| = u < ulp(x0) = 2u,  |x2| = u^2 < ulp(x1) = 2 u^2.     */
    double x0 = 1.0;
    double x1 = ldexp(1.0, -53);                 /* u   = 2^-53               */
    double x2 = ldexp(1.0, -106);                /* u^2 = 2^-106              */

    /* x0 + x1 = 1 + 2^-53 is EXACTLY the midpoint of [1, 1 + 2^-52].
     * x_bar = 1 + 2^-53 + 2^-106 is just ABOVE that midpoint, so the
     * correctly-rounded result is  1 + 2^-52 = nextafter(1, +inf).           */
    double correct = nextafter(1.0, 2.0);        /* = 1 + 2^-52               */

    double printed = RoundTW(x0, x1, x2, 1);
    double fixed_  = RoundTW(x0, x1, x2, 0);

    printf("x0 = %a  x1 = %a  x2 = %a\n", x0, x1, x2);
    printf("correct RN(x0+x1+x2)      = %a  (%.17g)\n", correct, correct);
    printf("RoundTW  (printed, '!=' ) = %a  (%.17g)   %s\n",
           printed, printed, printed == correct ? "ok" : "*** WRONG ***");
    printf("RoundTW  (fixed,   '==' ) = %a  (%.17g)   %s\n",
           fixed_,  fixed_,  fixed_  == correct ? "ok" : "*** WRONG ***");
    return 0;
}
