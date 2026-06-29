/*
 * test_zeros.c -- what happens to TWSum when a triple-word contains zeros?
 *
 * The merge step orders the 6 limbs by decreasing magnitude, so any zero
 * limb is pushed to the tail; VSEB then folds vanishing error terms back
 * instead of emitting a limb.  This program builds triple-words that
 * deliberately contain zero limbs (trailing zeros, interior zeros, exact
 * cancellation to a full zero, ...) and checks, for each case, that the
 * result of tw_sum:
 *
 *   (1) is magnitude-sorted   ( |r0| >= |r1| >= |r2| ),
 *   (2) has no zero "hole" followed by a non-zero limb
 *       (a well-formed TW pads zeros only at the tail),
 *   (3) represents the EXACT sum of the inputs (residual == 0 here,
 *       since 6 limbs sum without rounding in these small cases).
 *
 * The exact value of a sum of binary32 numbers is tracked with a Shewchuk
 * floating-point expansion (a list of non-overlapping floats whose sum is
 * the exact value); two_sum is error-free, so the expansion is exact.
 *
 * Build:  make test   (or: cc -O2 test_zeros.c tw_add.c -lm -o test_zeros)
 */
#include "tw_add.h"
#include <math.h>
#include <stdio.h>

/* error-free 2Sum, local copy (tw_add.c keeps its own static one) */
static void two_sum(float a, float b, float *r, float *e) {
    float s = a + b;
    float aa = s - b;
    float bb = s - aa;
    *e = (a - aa) + (b - bb);
    *r = s;
}

/* ---- exact float expansions (Shewchuk) ----------------------------- */
#define MAXE 64

/* grow: out[] is an exact expansion whose sum is (sum e[0..ne-1]) + f */
static int grow(const float *e, int ne, float f, float *out) {
    float q = f;
    int k = 0;
    for (int i = 0; i < ne; i++) {
        float s, h;
        two_sum(e[i], q, &s, &h);
        q = s;
        if (h != 0.0f)
            out[k++] = h;
    }
    out[k++] = q;
    return k;
}

/* exact sum of xs[0..n-1] as an expansion */
static int exact_sum(const float *xs, int n, float *out) {
    float tmp[MAXE];
    int ne = 0;
    for (int i = 0; i < n; i++) {
        int k = grow(out, ne, xs[i], tmp);
        for (int j = 0; j < k; j++)
            out[j] = tmp[j];
        ne = k;
    }
    return ne;
}

/* value of an expansion (summed small-to-large, in double, for display) */
static double value_of(const float *e, int ne) {
    /* simple insertion sort by |.| ascending */
    float s[MAXE];
    for (int i = 0; i < ne; i++)
        s[i] = e[i];
    for (int i = 1; i < ne; i++) {
        float v = s[i];
        int j = i - 1;
        while (j >= 0 && fabsf(s[j]) > fabsf(v)) {
            s[j + 1] = s[j];
            j--;
        }
        s[j + 1] = v;
    }
    double acc = 0.0;
    for (int i = 0; i < ne; i++)
        acc += (double)s[i];
    return acc;
}

/* exact residual  (r0+r1+r2) - (a + b)  as a double (0 means exact) */
static double residual(tw_fpr a, tw_fpr b, tw_fpr r) {
    float terms[9] = {r.x[0],  r.x[1],  r.x[2],  -a.x[0], -a.x[1],
                      -a.x[2], -b.x[0], -b.x[1], -b.x[2]};
    float e[MAXE];
    int ne = exact_sum(terms, 9, e);
    return value_of(e, ne);
}

static double tw_value(tw_fpr a) {
    float terms[3] = {a.x[0], a.x[1], a.x[2]};
    float e[MAXE];
    int ne = exact_sum(terms, 3, e);
    return value_of(e, ne);
}

/* ---- well-formedness checks ---------------------------------------- */
static int is_sorted(tw_fpr r) {
    return fabsf(r.x[1]) <= fabsf(r.x[0]) && fabsf(r.x[2]) <= fabsf(r.x[1]);
}

/* a zero limb must not be followed by a non-zero one */
static int no_hole(tw_fpr r) {
    if (r.x[0] == 0.0f && (r.x[1] != 0.0f || r.x[2] != 0.0f))
        return 0;
    if (r.x[1] == 0.0f && r.x[2] != 0.0f)
        return 0;
    return 1;
}

static tw_fpr mk(float a, float b, float c) {
    tw_fpr r;
    r.x[0] = a;
    r.x[1] = b;
    r.x[2] = c;
    return r;
}

/* ---- normalise three floats into a well-formed triple-word (ToTW) --- */
static void fast_two_sum(float a, float b, float *r, float *e) {
    float s = a + b;
    float z = s - a;
    *e = b - z;
    *r = s;
}

static tw_fpr to_tw(float a, float b, float c) {
    float d0, d1, s1, e0, e1, e2;
    /* d0+d1 = a+b */
    two_sum(a, b, &d0, &d1);
    /* vec_sum on (d0,d1,c) */
    two_sum(d1, c, &s1, &e2);
    two_sum(d0, s1, &e0, &e1);
    /* VSEB(3) on (e0,e1,e2) */
    tw_fpr r;
    float r0, ep0;
    fast_two_sum(e0, e1, &r0, &ep0);
    r.x[0] = r0;
    fast_two_sum(ep0, e2, &r.x[1], &r.x[2]);
    return r;
}

static int failures = 0;

static void run(const char *name, tw_fpr a, tw_fpr b) {
    tw_fpr r = tw_sum(a, b);
    double res = residual(a, b, r);
    int sorted = is_sorted(r);
    int hole = !no_hole(r);

    printf("--- %s\n", name);
    printf("  a      = (%.9g, %.9g, %.9g)\n", a.x[0], a.x[1], a.x[2]);
    printf("  b      = (%.9g, %.9g, %.9g)\n", b.x[0], b.x[1], b.x[2]);
    printf("  a+b    = (%.9g, %.9g, %.9g)\n", r.x[0], r.x[1], r.x[2]);
    printf("  value  a=%.17g  b=%.17g  r=%.17g\n", tw_value(a), tw_value(b),
           tw_value(r));
    printf("  residual r-(a+b) = %.3e   sorted=%s   tail-padded=%s\n", res,
           sorted ? "yes" : "NO", hole ? "NO (hole!)" : "yes");

    if (!sorted) {
        printf("  *** FAIL: result not magnitude-sorted\n");
        failures++;
    }
    if (hole) {
        printf("  *** FAIL: zero limb followed by non-zero limb\n");
        failures++;
    }
    if (res != 0.0) {
        printf("  *** FAIL: result is not the exact sum\n");
        failures++;
    }
    printf("\n");
}

int main(void) {
    const float u = 0x1p-24f;            /* binary32 unit roundoff */
    const float u2 = 0x1p-48f;           /* u^2 */

    printf("TWSum behaviour when triple-words contain zeros (binary32)\n\n");

    /* 1. trailing zeros only (the normal, well-formed shape) */
    run("trailing zeros: (1,0,0) + (u/2,0,0)",
        mk(1.0f, 0.0f, 0.0f), mk(0.5f * u, 0.0f, 0.0f));

    /* 2. one full zero operand */
    run("zero operand: (1,u,u^2) + (0,0,0)",
        mk(1.0f, u, u2), mk(0.0f, 0.0f, 0.0f));

    /* 3. interior zero limb in an input (x1 = 0 but x2 != 0) */
    run("interior zero in a: (1,0,u^2) + (u/2,0,0)",
        mk(1.0f, 0.0f, u2), mk(0.5f * u, 0.0f, 0.0f));

    /* 4. exact cancellation of the leading limbs -> zero head */
    run("cancel heads: (1,u,u^2) + (-1,u,u^2)",
        mk(1.0f, u, u2), mk(-1.0f, u, u2));

    /* 5. total cancellation -> result should be (0,0,0) */
    run("total cancel: (1,u,u^2) + (-1,-u,-u^2)",
        mk(1.0f, u, u2), mk(-1.0f, -u, -u2));

    /* 6. zeros that force vanishing error terms inside VSEB:
          both operands share the same limbs, doubling cleanly */
    run("clean double: (1,0,0) + (1,0,0)",
        mk(1.0f, 0.0f, 0.0f), mk(1.0f, 0.0f, 0.0f));

    /* 7. tiny + zero-padded big, with a zero in the middle of the merge */
    run("mixed zeros: (2,0,u^2) + (0,u,0)",
        mk(2.0f, 0.0f, u2), mk(0.0f, u, 0.0f));

    /* ---- randomised fuzz: well-formed TWs with random zero injection -- *
     * Generates P-nonoverlapping triple-words, randomly zeros some limbs,
     * then checks that tw_sum stays magnitude-sorted, tail-padded (no
     * zero holes) and within the triple-word relative-error bound.        */
    {
        uint32_t st = 0x12345678u; /* deterministic LCG, reproducible */
#define NEXT() (st = st * 1664525u + 1013904223u)
#define FRAND() ((float)((NEXT() >> 8) & 0xFFFFFF) / (float)0x1000000) /*[0,1)*/

        const int N = 500000;
        const double bound = 2.0 * (double)u * u * u + 4.2 * (double)u2 * u2;
        const double slack = 1.0 + 1e-6;
        int bad_sorted = 0, bad_hole = 0, bad_bound = 0, with_zero = 0;
        double worst = 0.0;

        for (int t = 0; t < N; t++) {
            /* a magnitude ~ [1,2), b ~ a*u, c ~ a*u^2 (signed) */
            float ah = 1.0f + FRAND();
            tw_fpr x = to_tw(ah, (FRAND() - 0.5f) * ah * (2.0f * u),
                             (FRAND() - 0.5f) * ah * (2.0f * u2));
            float bh = 1.0f + FRAND();
            tw_fpr y = to_tw(bh, (FRAND() - 0.5f) * bh * (2.0f * u),
                             (FRAND() - 0.5f) * bh * (2.0f * u2));

            /* inject zeros into trailing limbs with some probability */
            int injected = 0;
            if ((NEXT() & 3) == 0) { x.x[2] = 0.0f; injected = 1; }
            if ((NEXT() & 3) == 0) { x.x[1] = 0.0f; x.x[2] = 0.0f; injected = 1; }
            if ((NEXT() & 7) == 0) { y.x[2] = 0.0f; injected = 1; }
            if ((NEXT() & 7) == 0) { y = mk(0.0f, 0.0f, 0.0f); injected = 1; }
            if (injected) with_zero++;

            tw_fpr r = tw_sum(x, y);
            if (!is_sorted(r)) bad_sorted++;
            if (!no_hole(r)) bad_hole++;

            double sref = tw_value(x) + tw_value(y);
            double res = fabs(residual(x, y, r));
            if (sref != 0.0) {
                double rel = res / fabs(sref);
                if (rel > worst) worst = rel;
                if (rel > bound * slack) bad_bound++;
            } else if (res != 0.0) {
                bad_bound++; /* exact zero sum must give exact zero result */
            }
        }

        printf("=== randomised fuzz (%d trials, %d with injected zeros) ===\n",
               N, with_zero);
        printf("  worst relative error : %.3e  (bound 2u^3+4.2u^4 = %.3e)\n",
               worst, bound);
        printf("  not magnitude-sorted : %d\n", bad_sorted);
        printf("  zero holes           : %d\n", bad_hole);
        printf("  bound violations     : %d\n\n", bad_bound);
        failures += bad_sorted + bad_hole + bad_bound;
#undef NEXT
#undef FRAND
    }

    if (failures == 0)
        printf("OK: all zero-containing cases stay well-formed and within "
               "bound\n");
    else
        printf("FAIL: %d check(s) failed\n", failures);
    return failures != 0;
}
