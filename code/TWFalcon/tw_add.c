/*
 * Triple-word ADDITION only (TWSum, Algorithm 8).
 *
 * Extracted verbatim from the upstream reference implementation
 *   NXP-Research/TWFalcon : c-fn-dsa-multiple/triple_float.c
 *   Copyright 2025 NXP -- SPDX-License-Identifier: MIT
 *
 * Kept: two_sum, fast_two_sum, vec_sum6, vseb_sum, merge_noloop, tw_sum, tw_sub.
 * All other operators (products, division, sqrt, conversions, ...) have been
 * dropped -- see ../../example/TWFalcon/triple_float.c for the full source.
 */
#include "tw_add.h"
#include <math.h>

/* ---- Algorithm 2: 2Sum. Always exact: r + e = a + b. ---------------- */
static inline void two_sum(const float a, const float b, float *r, float *e) {
    float aa, bb, delta_a, delta_b, s;

    s = a + b;
    aa = s - b;
    bb = s - aa;
    delta_a = a - aa;
    delta_b = b - bb;
    *e = delta_a + delta_b;
    *r = s;
}

/* ---- Algorithm 1: Fast2Sum. Exact when |a| >= |b|: r + e = a + b. ---- */
static inline void fast_two_sum(const float a, const float b, float *r,
                                float *e) {
    float z;

    *r = a + b;
    z = *r - a;
    *e = b - z;
}

/* ---- Algorithm 4: VecSum on the 6 merged terms ---------------------- */
static inline void vec_sum6(const float x0, const float x1, const float x2,
                            const float x3, const float x4, const float x5,
                            float *e0, float *e1, float *e2, float *e3,
                            float *e4, float *e5) {
    float s1, s2, s3, s4;

    two_sum(x4, x5, &s4, e5);
    two_sum(x3, s4, &s3, e4);
    two_sum(x2, s3, &s2, e3);
    two_sum(x1, s2, &s1, e2);
    two_sum(x0, s1, e0, e1);
}

/* ---- Algorithm 5: VecSumErrBranch (VSEB), keeping 3 terms ----------- *
 * NOTE: this is exactly the branch that reacts to a ZERO error term.
 * After each fast_two_sum, if the produced error ep is *exactly* 0 the
 * running value is folded back (ep := r) instead of emitting a result
 * limb, so the number of emitted limbs `j` depends on how many error
 * terms vanish.  This is the spot where "TWR contains zero" matters; the
 * test in test_zeros.c probes it directly.                              */
static inline void vseb_sum(const float e0, const float e1, const float e2,
                            const float e3, const float e4, const float e5,
                            float y[3]) {
    int j;
    float ep0, ep1, ep2, ep3;
    float r0, r1, r2, r3;
    float yy[6];

    j = 0;

    fast_two_sum(e0, e1, &r0, &ep0);
    if (ep0 != 0.) {
        yy[0] = r0;
        j++;
    } else {
        ep0 = r0;
    }

    fast_two_sum(ep0, e2, &r1, &ep1);
    if (ep1 != 0.) {
        yy[j] = r1;
        j++;
    } else {
        ep1 = r1;
    }

    fast_two_sum(ep1, e3, &r2, &ep2);
    if (ep2 != 0.) {
        yy[j] = r2;
        j++;
    } else {
        ep2 = r2;
    }

    fast_two_sum(ep2, e4, &r3, &ep3);
    if (ep3 != 0.) {
        yy[j] = r3;
        j++;
    } else {
        ep3 = r3;
    }

    fast_two_sum(ep3, e5, &yy[j], &yy[j + 1]);

    if (j == 0) {
        yy[2] = 0;
    }

    y[0] = yy[0];
    y[1] = yy[1];
    y[2] = yy[2];
}

/* ---- Merge two magnitude-sorted triples into 6 sorted terms --------- *
 * Branchy (non-constant-time) merge, by decreasing magnitude.          */
void merge_noloop(const tw_fpr a, const tw_fpr b, float z[6]) {
    if (__builtin_fabsf(a.x[0]) > __builtin_fabsf(b.x[0])) {
        z[0] = a.x[0];
        if (__builtin_fabsf(a.x[1]) > __builtin_fabsf(b.x[0])) {
            z[1] = a.x[1];
            if (__builtin_fabsf(a.x[2]) > __builtin_fabsf(b.x[0])) {
                z[2] = a.x[2];
                z[3] = b.x[0];
                z[4] = b.x[1];
                z[5] = b.x[2];
            } else {
                z[2] = b.x[0];
                if (__builtin_fabsf(a.x[2]) > __builtin_fabsf(b.x[1])) {
                    z[3] = a.x[2];
                    z[4] = b.x[1];
                    z[5] = b.x[2];
                } else {
                    z[3] = b.x[1];
                    z[4] = a.x[2];
                    z[5] = b.x[2];
                }
            }

        } else {
            z[1] = b.x[0];
            if (__builtin_fabsf(a.x[1]) > __builtin_fabsf(b.x[1])) {
                z[2] = a.x[1];
                if (__builtin_fabsf(a.x[2]) > __builtin_fabsf(b.x[1])) {
                    z[3] = a.x[2];
                    z[4] = b.x[1];
                    z[5] = b.x[2];
                } else {

                    z[3] = b.x[1];
                    z[4] = a.x[2];
                    z[5] = b.x[2];
                }
            } else {
                z[2] = b.x[1];
                if (__builtin_fabsf(a.x[1]) > __builtin_fabsf(b.x[2])) {
                    z[3] = a.x[1];
                    z[4] = a.x[2];
                    z[5] = b.x[2];
                } else {
                    z[3] = b.x[2];
                    z[4] = a.x[1];
                    z[5] = a.x[2];
                }
            }
        }
    } else {
        z[0] = b.x[0];
        if (__builtin_fabsf(a.x[0]) > __builtin_fabsf(b.x[1])) {
            z[1] = a.x[0];
            if (__builtin_fabsf(a.x[1]) > __builtin_fabsf(b.x[1])) {
                z[2] = a.x[1];
                if (__builtin_fabsf(a.x[2]) > __builtin_fabsf(b.x[1])) {
                    z[3] = a.x[2];
                    z[4] = b.x[1];
                    z[5] = b.x[2];
                } else {

                    z[3] = b.x[1];
                    z[4] = a.x[2];
                    z[5] = b.x[2];
                }
            } else {
                z[2] = b.x[1];
                if (__builtin_fabsf(a.x[1]) > __builtin_fabsf(b.x[2])) {
                    z[3] = a.x[1];
                    z[4] = a.x[2];
                    z[5] = b.x[2];
                } else {
                    z[3] = b.x[2];
                    z[4] = a.x[1];
                    z[5] = a.x[2];
                }
            }
        } else {
            z[1] = b.x[1];
            if (__builtin_fabsf(a.x[0]) > __builtin_fabsf(b.x[2])) {
                z[2] = a.x[0];
                if (__builtin_fabsf(a.x[1]) > __builtin_fabsf(b.x[2])) {
                    z[3] = a.x[1];
                    z[4] = a.x[2];
                    z[5] = b.x[2];
                } else {
                    z[3] = b.x[2];
                    z[4] = a.x[1];
                    z[5] = a.x[2];
                }
            } else {
                z[2] = b.x[2];
                z[3] = a.x[0];
                z[4] = a.x[1];
                z[5] = a.x[2];
            }
        }
    }
}

/* ---- Algorithm 8: TWSum -- sum of two triple-word numbers ----------- */
tw_fpr tw_sum(const tw_fpr a, const tw_fpr b) {
    float e0, e1, e2, e3, e4, e5, z[6];
    tw_fpr r;

    merge_noloop(a, b, z);
    vec_sum6(z[0], z[1], z[2], z[3], z[4], z[5], &e0, &e1, &e2, &e3, &e4, &e5);

    vseb_sum(e0, e1, e2, e3, e4, e5, r.x);
    return r;
}

tw_fpr tw_sub(tw_fpr x, tw_fpr y) {
    y.x[0] = -y.x[0];
    y.x[1] = -y.x[1];
    y.x[2] = -y.x[2];
    return tw_sum(x, y);
}
