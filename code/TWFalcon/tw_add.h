/*
 * Triple-word ADDITION only (TWSum, Algorithm 8).
 *
 * Extracted from the upstream reference implementation
 *   NXP-Research/TWFalcon : c-fn-dsa-multiple/triple_float.{c,h}
 *   Copyright 2025 NXP -- SPDX-License-Identifier: MIT
 *
 * Only the pieces needed for the sum of two triple-word numbers are kept:
 *   tw_sum  = merge_noloop -> vec_sum6 -> vseb_sum
 *   tw_sub  = negate + tw_sum
 *
 * A triple-word number is an unevaluated sum of three binary32 floats
 * (x[0], x[1], x[2]), magnitude-sorted and "P-nonoverlapping".
 * The working precision is binary32, i.e. u = 2^-24 (this is what Falcon
 * uses); the companion Rocq/Coq proofs in ../coq reason about the same
 * algorithm in binary64.
 */
#ifndef TW_ADD_H
#define TW_ADD_H

#include <stdint.h>

typedef struct {
    float x[3];
} tw_fpr;

/* r = a + b   (Algorithm 8, TWSum) */
tw_fpr tw_sum(const tw_fpr a, const tw_fpr b);

/* r = x - y */
tw_fpr tw_sub(tw_fpr x, tw_fpr y);

#endif /* TW_ADD_H */
