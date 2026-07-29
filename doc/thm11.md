# Theorem 11 — Algorithm 15 (3SqRt): square root of a triple word

Paper: `doc/paper3.pdf` Section 10, Algorithm 15 and Theorem 11.
Claim: relative error `<= 24u^3 + 10260u^4` (accurate) resp.
`39u^3 + 10333u^4` (fast), for `p >= 11`.
The paper's own proof: `doc/Algorithms_for_Triple-Word_Arithmetic.pdf` §3.
Code: `code/coq/ThreeSqRt.v`.

**This file records OUR proof, which is not the paper's.** Where the two
differ is the subject of §4; the paper's route is kept in §3 for comparison,
because our *statement* is theirs verbatim.

## 0. Status

| | |
|---|---|
| `ThreeSqRt_isTW`, `ThreeSqRtFast_isTW` | **proved, unconditional** |
| `ThreeSqRt_error`, `ThreeSqRtFast_error` | **proved, with the paper's own constants** |

**Algorithm 15 is complete: zero admits.** Theorem 11 holds verbatim as
published — `24u^3 + 10260u^4` and `39u^3 + 10333u^4` — despite every
intermediate constant of ours being worse than the paper's.

## 1. The algorithm

    Require: x TW, x0 > 0 ; p >= 11

      a      <- RN((1 + 4u) / RN(sqrt x0))
      a'     =  a/2                             (exact)
      h0(1), h11(1) <- 2Prod(a, x0)
      h1(1)  <- RN(h11(1) + a x1)               (FMA)
      h01(2), h11(2) <- 2Prod(a', h0(1))
      h0(2)  <- 3/2 - h01(2)                    (exact)
      h1(2)  <- -RN(h11(2) + a' h1(1))          (FMA)
      b01, b11 <- 2Prod(a, h0(2))
      b12    <- RN(b11 + a h1(2))               (FMA)
      b      <- Fast2Sum(b01, b12)              (a DW, b ~ 1/sqrt x)
      b'     =  b/2                             (exact)
      i(1)   <- 3Prod_{2,3}(b, x)               (~ sqrt x)
      i(2)   <- 3/2 - 3Prod_{2,3}(b', i(1))     (~ 1, head exactly 1)
      y      <- 3Prod_{3,3}(i(1), i(2))

Iteration: `r <- r(3/2 - (1/2) r^2 x)`, quadratically convergent to
`1/sqrt x`.

## 2. The two Newton identities (both proved, both pure `field`)

    sqrt_newton_id   : (b(s*s))(3/2 - (1/2)b^2(s*s)) - s
                         = -s (t-1)^2 ((t-1)+3) / 2      , t = b s
    sqrt_newton_seed : a(3/2 - (1/2)a^2(s*s))s - 1
                         = -((as-1)^2)((as-1)+3) / 2

The second is the first with one factor of `x` removed — the refined *seed*
rather than the final product. Both are stated on `s` and `b`, not on `x` and
`1/sqrt x`, precisely so that no division and no `sqrt` appears and `field`
closes them.

## 3. What the paper's proof says

Its global bound is

    |y - sqrt x| <= ( d1 (1.5 + 287u^2) + d2 (0.5 + 123u^2)
                    + d3 (1 + 162u^2) + 9916u^4 ) sqrt x

whence `24 = 1.5(10.5) + 0.5(10.5) + 3` and `39 = 1.5(18) + 0.5(18) + 3`. It
also gives `|b - 1/sqrt x| <= (81u^2 + 622u^3)|1/sqrt x|`, and states that
`h0(2)` is exact "because `h0,1(2) >= 0.5` (this is why we started with
`1 + 4u` instead of `1`)". `p >= 11` is required by the modified `i(2)`
product, not by that exactness.

## 4. Where our proof differs, and why it has to

### 4.1 The cancellation — the load-bearing difference

The paper's weight `1.5` on `d1` comes from a triangle inequality on
`|d1 - (d1+d2)/2|`. That discards a real cancellation: `i(1)` occurs **twice**
— once as a factor of `y`, once inside `i(2)` — with opposite signs. We isolate
it in a single bracket, through the telescoping split (`sqrt_error_split`,
proved by `field`):

    y - s = (y - i1 i2)                                   [A: d3]
          + (- i1 (P - b' i1))                            [B: d2]
          + (i1 - b X)((3/2 - (1/2)b^2 X) - (b/2) i1)     [C: d1]
          + (b X (3/2 - (1/2)b^2 X) - s)                  [D: residual]

**`C`'s bracket is `~ 1 - 1/2 = 1/2`, not `1`.** That is the entire
difference, and putting it in one bracket is what makes it provable rather
than an appeal to a first-order expansion. The weights become `(1/2, 1/2, 1)`.

This is not optional for us. Termwise, with our `d3`, Theorem 11 comes out at
`29u^3 / 44u^3` and the published bound fails on both terms at once; through
`C` it is `16.5u^3 / 24u^3` and holds.

### 4.2 The sharp seed bound is neither reachable nor needed

The paper's `81u^2 + 622u^3` is **not used**, and has been removed.

*Not reachable by this route.* `sqrtA_bound_full` gives `e = a sqrt X - 1` in
`[0, 8u]`, so the Newton residual is already `(3/2)(8u)^2 = 96u^2 > 81u^2`
before any rounding is added; reaching `81` needs some 5% less slack in both
the seed and the rounding accounting. And `81` is not negotiable:
`newton_residual_const` shows the paper's `9916u^4` is *exactly* `E^2(3+E)/2`
at `E = 81u^2 + 622u^3` — `9915.5u^4` at `p = 11`, `9989.9u^4` at `p = 10`,
where it fails. Independent confirmation both that `p >= 11` is real and that
their `E` is what they say it is.

*Not needed.* The cancellation leaves `24 - 16.5 = 7.5u^3`, worth `15360u^4`
at `p >= 11`, against the `12729u^4` our crude `120u^2` costs. The
**published** constants therefore follow from the crude bound alone — for both
variants, the fast one with far more room.

### 4.3 A head bound is not a full bound

`sqrtA_bound` pins `a sqrt (tw0 x)`, the **head**; the Newton form needs
`a sqrt (TWval x)`. They differ at the `u` level because `|x1| <= 2u|x0|`:
`sqrt(TWval x)/sqrt(tw0 x) = 1 +- 1.1u`. Conflating them cost a false start.
The bridge is `sqrtA_bound_full`, and the cheap route to it is to work with
the **square**: `t = a sqrt X` has `t*t = a^2 X`, pure algebra, and `leq_sqrt`
(`Rmore.v`) converts a bound on `t*t` into one on `t`. Expanding `sqrt(1+d)`
is never needed.

### 4.4 The head threshold had to become a parameter

`head_one`'s `35u^2` cannot reach Algorithm 15: at the call site the second
factor is `i(1) = 3Prod(b,x)`, so the product is `b^2 x = (b sqrt x)^2` and
the seed error enters **squared** — `162u^2`, later `241u^2`. Algorithm 13
never meets this, because there the second factor is `x` itself: one power of
the seed error, not two. `ThreeReci.v` therefore gained `head_eq_1_c` and
`head_one_gen_c` with side condition `c u <= 1/4` (so `c <= 512` at
`p >= 11`); `head_half` runs at `c = 300`. Bumping the literal does **not**
work — the proof balances it against its own `200u^2` slack term.

### 4.5 `40u^2` was unreachable, and that forced a change in ThreeProdOne.v

`ThreeProdOneTW_error` (Algorithm 20) required its head-`1` second argument to
satisfy `|y - 1| <= 40u^2`. That constant was chosen for **Algorithm 14**,
where `i = 2 - mul1 b x` and the seed bound `|b x - 1| <= 35u^2` enters
**once**. Algorithm 15 cannot meet it. Here

    i(2) = 3/2 - mul2 b' i(1),   b' i(1) ~ (1/2)(b sqrt x)^2 = (1/2)(1 + e)^2

so `i(2) = 1 - e` and what survives is the **seed error itself** — `100u^2` by
`sqrtBW_x_err_crude`, and `81u^2` even by the paper's own sharp bound. Neither
fits in `40`. The honest value is `101.01u^2`; we state `105u^2`.

So `ThreeProdOne.v` gained `ThreeProdOneTW_error_c`, parametric in the
tolerance `c` over `40 <= c <= 112`:

    delta3(c) = 6u^3 + (31c + 10)u^4

The `6u^3` head is `eta3 + eta4`, which see `b'1` and `x2` alone and never
`y` — so it does **not** move with `c`; only the `u^4` coefficient does, and
linearly. At `c = 40` that is exactly `1250`, the constant Algorithm 14
already relies on, so `ThreeProdOneTW_error` is now a corollary with its
statement unchanged and **`ThreeDiv.v` needed no edit at all** — Theorem 10's
`27u^3 + 2500u^4` and `42u^3 + 2575u^4` are untouched. Algorithm 15 runs at
`c = 105`, i.e. `3265u^4`.

`40 <= c` is not cosmetic: at `c = 0` the conclusion would have to beat the
`-18u^4` that the factor `(1 - 3u)` costs against the `6u^3` head, and
`31c + 10` does not until `c ~ 15`.

Lesson for the toolbox: **a shared lemma's numeric side condition is an
interface.** Ours was fixed by the first caller and silently excluded the
second.

### 4.6 Our seed statement is two-sided, and that matters

    1 + 2u - 8u^2 <= a sqrt x0 <= 1 + 6u + 12u^2

The **lower** bound is the whole point of the `1 + 4u`: it forces
`a sqrt x0 > 1`, so the square stays above `1` and `h01(2) >= 1/2` — the
paper's own stated reason for the constant. (An early draft of this file said
`|a sqrt x0 - 1| <= 4u + 8u^2`. That is false: binary64 search reaches `5.50u`
and the algebra allows `6u`.)

## 5. The resulting constants

| | ours | published |
|---|---|---|
| `d1`, `d2` (Alg 11 / 12) | `10.5u^3+39u^4` / `18u^3+75u^4` | same |
| `d3` (Alg 20), at `c = 105` | `6u^3 + 3265u^4` | `3u^3 + 264u^4` |
| seed `E` | `100u^2` | `81u^2 + 622u^3` |
| residual `E^2(3+E)/2` | `15200u^4` | `9916u^4` |
| **Thm 11, accurate** | `16.5u^3 + 18504u^4` | `24u^3 + 10260u^4` |
| **Thm 11, fast** | `24u^3 + 18540u^4` | `39u^3 + 10333u^4` |

and `18504 - 10260 = 8244u^4 <= 7.5u^3` for `u <= 1/1099`, i.e. from
`p = 11` with a factor-1.9 margin; the fast variant needs only
`8207u^4 <= 15u^3`, `u <= 1/547`. **The published statement holds for us
verbatim**, despite every intermediate constant being worse — the first place
in this development where that happens, and it survived `d3` more than
doubling at `u^4` when the tolerance had to be relaxed (§4.5).

## 6. The error half, as built

    sqrtAux_bX_le       |b X| <= (1 + 121u^2) sqrt x
    sqrtAux_i1_le       |i1| <= (1 + 130u^2) sqrt x       sits on the above
    sqrtAux_bracket_le  |bracket of C| <= 1/2 + 300u^2    the cancellation
    sqrtAux_b_i1_le     |b i1 - 1| <= 202u^2              the seed error SQUARED
    sqrtAux_i2_near_1   |i2 - 1| <= 105u^2                what mul3 demands
    sq_cA, sq_cB, sq_cC the three coefficient facts, framed for nra
    sqrt_error_core     the four-way split, as PURE ALGEBRA on reals
    ThreeSqRtAux_error  the assembly over it

then the two instantiations, on the `ThreeDiv_error` pattern.

`sqrt_error_core` is the analogue of ThreeDiv.v's `div_error_core`: by the
time it fires every floating-point fact has been discharged, and what is left
is `sqrt_error_split` plus eight magnitude bounds. Its weights are
`(1/2, 1/2, 1)` — §4.1 — with `400u^2` corrections that cost `O(u^5)` at the
call sites and exist only so that no single step has to be tight.

## 7. Reuse and traps

Proved and reusable: `sqrt_newton_id`, `sqrt_newton_seed`,
`sqrt_error_split`, `newton_form_id`, `sqrtA_bound`, `sqrtA_bound_full`,
`sqrtA_sq_le`, `sqrtH01_2_range`, `sqrtH0_2_exact`, `is_imul_3_2`,
`TWval_split`, `isTW_low_le`, `isTW_TWval_gt0`, `TWval_sqrtBW`, the
eleven-lemma `sqrtB_isDW` chain, the three `*_sum_le` bounds,
`sqrtBW_newton_form`, `sqrtBW_x_err_crude`, `u_le_2048`,
`newton_residual_const`.

Traps hit repeatedly, all now commented in place:

- **A term cannot be rewritten into something that contains it.** `TWval x`
  sits inside `sqrt (TWval x)`; `x0` inside `sqrt x0`. Either generalise to
  abstract `r a` with `r*r = x0` and substitute with `<-`, or `set` the `sqrt`
  first — `set s := sqrt (TWval x)` *hides* `TWval x`, after which
  `rewrite -HsX` is safe.
- **`ring` cannot cross a `/2`**; `field` can. This cost many build cycles.
- **`nra` will not square a range, nor chain a `(1+u)` factor through a
  triangle inequality.** Hand it the squared bounds via `Rmult_le_compat`, or
  spell the difference out as a manifestly nonnegative term so `lra` suffices.
- **`0 <= X * X` wants `Rle_0_sqr`**, not `nra`.
- **`/=` does not reduce `TwoProd`'s projections usefully** — the same reason
  `vecSum`/`vseb` are on the never-`/=` list. Use `TwoProd_exact`, or a
  definitional bridge, `have -> : sqrtH0_1 x0 = RND (sqrtA x0 * x0) by [].`
- **`Rabs_pos_eq` rewrites the FIRST `Rabs`** — name the target.
- **A lemma's hypothesis-only variables cannot be inferred.** `apply:` on
  `newton_form_id` leaves six metavariables; pass them positionally.
- **Verify an identity numerically before writing it in Coq.** Both
  `newton_form_id` and `sqrt_error_split` were checked over 200k random points
  first — far cheaper than a wasted three-minute build on a mis-stated goal.
