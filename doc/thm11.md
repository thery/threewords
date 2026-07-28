# Theorem 11 — Algorithm 15 (3SqRt): square root of a triple word

Paper: `doc/paper3.pdf` Section 10, Algorithm 15 and Theorem 11.
Proof: **`doc/Algorithms_for_Triple-Word_Arithmetic.pdf` Section 3** — the
supplementary material `paper3.pdf` defers to.
Claim: relative error `<= 24u^3 + 10260u^4` (accurate) resp.
`39u^3 + 10333u^4` (fast), for `p >= 11`.
Code: `code/coq/ThreeSqRt.v`.

## 0. Where the proof is

`paper3.pdf` says only "the major steps of the proof are given in the appendix,
see supplementary material".  The long version `doc/old-triplewors.pdf` is no
help: it stops at Section 9 (the quotient) and its own roadmap reads
"Section 10 **[???]**" — a placeholder never filled in.  The supplementary
appendix, however, does contain the proof, in a little over a page.  It is
terse ("much of the analysis is very similar to what was done for reciprocal
and division, so we only focus on the differences") but it gives every
constant, which is what we need.

Note its cross-references are broken (`Algorithm ??` throughout) and its
algorithm numbering differs from the long version's: the head-`1` DW×TW
product it calls Algorithm 17 and the TW×TW one Algorithm 18 are the ones this
development calls Algorithm 18 and Algorithm 20 (`ThreeProdOne.v`), following
`old-triplewors.pdf`.

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
      return (y0, y1, y2)

The iteration is `r <- r (3/2 - (1/2) r^2 x)`, quadratically convergent to
`1/sqrt x`.  Structurally this is 3Div with three changes: the seed involves a
real square root; `2 - .` becomes `3/2 - .` (`sub32TW`), with the two halvings
exact scalings by `pow (-1)`; the last product is again the TW×TW one on a
head-`1` second argument, i.e. `ThreeProdOneTW`.

## 2. What the supplementary states

Three facts, and then the assembly.

- **`h0(2)` is exact** "because `h0,1(2) >= 0.5` (this is why we started with
  `1 + 4u` instead of `1`)".  That is the whole argument: `h01(2)` sits in
  `[1/2, 1)` where `ulp = u`, `3/2` is a multiple of `u` there, so the
  difference is too, and it lands in `(1/2, 1]` — representable.  **Not**
  Sterbenz, whose hypothesis fails outright for `3/2 - 1/2`.
- **`p >= 11` comes from the `i(2)` product**, not from `h0(2)`: the modified
  algorithm used there has its penultimate line replaced by
  `e1 <- Fast2Sum(.5)(-z00+, s1)`, and "this works provided that `p >= 11`".
- **The two intermediate bounds**:

      |b - 1/sqrt x|                     <= (81u^2 + 622u^3) |1/sqrt x|
      |b x (1.5 - (1/2) b^2 x) - sqrt x| <= 9916u^4 sqrt x

  The first is the seed; compare Algorithm 13's `34u^2 + 126u^3` — the square
  root seed is more than twice as sloppy, which is where Theorem 11's large
  `u^4` term comes from.  The second is the Newton residual, and it is `O(u^4)`
  exactly as `sqrt_newton_id` predicts.

- **The global bound**:

      |y - sqrt x| <= ( d1 (1.5 + 287u^2)
                      + d2 (0.5 + 123u^2)
                      + d3 (1   + 162u^2) + 9916u^4 ) sqrt x

  with `d1, d2, d3` the three products' relative errors.  Check:
  `24 = 1.5(10.5) + 0.5(10.5) + 3` and `39 = 1.5(18) + 0.5(18) + 3`, and on
  `u^4`, `1.5(39) + 0.5(39) + 263 + 9916 = 10257 ~ 10260`.  It all closes.

## 3. The Newton identity (PROVED, `sqrt_newton_id`)

With `x = s*s` and `t = b*s`:

    (b * (s*s)) * (3/2 - (1/2) * (b*b) * (s*s)) - s
      = - s * (t - 1)^2 * ((t - 1) + 3) / 2

Pure `ring` after substituting `x = s*s` — no division, no `sqrt`, which is why
it is stated on `s` and `b` rather than on `x` and `1/sqrt x`.  The analogue of
`newton_id` in `ThreeReci.v`.  It is what makes the seed error enter only
squared, hence the `9916u^4` above and nothing at `u^3`.

## 4. The one place we must beat the supplementary

Our `d3` is `8u^3 + 1330u^4`, not the announced `3u^3 + 263u^4` — Algorithm
20's `delta3` is loose in our development, see `doc/thm10.md`.  Feeding that
into the supplementary's assembly gives

| | `d1` | `d2` | `d3` | total |
|---|---|---|---|---|
| paper, acc | `1.5 × 10.5` | `0.5 × 10.5` | `1 × 3` | **24u³** |
| ours, literal route, acc | `1.5 × 10.5` | `0.5 × 10.5` | `1 × 8` | 29u³ |
| ours, sharpened, acc | `0.5 × 10.5` | `0.5 × 10.5` | `1 × 8` | **18.5u³** |
| paper, fast | `1.5 × 18` | `0.5 × 18` | `1 × 3` | **39u³** |
| ours, literal route, fast | `1.5 × 18` | `0.5 × 18` | `1 × 8` | 44u³ |
| ours, sharpened, fast | `0.5 × 18` | `0.5 × 18` | `1 × 8` | **26u³** |

So the literal route reproduces Theorem 10's fate exactly — `29`/`44` against a
published `24`/`39`.  But **the supplementary's weight `1.5` on `d1` is itself
loose**, and provably: writing `b = (1+e)/s`,

    i(1)    = (1+e) s (1+d1)
    b' i(1) = (1+e)^2 (1+d1) / 2
    i(2)    = 3/2 - (1+e)^2 (1+d1)(1+d2)/2   ~  1 - e - (d1+d2)/2
    y       = i(1) i(2) (1+d3)

so to first order

    y/s ~ (1 + e + d1 + d3)(1 - e - (d1+d2)/2) = 1 + d1/2 - d2/2 + d3 .

`i(1)` occurs **twice** — once as a factor of `y`, once inside `i(2)` — with
opposite signs, so its error half-cancels; the seed error `e` cancels outright
(Newton is self-correcting).  The supplementary reaches `1.5` by bounding
`|d1 - (d1+d2)/2|` with the triangle inequality as `|d1| + |d1|/2 + |d2|/2`,
discarding the cancellation.

**Consequence for the formalisation**: state Theorem 11 with the published
constants and prove them *through the cancellation*.  Concretely, in step (3)
of the assembly keep the signed decomposition

    y - s = (y - i(1) i(2)) + i(1) (i(2) - (3/2 - b' i(1)))
          + (i(1) - b x)(3/2 - (1/2) b^2 x)
          + [(b x)(3/2 - (1/2) b^2 x) - s]

and do **not** pass to absolute values until after the second and third terms
have been combined — that is where the factor three lives.

## 5. Proof obligations, in the order to attack them

1. **`sqrtA_bound`** — the seed.  The one genuinely new analytic step; nothing
   else in the development computes with `sqrt`.
2. **`sqrtH0_2_exact`** — via `h01(2) >= 1/2`, per Section 2.  Grid arithmetic
   once the binade is pinned.
3. **`sqrtB_isDW`** — mirrors `reciB_isDW`.  **Check the Fast2Sum ordering
   `|b01| >= |b12|`** rather than assuming it.  The supplementary repeats, for
   its Algorithm 17, exactly the justification we already machine-checked as
   false ("a Fast2Sum can be used … because if the condition for Fast2Sum to be
   errorless is not satisfied, this means that `|b1|` is very small, so that the
   global error will be small anyway" — see `doc/alg18_fast2sum_bug.py`, which
   reaches `32u^3`).  If the ordering cannot be proved, use `Fast2SumS`; it
   costs no extra flop.
4. **`sqrtBW_x_err`** — `81u^2 + 622u^3`, from the supplementary.
5. **`head_half`** — `tw0 (mul b' i(1)) = 1/2`.  **Do not re-prove**: `b'` is
   `scaleTW (-1) b`, the products commute with scaling (`ThreeProdDW_scale`),
   and `head_one` is already proved for Algorithms 11 and 12, so this should
   fall out of `head_one` plus `isTW_scale` / `TWval_scale`.
6. **`ThreeSqRtAux_error`** — the assembly, generic in `d1, d2, d3`, stated in
   the supplementary's shape so the route can be followed literally first, then
   sharpened per Section 4.

## 6. Reuse checklist

Already proved, do not re-derive: `ThreeProdDW_error` (10.5u³),
`ThreeProdDWFast_error` (18u³), `ThreeProdOneTW_error` (8u³, head-`1` second
argument) and the three `_isTW`; `head_one` for both DW×TW products; `scaleTW`
/ `TWval_scale` / `isTW_scale` (`ThreeProd.v`); `Fast2SumS` (`TwoSum.v`);
`reciB_isDW` and `reciBW_x_err` as the templates for steps 3 and 4; the whole
`sub2TW` block in `ThreeReci.v` as the template for `sub32TW`.  **Theorem 11
needs no new product bound** — unlike Theorems 9 and 10.
