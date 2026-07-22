# Erratum: Algorithm 7 (RoundTW) / Theorem 5 — inner test polarity

**Status:** the formalisation (`code/coq/TWSum.v`) uses the *corrected* condition.
The change versus the paper's printed Algorithm 7 is documented here; a note is
also left in `TWSum.v` at the `RoundTW` definition.

## The problem

Algorithm 7, as printed, takes the directional (`RU`/`RD` by `sign(x2)`) branch
when `x0 + 2*x1` is exact **and** `RN(-(3/2 u - 2 u^2)*x0) = x1`, i.e. the first
`if` returns `RN(x0+x1)` on

```
RN(x0 + 2*x1) inexact   OR   RN(-(3/2 u - 2 u^2)*x0) != x1.
```

This has the wrong polarity. At a **genuine midpoint** `x1 = ±½ ulp(x0)`, the
value `RN(-(3/2 u - 2 u^2)*x0)` is a small float of magnitude `≈ (3/2)u|x0|` and
(for a positive `x1`) of the opposite sign, so it never equals `x1`; the printed
test `!= x1` is therefore *true*, routing to `RN(x0+x1)` and **ignoring `x2`**.
Conversely the paper's "special" false-positive `x0 = 1+2u, x1 = -3/2 u` is
exactly the configuration where `RN(-(3/2 u - 2 u^2)*x0) = x1`.

So the printed condition returns `RN(x0+x1)` at genuine midpoints (wrong) and
goes directional on the special non-midpoint (wrong).

## Running counterexample (binary64, `p = 53`, `u = 2^-53`)

`x_bar = (x0, x1, x2) = (1, u, u^2) = (1, 2^-53, 2^-106)` is a valid TW
(`|x1| < ulp(x0) = 2u`, `|x2| < ulp(x1)`), and `x0+x1 = 1 + 2^-53` is exactly the
midpoint of `[1, 1+2^-52]`.

| quantity | value |
|---|---|
| correct `RN(x0+x1+x2)` | `1 + 2^-52 = 0x1.0000000000001p+0` |
| RoundTW, printed (`!=`) | `1` — **wrong** |
| RoundTW, fixed (`=`)   | `1 + 2^-52` — correct |

`doc/roundtw_bug.c` reproduces this with real IEEE-754 operations under the three
rounding modes (`fesetround`), the genuine Fast2Sum exactness test, and FP
computation of `(⋆)`. Build/run:

```
cc -O0 -frounding-math doc/roundtw_bug.c -lm -o /tmp/roundtw_bug && /tmp/roundtw_bug
```

An exact-rational sweep over random valid TW triples confirms: the printed
condition is wrong on ~0.3% of inputs (all of them midpoints) for `p = 4,6,8,10`;
the fixed condition is correct on every input.

## The fix

Change line 1 of Algorithm 7 so the first `if` returns `RN(x0+x1)` on

```
RN(x0 + 2*x1) inexact   OR   RN(-(3/2 u - 2 u^2)*x0) = x1        (= instead of !=)
```

Equivalently, enter the directional branch iff `x0+2x1` is exact **and**
`RN(-(3/2 u - 2 u^2)*x0) != x1`. With this the proof text is literally correct:
`(⋆)` (as `= x1`) is true in the special case and false at genuine midpoints, so
the first condition is false — and the directional branch taken — exactly when
`x0+x1` is a midpoint.

Corrected Algorithm 7 (paper syntax):

```
Require: x_bar = (x0,x1,x2) a TW.   Ensure: y = RN(x_bar).
  if RN(x0 + 2 x1) inexact operation or (*) RN(-(3/2 u - 2 u^2) x0) = x1 then
      y <- RN(x0 + x1)
  else if x2 > 0 then y <- RU(x0 + x1)
  else if x2 < 0 then y <- RD(x0 + x1)
  else               y <- RN(x0 + x1)
  return y
```
