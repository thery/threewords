# Theorem 5 — RoundTW (round a triple word to the nearest float)

> **STATUS (2026-07-22).** `RN_add_lt_quarter`, `RoundTW_add_float`,
> `is_imul_gap`, `RN_between_midp` (replacing the vague `RN_add_notmid`/
> `RN_add_mid` placeholders) and `RoundTW_correct` are **proved**. One admit
> remains: `RoundTW_cond` (the tie-detector). **A bug was found**: Algorithm 7's
> inner `(⋆)` test polarity is inverted — the directional branch must fire on
> `RN(-(3/2u-2u²)x0) <> x1`, not `= x1`. `RoundTW`/`RoundTW_cond` in `TWSum.v`
> now use the corrected condition. See `doc/roundtw-erratum.md` and
> `doc/roundtw_bug.c` for the verified counterexample `(1, u, u²)`.

Companion doc. Source: `doc/paper3.pdf` §4, p. 5. Setting FLX, `u = 2^{-p}`,
`RN` = round-to-nearest (ties-to-even), `RU`/`RD` = round toward `+∞`/`−∞`.

## Algorithm 7 — RoundTW(x₀, x₁, x₂)   (3 operations & 4 tests)

> Require: `x̄ = (x₀,x₁,x₂)` a TW.   Ensure: `y = RN(x̄)` (= `RN(x₀+x₁+x₂)`).
>
> ```
> if RN(x₀ + 2·x₁) inexact  or  (⋆) RN(−(3/2·u − 2u²)·x₀) ≠ x₁ then
>     y ← RN(x₀ + x₁)
> else if x₂ > 0 then  y ← RU(x₀ + x₁)
> else if x₂ < 0 then  y ← RD(x₀ + x₁)
> else                 y ← RN(x₀ + x₁)
> return y
> ```

"`RN(x₀+2x₁)` inexact" means `x₀ + 2x₁` is not a float, i.e.
`RN(x₀+2x₁) ≠ x₀+2x₁`. (In practice: `(s,e) = Fast2Sum(x₀, 2x₁)`, test `e ≠ 0`.)

So the **first condition** is `¬format(x₀+2x₁) ∨ RN(−(3/2u−2u²)·x₀) ≠ x₁`.
When it is **false** (i.e. `x₀+2x₁` is a float **and**
`RN(−(3/2u−2u²)·x₀) = x₁`), the algorithm rounds directionally by the sign of
`x₂`; otherwise it returns `RN(x₀+x₁)`.

## Theorem 5

> If `x̄` is a TW, then `RoundTW(x̄) = RN(x̄)`, provided `p ≥ 4`.

## Proof (verbatim, p. 5)

> First, if `x₀+x₁` is a FP number, then `y = x₀+x₁` anyway, and it is easy to
> check that `x₀+x₁ = RN(x̄)`. We suppose for the sequel that this is not the
> case.
>
> Given `|x₁| < ulp(x₀)`, the first condition is false iff `x₀+x₁` is halfway
> between two consecutive FP numbers, or in a special case that can (WLOG) be
> reduced to `x₀ = 1 + 2u` and `x₁ = −3/2 u`. When that first condition is
> false, Condition `(⋆)` is designed to be true in the special case, but false
> elsewise (because of the magnitude of `|x₁|`).
>
> - If `x₀+x₁` is halfway between two adjacent FP numbers, then the rounding is
>   decided by the sign of `x₂`.
> - Otherwise, one easily checks that `RN(x₀+x₁+x₂) = RN(x₀+x₁)`, given
>   `|x₂| < ulp(x₁)`. ∎

## Structural reading (for the formalisation)

Target: `RoundTW x₀ x₁ x₂ = RN(x₀+x₁+x₂)` for `isTW (x₀,x₁,x₂)` (so
`|x₁| < ulp x₀`, `|x₂| < ulp x₁`, all floats), `p ≥ 4`.

Case on the algorithm's control flow:

1. **`x₀+x₁` is a float** (`format (x₀+x₁)`). Then `RN(x₀+x₁) = x₀+x₁`, and
   `RN(x₀+x₁+x₂) = x₀+x₁` too (since `|x₂| < ulp x₁ ≤ …`, `x₀+x₁+x₂` rounds
   back to the float `x₀+x₁`). Both the directional and the `RN` branches
   return `x₀+x₁`, so the result is correct **regardless of the condition** —
   need only `RN(x₀+x₁+x₂) = x₀+x₁`.
   (Helper: `format f → |d| ≤ ½ ulp f → RN(f+d) = f`, and `|x₂| < ulp x₁`
   gives `|x₂| ≤ ½ ulp(x₀+x₁)` here.)

2. **`x₀+x₁` not a float.** Let `m = x₀+x₁`, `f = RN(m)` (`= RN(x₀+x₁)`).
   Split on whether `m` is a **midpoint** (`m = (g + succ g)/2` for the DN
   float `g`), i.e. `m − round_DN m = ½ ulp(round_DN m)`:
   - **midpoint** (the algorithm's directional branch must fire):
     `RN(x₀+x₁+x₂) = RN(m + x₂)`; since `m` is the midpoint and `|x₂| < ulp x₁`
     is small, the sign of `x₂` decides:
     `x₂ > 0 ⟹ RN(m+x₂) = RU(m)`, `x₂ < 0 ⟹ RD(m)`, `x₂ = 0 ⟹ RN(m)`.
     So the directional branch is exactly `RN(m+x₂)`. **Need**: the first
     condition is *false* here (so the algorithm takes the directional branch).
   - **not a midpoint**: `RN(x₀+x₁+x₂) = RN(x₀+x₁) = f` (the tail `x₂` is too
     small to cross the midpoint). **Need**: the first condition is *true*
     here (so the algorithm returns `RN(x₀+x₁)`) — this is the correctness of
     the `¬format(x₀+2x₁) ∨ (⋆)` tie-detector.

**The tie-detector** (`¬format(x₀+2x₁) ∨ (⋆)` is false ⟺ `m` is a midpoint,
in the reduced special case handled by `(⋆)`): `m = x₀+x₁` is a midpoint iff
`2m = 2x₀ + 2x₁` sits at a `½ulp` grid point, detected via the exactness of
`x₀ + 2x₁`; `(⋆)` = `RN(−(3/2u−2u²)·x₀) = x₁` rescues the one special
configuration `x₀ = 1+2u`, `x₁ = −3/2 u` where the exactness test alone
misfires. **This is the delicate part** and where `p ≥ 4` enters.

**Machinery**: `RN`/`RU`/`RD` = `round beta fexp` with `Znearest choice` /
`Zceil` / `Zfloor`; Flocq `round_DN_UP` / `round_N_eq_DN`/`_UP`, `succ`/`pred`,
`ulp`; the DW/TW separation `|x₁| < ulp x₀`, `|x₂| < ulp x₁` from `isTW`.

## Plan

- **Helper A** (case 1): `format f → |d| ≤ ½ ulp f → RN(f + d) = f`.
- **Helper B** (non-midpoint): `¬midpoint m → |d| < ½ ulp(round_DN m)-slack →
  RN(m + d) = RN(m)`.
- **Helper C** (midpoint): `midpoint m → x₂>0 → RN(m+x₂) = RU m` (and the two
  symmetric statements).
- **Tie-detector** (the core): `¬format(x₀+2x₁) ∨ RN(−(3/2u−2u²)x₀)≠x₁`
  is false ⟺ `x₀+x₁` is a midpoint (given `isTW`), and in the special case.
- **RoundTW** definition + **`RoundTW_correct`** = Theorem 5, assembled.

## Refined bounds (found while filling)

The "one easily checks" in the non-midpoint case rests on a divisibility fact,
not just `|x₂| < ulp x₁`:

Let `m = x₀+x₁`, `g = round_DN m`, `mid = g + ½ ulp g`. Then
`m − mid = (x₀ − g) + x₁ − ½ ulp g` is a **multiple of `ulp x₁`**: from
`|x₁| < ulp x₀` we get `cexp x₁ < cexp x₀`, so `x₀`, `g` and `½ ulp g =
pow(cexp x₀ − 1)` are all multiples of `pow(cexp x₁) = ulp x₁`, as is `x₁`.
Hence, when `m` is **not** a midpoint, `m − mid ≠ 0` is a nonzero multiple of
`ulp x₁`, so `|m − mid| ≥ ulp x₁ > |x₂|`. Therefore `m + x₂` stays on the same
side of `mid` as `m`, giving `RN(m + x₂) = RN(m)`.

So the honest helper interfaces are:
- `RN_add_notmid m d : ~ format m -> Rabs d < Rabs (m − mid m) -> RN(m+d)=RN m`
  (`mid m := round_DN m + ½ ulp(round_DN m)`), and the assembly supplies
  `|x₂| < ulp x₁ ≤ |m − mid|` via the divisibility above;
- `RN_add_mid m d : is_midpoint m -> Rabs d < ½ ulp(round_DN m) -> RN(m+d) = RU/RD/RN m by sign of d`, with `|x₂| < ulp x₁ ≤ ½ ulp g` (again `2 ulp x₁ ≤ ulp x₀`);
- `RoundTW_add_float`: `2 ulp x₁ ≤ ulp(x₀+x₁)`, so `|x₂| < ½ ulp(x₀+x₁)` and the float rounds back to itself.

## Fill status (in progress)

Skeleton merged (`RoundTW` def + `is_midpoint` + 5 helper/theorem admits, plus
the foundational `RN_add_lt_quarter`). Order of attack when resuming:

1. **`RN_add_lt_quarter`** (`format f -> |d| < ¼ ulp f -> RN(f+d) = f`) — the
   foundational rounding lemma. Provable via `round_N_le_midp` /
   `round_N_ge_midp`; the one obligation is the gap facts
   `f + ½ ulp f ≤ succ f` and `pred f ≤ f − ½ ulp f`. The **toward-zero** gap
   is `½ ulp` (not `ulp`) at a power of two — use `pred_plus_ulp`
   (`pred g + ulp(pred g) = g`, `g>0`) + `ulp_pred_pos` (its second disjunct
   `g = pow(mag g − 1)` gives `ulp(pred g) = ½ ulp g`); reduce `f<0` by
   `succ_opp`/`pred_opp`/`ulp_opp`. A `Prec_gt_0 p` instance is in scope
   (`TWSum.v` `p_gt_0`), so `FLX_exp_valid` etc. resolve by typeclass.
2. `RoundTW_add_float` (needs `Rabs x1 < ulp x0` added to its hyps; then
   `|x2| < ulp x1 ≤ 2u ulp(x0+x1) ≤ ¼ ulp(x0+x1)`, apply `RN_add_lt_quarter`).
3. `RN_add_notmid` / `RN_add_mid` (restated with the `|d| < |m − mid|` /
   `< ½ ulp(round_DN m)` bounds — see "Refined bounds" above).
4. `RoundTW_cond` — the tie-detector, the hard core (where `p ≥ 4` enters).
5. `RoundTW_correct` — assembly (`format(x0+x1)` case first, then
   midpoint/non-midpoint via `RoundTW_cond`).
