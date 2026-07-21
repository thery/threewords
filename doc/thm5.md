# Theorem 5 — RoundTW (round a triple word to the nearest float)

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
