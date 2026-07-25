# Theorem 7 (Alg 9), §6.2 part 2 — the `ε₅ ≠ 0` error case

This is the piece the published paper (`doc/paper3.pdf`) **omits** ("the error
is shown not too large when `ε₅ ≠ 0`, details omitted"). The full argument
survives in the older draft `doc/old-triplewors.pdf` as the proof of its
**Theorem 10** (old numbering: `3Prod^acc_{3,3}` = Algorithm 12 there =
Algorithm 9 / Theorem 7 here). This note transcribes that proof and maps it to
the Coq obligation `ThreeProd_error_eps5nz` in `code/coq/ThreeProd.v`.

See `doc/thm7.md` §6.2 part 2 for the algorithm, the term names
(`z00±, z01±, z10±, b0, b1, b2, c, z3, s3, e0..e4`) and the `ε₀..ε₅`
decomposition; only the sharpening is new here.

## The gap

The naive triangle bound (paper3, and `eps04_sum` + `eps5_bound` in Coq) gives

```
|ε₀+···+ε₄| ≤ 28u³ − 11.9u⁴
|ε₅|        ≤ (2u³ + 4.2u⁴)·|z00⁺+b0+b1+c+z3|   (Theorem 3, VSEB k=3)
```

Keeping the **full** `ε₅` term over `x̄ȳ ≥ 1 − 4u` yields only

```
|r̄ − x̄ȳ| / |x̄ȳ| ≤ (2u³+4.2u⁴) + (28u³−11.9u⁴)(1+2u³+4.2u⁴)/(1−4u)
                 ≤ 30u³ + 111u⁴          -- OVER the 28u³+107u⁴ budget.
```

So the `ε₅` truncation and the "big" `εᵢ` cannot both be large at once.

## The sharpening (old draft, Theorem 10)

> *"We want to improve this bound based on the fact that, when the other error
> terms are big, we must have `ε₅ = 0`."*

Four cases; in the first three a source term is *small*, in the fourth the
truncation *vanishes*.

- **`|y2| < u²`** (symmetric: `|x2| < u²`). Then
  `|x0·y2| ≤ (2−2u)(u²−u³)`, so `|ε₁| ≤ 2u³` (instead of `4u³`). Hence
  `|ε₀+···+ε₄| ≤ 26u³ − 11.9u⁴`, and even keeping the full `ε₅`:
  ```
  |r̄−x̄ȳ|/|x̄ȳ| ≤ (2u³+4.2u⁴) + (26u³−11.9u⁴)(1+2u³+4.2u⁴)/(1−4u)
               ≤ 28u³ + 103u⁴  ≤ 28u³ + 107u⁴.
  ```

- **`|c| < 4u²`**. Then `|ε₄| ≤ 2u³`, and the same computation gives
  `≤ 28u³ + 103u⁴`.

- **`|z3| < 4u²`**. Then `|ε₃| ≤ 2u³`, likewise `≤ 28u³ + 103u⁴`.

- **the only remaining case** —
  `u ≤ |x1|,|y1| < 2u`, `u² ≤ |x2|,|y2| < 2u²`, `|c| ≥ 4u²`, `|z3| ≥ 4u²`.
  Here
  - `|z00⁺| ≥ 1` and `uls(z00⁺) ≥ 4u²`, and `|z01⁺|, |z10⁺| ≥ u`, so
    **`z00⁺, b0, b1, c, z3` are all divisible by `8u³`**;
  - `|z00⁺ + b0 + b1 + c + z3| < 5`, hence `|r0| ≤ 5`.

  A fourth nonzero output term would, by P-nonoverlapping from `r0` (magnitude
  `≤ 5`), be `< 8u³`; but every term is a multiple of `8u³`, so a nonzero one is
  `≥ 8u³` — contradiction. Therefore VSEB(3) drops nothing, **`ε₅ = 0`**, and
  ```
  |r̄−x̄ȳ|/|x̄ȳ| ≤ (28u³−11.9u⁴)/(1−4u) ≤ 28u³ + 107u⁴.
  ```

The bound is tight: at `p = 53` the witness (2) of the paper attains
`≈ (28 − 10⁻⁵)u³`.

## Formalisation plan (`ThreeProd_error_eps5nz`)

The Coq lemma assumes `sumR(vseb e) − sumR(vsebK 3 e) ≠ 0` (i.e. `ε₅ ≠ 0`).
By the **contrapositive of case 4**, `ε₅ ≠ 0` forces us out of case 4, so at
least one of `|y2| < u²`, `|x2| < u²`, `|c| < 4u²`, `|z3| < 4u²` holds. In each
such sub-case a single `εᵢ` shrinks to `2u³` and the *full*-`ε₅` bound
`≤ 28u³ + 103u⁴ ≤ 28u³ + 107u⁴` closes the goal — no case-4 machinery needed on
this branch.

Concretely:

1. **Sub-case bounds.** Refine `eps1_bound` / `eps4_bound` / `eps3_bound` /
   `eps0_bound` under the respective smallness hypothesis (a `2u³` variant of
   each), then re-run `eps04_sum` to `≤ 26u³ − 11.9u⁴`, and a `103u⁴`-slack
   variant of `error_assembly` keeping `eps5_bound`.

2. **Case 4 ⇒ ε₅ = 0** (only needed if one proves the disjunction by ruling
   case 4 in-and-out rather than by direct casing). The divisibility
   `8u³ ∣ z00⁺,b0,b1,c,z3` reuses the *same* machinery built for item (a):
   `is_imul_*`, `is_imul_uls_ge`, `format_imul_cexp`, and the
   `uls(z01⁺),uls(z10⁺) ≥ u` bounds; `|r0| ≤ 5` from
   `|z00⁺+b0+b1+c+z3| < 5`; the "4th term `< 8u³` but `∣ 8u³`" contradiction is
   a P-nonoverlap + `is_imul_pow_le_abs` argument. This yields
   `sumR(vseb e) = sumR(vsebK 3 e)`, contradicting the hypothesis.

The cheapest route is to case directly on the four smallness tests (avoiding a
full formal case-4 ⇒ ε₅=0 proof): each smallness branch closes by (1); the
"all-big" branch is impossible because it forces `ε₅ = 0` against the
hypothesis, so it need only be discharged via the divisibility argument of (2).

RISK: (2) is delicate (tight at `p ≥ 6`); the `8u³` grid and the `< 5`
magnitude are the crux, mirroring `s3_div_facts` / `s3_le_15max` from item (a).
