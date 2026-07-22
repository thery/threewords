# Theorem 7 — 3Prod (product of two triple words)

> **STATUS (2026-07-22).** Skeleton stage. `doc/paper3.pdf` §6, p. 6–7.
> Setting FLX, `u = 2^{-p}`, `RN` = round-to-nearest (ties-to-even), `ufp`/`uls`
> as in the paper. This is the FIRST algorithm of the multiplication half
> (Alg 9–18 / Thm 7–11).

Companion doc. Reuses `TwoProd` (Alg 3, `MULTmore.v`), `VecSum` (Alg 4),
`VSEB` (Alg 5) and the `isTW` predicate (`TWR.v`); the correctness proof leans
on the Theorem-6 machinery (`Thm6.v`).

## Algorithm 9 — 3Prodᵃᶜᶜ₃,₃(x̄, ȳ)   (46 operations & 2 tests)

> Require: `x̄ = (x₀,x₁,x₂)`, `ȳ = (y₀,y₁,y₂)` TW; `p ≥ 6`.
> Ensure: `r̄` TW and `|r̄ − x̄ȳ| ≤ (28u³ + 107u⁴)·|x̄ȳ|`.
>
> ```
> (z₀₀⁺, z₀₀⁻) ← 2Prod(x₀, y₀)
> (z₀₁⁺, z₀₁⁻) ← 2Prod(x₀, y₁)
> (z₁₀⁺, z₁₀⁻) ← 2Prod(x₁, y₀)
> (b₀, b₁, b₂) ← VecSum(z₀₀⁻, z₀₁⁺, z₁₀⁺)
> c    ← RN(b₂ + x₁·y₁)        (FMA)
> z₃,₁ ← RN(z₁₀⁻ + x₀·y₂)      (FMA)
> z₃,₂ ← RN(z₀₁⁻ + x₂·y₀)      (FMA)
> z₃   ← RN(z₃,₁ + z₃,₂)
> (e₀, e₁, e₂, e₃, e₄) ← VecSum(z₀₀⁺, b₀, b₁, c, z₃)
> r₀ ← e₀
> (r₁, r₂) ← VSEB(2)(e₁, e₂, e₃, e₄)
> return (r₀, r₁, r₂)
> ```

`2Prod(a,b) = (RN(a·b), RN(a·b − RN(a·b)))` (Alg 3): the rounded product and its
(exactly representable, in FLX) error. The four `RN(· + ·)` product terms are
FMAs (single rounding of `a + b·c`).

The optimisation `r₀ = e₀` (rather than `VSEB(3)(e₀,…,e₄)`) saves no operation
but removes the first VSEB branch. It is justified in the proof (part 1, ⋆):
since `e₀ = RN(e₀ + e₁)` (top of a VecSum output), the two forms agree.

## Theorem 7

> If `x̄, ȳ` are TW numbers and `p ≥ 6`, then `3Prodᵃᶜᶜ₃,₃(x̄, ȳ)` is a TW
> number, and its relative error is bounded by `28u³ + 107u⁴`.

## Proof (paper §6.1–6.2, p. 6–7)

WLOG `1 ≤ x₀, y₀ < 2`, so `|x₁|,|y₁| < 2u` and `|x₂|,|y₂| < 2u²`.

### §6.1 — Bounds on the terms

| term | bound | | term | bound |
|------|-------|-|------|-------|
| `z₀₀⁺` | `1 ≤ · < 4` | | `|x₁y₁|` | `< 4u²−4u³` |
| `z₀₀⁻` | `≤ 2u`, `uls ≥ 4u²` | | `|c|` | `< 8u²` |
| `z₀₁⁺, z₁₀⁺` | `< 4u` | | `|x₀y₂|,|x₂y₀|` | `< 4u²` |
| `z₀₁⁻, z₁₀⁻` | `≤ 2u²` | | `|b₂|` | `≤ 4u²` |
| `z₃,₁, z₃,₂` | `≤ 6u²` | | `|z₃|` | `≤ 12u²` |
| | | | `|s₃|` | `≤ 20u²` |

(`s₃ := RN(c + z₃)` and `a := RN(z₀₁⁺ + z₁₀⁺)` are the intermediate VecSum sums.)

### §6.2 part 1 — (r₀, r₁, r₂) is a TW number

**⋆ The last two lines equal `VSEB(3)(e₀,e₁,e₂,e₃,e₄)`.**
- If `e₁ ≠ 0`: `e₀ = RN(e₀ + e₁)` concludes immediately.
- If `e₁ = 0`: one checks `|s₁|,|s₂|,|s₃| < 16u ≤ ½ ufp(z₀₀⁺)`, so the next
  nonzero `|eᵢ|` is `< ½ ulp(e₀)`, which concludes.

**⋆ With that equivalent version, `(r₀,r₁,r₂)` is P-nonoverlapping.** By
Theorem 2 it suffices that `VecSum(z₀₀⁺, b₀, b₁, s₃)` is F-nonoverlapping and
that `e₄` is F-nonoverlapping with the rest.

- **`(z₀₀⁺, b₀, b₁, s₃)` satisfies the Theorem-1 conditions.** `ufp(z₀₀⁺) ≥ 1`
  is ≫ 4× any other term; and when nonzero, `ufp(b₁) ≤ ½ ulp(b₀) < ½ ufp(b₀)`.
  WLOG `|x₁| ≥ |y₁|`. Then `|s₃| ≤ 10 ulp(x₁)`, and Lemma 1 gives
  `½ ulp(x₁) ∣ a` with `½ ulp(x₁) ≤ u² < uls(z₀₀⁻)`, so `½ ulp(x₁) ∣ b₀, b₁`.
  Case split on `I` (the violation-index set of Theorem 1):
  - `s₃ = 0`: `I = ∅`.
  - `s₃ ≠ 0, b₀ = 0` (so `b₁ = 0`): `I = ∅`.
  - `s₃ ≠ 0, b₀ ≠ 0, b₁ = 0`: `I = {1}`, via `ufp(s₃) ≤ ¼ ufp(z₀₀⁺)` and
    `ufp(s₃) ≤ 2^{p−2} uls(b₀)` (uses `p ≥ 6`).
  - `s₃ ≠ 0, b₀ ≠ 0, b₁ ≠ 0`: `I = {2}`, via `ufp(s₃) ≤ 16 ufp(b₁) ≤ ¼ ufp(b₀)`
    and `ufp(s₃) ≤ 2^{p−2} uls(b₁)` (uses `p ≥ 6`).

- **`e₄` is F-nonoverlapping with the rest.** `ulp(s₃) ≥ 2|e₄|`;
  `uls(b₀),uls(b₁) ≥ ½ ulp(x₁) ≥ 1/20 |s₃| ≥ ulp(s₃)` (`p ≥ 6`);
  `ulp(z₀₀⁺) ≥ 2u > ulp(s₃)`. Hence `e₀,e₁,e₂` are divisible by
  `ulp(s₃) ≥ 2|e₄|`.

**Lemma 1.** For all FP `x, y`, `½ ulp(x) ∣ RN(x + y)`.

### §6.2 part 2 — Relative error ≤ 28u³ + 107u⁴

Three error sources: ignored terms, the roundings of `z₃`/`c`, and the terms
dropped by VSEB. A naive analysis:

```
|ε₀| = |x₁y₂ + x₂y₁ + x₂y₂| ≤ 2(2u−2u²)(2u²−2u³)+(2u²−2u³)² ≤ 8u³ − 11.9u⁴
|ε₁| = |(z₁₀⁻ + x₀y₂) − z₃,₁| ≤ u·ufp(z₁₀⁻ + x₀y₂) ≤ u·ufp(2u²+4u²) ≤ 4u³
|ε₂| = |(z₀₁⁻ + x₂y₀) − z₃,₂| ≤ 4u³
|ε₃| = |(z₃,₁ + z₃,₂) − z₃| ≤ 8u³
|ε₄| = |(b₂ + x₁y₁) − c| ≤ 4u³
|ε₅| = |(z₀₀⁺+b₀+b₁+c+z₃) − (r₀+r₁+r₂)| ≤ (2u³+4.2u⁴)|z₀₀⁺+b₀+b₁+c+z₃|
```

(`ε₅` is the Theorem-3 truncation bound at `k = 3`.) Now
`x̄, ȳ ≥ 1 − (2u−2u²) − (2u²−2u³) ≥ 1 − 2u`, so `x̄ȳ ≥ 1 − 4u`. The error is
shown not too large when `ε₅ ≠ 0` (details omitted in the paper), giving

```
|r̄ − x̄ȳ| / |x̄ȳ| ≤ (28u³ − 11.9u⁴)/(1 − 4u) ≤ 28u³ + 107u⁴.
```

The bound is tight: at `p = 53` the witness (2) in the paper attains
`≈ (28 − 10⁻⁵)u³`.

## Structural reading (for the formalisation)

- **Definition** `ThreeProd (x y : twR) : twR`, transcribing Algorithm 9
  verbatim on top of `TwoProd`, `vecSum`, `vsebK` and the FMA products
  (`RN (b + a*c)`).
- **`ThreeProd_isTW`** — `isTW x → isTW y → isTW (ThreeProd x y)` (`p ≥ 6`).
  Assembled from the §6.2 part-1 case study. The core is the F-nonoverlapping
  of `VecSum(z₀₀⁺, b₀, b₁, s₃)` plus the `e₄` divisibility; then Theorem 6
  (`vecSum_vseb_Pnonoverlap`) / Theorem 2 (`vseb_Pnonoverlap`) supply the
  P-nonoverlapping conclusion, read off the first three limbs exactly as in
  `TWSum_isTW`.
- **`ThreeProd_error`** — `|TWval (ThreeProd x y) − TWval x * TWval y| ≤
  (28u³ + 107u⁴) * |TWval x * TWval y|` (`p ≥ 6`). Sum of the six `εᵢ` bounds
  over `1 − 4u`, with `ε₅` from `Pnonoverlap_truncate_error` (Theorem 3, k = 3).
- **Lemma 1** (`half_ulp_div_RN_add`): `½ ulp(x) ∣ RN(x + y)` — new, needed for
  the `b₀,b₁` divisibility.

## Plan (order of attack)

1. Definition `ThreeProd` + the two theorem statements with `have`/`admit`
   skeletons (this PR).
2. §6.1 term bounds as named lemmas (`ThreeProd_bounds_*`).
3. Lemma 1, then the four-case `I` study → F-nonoverlapping of the 4-term inner
   VecSum → `ThreeProd_isTW`.
4. The six `εᵢ` bounds → `ThreeProd_error`.
