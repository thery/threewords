# Theorem 8 — 3Prodᵃᶜᶜ₂,₃ (product of a double word by a triple word)

> **STATUS (2026-07-25).** SKELETON. `code/coq/ThreeProdDW.v` defines `isDW`
> and `ThreeProdDW` (Algorithm 11 transcribed verbatim) and states its two
> correctness results, `ThreeProdDW_isTW` and `ThreeProdDW_error`
> (`10.5u³ + 39u⁴`); both are `Admitted`.
> `doc/paper3.pdf` §7, p. 7–8. The published paper omits the proof of
> Theorem 8 entirely ("the proof is omitted"); it is recovered from
> `doc/old-triplewors.pdf` §7 (Algorithm 14 / Theorem 11), reproduced below.
> Setting FLX, `u = 2^{-p}`, `RN` = round-to-nearest (ties-to-even), `ufp`/`uls`
> as in the paper; `p ≥ 6`.

## Algorithm 11 — 3Prodᵃᶜᶜ₂,₃(x̄, ȳ)   (45 operations & 2 tests)

> Require: `x̄ = (x₀,x₁)` DW, `ȳ = (y₀,y₁,y₂)` TW; `p ≥ 6`.
> Ensure: `r̄` TW and `|r̄ − x̄ȳ| ≤ (10.5u³ + 39u⁴)·|x̄ȳ|`.
>
> ```
> (z₀₀⁺, z₀₀⁻) ← 2Prod(x₀, y₀)          ⎫
> (z₀₁⁺, z₀₁⁻) ← 2Prod(x₀, y₁)          ⎪
> (z₁₀⁺, z₁₀⁻) ← 2Prod(x₁, y₀)          ⎬ same 5 first lines as Algorithm 9
> (b₀, b₁, b₂) ← VecSum(z₀₀⁻, z₀₁⁺, z₁₀⁺)⎪
> c    ← RN(b₂ + x₁·y₁)        (FMA)    ⎭
> z₃,₁ ← RN(z₁₀⁻ + x₀·y₂)      (FMA)
> z₃   ← RN(z₃,₁ + z₀₁⁻)                ← Algorithm 9's z₃,₂ = RN(z₀₁⁻ + x₂y₀)
>                                          collapses to z₀₁⁻ when x₂ = 0
> (e₀, e₁, e₂, e₃, e₄) ← VecSum(z₀₀⁺, b₀, b₁, c, z₃)
> r₀ ← e₀
> (r₁, r₂) ← VSEB(2)(e₁, e₂, e₃, e₄)
> return (r₀, r₁, r₂)
> ```

Algorithm 11 **is Algorithm 9 with `x₂ = 0`**: the FMA `z₃,₂ = RN(z₀₁⁻ + x₂y₀)`
becomes `RN(z₀₁⁻) = z₀₁⁻` (an error of a rounded product, hence a float), which
saves one operation. Everything else is literally the same term list.

## Theorem 8

> If `x̄` is a DW number and `ȳ` is a TW number, then the relative error of
> `3Prodᵃᶜᶜ₂,₃(x̄, ȳ)` is bounded by `10.5u³ + 39u⁴`, provided `p ≥ 6`.

## Part 1 — correctness (the result is a TW)

Immediate (paper §7.1): "since Algorithm 11 is a particular case of Algorithm 9,
correctness is directly ensured, provided that `p ≥ 6`". Formally,
`ThreeProdDW x̄ ȳ = ThreeProd (x₀, x₁, 0) ȳ` and a DW is a TW with a zero third
limb, so `ThreeProd_isTW` gives the result.

## Part 2 — the error bound (old paper §7.4)

WLOG `1 ≤ x₀, y₀ < 2`. Being a **DW**, `|x₁| ≤ ½ulp(x₀) = u` (Algorithm 9 only
had `|x₁| < 2u`); as before `|y₁| < 2u`, `|y₂| < 2u²`.

### §7.2 — bounds on the terms (tighter than §6.1)

| term | bound | | term | bound |
|------|-------|-|------|-------|
| `z₀₀⁺` | `1 ≤ · < 4` | | `|x₁y₁|` | `< 2u²` |
| `z₀₀⁻` | `≤ 2u`, `uls ≥ 4u²` | | `|c|` | `≤ 6u²` |
| `z₀₁⁺` | `< 4u` | | `|x₀y₂|` | `< 4u²` |
| `z₁₀⁺` | `< 2u` | | `|b₂|` | `≤ 4u²` |
| `z₀₁⁻` | `≤ 2u²` | | `|z₃,₁|` | `≤ 5u²` |
| `z₁₀⁻` | `≤ u²` | | `|z₃|` | `≤ 7u²` |
| | | | `|s₃|` | `≤ 13u²` |

### The naive analysis

There is **no ε₂** (Algorithm 9's `z₃,₂` term disappears), and `ε₀` loses its
`x₂` contributions:

```
|ε₀| = |x₁y₂|                        ≤ 2u³ − 2u⁴
|ε₁| = |(z₁₀⁻ + x₀y₂) − z₃,₁|        ≤ u·ufp(u² + 4u²)  ≤ 4u³
|ε₃| = |(z₃,₁ + z₀₁⁻) − z₃|          ≤ u·ufp(5u² + 2u²) ≤ 4u³
|ε₄| = |(b₂ + x₁y₁) − c|             ≤ u·ufp(4u² + 2u²) ≤ 4u³
|ε₅| = |(z₀₀⁺+b₀+b₁+c+z₃) − (r₀+r₁+r₂)| ≤ (2u³+4.2u⁴)|z₀₀⁺+b₀+b₁+c+z₃|
```

so `|ε₀+…+ε₄| ≤ 14u³ − 2u⁴`, giving the naive `16u³ + 62u⁴` — not good enough.

### ⋆ Refinement 1: a big error forces a big product

- If `|ε₁| > 2u³`: since `|z₁₀⁻| ≤ u²`, one needs `|x₀y₂| > 3u²`, so `|x₀| > 1.5`
  and hence `x̄ȳ ≥ 1.5 − 6u`.
- If `|ε₄| > 2u³`: since `|x₁y₁| ≤ 2u²`, one needs `|b₂| > 2u²`, so
  `|z₀₁⁺ + z₁₀⁺| > 4u`, i.e. `x₀(2u−2u²) + y₀u ≥ 4u`, so `x₀y₀ ≥ 1.5` and
  `x̄ȳ ≥ 1.5 − 5u`.

So either `x̄ȳ ≥ 1.5 − 6u`, or both `|ε₁| ≤ 2u³` and `|ε₄| ≤ 2u³`.

### ⋆ Refinement 2: ε₅ ≠ 0 is constraining

- If `ufp(r₀) ≥ 2`: P-nonoverlapping gives `r̄ ≥ 2 − 4u`, so `x̄ȳ ≥ 2 − 5u`.
- If `ufp(r₀) ≤ 1`: for `ε₅ ≠ 0` one of `z₀₀⁺, z₀₀⁻, z₀₁⁺, z₁₀⁺, c, z₃` must
  fail to be divisible by `2u³`, hence be `< u²` in absolute value. Now
  `z₀₀⁺, z₀₀⁻` are always divisible by `4u²`, and:
  - `|z₁₀⁺| < u²` ⇒ `|x₁| < u²` ⇒ `|ε₀| ≤ 2u⁴`;
  - `|z₀₁⁺| < u²` ⇒ `|y₁| < u²` ⇒ `|y₂| < u³` ⇒ `|ε₀| ≤ u⁴`;
  - `|z₃| < u²` ⇒ `|ε₃| ≤ ½u³`;
  - `|c| < u²` ⇒ `|ε₄| ≤ ½u³`.

### ⋆ The final case analysis

```
x̄ȳ ≥ 2 − 5u                       : (2u³+4.2u⁴) + (14u³−2u⁴)(1+2u³+4.2u⁴)/(2−5u)
                                                                   ≤ 10u³
2−5u > x̄ȳ ≥ 1.5−5u, ε₅ = 0        : (14u³−2u⁴)/(1.5−5u)            ≤ 10u³
2−5u > x̄ȳ ≥ 1.5−5u, ε₅ ≠ 0        : (2u³+4.2u⁴)
                                     + (12u³+2u⁴)(1+2u³+4.2u⁴)/(1.5−5u)
                                                                   ≤ 10u³+34u⁴
1.5−6u > x̄ȳ, ε₅ = 0               : (10u³−2u⁴)/(1−4u)              ≤ 10u³+41u⁴
1.5−6u > x̄ȳ, ε₅ ≠ 0               : (2u³+4.2u⁴)
                                     + (8.5u³−2u⁴)(1+2u³+4.2u⁴)/(1−4u)
                                                                ≤ 10.5u³+39u⁴
```

(the last line is the worst case, reached when only `|c| < u²` holds — the other
sub-cases are partly redundant with `1.5−6u > x̄ȳ`). The paper adds that it is
unclear whether `10.5u³+39u⁴` is tight, "but it is not so far from optimality":
in binary64, `(x₀,x₁) = (1+3·2²⁷u, u−2²⁷u²)` and
`(y₀,y₁,y₂) = (1+(3·2²⁶+6)u, 2u−5·2²⁷u², 2u²−26u³)` come close.

## Rocq map (`code/coq/ThreeProdDW.v`)

| paper object | Rocq |
|---|---|
| DW number | `isDW` (a `twR` with `x₂ = 0` and `2\|x₁\| ≤ ulp x₀`) |
| Algorithm 11 | `ThreeProdDW` |
| result is TW | `ThreeProdDW_isTW` (**admitted**) |
| Theorem 8 (`10.5u³+39u⁴`) | `ThreeProdDW_error` (**admitted**) |

Reuse plan (as for Algorithm 10 — see `doc/alg10.md`):

- **part 1** is a one-liner: `ThreeProdDW_eq` (`ThreeProdDW x̄ ȳ =
  ThreeProd (x₀,x₁,0) ȳ`, since `RN(z₀₁⁻ + 0·y₀) = z₀₁⁻` by `round_generic` on
  `format_err_mul`) plus `isDW_isTW` and `ThreeProd_isTW`.
- **part 2** re-instantiates the Algorithm-9 error skeleton with `x₂ = 0`: the
  WLOG scale/sign reduction, `error_decomp`/`sumR_e_decomp`, `eps5_bound`
  (generic), `eps5_zero_all_big`-style divisibility, `vecSum_imul_forward`,
  `vseb_imul_forward`. New work: a `dw_norm` normalisation carrying `|x₁| ≤ u`,
  the tighter §7.2 term bounds, the two refinements above (which need the
  P-nonoverlap lower bound on `r̄` from `sumR_ufp_lower`), and the five-case
  assembly.
