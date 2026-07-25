# Algorithm 12 — 3Prodᶠᵃˢᵗ₂,₃ (fast product of a double word by a triple word)

> **STATUS (2026-07-25).** `ThreeProdDWFast_isTW` is **PROVED**;
> `ThreeProdDWFast_error` (`18u³ + 75u⁴`) is still `Admitted`.
> `code/coq/ThreeProdDWFast.v` defines `ThreeProdDWFast` (Algorithm 12
> transcribed verbatim); part 1 is `ThreeProdDWFast_eq` + `isDW_isTW` +
> `ThreeProdFast_isTW`.
> `doc/paper3.pdf` §7.2, p. 8 (the *faster version*). As for Theorem 8 the
> published paper gives no proof; the details come from
> `doc/old-triplewors.pdf` §7.5 (Algorithm 15), reproduced below.
> Setting FLX, `u = 2^{-p}`, `RN` = round-to-nearest (ties-to-even), `ufp`/`uls`
> as in the paper; `p ≥ 6`.

## Algorithm 12 — 3Prodᶠᵃˢᵗ₂,₃(x̄, ȳ)   (37 operations & 1 test)

> Require: `x̄ = (x₀,x₁)` DW, `ȳ = (y₀,y₁,y₂)` TW; `p ≥ 6`.
> Ensure: `r̄` TW and `|r̄ − x̄ȳ| ≤ (18u³ + 75u⁴)·|x̄ȳ|`.
>
> ```
> (z₀₀⁺, z₀₀⁻) ← 2Prod(x₀, y₀)          ⎫
> (z₀₁⁺, z₀₁⁻) ← 2Prod(x₀, y₁)          ⎪
> (z₁₀⁺, z₁₀⁻) ← 2Prod(x₁, y₀)          ⎬ same 5 first lines as Algorithm 9
> (b₀, b₁, b₂) ← VecSum(z₀₀⁻, z₀₁⁺, z₁₀⁺)⎪
> c    ← RN(b₂ + x₁·y₁)        (FMA)    ⎭
> z₃,₁ ← RN(z₁₀⁻ + x₀·y₂)      (FMA)
> z₃   ← RN(z₃,₁ + z₀₁⁻)                ← Algorithm 11's line (x₂ = 0)
> s₃   ← RN(c + z₃)                     ← single rounding (no 2Sum, no e₄)
> (e₀, e₁, e₂, e₃) ← VecSum(z₀₀⁺, b₀, b₁, s₃)
> r₀ ← e₀
> (r₁, r₂) ← VSEB(2)(e₁, e₂, e₃)
> return (r₀, r₁, r₂)
> ```

Algorithm 12 is to Algorithm 11 exactly what Algorithm 10 is to Algorithm 9:
the low word `e₄ = (c + z₃) − s₃` is dropped. Equivalently, **Algorithm 12 is
Algorithm 10 with `x₂ = 0`** — which is how correctness is inherited.

## Part 1 — correctness (the result is a TW)

Immediate, as in §7.1: `ThreeProdDWFast x̄ ȳ = ThreeProdFast (x₀, x₁, 0) ȳ`, and
a DW is a TW with a zero third limb, so `ThreeProdFast_isTW` gives the result.

## Part 2 — the error bound (old paper §7.5)

The five sources of Theorem 8 are unchanged (`doc/thm8.md`) — in particular
there is no `ε₂` and `ε₀ = x₁y₂ ≤ 2u³ − 2u⁴` — and there is **one more**, the
term Algorithm 12 drops:

```
|ε₄′| = |(c + z₃) − s₃| ≤ u·ufp(c + z₃) ≤ u·ufp(6u² + 7u²) ≤ 8u³
```

so the naive numerator is `22u³ − 2u⁴`. The case analysis is *simpler* than
Theorem 8's, because (old paper) "we can consider `s₃` instead of `c` and `z₃`,
which eliminates the case with redundancy":

- **a large `ε₁` or `ε₄` forces `x̄ȳ ≥ 1.5 − 7u`** (`eps1_big_prod_dw`,
  `eps4_big_prod_dw`, reused verbatim from Theorem 8);
- **`ε₅ ≠ 0` forces** either `x̄ȳ ≥ 2 − 5u`, or one of `z₀₁⁺`, `z₁₀⁺`, `s₃`
  below `u²` — the `2u³`-grid argument again, now on the four-limb list.

Three cases suffice:

```
x̄ȳ ≥ 1.5 − 7u                : K = 22u³ − 2u⁴  (naive), with ε₅
x̄ȳ < 1.5 − 7u, ε₅ = 0        : K = 18u³ − 2u⁴  (|ε₁|,|ε₄| ≤ 2u³)
x̄ȳ < 1.5 − 7u, ε₅ ≠ 0        : K = 16u³ + 2u⁴  (one more source shrinks)
```

matching the old paper's own final line

```
|r̄ − x̄ȳ|/|x̄ȳ| ≤ max( (18u³−2u⁴)/(1−4u),
                      (2u³+4.2u⁴) + (16u³+2u⁴)(1+2u³+4.2u⁴)/(1−4u) )
              ≤ 18u³ + 75u⁴
```

(the last case is the tight one: it needs `u ≤ 1/64`, i.e. `p ≥ 6`). The paper
notes the bound is very tight — the binary64 input of §6.3 gives a relative
error `≈ (18 − 2.4·10⁻⁶)u³`.

## Rocq map (`code/coq/ThreeProdDWFast.v`)

| paper object | Rocq |
|---|---|
| Algorithm 12 | `ThreeProdDWFast` |
| result is TW | `ThreeProdDWFast_isTW` (**proved**), via `ThreeProdDWFast_eq` |
| error `18u³+75u⁴` | `ThreeProdDWFast_error` (**admitted**) |

Reuse plan:

- **part 1**: `ThreeProdDWFast_eq` (Algorithm 12 = Algorithm 10 at `x₂ = 0`,
  since `RN(z₀₁⁻ + 0·y₀) = z₀₁⁻`) + `isDW_isTW` + `ThreeProdFast_isTW`.
- **part 2**: Algorithm 10's `innerF_Fnonoverlap`, `ThreeProdFast_norm_eq`,
  `sumR_eF_decomp`, `epsp4_bound`-style caps and `eps5_bound`; Theorem 8's
  `dw_norm` machinery, §7.2 term bounds, `eps1_big_prod_dw`/`eps4_big_prod_dw`,
  `err_small_of_round`, `eps0_small_of_z01p`/`_z10p` and the two assembly
  lemmas. New: `epsp4_bound_dw` (`≤ 8u³`), the four-limb error identity at
  `x₂ = 0`, the `ε₅ ≠ 0` disjunction on `s₃`, and the three-case assembly.
