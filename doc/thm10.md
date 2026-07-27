# Theorem 10 — Algorithm 14 (3Div): the quotient of two triple words

> **STATUS (2026-07-27). PROVED, zero admits.**
> `ThreeDiv_isTW`, `ThreeDivFast_isTW`, `ThreeProdOneTW_isTW`, the whole error
> chain (`div_error_assembly`, `div_error_core`, `ThreeDivAux_error`,
> `ThreeDiv_error`, `ThreeDivFast_error`) and `ThreeProdOneTW_error` are all
> `Qed`.  **Both of Theorem 10's constants had to move** — see the last two
> sections.
> Files: `code/coq/ThreeDiv.v` (the algorithm) and `code/coq/ThreeProdOne.v`
> (Algorithm 20, its final product).
> Setting FLX, `u = 2^{-p}`, `RN` = round-to-nearest (ties-to-even); `p ≥ 10`.

## Algorithm 14 — 3Div(z̄, x̄)

> Require: `z̄, x̄` TW, `x₀ ≠ 0`; `p ≥ 10`.
> Ensure: `ȳ` TW and `|ȳ − z̄/x̄| ≤ (24u³ + 1509u⁴)·|z̄/x̄|` (119 operations &
> 4 tests, accurate products), resp. `≤ (39u³ + 1582u⁴)·|z̄/x̄|` (103 & 2, fast).
>
> ```
> [the five lines of Algorithm 13]        -- a, h₁,₁, h₁, b₀,₁/b₁,₁, b₁,₂
> b̄  ← Fast2Sum(b₀,₁, b₁,₂)               -- a DW, b̄ ≈ 1/x̄
> ī  ← 2 − 3Prod₂,₃(b̄, x̄)                 -- head 1, as in Algorithm 13
> ā  ← 3Prod₂,₃(b̄, z̄)
> ȳ  ← 3Prod₃,₃(ā, ī)
> ```

**Why `(z̄b̄)(2 − b̄x̄)` and not `z̄(b̄(2 − b̄x̄))`** (old paper §9): the two
products `z̄b̄` and `2 − b̄x̄` become independent, hence parallelisable; and the
optimisations that `i₀ = 1` allows are worth more on a TW × TW product than on
a DW × TW one.

In Rocq the three products are parameters — `ThreeDivAux mul1 mul2 mul3` —
with `mul1`, `mul2` the DW × TW products (Algorithm 11 or 12) and `mul3` the
TW × TW product with a head-`1` second argument (Algorithm 20).

## Algorithm 20 — the final product (old paper §9, 21 flops)

`3Prod^fast₃,₃(a₀,a₁,a₂,(1),i₁,i₂)`. It is **Algorithm 18 with one extra
line**, and its first argument is a triple word rather than a double word:

```
z01⁺, z01⁻ ← 2Prod(a₀, i₁)
b′₀, b′₁   ← Fast2SumS(a₁, z01⁺)          -- sorted; see Theorem 9's finding 3
z₃,₁ ← RN(z01⁻ + a₁i₁) ; z₃ ← RN(z₃,₁ + a₀i₂)
s₃′  ← RN(b′₁ + z₃)                        -- Algorithm 18's s₃
s₃   ← RN(s₃′ + a₂)                        -- THE one new line
e₀,e₁,e₂ ← VecSum(a₀, b′₀, s₃) ; y₀ ← e₀ ; y₁,y₂ ← Fast2SumS(e₁,e₂)
```

`ThreeProdOne.v` shares everything up to `s₃′` between the two algorithms: the
term bounds are stated with the **triple-word** hypothesis `|x₁| ≤ 2u|x₀|`,
which a double word satisfies a fortiori, so Algorithms 18 and 20 use the same
`p18z01p_le … p18s3_le`, and Algorithm 20 adds only `p20s3_le`.

## What is proved, and how

**`isTW` (done).** `ThreeDivAux_isTW` is Algorithm 13's assembly with one
product more: `mul1` must return a TW and satisfy `head_one` (so `2 − mul1 b x`
is a TW, by `sub2TW_isTW`), `mul2` must return a TW, and `mul3` must do so on a
head-`1` second argument. `reciB_isDW`, `reciBW_x_err` and `head_one` for
Algorithms 11/12 are all reused unchanged from Theorem 9.
`ThreeProdOneTW_isTW` mirrors `ThreeProdOne_isTW`: `vecSum_head_sep` gives the
half-ulp between the two leading limbs of the inner VecSum, `Fast2SumS` makes
the pair below it a double word; only the constants change (`|x₁| ≤ 2u|x₀|`
and `|x₂| ≤ 4u²|x₀|` push `|S| ≤ 8u|x₀|` and the head window to `½ + 10u`).

**The error (proved, top down).** With `δ₁` the relative error of `ī`
(relative to `x̄b̄`), `δ₂` that of `ā` and `δ₃` that of the final product:

```
|ȳ − z̄/x̄| ≤ ( δ₁(1 + 71u²) + (δ₂ + δ₃)(1 + 107u²) + 1165u⁴ )·|z̄/x̄|
```

with `δ₁ = δ₂ = 10.5u³+39u⁴` (Alg 11) or `18u³+75u⁴` (Alg 12) — both already
proved — and `δ₃` = Algorithm 20's bound. Whence `24 = 10.5+10.5+3` and
`39 = 18+18+3`. Steps, and what each already has:

| step | needs | state |
|---|---|---|
| 1 | `b` is a DW, `\|b x − 1\| ≤ 34u²+123u³` | `reciB_isDW`, `reciBW_x_err` — **proved** (Alg 13) |
| 2 | `i` has head 1 and `\|i − 1\| ≤ 40u²` | `head_one` + `sub2TW_isTW`; the `\|i−1\|` bound was factored out of `ThreeReciAux_error` as **`sub2_near_one`** (ThreeReci.v) and both theorems now call it — **proved** |
| 3 | `y − z/x = (y − a i) + (a − b z) i + (b z)(x b − p) + z(b(2−xb) − 1/x)` | `newton_id`, `newton_sq_le` (`1165u⁴`) — **proved** |
| 4 | the final arithmetic on four error terms | **`div_error_assembly`** — `reci_error_assembly` with the extra product; **proved** |
| 5 | `δ₃` | `ThreeProdOneTW_error` — **the only thing still admitted** |

Steps 2–4 are packaged as **`div_error_core`**, which knows nothing about
triple words: it takes the six bare reals `B, X, Z, P, A, Y` with the three
products' relative errors and returns Theorem 10's bound. `ThreeDivAux_error`
is then five lines of glue, and the two theorems are one instantiation each.

## The proved constants, and why they differ from the paper

| variant | paper | proved |
|---|---|---|
| accurate | `24u³ + 1509u⁴` | **`29u³ + 2576u⁴`** |
| fast | `39u³ + 1582u⁴` | **`44u³ + 2650u⁴`** |

**The `u³` term is the paper's own arithmetic, not a slack in ours.**
`24 = 10.5 + 10.5 + 3` and `39 = 18 + 18 + 3` charge Algorithm 20 with `3u³`.
Its honest cost on a *triple* word is `8u³` (`ThreeProdOneTW_error`), whence
`29 = 10.5 + 10.5 + 8` and `44 = 18 + 18 + 8`.

Where the `8u³` comes from — the two roundings at the bottom of the chain:

| term | Alg 18 (DW first argument) | Alg 20 (TW first argument) |
|---|---|---|
| `η₃ = RN(b′₁+z₃) − (b′₁+z₃)`, from `\|b′₁\| ≤ u·\|b′₀\|` | `u·(u² + …) = 1u³` | `u·(2u² + …) = **2u³**` |
| `η₄ = RN(s₃′+x₂) − (s₃′+x₂)`, from `\|x₂\| ≤ 4u²\|x₀\|` | — (no `x₂`) | `u·(2u² + 4u² + …) = **6u³**` |

A triple word only guarantees `|x₁| < ulp(x₀) ≤ 2u|x₀|` and
`|x₂| < ulp(x₁) ≤ 4u²|x₀|` — *twice* a double word's separation at each level.
The paper's `3u³ = 1u³ (η₃) + 2u³ (η₄)` is what one gets from the double-word
separations `|x₁| ≤ u|x₀|`, `|x₂| ≤ u²|x₀|`, which a P-nonoverlapping triple
word does not satisfy.

**A possible tightening, not taken here.** In Algorithm 14 the first argument
of Algorithm 20 is `ā = 3Prod(b̄, z̄)`, whose last two limbs come out of a
`Fast2SumS` and therefore form a *double* word: `|a₂| ≤ u|a₁| ≤ 2u²|a₀|`, half
of what a general triple word allows. Strengthening the multipliers'
postcondition to record that would bring `η₄` to `4u³` and `δ₃` to `6u³`,
hence Theorem 10 to `27u³` / `42u³`. It would still not reach the published
`24u³` / `39u³`.

The `u⁴` figures are `29u³ + 2575.81u⁴` and `44u³ + 2649.11u⁴` exactly, at
`u = 2^{-10}`. `δ₃ = 8u³ + 1330u⁴` itself is stated for `p ≥ 6` (`u ≤ 1/64`),
where the honest chain gives `8u³ + 1211u⁴` against `|x₀|` and the division by
`|x̄ȳ| ≥ (1−4u)|x₀|` accounts for the rest.
