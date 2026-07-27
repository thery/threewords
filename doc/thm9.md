# Theorem 9 — Algorithm 13 (3Reci): the reciprocal of a triple word

> **STATUS (2026-07-27).** **PART 1 IS COMPLETE — `isTW` is now unconditional.**
> `ThreeReci_isTW`/`ThreeReciFast_isTW` are `Qed` on top of the whole §8.2
> chain — `reciB_isDW` (the Newton word is a DW) and `reciBW_x_err`
> (`|b̄x̄ − 1| ≤ 34u² + 123u³`) — **and of §8.3 `head_one`, now PROVED for both
> multipliers**. 2 admits left in `code/coq/ThreeReci.v`: `ThreeReci_error`
> and `ThreeReciFast_error` (Theorem 9 itself). PRs #130, #131 merged.
>
> **How §8.3 was proved.** It cannot be proved from the multiplier's OUTPUT:
> `(1+2u, −2u+2u², …)` is P-nonoverlapping and sums to `1 + O(u²)` with head
> `1+2u`. The argument runs on the pre-VSEB VecSum limbs, where `e₀`, `e₁` are
> the two words of ONE 2Sum, giving the genuine half-ulp `2|e₁| ≤ ulp e₀`
> (`vecSum_head_sep`). The chain, all generic in `VecSum.v`:
> `vecSumAux_run_le` (running sum ≤ `(1+u)ⁿ·mass`), `vecSumAux_err_le`
> (accumulated rounding error ≤ `n u (1+u)ⁿ·mass`), `vecSum_head_tail_le` and
> `vecSum_head_gap` — the leading limb is within **half an ulp plus the
> accumulated error of the entries below it** of the whole sum. Each
> multiplier then supplies just two numbers: `D` (`inner_sum_err_dw(F)`, the
> §7.2 sources) and `B` (`inner_low_mass_dw(F)`, the mass of the low entries,
> `O(u)` here), giving `_head_gap_norm`. The scale/sign WLOG
> (`head_gap_gen`) and the last step (`head_one_gen`) are generic in the
> multiplier, so Algorithms 11 and 12 each instantiate them in five lines.
>
> **Two corrections to the old paper's §8.3.** (i) Its tail bound is stated
> with `uls`, which is NOT enough: `[16; −8; −4; −2; −1]` is F-nonoverlapping
> and sums to `1` with head `16`. The argument needs the **ulp**-scale
> separation of the two leading limbs, which only the 2Sum structure gives.
> (ii) `p ≥ 10` is genuinely needed, not `p ≥ 9`: `head_eq_1`'s margins are
> `u − 200u²` above `1` and `u/2 − 200u²` below, so the binding constraint is
> `u < 1/472`.
>
> `doc/paper3.pdf` §8, Theorem 9 — the published proof is in supplementary
> material we do not have; the route below is recovered from
> `doc/old-triplewors.pdf` §8.
> Setting FLX, `u = 2^{-p}`, `RN` = round-to-nearest (ties-to-even), `ufp`/`uls`
> as in the paper; `p ≥ 10`.

## Algorithm 13 — 3Reci(x₀, x₁, x₂)

> Require: `x̄ = (x₀,x₁,x₂)` TW, `x₀ ≠ 0`; `p ≥ 10`.
> Ensure: `ȳ` TW and `|ȳ − x̄⁻¹| ≤ (11.5u³ + 1465u⁴)·|x̄⁻¹|` (73 operations &
> 2 tests, `3Prod₂,₃` = Algorithm 11), resp. `≤ (19u³ + 1502u⁴)·|x̄⁻¹|`
> (65 operations & 1 test, `3Prod₂,₃` = Algorithm 12).
>
> ```
> a    ← RN((1 + 2u)/x₀)
> h₁,₁ ← 2Prod2_{(1+2u)}(a, x₀) = RN(a·x₀ − (1 + 2u))   (FMA)
> h₁   ← RN(−h₁,₁ − a·x₁)                               (FMA)
> b₀,₁, b₁,₁ ← 2Prod(a, 1 − 2u)
> b₁,₂ ← RN(b₁,₁ + a·h₁)                                (FMA)
> b̄    ← Fast2Sum(b₀,₁, b₁,₂)                           (a DW)
> ī    ← 2 − 3Prod₂,₃(b̄, x̄)
> ȳ    ← 3Prod₂,₃(b̄, ī)
> return (y₀, y₁, y₂)
> ```

The algorithm is one Newton-Raphson step `r_{n+1} = r_n(2 − r_n x)` in DW
arithmetic (lines 1–6, producing `b̄ ≈ 1/x̄`) followed by one in TW arithmetic
(lines 7–8).

**Why `1 + 2u` and not `1`.** For any float `x`, `RN(x·RN((1+2u)/x)) = 1 + 2u`
exactly ("the proof is straightforward", paper §8). So the head of
`2 − a·(x₀+x₁)` is the *constant* `h₀ = 2 − (1+2u) = 1 − 2u`: it is a **virtual
word**, costing no operation, and `h₁,₁` is exactly the error of the product
`a·x₀` taken with respect to `1 + 2u`. The pair `h̄ = (h₀, h₁) = (1 − 2u, h₁)`
is a DW approximating `2 − a(x₀+x₁)`.

The old paper computes `h₀,₁, h₁,₁ ← 2Prod(x₀, a)` and then `h₀ ← 2 − h₀,₁`,
which is exact by **Sterbenz** because

```
|h₀,₁| ≥ (1−u)|x₀a| ≥ (1−u)²(1+2u) ≥ 1 − 3u² > 1 − u   ⟹   |h₀,₁| ≥ 1
```

— the same fact, one operation more. `paper3` folds it away; our definition
follows `paper3`.

## Part 1 — the result is a triple word

Both products are calls to Algorithm 11 (resp. 12), whose result is a TW
(`ThreeProdDW_isTW`, `ThreeProdDWFast_isTW`) as soon as the first argument is a
DW and the second a TW. So there are only two things to prove:

1. **`b̄ = Fast2Sum(b₀,₁, b₁,₂)` is a DW.** Fast2Sum is error-free and its
   result satisfies `2|b₁| ≤ ulp(b₀)` when the exponents are ordered, which
   holds because `|b₁,₂| ≲ u|b₀,₁|` (`b₀,₁ = RN(a(1−2u))` is of the size of
   `a`, and `b₁,₂ = RN(b₁,₁ + a·h₁)` with `|b₁,₁| ≤ u|a|` and
   `|h₁| ≤ 3u + 10u²`).
2. **`2 − ē` preserves `isTW`** (`sub2TW`): the two low limbs are negated, and
   the head `2 − e₀` must keep the same `ulp` as `e₀`. This is where `e₀ = 1`
   (§8.3 below) is used, and it is exact by Sterbenz.

## Part 2 — the error bound (old paper §8.2)

With the first product seen as a black box. Write `x = x₀ + x₁` where useful.

```
|a − 1/x₀|            ≤ |a − (1+2u)/x₀| + |2u/x₀| ≤ (3u + 2u²)|1/x₀|
                      ⟹ (1−4u)/|x₀| ≤ |a| ≤ (1+4u)/|x₀|
|h₀| ≤ 1 + 4u ;   |h₁| ≤ u|x₀a| + |a|·2u|x₀| ≤ 3u + 10u²
|1/x₀ − 1/(x₀+x₁)|    ≤ (2u − 2u²)|1/(x₀+x₁)|
|a − 1/(x₀+x₁)|       ≤ (5u + 4u²)|1/(x₀+x₁)| ,  |a| ≤ (1+6u)/|x₀+x₁|
|a(2 − (x₀+x₁)a) − 1/(x₀+x₁)| = |x₀+x₁|·(a − 1/(x₀+x₁))²
                      ≤ (25u² + 41u³)|1/(x₀+x₁)|          (Newton, quadratic)
|h̄ − (2 − (x₀+x₁)a)| = |h₁ − (−h₁,₁ − a x₁)| ≤ u|h₁,₁ + a x₁| ≤ 3u² + 12u³
|b̄ − a·h̄|            = |b₁,₂ − (b₁,₁ + a h₁)| ≤ u(u|a h₀| + |a h₁|)
                      ≤ (4u² + 14u³)|a|
|b̄ − 1/(x₀+x₁)|      ≤ (7u² + 26u³)|a| + (25u² + 41u³)|1/(x₀+x₁)|
                      ≤ (32u² + 110u³)|1/(x₀+x₁)|
|1/(x₀+x₁) − 1/x̄|    ≤ 2u²/(1−2u)·|1/x̄| ≤ (2u² + 5u³)|1/x̄|
|b̄ − 1/x̄|           ≤ (34u² + 115u³)|1/x̄|
                      ⟹ (1−35u²)/|x̄| ≤ |b̄| ≤ (1+35u²)/|x̄|
|b̄(2 − x̄b̄) − 1/x̄|  = |x̄|·(b̄ − 1/x̄)² ≤ 1172u⁴|1/x̄|      (Newton, quadratic)
```

> **Remark 8 (old paper).** The `1172u⁴` residue is negligible for large `p`
> because Newton doubles the precision at each step — it jumps from `2` to `4`,
> not to `3`. This is why it does not matter that the first step was computed
> sloppily (starting from `1 + ulp(1)` instead of `1`).

Let `δ₁` be the relative error committed when computing `ī` (relative to `x̄b̄`)
and `δ₂` the one for `ȳ` (relative to `b̄ī`). Then

```
|ī − (2 − x̄b̄)| ≤ δ₁|x̄b̄| ≤ δ₁(1 + 35u²) ,   |ī| ≤ |2 − x̄b̄| + … ≤ 1 + 71u²
|ȳ − b̄ī|       ≤ δ₂|b̄ī| ≤ δ₂(1 + 71u²)|b̄|
```

and, adding the Newton residue,

```
|ȳ − 1/x̄| ≤ ( δ₁(1 + 71u²) + δ₂(1 + 107u²) + 1172u⁴ )·|1/x̄| .
```

**Everything then reduces to bounding `δ₁` and `δ₂`.**

- `δ₁` is exactly the error of the DW × TW product on general inputs:
  `δ₁ ≤ 10.5u³ + 39u⁴` (Theorem 8, Algorithm 11) or `δ₁ ≤ 18u³ + 75u⁴`
  (Algorithm 12) — **already proved here**, usable as black boxes.
- `δ₂ ≈ 1u³` — this is the key point, and it is what makes the final constants
  `11.5 = 10.5 + 1` and `19 = 18 + 1`. The second product multiplies `b̄` by a
  triple word `ī` whose head is `1` and whose second limb is `O(u²)` (see §8.3:
  `|x̄b̄ − 1| ≤ 34u² + 74u³`), so nearly every error source of Theorem 8
  collapses and what is left is essentially the final truncation to three
  limbs. **This sharper bound is not any of the four multiplication theorems we
  have; it has to be re-derived** (the paper hides it inside its Algorithm 18,
  a *modified* `3Prod^fast₂,₃(b₀, b₁, (1), i₁, i₂)`, 20 flops).

## §8.3 — the computation of `ī`, and why `p ≥ 10`

`|b̄x̄ − 1| ≤ 34u² + 74u³`, and inside `3Prod₂,₃(b̄, x̄)` the intermediate
`ē` satisfies `|ē − b̄x̄| ≤ 20u³`, so `|ē − 1| ≤ 35u²`. Since `ē` is
F-nonoverlapping, `|e₀ − ē| ≤ (1 − 2^{-4})·uls(e₀)`, so `|e₀| > 1` would force
`|ē| ≥ (1+2u) − (1 − 2^{-4})·2u = 1 + 2^{-3}u > 1 + 35u²`, excluded. Hence

```
e₀ = 1 .
```

> **Remark 9 (old paper).** This is the property that requires `p ≥ 9` a
> priori, "even if it would probably also work for `p = 8`, `7` and maybe even
> `6`". `paper3` states `p ≥ 10`; `ThreeReci.v` assumes `p ≥ 10`.

Consequently `ī = 2 − ē = (1, −e₁, −e₂)`: the subtraction is exact and costs
one operation, which the paper avoids altogether by turning some `+` into `−`
inside the multiplication (its Algorithm 16). **We formalise Algorithm 13 as
written**, with the explicit `sub2TW`; the sign-folded Algorithms 16–18 are a
later, purely operational refinement.

## Discrepancies

| | old paper (§8, Alg 16, Thm 12) | `paper3` (§8, Alg 13, Thm 9) |
|---|---|---|
| precision | `p ≥ 9` | `p ≥ 10` |
| accurate | `11.5u³ + 1473u⁴` (75 flops & 2 tests) | `11.5u³ + 1465u⁴` (73 & 2) |
| fast | `19u³ + 1510u⁴` (67 flops & 1 test) | `19u³ + 1502u⁴` (65 & 1) |
| `h₀` | computed, `h₀ ← 2 − h₀,₁` (exact, Sterbenz) | virtual constant `1 − 2u` |

The two saved operations are exactly the `2Prod(x₀,a)` head and the `2 − h₀,₁`
of the old version.

**Decision: the theorems state `paper3`'s bounds** — `11.5u³ + 1465u⁴` and
`19u³ + 1502u⁴` (`ThreeReci_error`, `ThreeReciFast_error`). The old paper's
chain is only the *route*; it is written with slack (its own `1473u⁴` /
`1510u⁴`), so wherever it falls short of `1465`/`1502` the intermediate
constants have to be tightened — the statement is not to be weakened to the old
values. Only the `u⁴` terms are at stake: both papers agree on `11.5u³` and
`19u³`, and the `u⁴` slack sits in the `1172u⁴` Newton residue and in the
`(1 + 71u²)`/`(1 + 107u²)` factors, all of which are stated generously above.

## New ingredients (nothing like them in the development yet)

1. **A division.** `a = RN((1+2u)/x₀)` — the development has no lemma about
   `RN(_/_)` so far; the needed bound is `|a − (1+2u)/x₀| ≤ u|(1+2u)/x₀|`
   (plain `relative_error_le`) plus the exactness of the *starting point*:
2. **`RN(x·RN((1+2u)/x)) = 1 + 2u`** for any float `x`. Paper: "the proof is
   straightforward"; it is what makes `h₀` virtual and `h₁,₁` an error-free
   transform.
3. **Sterbenz exactness**, twice: for `2 − e₀` (with `e₀ = 1`) and, in the old
   formulation, for `2 − h₀,₁`. Flocq's `Sterbenz` module is already imported
   everywhere here.
4. **Fast2Sum as a DW producer.** `Fast2Sum` is now defined in
   `code/coq/TwoSum.v` (`Fast2Sum`, `Fast2Sum_hi`, `format_Fast2Sum`); its
   exactness is `Fast2Sum_correct_aux` of `Fast2Sum_robust_flx.v`. Feeding
   `isDW` needs the ordering hypothesis discharged from `|b₁,₂| ≲ u|b₀,₁|`.
5. **A specialised DW × TW error bound** for the second product, `δ₂ ≈ 1u³`
   (see above). The `ε₀…ε₅` machinery of `ThreeProdDW.v`/`ThreeProdDWFast.v`
   should re-instantiate with `y₀ = 1`, `|y₁| = O(u²)`, `|y₂| = O(u⁴)`.

## Rocq map (`code/coq/ThreeReci.v`)

| paper object | Rocq |
|---|---|
| `2 − x̄` on triple words | `sub2TW`, `TWval_sub2TW` |
| Algorithm 13, generic in `3Prod₂,₃` | `ThreeReciAux` |
| Algorithm 13 with Algorithm 11 | `ThreeReci` |
| Algorithm 13 with Algorithm 12 | `ThreeReciFast` |
| result is a TW | `ThreeReci_isTW`, `ThreeReciFast_isTW` |
| §8.3, head is `1` | `ThreeProdDW_head_one`, `ThreeProdDWFast_head_one` |
| §8.3, pure FP core | `head_eq_1` |
| §8.3, generic steps | `head_gap_gen`, `head_one_gen`, `head_gap_scale` |
| §8.3, per multiplier | `_head_gap_norm`, `inner_sum_err_dw(F)`, `inner_low_mass_dw(F)` |
| §8.3, generic VecSum | `vecSum_head_sep`, `vecSumAux_run_le`, `vecSumAux_err_le`, `vecSum_head_tail_le`, `vecSum_head_gap` |
| **Theorem 9**, accurate `11.5u³+1465u⁴` | `ThreeReci_error` (*admitted*) |
| **Theorem 9**, fast `19u³+1502u⁴` | `ThreeReciFast_error` (*admitted*) |

Black boxes already available: `ThreeProdDW_isTW`, `ThreeProdDW_error`
(Theorem 8), `ThreeProdDWFast_isTW`, `ThreeProdDWFast_error`, the whole DW
inventory of `ThreeProdDW.v` (`isDW`, `isDW_isTW`, `dw_norm`, …) and the
generic FLX helpers of `ThreeProd.v` (`u_abs_le_ulp`, `err_mul_le_ulp`,
`round_err_le`, …).
