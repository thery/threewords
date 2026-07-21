# paper3 ↔ formalisation map

Catalogue of every algorithm, theorem and definition in `doc/paper3.pdf`
(Fabiano, Muller, Picot, *Algorithms for triple-word arithmetic*, IEEE TC 2019,
11 pp.), with formalisation status in `code/coq/`. `✓` proved (zero admits,
axioms = classical logic + funext + reals), `—` not formalised.

Setting: radix 2, precision `p`, **unbounded exponent** (the paper's own model =
Flocq's FLX), `u = 2^{-p}`.

## Definitions

| # | Definition | Formalised |
|---|---|---|
| 1 | P-nonoverlapping (Priest): `∀i, |xᵢ₊₁| < ulp(xᵢ)` | ✓ `Nonoverlap.Pnonoverlap` |
| 2 | F-nonoverlapping (Fabiano): `∀i, |xᵢ₊₁| ≤ ½ uls(xᵢ)` | ✓ `Nonoverlap.Fnonoverlap_aux` |
| 3 | Nonoverlapping wIZ (with interleaving zeros) | ✓ `Nonoverlap.Fnonoverlap` |
| 4 | Double-word (DW): `(x₀,x₁)`, `x₀ = RN(x₀+x₁)` | ✓ (implicit; `TWR` uses the TW case) |
| 5 | Triple-word (TW): P-nonoverlapping triplet | ✓ `TWR.isTW` |

## §2 Basic blocks

| Alg | Name (ops) | Theorem / property | Formalised |
|-----|------------|--------------------|-----------|
| 1 | Fast2Sum(a,b) (3) — error of FP add, magnitudes known | correctness | ✓ `Fast2Sum_robust_flx.v` |
| 2 | 2Sum(a,b) (6) — error of FP add | correctness | ✓ `TwoSum.v` |
| 3 | 2Prod(a,b) (2, FMA) — error of FP mult | correctness | — |
| 4 | VecSum(x₀…x_{n-1}) (6n−6) | **Thm 1** (F-nonoverlap wIZ) + **Cor 1** | ✓ `VecSum.vecSum_Fnonoverlap_core`, `vecSum_Fnonoverlap` (Cor 1) |
| 5 | VSEB(e₀…e_{n-1}) (6n−6, n−2 tests) | **Thm 2** (P-nonoverlap) | ✓ `VSEB.v` |
|   |   | **Thm 3** (rel. error of keeping first `k` terms ≤ `2u^k + 4.2u^{k+1}`, `p≥6`) | ✓ `Nonoverlap.Pnonoverlap_truncate_error` (general `k`; `TWSum_error` = its `k=3`) |

## §3–5 Conversions and addition

| Alg | Name (ops) | Theorem | Formalised |
|-----|------------|---------|-----------|
| 6 | ToTW(a,b,c) (21, 1 test) — 3 FP → TW | **Thm 4** (`p≥4`) | ✓ `ToTW_isTW` |
| 7 | RoundTW(x₀,x₁,x₂) (3, 4 tests) — TW → nearest FP | **Thm 5** (`RoundTW(x̄)=RN(x̄)`, `p≥4`) | — |
| 8 | TWSum(x,y) (42, 8 tests) — sum of two TW | **Thm 6** (result is TW, `p≥4`) + error `2u³+4.2u⁴` | ✓ `TWSum_isTW` / `TWSum_error`; Thm 6 core = `Thm6.vecSum_vseb_Pnonoverlap` |

**Note on Theorem 6 (`p≥4` is needed; ≤6 inputs is needed).** The raw VecSum
output is *not* F-nonoverlapping — machine-checked counterexample
`CEThm6.not_Fnonoverlap_vecSum_l` (`[15;15;15/16;15/16]` at `p=4`). VSEB
repairs it. Theorem 6 is false for 7 inputs (paper's own `[1-u,-1+2u,…]`
witness). See `doc/thm6.md`.

## §6–10 Multiplication, division, square root — none formalised

| Alg | Name (ops) | Theorem | Formalised |
|-----|------------|---------|-----------|
| 9  | 3Prod^acc_{3,3}(x,y) (46, 2 tests) — TW × TW | **Thm 7** (err `28u³+107u⁴`, `p≥6`) | — |
| 10 | 3Prod^fast_{3,3}(x,y) (38, 1 test) | err `44u³+176u⁴` | — |
| 11 | 3Prod^acc_{2,3}(x,y) (45, 2 tests) — DW × TW | **Thm 8** (err `10.5u³+39u⁴`, `p≥6`) | — |
| 12 | 3Prod^fast_{2,3}(x,y) (37, 1 test) | err `18u³+75u⁴` | — |
| 13 | 3Reci(x) (73, 2 tests) — reciprocal (Newton) | **Thm 9** (`p≥10`) | — |
| 14 | 3Div(z,x) (119, 4 tests) — quotient | **Thm 10** (err `24u³+1509u⁴`, `p≥10`) | — |
| 15 | 3SqRt(x) (127, 4 tests) — square root (Newton) | **Thm 11** (err `24u³+10260u⁴`, `p≥11`) | — |
| 16–18 | appendix: sign-folded product variants | (support Thms 9–11) | — |

Supporting: **Lemma 1** (`½ulp(x) ∣ RN(x+y)`) — used in the Thm 7 proof — not
formalised (only needed for multiplication).

## Summary

**Formalised: the complete addition path.** Basic blocks Fast2Sum + 2Sum
(Alg 1, 2); VecSum with Theorem 1 and Corollary 1 (Alg 4); VSEB with Theorem 2
and the general Theorem 3 truncation bound (Alg 5); ToTW with Theorem 4
(Alg 6); and TWSum with Theorem 6 and its `2u³+4.2u⁴` error bound (Alg 8),
instantiated at binary64. All zero-admit.

**Not formalised:** 2Prod (Alg 3), the conversion RoundTW (Alg 7 / Thm 5),
and the entire multiply/divide/reciprocal/sqrt half of the paper (Alg 9–18 /
Thm 7–11).
