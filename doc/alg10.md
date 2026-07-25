# Algorithm 10 — 3Prodᶠᵃˢᵗ₃,₃ (fast product of two triple words)

> **STATUS (2026-07-25).** **COMPLETE — zero admits.** `ThreeProdFast_isTW`
> and `ThreeProdFast_error` (`44u³ + 176u⁴`) are both `Qed` in
> `code/coq/ThreeProdFast.v`, which defines `ThreeProdFast` (Algorithm 10
> transcribed verbatim). Both proofs re-instantiate the Algorithm-9 skeleton of
> `ThreeProd.v` (see `doc/thm7.md`, `doc/thm7-eps5.md`): every Section-6.1
> bound, the four-case `I`-set study `inner_head_Fnonoverlap` and the
> `eps0..eps5` error bounds are reused *verbatim*, the only new mathematics
> being the extra source `eps4' = (c + z3) - s3`. `Print Assumptions` = classic
> reals + funext, as everywhere else in the development.
> Setting FLX, `u = 2^{-p}`, `RN` = round-to-nearest (ties-to-even), `ufp`/`uls`
> as in the paper; `p ≥ 6`.

## Algorithm 10 — 3Prodᶠᵃˢᵗ₃,₃(x̄, ȳ)   (38 operations & 1 test)

> Require: `x̄ = (x₀,x₁,x₂)`, `ȳ = (y₀,y₁,y₂)` TW; `p ≥ 6`.
> Ensure: `r̄` TW and `|r̄ − x̄ȳ| ≤ (44u³ + 176u⁴)·|x̄ȳ|`.
>
> ```
> (z₀₀⁺, z₀₀⁻) ← 2Prod(x₀, y₀)          ⎫
> (z₀₁⁺, z₀₁⁻) ← 2Prod(x₀, y₁)          ⎪
> (z₁₀⁺, z₁₀⁻) ← 2Prod(x₁, y₀)          ⎬ same 5 first lines as Algorithm 9
> (b₀, b₁, b₂) ← VecSum(z₀₀⁻, z₀₁⁺, z₁₀⁺)⎪
> c    ← RN(b₂ + x₁·y₁)        (FMA)    ⎭
> z₃,₁ ← RN(z₁₀⁻ + x₀·y₂)      (FMA)
> z₃,₂ ← RN(z₀₁⁻ + x₂·y₀)      (FMA)
> z₃   ← RN(z₃,₁ + z₃,₂)
> s₃   ← RN(c + z₃)                     ← single rounding (no 2Sum, no e₄)
> (e₀, e₁, e₂, e₃) ← VecSum(z₀₀⁺, b₀, b₁, s₃)
> r₀ ← e₀
> (r₁, r₂) ← VSEB(2)(e₁, e₂, e₃)
> return (r₀, r₁, r₂)
> ```

The **only** difference with Algorithm 9 is the fourth-from-last line. Algorithm
9 computes `(s₃, e₄) = 2Sum(c, z₃)` *inside* its five-input
`VecSum(z₀₀⁺, b₀, b₁, c, z₃)` and keeps the low word `e₄`; Algorithm 10 rounds
`c + z₃` once and **drops** `e₄ = (c + z₃) − s₃`. This saves 8 operations and
one test (the paper's count: 46 ops & 2 tests → 38 ops & 1 test) and costs one
extra error term, `|e₄| ≤ 16u³`, whence `44u³ = 28u³ + 16u³`.

Note the shared prefix is literal: `z₀₀⁺, z₀₀⁻, z₀₁⁺, z₀₁⁻, z₁₀⁺, z₁₀⁻, b₀, b₁,
b₂, c, z₃,₁, z₃,₂, z₃` and `s₃ = RN(c + z₃)` are *the same terms* as in
Algorithm 9 (where `s₃` is the high word of `2Sum(c, z₃)`, i.e. `RN(c + z₃)`
again). Hence **every §6.1 bound of `doc/thm7.md` transfers verbatim**, as does
the F-nonoverlapping study of the head `VecSum(z₀₀⁺, b₀, b₁, s₃)`.

## Statement

> If `x̄, ȳ` are TW numbers and `p ≥ 6`, then `3Prodᶠᵃˢᵗ₃,₃(x̄, ȳ)` is a TW
> number, and its relative error is bounded by `44u³ + 176u⁴`.

The paper adds that this bound is *very tight*: the binary64 input of §6.3
already gives a relative error `≈ (44 − 10⁻⁵)u³`.

## Part 1 — (r₀, r₁, r₂) is a TW number

"Correctness is still ensured for the same reasons, provided that `p ≥ 6`"
(old paper §6.6). Concretely, part 1 of `doc/thm7.md` applies with *less* work:

- **⋆ The last two lines equal `VSEB(3)(e₀,e₁,e₂,e₃)`** — unchanged argument:
  `e₀ = RN(e₀ + e₁)` at the top of a VecSum output (`e₁ ≠ 0` case), and the
  `e₁ = 0` case is the same magnitude check.
- **The head `VecSum(z₀₀⁺, b₀, b₁, s₃)` is F-nonoverlapping** — this is
  *exactly* Algorithm 9's inner list, so the four-case `I ∈ {∅,{1},{2}}` study
  of Theorem 1 does not have to be redone.
- **No `e₄` tail.** Algorithm 9 needed the extra step "`e₄` is F-nonoverlapping
  with the rest" (`ulp(s₃) ≥ 2|e₄|` plus divisibility of `e₀,e₁,e₂` by
  `ulp(s₃)`). Algorithm 10 has no `e₄`, so that item disappears entirely.
- Theorem 2 then gives that `VSEB` of the head list is P-nonoverlapping, and
  reading off the first three limbs gives `isTW`.

## Part 2 — Relative error ≤ 44u³ + 176u⁴

The six error sources of Theorem 7 are unchanged (`doc/thm7.md` §6.2 part 2):

```
|ε₀| = |x₁y₂ + x₂y₁ + x₂y₂|                     ≤ 8u³ − 11.9u⁴
|ε₁| = |(z₁₀⁻ + x₀y₂) − z₃,₁|                   ≤ 4u³
|ε₂| = |(z₀₁⁻ + x₂y₀) − z₃,₂|                   ≤ 4u³
|ε₃| = |(z₃,₁ + z₃,₂) − z₃|                     ≤ 8u³
|ε₄| = |(b₂ + x₁y₁) − c|                        ≤ 4u³
|ε₅| = |(z₀₀⁺+b₀+b₁+c+z₃) − (r₀+r₁+r₂)|         ≤ (2u³+4.2u⁴)|z₀₀⁺+b₀+b₁+c+z₃|
```

and there is **one more** — the term Algorithm 10 drops (old paper §6.6):

```
|ε₄′| = |(c + z₃) − s₃| ≤ u·ufp(c + z₃) ≤ u·ufp(12u² + 8u²) ≤ 16u³
```

(using `|z₃| ≤ 12u²` and `|c| ≤ 8u²` from §6.1, so `ufp(c + z₃) ≤ 16u²`.)

Hence `|ε₀ + … + ε₄ + ε₄′| ≤ 44u³ − 11.9u⁴`, and with `x̄ȳ ≥ 1 − 4u`:

```
|r̄ − x̄ȳ| / |x̄ȳ| ≤ (44u³ − 11.9u⁴)/(1 − 4u) ≤ 44u³ + 176u⁴
```

The last inequality is `704u² ≤ 11.9u`, i.e. `u ≤ 0.0169`, which holds since
`p ≥ 6` gives `u ≤ 1/64` — this is where `p ≥ 6` is spent in the error bound,
exactly as for Algorithm 9.

As for Algorithm 9, the case `ε₅ ≠ 0` needs the refined argument (old paper
§6.6: "similarly to the previous case, we can make as is `ε₅ = 0`"), i.e. the
four-case study of `doc/thm7-eps5.md`: if `|y₂| < u²`, or `|x₂| < u²`, or
`|c| < 4u²`, or `|z₃| < 4u²`, then one of `ε₁, ε₂, ε₃, ε₄` halves to `2u³` and
the numerator drops to `42u³ − 11.9u⁴`; otherwise all of `z₀₀⁺, b₀, b₁, c, z₃`
are divisible by `8u³` and `|z₀₀⁺+b₀+b₁+c+z₃| < 5`, so a fourth nonzero
P-nonoverlapping limb would be `< 8u³` — impossible — and `ε₅ = 0`. In the
first case

```
(2u³ + 4.2u⁴)(1 + …) + (42u³ − 11.9u⁴)/(1 − 4u) ≤ 44u³ + 176u⁴
```

with room to spare (`≈ 44u³ + 160.3u⁴`), the `u⁴` slack being far less tight
than Algorithm 9's.

## Rocq map (`code/coq/ThreeProdFast.v`)

| paper object | Rocq |
|---|---|
| Algorithm 10 | `ThreeProdFast` |
| result is TW | `ThreeProdFast_isTW` (**proved**) |
| error `44u³+176u⁴` | `ThreeProdFast_error` (**proved**) |

What is reused from `ThreeProd.v` (all `Qed`, generalised over
`p Hp2 Hp6 choice choice_sym` once the section is closed — applied with `@`;
the local `vecSum`/`vseb`/… notations are re-declared in `ThreeProdFast.v`):

- **WLOG reduction**: `tw_norm`, `tw_normP`, `isTW_normalize`, `isTW_scale`,
  `isTW_opp`, `isTW_zero_lead`, `error_scale_transfer`, and the generic
  scale/sign machinery (`round_scale`, `vecSum_scale`, `vsebK_scale`,
  `TwoProd_scale` and their `_opp` twins, `vsebAux_zeros`). The five wrappers
  `ThreeProdFast_scale` / `_opp` / `_opp_r` / `_0l` / `_0r` are re-proved by the
  same scripts as Algorithm 9's (only the last VecSum line changes: four inputs
  and the extra `s3 = RN(c + z3)` rounding).
- **§6.1 term bounds** (identical terms): `z00p_lb`/`z00p_ub`, `z00m_bound`,
  `z00m_imul`, `z01p_bound`/`z10p_bound`, `z01m_bound`/`z10m_bound`, `b2_bound`,
  `c_bound`, `z31_bound`/`z32_bound`, `z3_bound`, `s3_bound`, `x1y1_bound`,
  `x0y2_bound`/`x2y0_bound`.
- **part 1**: `inner_head_Fnonoverlap` (the four-case `I`-set study — the single
  most expensive lemma of Theorem 7, reused *verbatim*: its `s3` is
  `dwh (TwoSum c z3)`, which is Algorithm 10's `RN(c + z3)` by `TwoSum_hi`),
  `vseb_star` (`e₁ ≠ 0` half, generic in the list), `Pnonoverlap_isTW3`,
  `vseb_Pnonoverlap` (Thm 2), `format_vecSum` / `format_vseb`, and the NEW
  shared `vseb_head3_dom` (the generic VSEB head-domination read-off, factored
  out of `vseb_head3_e1zero` so both algorithms use it).
- **part 2**: `eps0_bound` … `eps4_bound`, `eps04_sum`, `eps5_bound`
  (Thm 3 truncation at `k = 3`), `xy_ge`, `eps5_zero_all_big`,
  `eps5nz_forces_small`, and the assembly pattern `error_assembly` /
  `error_assembly_eps5` (re-calibrated to `44u³ + 176u⁴`).

New work specific to Algorithm 10 — part 1, **done**:

1. `ThreeProdFast_scale` / `_opp` / `_opp_r` / `_0l` / `_0r` (the WLOG
   plumbing).
2. `vsebFast_head3_e1zero` — the `e₁ = 0` half of the star identity on the
   FOUR-limb `e`; same script as `vseb_head3_e1zero` with one running-sum step
   fewer (`|s₃| ≤ 20u²`, `|RN(b₁+s₃)| ≤ 32u²`, `|RN(b₀+…)| ≤ 11u`).
3. `ThreeProdFast_norm_eq` (star identity), `ThreeProdFast_isTW_norm`,
   `ThreeProdFast_isTW`.

Part 2 (the error bound), **done**:

4. `epsp4_bound` : `|(c + z₃) − s₃| ≤ 16u³` (from `c_bound`, `z3_bound` and
   `round_err_le`, via the new `pow_5m2p`/`pow_5m3p`).
5. `sumR_eF_decomp` — the error identity on the four-limb VecSum: Algorithm 9's
   `sumR_e_decomp` plus the single extra term `c + z₃ − s₃`.
6. `eps04p_sum` (`44u³ − 11.9u⁴`), `error_assembly_fast` (`44u³ + 176u⁴`),
   `error_assembly_eps5_fast` (numerator `42u³ − 11.9u⁴` plus the full `ε₅`,
   splitting the budget as `2u³+4.2u⁴` for `ε₅` and `42u³+171.8u⁴` for the
   rest), `eps5nzF_forces_small`, `eps5nzF_numerator` and `eps5F_zero_all_big`
   (the four-limb grid argument: `s₃ = RN(c + z₃)` inherits the `8u³` grid from
   `c` and `z₃`).
