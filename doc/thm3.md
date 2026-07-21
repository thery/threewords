# Theorem 3 — relative error of truncating a P-nonoverlapping sequence

Companion doc. Source: `doc/paper3.pdf` §2.2, p. 4. Setting FLX, `u = 2^{-p}`,
`ufp x = 2^{mag(x)-1}`.

## Statement

> **Theorem 3.** The relative error caused by keeping only the first `k` terms
> of a P-nonoverlapping sequence is bounded by `2u^k + 4.2·u^{k+1}`, provided
> that `p ≥ 6`.

For a P-nonoverlapping `(y₀,…,y_{n-1})`, keeping the first `k` terms means
returning `y₀+…+y_{k-1}`; the error is the dropped tail `y_k+…+y_{n-1}`, and the
claim is `|y_k+…+y_{n-1}| ≤ (2u^k + 4.2u^{k+1})·|y₀+…+y_{n-1}|`.

## Proof (verbatim, p. 4)

> We have by P-nonoverlapping:
>   `ufp(y_k) ≤ u·ufp(y_{k-1}) ≤ … ≤ u^k·ufp(y₀)`,
> hence
>   `|y_k| + … + |y_{n-1}| ≤ (2−2u)(u^k + u^{k+1} + … + u^n)·ufp(y₀)`,
> hence `|y_k| + … + |y_{n-1}| ≤ 2u^k·ufp(y₀)`.
> We also have,
>   `|y₀ + … + y_{n-1}| ≥ |y₀| − |y₁ + … + y_{n-1}| ≥ (1−2u)·ufp(y₀)`.
> Therefore,
>   `|y_k + … + y_{n-1}| ≤ (2u^k/(1−2u))·|y₀ + … + y_{n-1}|`,
> which implies the theorem. ∎

The last step needs `2u^k/(1−2u) ≤ 2u^k + 4.2u^{k+1}`, i.e. (dividing by
`u^k>0`) `2/(1−2u) ≤ 2 + 4.2u`, i.e. `2 ≤ (2+4.2u)(1−2u) = 2 + 0.2u − 8.4u²`,
i.e. `u ≤ 0.2/8.4 = 1/42`. `p ≥ 6` gives `u ≤ 1/64 ≤ 1/42`.

## Formalisation plan (`Nonoverlap.v`, reusable lemmas)

The paper's four steps, each a standalone lemma about a P-nonoverlapping `l`
(`ufp₀ := ufp (nth 0 l 0)`):

1. **`ufp_decay_pow`**: `nth 0 l k ≠ 0 → ufp (nth 0 l k) ≤ u^k · ufp₀`.
   Induction on `k`; step is `ufp_ulp_step` (`ufp(y_{k+1}) ≤ u ufp(y_k)`) with
   `nth_step_zero` giving `nth l k ≠ 0` from `nth l (k+1) ≠ 0`. (This is the
   paper's `ufp(y_k) ≤ u·ufp(y_{k-1}) ≤ … ≤ u^k·ufp(y₀)`.)
2. **`sumR_drop_ufp_bound`**: `|sumR (drop k l)| ≤ 2·u^k · ufp₀`.
   If `nth l k = 0`, `small_head_zero` makes `sumR (drop k l) = 0`. Else
   `sumR_ufp_bound` on `drop k l` gives `≤ 2 ufp(nth l k)`, then step 1.
   (`sumR_ufp_bound` IS the paper's `(2−2u)(u^k+…)ufp ≤ 2u^k ufp`, already
   proved by the geometric argument.)
3. **`sumR_ufp_lower`**: `nth 0 l 0 ≠ 0 → (1−2u)·ufp₀ ≤ |sumR l|`.
   `|sumR l| ≥ |y₀| − |sumR (drop 1 l)| ≥ ufp₀ − 2u·ufp₀`, via `ufp_le_abs`
   and step 2 at `k = 1`.
4. **`Pnonoverlap_truncate_error`** (= Theorem 3): from 2 and 3,
   `|sumR (drop k l)| ≤ (2u^k + 4.2u^{k+1})·|sumR l|`, under `u ≤ /64`
   (the `p ≥ 6` hypothesis, passed explicitly to keep `Nonoverlap.v` generic).

Then the existing `TWSum_error`'s hand-rolled `k=3` block (the `d0/d1/d2`
decay + `Hlow` + the `2u³ ≤ (2u³+4.2u⁴)(1−2u)` scalar step) is replaced by
`Pnonoverlap_truncate_error` at `k = 3`.
