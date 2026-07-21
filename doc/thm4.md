# Theorem 4 — ToTW (three FP numbers → a triple word)

Companion to `doc/thm1.md` / `doc/thm6.md`. Source: `doc/paper3.pdf` §3, p. 5.
Setting FLX (radix 2, precision `p`, unbounded exponent), `u = 2^{-p}`.

## Algorithm 6 — ToTW(a, b, c)   (21 operations & 1 test)

> Ensure: `r̄` is a TW and `r̄ = a + b + c`.
>
> ```
> d₀, d₁       ← 2Sum(a, b)
> e₀, e₁, e₂   ← VecSum(d₀, d₁, c)
> r₀, r₁, r₂   ← VSEB(e₀, e₁, e₂)
> return (r₀, r₁, r₂)
> ```

VecSum on the 3-tuple `(d₀, d₁, c)` (recall VecSum runs from the last term):
  - `s₂ = c`;
  - `(s, e₂) = 2Sum(d₁, c)`,  `s := RN(d₁ + c)`  — the intermediate value;
  - `(s₀, e₁) = 2Sum(d₀, s)`;
  - `e₀ = s₀`.

## Theorem 4

> If `a, b, c` are FP numbers, then `ToTW(a, b, c)` is a TW, provided `p ≥ 4`.

## Proof (verbatim, p. 5)

> If `(e₀, e₁, e₂)` is F-nonoverlapping, then Theorem 2 concludes.
>
> First, `|e₁| ≤ ½ ulp(e₀)` gives `(e₀, e₁)` F-nonoverlapping. We denote
> `s := RN(d₁ + c)` the intermediate value in `VecSum(d₀, d₁, c)`.
>
> - **If `e₁ ≠ 0`**, we suppose without loss of generality that
>   `uls(e₁) = u`, and [that `(e₁,e₂)` is not F-nonoverlapping, i.e.
>   `|e₂| > ½u`]. Then `|e₂| ≤ ½ ulp(s)` so `s ≥ 1`, `2u ∣ s`; but `e₁` is not
>   divisible by `2u`, so `d₀ < 1`, so `|d₁| ≤ ½ ulp(d₀) ≤ ½u`. Furthermore,
>   `|c + d₁| ≥ 1 + ½u`. Thus `|c| ≥ (1 + ½u) − ½u = 1`, so
>   `ulp(c) ≥ 2u > 2|d₁|`, so `s = c` and `e₂ = d₁`, which is impossible since
>   `|e₂| > ½u ≥ |d₁|`. So `(e₁, e₂)` is F-nonoverlapping too.
> - **If `e₁ = 0`**, then the same reasoning works with `e₀` instead of `e₁`.
>   ∎

## Structural reading (for the formalisation)

Target: `isTW (ToTW a b c)`. Route:

1. **Reduce to Theorem 2.** `ToTW a b c = vseb (vecSum [d₀; d₁; c])` and
   `VSEB.vseb_Pnonoverlap` (Thm 2, already proved): if `[e₀;e₁;e₂]` is
   F-nonoverlapping wIZ and the size fits, its VSEB is P-nonoverlapping, i.e.
   the first three limbs form a TW. So the crux is:

     **`Fnonoverlap (vecSum [d₀; d₁; c])`**, where `(d₀,d₁) = 2Sum(a,b)`.

2. **`(e₀, e₁)` step is free**: `e₁ = dwl (2Sum(d₀, s))`, so
   `|e₁| ≤ ½ ulp(s₀) = ½ ulp(e₀)`, hence `|e₁| ≤ ½ uls(e₀)` — the first
   F-nonoverlap conjunct — from the generic 2Sum half-ulp bound.

3. **`(e₁, e₂)` step is the work**: show `|e₂| ≤ ½ uls(e₁)` (when `e₁ ≠ 0`;
   symmetric `e₀` when `e₁ = 0`). By contradiction, WLOG `uls(e₁) = u`, assume
   `|e₂| > ½u`. The chain (each step is a divisibility/ulp fact about the two
   2Sums):
     - `e₂ = dwl(2Sum(d₁,c))` ⟹ `|e₂| ≤ ½ ulp(s)`; with `|e₂| > ½u` ⟹
       `ulp(s) ≥ 2u` ⟹ `|s| ≥ 1` and `2u ∣ s`;
     - `e₁ = dwl(2Sum(d₀,s))` with `uls(e₁)=u` (odd multiple of `u`) and
       `2u ∣ s` ⟹ `2u ∤ d₀` ⟹ `|d₀| < 1` ⟹ `|d₁| ≤ ½ ulp(d₀) ≤ ½u`
       (`d₁ = dwl(2Sum(a,b))`);
     - then `|c| ≥ 1`, so `ulp(c) ≥ 2u > 2|d₁|`, Sterbenz/2Sum forces
       `s = RN(d₁+c) = c` and `e₂ = d₁` — contradicting `|e₂| > ½u ≥ |d₁|`.

**Machinery already in the tree**: `TwoSum.v` (2Sum: `dwl`, half-ulp bound
`magnitude_TwoSum`, error divisibility `TwoSum_err_imul`, `uls` facts),
`VecSum.v` (`vecSumAux` on 3 elements, `vecSum_run_*`), `VSEB.v`
(`vseb_Pnonoverlap` = Thm 2), `TWR.v` (`isTW`). No new algorithm needed — ToTW
is a composition of existing ones; the content is the `(e₁,e₂)` divisibility
argument (roughly the flavour of `Thm6`'s §5.2 pinning, but far shorter — one
3-element instance, not the ≤6 case study).

**`p ≥ 4`** enters through the constants (`½u`, `2u`, `|c| ≥ 1`), as usual.
