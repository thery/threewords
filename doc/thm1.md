# Theorem 1 and Corollary 1 (VecSum), text version

Companion to `doc/thm6.md`. Source: `doc/paper3.pdf` (Fabiano, Muller, Picot,
*Algorithms for triple-word arithmetic*, IEEE TC 2019), as transcribed in the
formalisation (`code/coq/VecSum.v`) and cross-checked against the pen-and-paper
statement. **Setting: FLX** — radix 2, precision `p`, unbounded exponent (the
paper's own model, no `emin`). `u = 2^{-p}`, `ufp x = 2^{mag(x)-1}`,
`uls x` = weight of the rightmost nonzero bit of `x`.

Everything here is the input analysis of `VecSum` (Algorithm 4); the output
side (VSEB, Theorem 2, and the assembled Theorem 6) is in `doc/thm6.md`.

## Definitions

- **F-nonoverlapping (Def. 2, Fabiano)**: `(xᵢ)` with `∀i, |xᵢ₊₁| ≤ ½ uls(xᵢ)`.
- **wIZ / Def. 3** (what the formalisation calls `Fnonoverlap`): F-nonoverlap
  *with interleaving zeros* — delete the zeros of the sequence, then require
  plain F-nonoverlap on the survivors. (`VecSum` can emit interior zeros, so
  this is the honest statement.)

## Theorem 1 — VecSum is F-nonoverlapping (under the representable hypothesis)

> Let `(xᵢ)_{0≤i<n}` be floats admitting exponents `(kᵢ)` with
>   - **repr**: each `xᵢ = Mᵢ · 2^{kᵢ-p+1}` with `|Mᵢ| < 2^p`
>     (i.e. `xᵢ` lies on the `2^{kᵢ-p+1}` grid and `|xᵢ| ≤ 2·2^{kᵢ}`);
>   - **gap**: `k_{i+1} + 1 ≤ kᵢ` for every interior step (`i+2 < n`), and
>     `k_{i+1} ≤ kᵢ` for the last pair (`i+2 = n`).
>
> Then `VecSum(x₀,…,x_{n-1})` is F-nonoverlapping and has the same exact sum.

Formalised as `Thm1_hyp` + `vecSum_sep` / `vecSum_Fnonoverlap_core`
(**proved, Qed, axiom-clean**). Supporting quantitative bounds (used in the
proof and reused by Theorem 6):
  - **run bound** `VecSum_run_bound`: `|s_i| ≤ (2 - 2u)·2^{kᵢ}` where
    `s_i = (vecSumAux (drop i l)).2` is the running sum from position `i`;
  - **error bound** `vecSum_err_bound`: the emitted error `|eᵢ| ≤ 2u·2^{k_{i-1}}`.

The proof is a contradiction: if some later `|e_j|` exceeded `½ uls(e_i)`, an
input `x_w` (`w < t`) would have to sit off the `2^{g+1}` grid
(`vecSumAux_split` + `vecSumAux_imul`), and the gap on `k` makes that
impossible.

## Corollary 1 — VecSum on overlapping inputs (the reduction)

The inputs one actually has (magnitude-sorted floats with a bounded overlap)
do **not** directly satisfy Theorem 1's strict `gap`: two equal-magnitude
inputs give `k_{i+1} = kᵢ`, a plateau. Corollary 1 is the paper's **reduction**:
bump the exponent map to recover the strict gap, then apply Theorem 1.

### Hypothesis (`Cor1_hyp`)

Floats `(xᵢ)`, all format, with a designated *overlap set* `I ⊆ {indices}`
(the positions where an overlap is tolerated), such that:
  - **`I` is isolated**: `i ∈ I ⇒ 0 < i`, `i+1 < n`, and `i+1 ∉ I`
    (no two overlaps in a row);
  - **off `I`** (`i+1 < n`, `i ∉ I`): `2·ufp(x_{i+1}) ≤ ufp(xᵢ)`
    (a genuine one-exponent drop);
  - **on `I`** (`i ∈ I`): the *overlap bound*
    `ufp(x_{i+1}) ≤ 2^{p-2}·uls(xᵢ)`   ← **this is the key paper hypothesis**,
    and the two-back bound `4·ufp(x_{i+1}) ≤ ufp(x_{i-1})`.

**Note (why the overlap bound is not free).** `sorted_mag` + `pairwise_ulp`
alone do **not** imply the overlap bound. Counterexample at `p=4`:
`[15; 15; 0.5]` — `15` is odd, so no strict exponent map exists. Dropping the
overlap bound makes the statement false: `CEThm6`'s witness
`[15; 15; 15/16; 15/16]` satisfies `sorted_mag` + `pairwise_ulp` yet
`VecSum` of it, `[32; -1; 7/8; 0]`, is **not** F-nonoverlapping. So the overlap
bound is load-bearing, not decoration.

### The bump (`Cor1_bump_Thm1_hyp`)

Set `eₓ(i) = cexp(xᵢ) + p - 1 = mag(xᵢ) - 1` (so `ufp(xᵢ) = 2^{eₓ(i)}`), and

>   `kᵢ = eₓ(i)`                     off `I`,
>   `kᵢ = max(eₓ(i), eₓ(i+1) + 1)`   on `I`.

Then `Thm1_hyp k l` holds:
  - **repr off `I`**: `xᵢ` is a multiple of `2^{cexp(xᵢ)} = 2^{kᵢ-p+1}`
    (`format_imul_cexp`), mantissa `< 2^p`.
  - **repr on `I`**: when the `max` is `eₓ(i+1)+1`, the overlap bound
    `ufp(x_{i+1}) ≤ 2^{p-2} uls(xᵢ)` gives `2^{cexp(x_{i+1})+1} ∣ xᵢ`
    (`uls_imul` + `is_imul_pow_le`), i.e. `2^{kᵢ-p+1} ∣ xᵢ`; mantissa `< 2^p`
    from `|xᵢ| ≤ 2·2^{kᵢ}`.
  - **gap** (four cases on `i, i+1 ∈ I?`): off/off gives `k_{i+1}+1 ≤ kᵢ` from
    the one-exponent drop; the `on i+1` case uses the two-back bound
    `eₓ(i+2)+2 ≤ eₓ(i)` and `Z.max_lub`; `i ∈ I` alone bumps up so the strict
    gap survives.
  - **last pair** weak: `i+1` cannot be in `I` (it would need `i+2 < n`), so
    `k_{i+1} = eₓ(i+1) ≤ kᵢ`.

Then Corollary 1 is `Cor1_hyp l → Fnonoverlap (VecSum l) ∧ sumR (VecSum l) =
sumR l`, by feeding the bumped `k` to Theorem 1.

### FLX vs the old FLT transcription

Old `main` proved this under FLT and paid for it:
`Cor1_hyp` there also demanded **normality** `emin + p ≤ mag(xᵢ)` and
**nonzero** entries, and the bump proof carried `cexp = mag - p` via
`FLT_exp = max(·, emin)` (`Z.max_l` + the normality hypothesis) and a
`cexp_ge_emin` side condition on `repr`. Under FLX all of that **disappears**:
`cexp = mag - p` definitionally, and `repr` has no exponent lower bound. So the
FLX port of the bump is the same argument minus the `emin` bookkeeping.
