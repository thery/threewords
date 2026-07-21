# Theorem 6 of `paper3.pdf` — everything the paper says about it

Transcribed from `doc/paper3.pdf` (Fabiano, Muller, Picot, *Algorithms for
Triple-Word Arithmetic*, IEEE Trans. Computers, DOI 10.1109/TC.2019.2918451),
Section 5.1, page 5–6.

**Read this first, not the PDF.**  The PDF is two-column and `pdftotext`
interleaves the columns, so the theorem, its sketch and the counterexample come
out shuffled together with unrelated text.  This file is the de-shuffled
transcription; it exists so nobody has to re-extract it again.

> **The published paper does not contain a proof of Theorem 6.**  It gives the
> statement, a five-line sketch, and an explicit disclaimer that the proof is
> omitted for space (§1–§3 below).  `doc/paper.pdf` is a different
> (companion/overview) document and has no proof of it either.
>
> **BUT `doc/old-triplewors.pdf` does.**  In that earlier draft the same result
> is **Theorem 7**, and it carries the full detailed proof that the published
> version cut for space.  It is transcribed in **§5** below — that is the one
> to work from.  §1–§3 are kept because the published statement is the one the
> development targets, and because the two differ in ways that matter (§5.6).

---

## 0. Notation (paper §1, verbatim)

For a real `x ≠ 0`:

- `ufp(x) = 2^⌊log2 |x|⌋` — for an FP number, the weight of its **most**
  significant bit;
- `ulp(x) = ufp(x) · 2^(−p+1)` — the weight of its **least** significant bit;
- `uls(x)` = the largest power of 2 dividing `x`, i.e. the largest `2^k`
  (`k ∈ ℤ`) such that `x/2^k` is an integer — the weight of its **rightmost
  nonzero** bit.

Example (`p = 53`): `x = −1.01101₂ × 2^364` gives `ufp(x) = 2^364`,
`ulp(x) = 2^312`, `uls(x) = 2^359`.  Note `ulp(x) ≤ uls(x) ≤ |x|`.

`u = 2^(−p) = ½ ulp(1)`.  `RN` is round-to-nearest **ties-to-even**.

- **Definition 1.** `(xᵢ)` is *P-nonoverlapping* (Priest) when `∀i, |xᵢ₊₁| < ulp(xᵢ)`.
- **Definition 2.** `(xᵢ)` is *F-nonoverlapping* (Fabiano) when `∀i, |xᵢ₊₁| ≤ ½ uls(xᵢ)`.
- **Definition 3.** For any notion of nonoverlapping, `(xᵢ)` is *nonoverlapping
  wIZ* (with possible interleaving zeros) when there is a set `I₀` with
  `∀i ∈ I₀, xᵢ = 0` and `(xᵢ)_{i ∉ I₀}` nonoverlapping.

### The two algorithms and where `sᵢ` / `eᵢ` / `ϵᵢ` come from

The sketch below talks about `sᵢ` and `eᵢ`; they are named in **Algorithm 4**
(`VecSum`), which runs **right to left** (from the smallest term up):

```
Algorithm 4 – VecSum(x₀, …, x_{n−1}).           (6n−6 operations)
Ensure: e₀ + ⋯ + e_{n−1} = x₀ + ⋯ + x_{n−1}
  s_{n−1} ← x_{n−1}
  for i = n−2 downto 0 do
    sᵢ, e_{i+1} ← 2Sum(xᵢ, s_{i+1})
  end for
  e₀ ← s₀
  return (e₀, e₁, …, e_{n−1})
```

So `sᵢ` is the **running high word** (the tail sum from `i` on) and `e_{i+1}` is
the **error** dropped at step `i`.  `ϵᵢ` below is VSEB's accumulator, from
**Algorithm 5**, which runs **left to right** (from the largest term down):

```
Algorithm 5 – VSEB(e₀, …, e_{n−1}).      (6n−6 operations & n−2 tests)
Ensure: y₀ + ⋯ + y_{n−1} = e₀ + ⋯ + e_{n−1}
  j ← 0
  ϵ₀ ← e₀
  for i = 0 to n−3 do
    (rᵢ, ϵt_{i+1}) ← 2Sum(ϵᵢ, e_{i+1})
    if ϵt_{i+1} ≠ 0 then
      y_j ← rᵢ ; ϵ_{i+1} ← ϵt_{i+1} ; incr j
    else
      ϵ_{i+1} ← rᵢ
    end if
  end for
  y_j, y_{j+1} ← 2Sum(ϵ_{n−2}, e_{n−1})
  y_{j+2}, …, y_{n−1} ← 0
  return (y₀, y₁, …, y_{n−1})
```

---

## 1. Theorem 6 (verbatim)

> **Theorem 6.** Let `x₀, …, x₅` be FP numbers such that
>
> > `∀i, |x_{i+1}| ≤ |xᵢ|` and `∀i, |x_{i+2}| < ulp(xᵢ)`.
>
> Then `VSEB(VecSum(x₀, …, x₅))` is P-nonoverlapping, provided that `p ≥ 4`.

Note the conclusion is about **`VSEB ∘ VecSum`**, *not* about `VecSum` alone.
This is the whole point: the raw `VecSum(x₀,…,x₅)` need **not** be
F-nonoverlapping, and an earlier version of this development stated it that way
and was **false** — see `code/coq/CEThm6.v` for the machine-checked refutation
(`l = [15; 15; 15/16; 15/16]` at `p = 4`).  VSEB *repairs* the overlap.

## 2. Proof sketch (verbatim — this is the entire "proof")

> *Sketch of the proof:*  For space constraints, the proof of Theorem 6 is not
> detailed.  The main steps are:
>
> - prove by induction that `|sᵢ| ≤ 2 ufp(x_{i−1})` and `|sᵢ| ≤ 4 ufp(xᵢ)`;
> - if `eᵢ > ½ uls(e_j)` for some `j < i`, deduce some conditions on `i` and the
>   nearby terms in various cases;
> - conclude with a case study: `i ≤ 3` and `eᵢ > ½ uls(e_j)`; `i ≥ 4` and
>   `eᵢ > ½ uls(e_j)`; or `0 < eᵢ ≤ ½ uls(e_j)`.

That is the end of the paper's treatment.  There is no more.

## 3. Why `≤ 6` inputs is essential (verbatim)

> Interestingly enough, we can notice that Theorem 6 may not hold for more than
> 6 floating-point inputs.  Indeed, for 7 inputs, we can consider
>
> > `(xᵢ) = 1−u, −1+2u, −u+u², u−u², u²−u³, u²−u³, u³−u⁴`
>
> which gives `(eᵢ) = u, u², u², −u³, −u⁴`, and finally
>
> > `(yᵢ) = u, 2u², −u³, −u⁴`
>
> with `2u² = ulp(u)`.
>
> This is why it is reasonable to use the notion of P-nonoverlapping for TW
> numbers only, but not for general expansions, for which Algorithm 8 preserves
> ulp-nonoverlapping only [25, page 90].

Two things worth extracting from this example:

- it is a genuine counterexample at `n = 7`, so any proof **must** consume the
  `≤ 6` bound somewhere — a proof that never uses it is wrong;
- its `(eᵢ) = u, u², u², …` is itself **not** F-nonoverlapping (`u² > ½ uls(u²)`),
  which is the paper's own evidence, independent of `CEThm6.v`, that the
  intermediate `VecSum` output is not F-nonoverlapping in general.

---

## 4. What this leaves us to reconstruct

> **Superseded by §5.**  This section was written when the five-line sketch was
> believed to be all that existed.  The draft's full proof (§5) replaces the
> guesswork here.  Kept for the status table and the deviation list, both of
> which §5 confirms.

Mapping the sketch onto the development (`p`/`emin`-generic, `l = x₀…x₅`):

| Sketch step | Status in the Rocq development |
| --- | --- |
| `\|sᵢ\| ≤ 2 ufp(x_{i−1})`, `\|sᵢ\| ≤ 4 ufp(xᵢ)` | **Qed** — `VecSum.vecSum_run_ufp` |
| (per-step error bound, used by the case study) | **Qed** — `VecSum.vecSum_err_ufp` (`\|e_{i+1}\| ≤ 2u ufp(xᵢ)`) |
| ties-to-even boundary tie needed by step 1 | **Qed** — `VecSum.RN_midpoint_even` |
| "deduce conditions on `i`" + the three-way case study | **open** — `TWSum.vecSum_vseb_Pnonoverlap`, the project's only admit |

Deviations from the paper that the development already had to make, and why —
worth knowing before trusting the sketch's phrasing:

- **Ties-to-even is required, not optional.**  The paper says `RN` and means
  ties-to-even.  Step 1's same-binade case genuinely fails for a general
  symmetric tie-breaking rule: it reduces to `RN(x_j + s_{j+1}) ≤ 2 ufp(x_{j−1})`
  whose worst case is the exact midpoint `x_j + s_{j+1} = 2^(mag x_j) + ulp(x_j)`,
  which ties-away-from-zero rounds *up*, breaking the bound.  Hence the explicit
  `ties_to_even choice` hypothesis.
- **No underflow.**  The paper assumes an unlimited exponent range.  Under FLT
  the statement needs nonzero terms to be normal (`emin + p ≤ mag z`); see the
  `paper-no-underflow` note.
- **`eᵢ > ½ uls(e_j)` is sloppy in the paper** — `eᵢ` there stands for `|eᵢ|`
  (an unsigned comparison against a positive quantity), as the third bullet's
  `0 < eᵢ ≤ ½ uls(e_j)` makes clear.
- **The sketch is stated for a zero-free reading** (Definition 3, "wIZ").  Zeros
  in the `VecSum` output are real (`VecSum[−½; ½; 2^−55] = [0; 0; 2^−55]`) and
  must be handled separately.

---

# 5. THE DETAILED PROOF — `old-triplewors.pdf`, Theorem 7

The earlier draft `doc/old-triplewors.pdf` (§5.1, pages 5–6) states the same
result as **Theorem 7** and *proves it in full*.  Transcribed below, verbatim
in content, with the two columns de-interleaved and the layout regularised.
Bracketed italics are mine, not the source.

**Theorem 7.** Let `x₀, …, x₅` be FP such that `∀i, |x_{i+1}| ≤ |xᵢ|` and
`∀i, |x_{i+2}| < ulp(xᵢ)`.  Then `VSEB ∘ VecSum(x₀, …, x₅)` is
P-nonoverlapping, provided that `p ≥ 4`.

*(Remark 6 there is the same 7-input counterexample as §3 above.)*

## 5.1 Step ★1 — the running-sum bounds (= published bullet 1)

> *Proof:* ★ First, let us prove by descending induction that
> `|sᵢ| ≤ 2 ufp(x_{i−1})` and `|sᵢ| ≤ 4 ufp(xᵢ)`.
>
> - The initialization is clear.
> - We have `|s_{i+1}| ≤ 4 ufp(x_{i+1}) ≤ 4u ufp(x_{i−1})` and
>   `|xᵢ| ≤ (2−2u) ufp(x_{i−1})` so `|s_{i+1}| + |xᵢ| ≤ (2+2u) ufp(x_{i−1})` so
>   **after rounding (ties-to-even)** `|sᵢ| ≤ 2 ufp(x_{i−1})`.
> - We have `|s_{i+1}| ≤ 2 ufp(xᵢ)` and `|xᵢ| ≤ 2 ufp(xᵢ)` so
>   `|s_{i+1}| + |xᵢ| ≤ 4 ufp(xᵢ)` so `|sᵢ| ≤ 4 ufp(xᵢ)`.
>
> This gives the result by induction.
> What is more, we still have `|eᵢ| ≤ 2u ufp(x_{i−1})`.

*Note: the draft says "ties-to-even" here explicitly.  This is independent
confirmation that step 1 needs it — the published version never says so.  Our
`vecSum_run_ufp` + `RN_midpoint_even` are exactly this step, already Qed.*

## 5.2 Step ★2 — the conditions forced by a violation (= published bullet 2)

> ★ Let us suppose that `uls(e_j) = u` and `eᵢ ≥ 5/8 u` for some `j < i`.
> We are trying to find some conditions that will be used in the next steps.
>
> `|eᵢ| ≤ ½ ulp(s_{i−1})` gives `|s_{i−1}| ≥ 1`.
> Since `2u` divides `s_{i−1}` but not `e_j`, `∃i' ≤ i−2, ¬(2u | x_{i'})` so
> `|x_{i'}| < 1` so by isotony `|x_{i−2}| < 1`.
> This gives `|xᵢ| < u` so `|sᵢ| ≤ 2u`, and `|x_{i−1}| ≤ 1−u` so
> `|sᵢ| + |x_{i−1}| ≤ 1+u`.
> On the other hand, `|s_{i−1} + eᵢ| ≥ 1 + 5/8 u`.
> Being so close to equality implies (by an easy case study) `s_{i−1} = 1`,
> `x_{i−1} = 1−u` and `sᵢ = u + eᵢ`.
> In particular, `2u² | eᵢ`.

**At the right of `i`.**

> We saw that `x_{i−1} < 1`, so `eᵢ ≤ u`.
> What is more, `|xᵢ| < u`, so `∀i' ≥ i+1, |e_{i'}| ≤ u²`.
> We can have additional information in two cases:
>
> - **Case `eᵢ = u`.**  Then we saw that `sᵢ = 2u` and `xᵢ ≤ u−u²`.  So we must
>   have `s_{i+1} ≥ u` with `x_{i+1} < u`, so `s_{i+2} ≠ 0`.
>   **In particular, `i ≤ 3`.**
> - **Case `eᵢ = u − 2u²`.**  Then we saw `sᵢ = 2u − 2u²` and `xᵢ ≤ u−u²`.  So we
>   must have `s_{i+1} ≥ u−u²` with `x_{i+1} ≤ u−u²`, so either there is no more
>   non-zero `e_{i'}` or `i ≤ 3`.

**At the left of `i`.**

> We saw that `x_{i−1} = 1−u` and `x_{i−2} < 1`, so `|x_{i−2}| = 1−u`.
>
> - **Case `x_{i−2} = −1+u`.**  Then `e_{i−1} = 0` and `s_{i−2} = u`.
>   Afterwards, if `i ≥ 3`, then `|x_{i−3}| ≥ ½ u^{−1}` so `e_{i−2} = u` and
>   `s_{i−3} = x_{i−3}`.
> - **Case `x_{i−2} = 1−u`.**  Then `e_{i−1} = −u` and `s_{i−2} = 2`.
>   Afterwards, `s_{i−2}` and all the `x_{i'}`, `i' ≤ i−3`, are divisible by 1,
>   so it is the case for the `e_{i'}`, `i' ≤ i−2`.

## 5.3 Step ★3 — the VSEB part (= published bullet 3)

> ★ Finally, let us analyze the VSEB part.
> We consider `i₀` such that `y_j = r_{i₀−1}`, so `ϵ_{i₀} ≠ 0`.
> Let `i₁` be the index of the first `eᵢ` after `e_{i₀}` that is non-zero.
> In particular, `1 ≤ i₀ < i₁` so `i₁ ≥ 2`.
> We suppose WLOG that `uls(e_{i₀}) = u`.
> Then `|ϵ_{i₀}| ≥ u`, and `ulp(y_j) ≥ 2|ϵ_{i₀}| ≥ 2u`.

**★ Case `i₁ ≤ 3` and `e_{i₁} ≥ 5/8 u`.**

> - **Case `x_{i₁−2} = −1+u`.**  Then `e_{i₁−1} = 0` so `1 ≤ i₀ < i₁−1`, which
>   gives `i₁ = 3`.  Thus `|y_j| = |s₀| ≥ ½ u^{−1}` so `ulp(y_j) ≥ 1`, and
>   clearly `|y_{j+1}| < 1`.
> - **Case `x_{i₁−2} = 1−u`.**  Then `e_{i−1} = −u` and all the `eᵢ`, `i ≤ i₁−2`,
>   are divisible by 1.  Thus we must have `ϵ_{i₀} = −u`, so
>   `|ϵ_{i₀} + e_{i₁}| ≤ 3/8 u`.  What is more, from the previous results,
>   `|e_{i₁+1}|, …, |e₅| ≤ u²`.  Thus, because we are adding at most 3 of them,
>   `|y_{j+1}| < 2u`.

**★ Case `i₁ ≥ 4`** (so in particular there is no need to consider beyond
`r_{i₁}`) **and `e_{i₁} ≥ 5/8 u`.**

> From the previous results, either `|e_{i₁}| = u − 2u²` and this is the last
> non-zero `eᵢ`, or `|e_{i₁}| ≤ u − 4u²`.
> We have `|ϵ_{i₀}| + |e_{i₁}| ≤ |ϵ_{i₀}| + (u − 2u²) ≤ (2−2u)|ϵ_{i₀}|`, so
> `|r_{i₁−1}| ≤ (1−u) ulp(y_j)`.
>
> - **Case `|e_{i₁}| = u − 2u²`.**  Then `y_{j+1} = r_{i₁−1} < ulp(y_j)`.
> - **Case `|e_{i₁}| ≤ u − 4u²`.**  Then we have the stronger estimate
>   `|r_{i₁−1}| ≤ (1−2u) ulp(y_j)`.  What is more, from the previous results,
>   `|e_{i₁+1}| ≤ u² ≤ ½u ulp(y_j)`.  Thus, after rounding (ties-to-even),
>   `|r_{i₁}| ≤ (1−2u) ulp(y_j)`, so `|y_{j+1}| < ulp(y_j)`.

**★ Case `0 < e_{i₁} < 5/8 u`.**

> We have `|ϵ_{i₀}| + |e_{i₁}| ≤ |ϵ_{i₀}| + 5/8 u ≤ (1 + 5/8)|ϵ_{i₀}|, so
> `|r_{i₁−1}| ≤ 13/16 ulp(y_j)`.
>
> - **Case `|e_{i₁}| > ½u`.**  Similarly to what we saw before, we deduce that
>   `|x_{i₁−2}| < 1`, so `|x_{i₁}| < u` so `|e_{i₁+1}|, …, |e₅| ≤ u² ≤ u/2 ulp(y_j)`.
>   Thus, because we are adding at most 3 of them, `|y_{j+1}| ≤ 7/8 ulp(y_j)`
>   (**this part uses `p ≥ 4`, and ties-to-even for `p = 4`**).
> - **Case `|e_{i₁}| = ½u`.**  Then, thanks to ties-to-even, `2u | s_{i₁−1}`.
>   Similarly to what we saw before, we deduce that `|x_{i₁−2}| < 1`, so
>   `|x_{i₁}| < u` so `|e_{i₁+1}|, …, |e₅| ≤ u² ≤ u/2 ulp(y_j)`, and we conclude
>   like in the previous case.
> - **Case `½u > |e_{i₁}|` and `|e_{i₁}| ≠ ¼u`.**  Then `|r_{i₁−1}| ≤ 3/4 ulp(y_j)`.
>   What is more, `uls(e_{i₁}) ≤ 1/8 u` so `|e_{i₁+1}|, …, |e₅| ≤ 1/8 u ≤ 1/16 ulp(y_j)`,
>   and we conclude like in the previous cases.
> - **Case `|e_{i₁}| = ¼u`.**  Then `|r_{i₁−1}| ≤ 5/8 ulp(y_j)`.  What is more,
>   `uls(e_{i₁}) ≤ ¼u` so `|e_{i₁+1}|, …, |e₅| ≤ ¼u ≤ 1/8 ulp(y_j)`.  More
>   precisely, we can not have `|e₄| = |e₃|` (because this can not happen for
>   `i ≥ 4`) so `|e₅| ≤ uls(e₄) ≤ 1/16 ulp(y_j)`.  We conclude like in the
>   previous cases. ∎

## 5.4 What this proof actually needs

- **WLOG rescaling, twice**: `uls(e_j) = u` in ★2 and `uls(e_{i₀}) = u` in ★3.
  Every constant in the proof (`1`, `u`, `5/8 u`, `u²`, `1−u`, `½u^{−1}`) is
  stated *relative to that normalisation*.  This is why the proof is legible at
  all — and it is invalid under FLT with a real `emin`.  **FLX is what makes
  this proof transcribable**; under FLT it would have to be redone
  scaling-free with a symbolic carry, as `vecSum_sep` was.
- **Ties-to-even, three times**: in ★1 (`|sᵢ| ≤ 2 ufp(x_{i−1})`), in the
  `|e_{i₁}| ≤ u−4u²` case, and in `|e_{i₁}| = ½u` (to get `2u | s_{i₁−1}`).
  Confirms `ties_to_even` is the paper's own assumption, not our addition.
- **`p ≥ 4`**, explicitly, in the `|e_{i₁}| > ½u` case.
- **Divisibility** (`2u | s_{i−1}`, `2u² | eᵢ`, "divisible by 1"): our
  `vecSumAux_imul` / `is_imul` machinery.
- **`|eᵢ| ≤ ½ ulp(s_{i−1})`** — the 2Sum error bound against the *running sum*,
  which is what gives `|s_{i−1}| ≥ 1` after normalisation.
- **"at most 3 of them"** and **"no need to consider beyond `r_{i₁}`"** — this
  is where `≤ 6` inputs is paid for.

## 5.5 Where the ≤ 6 bound enters

Not in one place, but through the counting: `i₁ ≥ 2`, the split `i₁ ≤ 3` vs
`i₁ ≥ 4`, "we are adding at most 3 of them", and the final `|e₄| = |e₃|` /
`|e₅| ≤ uls(e₄)` argument, which reasons about indices 3, 4, 5 by name.  A
seventh input adds an index and the counting fails — consistent with the
7-input counterexample.

## 5.6 Discrepancies with the published sketch (READ THIS)

The published bullets are not a faithful compression of this proof:

1. **The threshold is `5/8 u`, not `½ uls(e_j)`.**  Published bullet 2 says
   "if `eᵢ > ½ uls(e_j)`"; the draft splits at `eᵢ ≥ 5/8 u` (with `uls(e_j) = u`,
   so `½ uls(e_j) = ½u ≠ 5/8 u`).  Following the published `½` threshold is
   therefore NOT following this proof, and the `½u` / `¼u` / `≠ ¼u` sub-cases
   in ★3 show the `½` boundary is a *separate* case split living *inside* the
   `< 5/8 u` branch.  The published sketch appears to have merged two different
   thresholds into one.
2. **The case study is on `i₁`, not `i`.**  Published bullet 3 says "`i ≤ 3`"
   / "`i ≥ 4`"; the draft's split is on `i₁` — *the index of the first non-zero
   `eᵢ` after `e_{i₀}`* — an index defined only in the VSEB part.  Bullet 2's
   `i` and bullet 3's `i₁` are different indices, and the sketch calls both `i`.
3. Bullet 3's third case is "`0 < eᵢ ≤ ½ uls(e_j)`"; the draft's is
   `0 < e_{i₁} < 5/8 u`.

So the published sketch is not just terse, it is **misleading**: two of its
three bullet-3 cases are stated with the wrong index and the wrong constant.
Work from §5, not from §2.

---

### Known blocker

`VSEB.vsebAux_Pnonoverlap` re-establishes its invariant through `Fnonoverlap` at
four points (`Fnonoverlap_TwoSum_merge`, `Fnonoverlap_head2`,
`Fnonoverlap_TwoSum_err`, `vsebAux_head_lt`), so it cannot be applied to the
`VecSum` output directly — that output is not F-nonoverlapping.  Closing the
admit needs either a weaker invariant that the `VecSum` output *does* satisfy and
VSEB still preserves (candidate: the factor-2 relaxation `|e_{i+1}| ≤ uls(eᵢ)`;
the `CEThm6` witness has `|7/8| ≤ uls(−1) = 1` but `> ½ uls(−1)`), or a direct
coupled `VecSum`+`VSEB` argument following the case study above.  Caution: under
the relaxed bound `|e| ≤ |ϵ|` becomes possible, so the `r = 0` branch is no
longer vacuous and leading cancellation must be handled.
