# Theorem 6 of `paper3.pdf` — everything the paper says about it

Transcribed from `doc/paper3.pdf` (Fabiano, Muller, Picot, *Algorithms for
Triple-Word Arithmetic*, IEEE Trans. Computers, DOI 10.1109/TC.2019.2918451),
Section 5.1, page 5–6.

**Read this first, not the PDF.**  The PDF is two-column and `pdftotext`
interleaves the columns, so the theorem, its sketch and the counterexample come
out shuffled together with unrelated text.  This file is the de-shuffled
transcription; it exists so nobody has to re-extract it again.

> **The headline: the paper does not contain a proof of Theorem 6.**  It gives
> the statement, a five-line sketch, and an explicit disclaimer that the proof
> is omitted for space.  Everything in §1–§3 below is all there is.  `doc/
> paper.pdf` is a different (companion/overview) document and has no proof of
> it either.  So closing `TWSum.vecSum_vseb_Pnonoverlap` means *reconstructing*
> a proof from the sketch, not transcribing one.

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
