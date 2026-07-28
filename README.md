# threewords

A [Rocq/Coq](https://rocq-prover.org) formalization of the correctly-rounded
computation of elementary functions in IEEE‑754 binary64 (double precision)
floating-point arithmetic, using *double-word* (and triple-word) representations.
The development formally verifies the algorithms and error bounds behind a
correctly-rounded `pow` function (`x^y`), together with its building blocks for
the logarithm and exponential (in `example/`), and a **complete** verification
of triple-word addition — including the paper's Theorem 6 — in `code/`.

Authors: Laurent Théry, Laurence Rideau — MIT License.

## Repository layout

```
doc/      research papers describing the algorithms and their proofs
example/  the elementary-function development
          coq/       the Rocq/Coq sources (algorithms, tables, supporting lemmas)
          TWFalcon/  upstream C reference implementation of the arithmetic
code/     triple-word arithmetic: a self-contained, complete verification
          coq/       the triple-word chain, up to TWSum and its error bound
          ocaml/     reference OCaml implementation of the addition
          TWFalcon/  C extraction of the addition + a "TW contains zeros" test
```

## `doc/`

| File | Contents |
|------|----------|
| `paper.pdf`  | Paper describing the formalized algorithms and error analysis. |
| `paper3.pdf` | Companion / extended paper for the development. |
| `Algorithms_for_Triple-Word_Arithmetic.pdf` | The **supplementary appendix** to `paper3.pdf`: the proofs of Theorems 9, 10 and 11 that the paper defers to. Terse, and its cross-references are broken (`Algorithm ??`), but it gives every constant. |
| `old-triplewors.pdf` | The long version of `paper3.pdf`, and an unfinished draft: it covers the sum, the products, the reciprocal (§8) and the quotient (§9), but its Section 10 was never written (the roadmap reads "Section 10 [???]"), so it says nothing about the square root. |

## `example/`

The Rocq/Coq sources live in `example/coq/`. Build with `cd example/coq && make`
(see the dependencies below); the build order is given in `_CoqProject`. The
upstream C reference implementation of the arithmetic is kept alongside in
`example/TWFalcon/` (see its `README.md`).

### Supporting libraries

| File | Contents |
|------|----------|
| `Nmore.v`   | Bit-manipulation helpers (`shrink`/`scalen`) that divide/multiply by powers of two while preserving low-order bits. |
| `Rmore.v`   | Additional lemmas on real numbers (division, abs, powers, sqrt, logarithm; includes irrationality of √2). |
| `Fmore.v`   | Floating-point facts in the FLX format: rounding, ULP, mantissa bounds, round-to-nearest. |
| `Rstruct.v` | Instantiates Rocq's reals as a MathComp archimedean real closed field, bridging the standard library and ssreflect/mathcomp. |
| `prelim.v`  | Preliminary FLT-format results: rounding, error bounds, fast-summation lemmas. |
| `MULTmore.v`| Lemmas on integer/floating-point multiplication and its interaction with rounding. |

### Fast2Sum

| File | Contents |
|------|----------|
| `Fast2Sum_robust.v`     | Robustness of the Fast2Sum algorithm: correct rounded sum and exact remainder within guaranteed error bounds. |
| `Fast2Sum_robust_flt.v` | Fast2Sum correctness and error bounds specialized to the FLT format. |

### Algorithms

| File | Contents |
|------|----------|
| `algoP1.v`     | Polynomial approximation `p1` of `ln(1 + z)` with verified error bounds. |
| `algoLog1.v`   | Double-precision logarithm `log1`: rounding-error bounds and correctness over the binary64 range. |
| `algoMul1.v`   | Double-word multiplication `mul1` (Lemma 5) used in the logarithm computation, with error bounds. |
| `algoQ1.v`     | Algorithm `q1`: degree-4 Horner polynomial approximation for the exponential, with error bounds. |
| `algoExp1.v`   | Double-word exponential `exp1` with rigorous error bounds. |
| `algoPhase1.v` | Phase 1 of the `x^y` algorithm; proves the result equals the correctly-rounded power when the phase succeeds (Theorem 1). |

### Precomputed tables

| File | Contents |
|------|----------|
| `tableINVERSE.v` | Reciprocal approximations for `[1/√2, √2)`, as reals and floats. |
| `tableLOGINV.v`  | Lookup table `LOGINV` of float pairs for the logarithm computation. |
| `tableT1.v`      | 64 float pairs approximating powers of two, with format/bound/accuracy proofs. |
| `tableT2.v`      | 64 float pairs approximating `2^(i/4096)` for `i = 0..63`, with correction terms. |

### Build files

`Makefile`, `Makefile.conf`, `Makefile.coq`, `Makefile.coq.conf`, `_CoqProject`
drive the Rocq/Coq build. `pow.pdf` is a generated document for the development.

## `code/`

A **complete** formalisation of the triple-word addition of `doc/paper3.pdf`
(Fabiano, Muller, Picot, *Algorithms for triple-word arithmetic*, IEEE TC 2019).
Both headline results — the sum of two triple words is a triple word, and its
relative error is at most `2u³ + 4.2u⁴` — are proved, with the only axioms
being classical logic, functional extensionality and the reals.

The whole development is carried out in Flocq's **FLX** format (unbounded
exponent range, `radix 2`, precision `p`), generic in `p ≥ 6` (binary64 is the instance `p = 53`). Working in FLX is what makes the central proof
(Theorem 6) tractable: it lets the argument rescale so that a rounding unit is
`u`, which is invalid once a real minimal exponent `emin` is present. See
`doc/thm6.md` for why, and for the full proof.

### Coverage of paper3

Which of `paper3.pdf`'s algorithms/theorems are formalised, each entry linked to
its Rocq definition/theorem. Full catalogue with lemma names in
`doc/paper3-map.md`; the proofs are written up in `doc/thm1.md`, `doc/thm3.md`,
`doc/thm4.md` and `doc/thm6.md`.

This table is generated by `scripts/gen_code_links.py`, which looks up each
identifier's current line so the links don't rot when the sources move:

```shell
python3 scripts/gen_code_links.py           # regenerate
python3 scripts/gen_code_links.py --check    # CI: fail if stale
```

Install `scripts/pre-commit` to regenerate it automatically whenever a commit
touches `code/coq/*.v`:

```shell
ln -s ../../scripts/pre-commit .git/hooks/pre-commit
```

<!-- CODE-LINKS:START -->

Links point at the Rocq definition/theorem. ✅ proved · 🚧 skeleton (definition + statements, proofs in progress) · ❌ not formalised.

| Alg | Paper object | Theorem | Status |
|----:|--------------|---------|:------:|
| 1 | Fast2Sum | [correctness](https://github.com/thery/threewords/blob/main/code/coq/Fast2Sum_robust_flx.v#L381) | ✅ |
| 2 | [2Sum](https://github.com/thery/threewords/blob/main/code/coq/TwoSum.v#L67) | [correctness](https://github.com/thery/threewords/blob/main/code/coq/TwoSum.v#L498) | ✅ |
| 3 | [2Prod](https://github.com/thery/threewords/blob/main/code/coq/MULTmore.v#L149) | [correctness](https://github.com/thery/threewords/blob/main/code/coq/MULTmore.v#L152) | ✅ |
| 4 | [VecSum](https://github.com/thery/threewords/blob/main/code/coq/VecSum.v#L110) | [Thm 1](https://github.com/thery/threewords/blob/main/code/coq/VecSum.v#L892) + [Cor 1](https://github.com/thery/threewords/blob/main/code/coq/VecSum.v#L1079) | ✅ |
| 5 | [VSEB](https://github.com/thery/threewords/blob/main/code/coq/VSEB.v#L118) | [Thm 2](https://github.com/thery/threewords/blob/main/code/coq/VSEB.v#L468) | ✅ |
|  | keep-first-`k` error | [Thm 3](https://github.com/thery/threewords/blob/main/code/coq/Nonoverlap.v#L792) | ✅ |
| 6 | [ToTW](https://github.com/thery/threewords/blob/main/code/coq/TWSum.v#L129) | [Thm 4](https://github.com/thery/threewords/blob/main/code/coq/TWSum.v#L314) | ✅ |
| 7 | [RoundTW](https://github.com/thery/threewords/blob/main/code/coq/TWSum.v#L364) | [Thm 5](https://github.com/thery/threewords/blob/main/code/coq/TWSum.v#L1031) | ✅ |
| 8 | [TWSum](https://github.com/thery/threewords/blob/main/code/coq/TWSum.v#L1209) | [Thm 6](https://github.com/thery/threewords/blob/main/code/coq/Thm6.v#L4365) + [error](https://github.com/thery/threewords/blob/main/code/coq/TWSum.v#L1326) | ✅ |
| 9 | [3Prod^acc (TW×TW)](https://github.com/thery/threewords/blob/main/code/coq/ThreeProd.v#L93) | [Thm 7](https://github.com/thery/threewords/blob/main/code/coq/ThreeProd.v#L4101) + [error](https://github.com/thery/threewords/blob/main/code/coq/ThreeProd.v#L4147) | ✅ |
| 10 | [3Prod^fast (TW×TW)](https://github.com/thery/threewords/blob/main/code/coq/ThreeProdFast.v#L106) | [isTW](https://github.com/thery/threewords/blob/main/code/coq/ThreeProdFast.v#L765) + [error](https://github.com/thery/threewords/blob/main/code/coq/ThreeProdFast.v#L1581) | ✅ |
| 11 | [3Prod^acc (DW×TW)](https://github.com/thery/threewords/blob/main/code/coq/ThreeProdDW.v#L118) | [isTW](https://github.com/thery/threewords/blob/main/code/coq/ThreeProdDW.v#L179) + [Thm 8](https://github.com/thery/threewords/blob/main/code/coq/ThreeProdDW.v#L1509) | ✅ |
| 12 | [3Prod^fast (DW×TW)](https://github.com/thery/threewords/blob/main/code/coq/ThreeProdDWFast.v#L113) | [isTW](https://github.com/thery/threewords/blob/main/code/coq/ThreeProdDWFast.v#L161) + [error](https://github.com/thery/threewords/blob/main/code/coq/ThreeProdDWFast.v#L984) | ✅ |
| 13 | [3Reci](https://github.com/thery/threewords/blob/main/code/coq/ThreeReci.v#L180) | [isTW](https://github.com/thery/threewords/blob/main/code/coq/ThreeReci.v#L1444) + [Thm 9 acc](https://github.com/thery/threewords/blob/main/code/coq/ThreeReci.v#L1700) + [Thm 9 fast](https://github.com/thery/threewords/blob/main/code/coq/ThreeReci.v#L1733) | ✅ |
| 14 | [3Div](https://github.com/thery/threewords/blob/main/code/coq/ThreeDiv.v#L118) | [isTW](https://github.com/thery/threewords/blob/main/code/coq/ThreeDiv.v#L169) + [Thm 10 acc](https://github.com/thery/threewords/blob/main/code/coq/ThreeDiv.v#L447) + [Thm 10 fast](https://github.com/thery/threewords/blob/main/code/coq/ThreeDiv.v#L488) | ✅ |
| 15 | [3SqRt](https://github.com/thery/threewords/blob/main/code/coq/ThreeSqRt.v#L268) | [isTW](https://github.com/thery/threewords/blob/main/code/coq/ThreeSqRt.v#L1544) + [Thm 11 acc](https://github.com/thery/threewords/blob/main/code/coq/ThreeSqRt.v#L1652) + [Thm 11 fast](https://github.com/thery/threewords/blob/main/code/coq/ThreeSqRt.v#L1661) | 🚧 |

<!-- CODE-LINKS:END -->

### `code/coq/`

Self-contained Rocq/Coq build: it bundles the triple-word files below together
with the supporting files it needs from `example/coq/` (`Nmore.v`, `Rmore.v`,
`Fmore.v`, `Rstruct.v`, `MULTmore.v`, `Fast2Sum_robust_flx.v`, `prelim.v`) plus
its own `Makefile` and `_CoqProject`, so it builds on its own with
`cd code/coq && make`. The build order (bottom of the stack first) is:

| File | Contents |
|------|----------|
| `Uls.v`       | `uls x`, the weight of the rightmost nonzero bit of a float, its 2‑adic valuation helpers, and the `is_imul` "multiple of a power of two" machinery. |
| `TwoSum.v`    | The error-free transforms 2Sum (Algorithm 2) and `Fast2Sum` (Algorithm 1): exactness, the format and half-ulp magnitude of the two words, and the divisibility of the error. |
| `Nonoverlap.v`| Separation predicates on sequences of floats: P-nonoverlapping (Priest, Def. 1), the pairwise-ulp order, magnitude-sortedness, and the list sum `sumR`. |
| `TWR.v`       | Triple-word numbers `twR` (Def. 5): a P-nonoverlapping triplet of floats, its projectors and real value. |
| `Merge.v`     | Merge two magnitude-sorted float sequences into one; preserves format, size and exact sum, and yields the pairwise-ulp order for two triple words. |
| `VecSum.v`    | Algorithm 4 (VecSum) and paper Theorem 1: its output is F-nonoverlapping. |
| `VSEB.v`      | Algorithm 5 (VecSumErrBranch) and paper Theorem 2: its output is P-nonoverlapping. |
| `Thm6.v`      | **Paper Theorem 6**: `VSEB (VecSum x₀ … x₅)` is P-nonoverlapping (`p ≥ 4`). The load-bearing result of the whole development; proved following `doc/thm6.md §5`. |
| `CEThm6.v`    | A machine-checked counterexample showing Theorem 6 *cannot* be strengthened: the raw `VecSum` output is not F-nonoverlapping (input `[15;15;15/16;15/16]` at `p = 4` gives `[32;-1;7/8;0]`). VSEB is what repairs the overlap. |
| `TWSum.v`     | Algorithm 8 (TWSum): the sum of two triple words. Its two correctness results — `TWSum_isTW` (the result is a triple word) and `TWSum_error` (relative error `≤ 2u³ + 4.2u⁴`). |
| `ThreeProd.v` | **Paper Theorem 7**: Algorithm 9 (3Prodᵃᶜᶜ₃,₃), the accurate product of two triple words. Its two correctness results — `ThreeProd_isTW` and `ThreeProd_error` (relative error `≤ 28u³ + 107u⁴`, `p ≥ 6`); see `doc/thm7.md` and `doc/thm7-eps5.md`. |
| `ThreeProdFast.v` | Algorithm 10 (3Prodᶠᵃˢᵗ₃,₃), the fast product of two triple words (8 operations and 1 test cheaper: the low word `e₄` of `s₃ = RN(c + z₃)` is dropped). Its two correctness results — `ThreeProdFast_isTW` (the result is a triple word) and `ThreeProdFast_error` (relative error `≤ 44u³ + 176u⁴`) — both proved, reusing Algorithm 9's Section-6.1 bounds, its four-case `inner_head_Fnonoverlap` and its `ε₀…ε₅` bounds verbatim; see `doc/alg10.md`. |
| `ThreeProdDW.v` | Algorithm 11 (3Prodᵃᶜᶜ₂,₃), the product of a **double** word by a triple word — Algorithm 9 with `x₂ = 0`. Its two correctness results — `ThreeProdDW_isTW` (Theorem 7 at `x₂ = 0`) and `ThreeProdDW_error` (**paper Theorem 8**, relative error `≤ 10.5u³ + 39u⁴`) — both proved; the paper omits the proof of Theorem 8, recovered in `doc/thm8.md`. |
| `ThreeProdDWFast.v` | Algorithm 12 (3Prodᶠᵃˢᵗ₂,₃), the fast product of a double word by a triple word — Algorithm 10 with `x₂ = 0`. Its two correctness results — `ThreeProdDWFast_isTW` (Algorithm 10 at `x₂ = 0`) and `ThreeProdDWFast_error` (relative error `≤ 18u³ + 75u⁴`) — both proved; the paper omits the error proof, recovered in `doc/alg12.md`. |
| `ThreeProdOne.v` | Algorithms 18 and 20 (3Prodᵒⁿᵉ), the product of a double word (Alg 18) resp. a **triple** word (Alg 20) by a triple word whose leading limb is exactly `1`. Its two correctness results — `ThreeProdOne_isTW` and `ThreeProdOne_error` (relative error `≤ u³ + 260u⁴`, an order of magnitude sharper than Theorem 8's `10.5u³`) — both proved; this is the second product of Algorithms 13 and 14, and the sharper bound is what makes Theorem 9's `11.5 = 10.5 + 1`. One deviation from the paper is necessary: its `Fast2Sum(b₁, z₀₁⁺)` is unjustified and loses `~32u³` on legal inputs (`doc/alg18_fast2sum_bug.py`); repaired at no operation cost by sorting the two arguments. |
| `ThreeReci.v` | Algorithm 13 (3Reci), the **reciprocal** of a triple word by one Newton-Raphson step (`p ≥ 10`), generic in the DW × TW product it calls: `ThreeReci` uses Algorithm 11 and `ThreeReciFast` Algorithm 12. Its four results — `ThreeReci_isTW`, `ThreeReciFast_isTW`, `ThreeReci_error` (**paper Theorem 9**, relative error `≤ 11.5u³ + 1830u⁴`) and `ThreeReciFast_error` (`≤ 19u³ + 1870u⁴`) — all proved; the paper's proof is in unavailable supplementary material, so the plan was recovered from `doc/old-triplewors.pdf` §8 in `doc/thm9.md`. The `u³` terms match the paper; our `u⁴` terms are larger, and honestly so. |
| `ThreeDiv.v` | Algorithm 14 (3Div), the **quotient** of two triple words (`p ≥ 10`) — Algorithm 13 with the dividend folded in, so that the two products `z·b` and `2 − b·x` become independent. Its four results — `ThreeDiv_isTW`, `ThreeDivFast_isTW`, `ThreeDiv_error` (**paper Theorem 10**, relative error `≤ 29u³ + 2576u⁴`) and `ThreeDivFast_error` (`≤ 44u³ + 2650u⁴`) — all proved; see `doc/thm10.md`. Our `29u³` is above the paper's, because our `δ₃` is `8u³ + 1330u⁴` where the paper asserts `3u³ + 264u⁴`: numerically the paper is **not** refuted, our bound is simply loose (`doc/alg20_delta3_search.py`). |
| `ThreeSqRt.v` | Algorithm 15 (3SqRt), the **square root** of a triple word by one Newton step on `r ← r(3/2 − ½r²x)` (`p ≥ 11`). **Skeleton**: the definition is complete and the Newton identity `sqrt_newton_id` is proved; the four results — `ThreeSqRt_isTW`, `ThreeSqRtFast_isTW`, `ThreeSqRt_error` (**paper Theorem 11**, `≤ 24u³ + 10260u⁴`) and `ThreeSqRtFast_error` (`≤ 39u³ + 10333u⁴`) — are stated and admitted, with the six intermediate obligations. Proved following `doc/Algorithms_for_Triple-Word_Arithmetic.pdf` §3 (`doc/old-triplewors.pdf` never wrote its Section 10 — its roadmap literally reads "Section 10 [???]"). Unlike Theorem 10, the published `24u³` should be reachable **despite** our looser `δ₃ = 8u³`: the supplementary's weight `1.5` on `δ₁` discards a cancellation between the two occurrences of `i⁽¹⁾`, and the true first-order weight is `0.5`. Plan in `doc/thm11.md`. |

### `code/ocaml/`

| File | Contents |
|------|----------|
| `addition.ml` | Reference OCaml (binary64) implementation of the same algorithm, with a randomised test that checks the error bound using exact floating-point expansions. Run with `cd code/ocaml && ocaml addition.ml`. |

### `code/TWFalcon/`

C extraction of just the addition (`tw_sum` = `merge_noloop` → `vec_sum6` →
`vseb_sum`) from the upstream `triple_float.c`, plus `test_zeros.c`, a test of
what happens when a triple-word contains zero limbs (the merge/VSEB corner that
motivated this directory). Build and run with `cd code/TWFalcon && make test`.
See its `README.md`.

## Requirements

- Rocq/Coq 9.0 or later
- [MathComp](https://math-comp.github.io) ssreflect & algebra 2.4.0+
- [Coquelicot](https://coquelicot.gitlabpages.inria.fr) 3.4.3+
- [Flocq](https://flocq.gitlabpages.inria.fr) 4.2.1+
- [Interval](https://coqinterval.gitlabpages.inria.fr) 4.11.2+

## Building

```shell
git clone https://github.com/thery/threewords.git
cd threewords/example/coq
make
```
