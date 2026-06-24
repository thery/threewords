# threewords

A [Rocq/Coq](https://rocq-prover.org) formalization of the correctly-rounded
computation of elementary functions in IEEE‑754 binary64 (double precision)
floating-point arithmetic, using *double-word* (and triple-word) representations.
The development formally verifies the algorithms and error bounds behind a
correctly-rounded `pow` function (`x^y`), together with its building blocks for
the logarithm and exponential.

Authors: Laurent Théry, Laurence Rideau — MIT License.

## Repository layout

```
doc/      research papers describing the algorithms and their proofs
example/  the Rocq/Coq development (algorithms, tables and supporting lemmas)
```

## `doc/`

| File | Contents |
|------|----------|
| `paper.pdf`  | Paper describing the formalized algorithms and error analysis. |
| `paper3.pdf` | Companion / extended paper for the development. |

## `example/`

The Rocq/Coq sources. Build with `make` (see the dependencies below). The build
order is given in `_CoqProject`.

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

## Requirements

- Rocq/Coq 9.0 or later
- [MathComp](https://math-comp.github.io) ssreflect & algebra 2.4.0+
- [Coquelicot](https://coquelicot.gitlabpages.inria.fr) 3.4.3+
- [Flocq](https://flocq.gitlabpages.inria.fr) 4.2.1+
- [Interval](https://coqinterval.gitlabpages.inria.fr) 4.11.2+

## Building

```shell
git clone https://github.com/thery/threewords.git
cd threewords/example
make
```
