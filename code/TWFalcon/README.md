# TWFalcon addition — C reference + zeros test

A self-contained extraction of **just the triple-word addition** (`TWSum`,
Algorithm 8) from the upstream reference implementation, plus a test that
probes what happens when a triple-word contains zero limbs.

This mirrors [`../coq/`](../coq) (the Rocq/Coq formalization of the same
addition) the way [`../../example/TWFalcon/`](../../example/TWFalcon) mirrors
[`../../example/coq/`](../../example/coq).

## Provenance

`tw_add.c` / `tw_add.h` are extracted from
[`NXP-Research/TWFalcon`](https://github.com/NXP-Research/TWFalcon)
(`c-fn-dsa-multiple/triple_float.{c,h}`, © 2025 NXP, MIT License). Only the
functions on the addition path are kept:

```
tw_sum = merge_noloop  ->  vec_sum6  ->  vseb_sum
```

plus `two_sum`, `fast_two_sum`, and `tw_sub` (negate + `tw_sum`). Everything
else (products, division, sqrt, conversions, the constant-time variants) is
dropped; the full source is in `../../example/TWFalcon/triple_float.c`.

The code works in **binary32** (`float`, `u = 2^-24`), exactly as upstream.
The companion Coq proofs reason about the same algorithm in binary64.

## Files

| File | Contents |
|------|----------|
| `tw_add.h`     | `tw_fpr` type and the `tw_sum` / `tw_sub` prototypes. |
| `tw_add.c`     | The extracted addition (`merge_noloop`, `vec_sum6`, `vseb_sum`, `tw_sum`, `tw_sub`). |
| `test_zeros.c` | Behaviour of `tw_sum` when triple-words contain zeros. |
| `Makefile`     | `make` builds the test; `make test` runs it. |

## The zeros question

The concern is the **merge** step (`merge_noloop`): it orders the six input
limbs by *strictly* decreasing magnitude, and `vseb_sum` folds any *exactly
zero* error term back into the running value instead of emitting a result
limb. When an input limb is `0`, ties and vanishing error terms appear, so it
is worth checking that the result is still:

1. **magnitude-sorted**  (`|r0| >= |r1| >= |r2|`),
2. **tail-padded**  (a zero limb is never followed by a non-zero one), and
3. **the exact / correctly-bounded sum** of the inputs.

`test_zeros.c` checks all three on seven hand-picked cases (trailing zeros,
a zero operand, an interior zero limb, head cancellation, total cancellation
to `(0,0,0)`, clean doubling, mixed zeros) and then on a reproducible
randomised fuzz (500k trials, ~75% with injected zeros).

## Running

```shell
cd code/TWFalcon
make test
```

Exit status is non-zero if any check fails. On the bundled cases and the fuzz,
every zero-containing input stays well-formed and within the triple-word
relative-error bound `2u³ + 4.2u⁴`.
