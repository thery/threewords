# TWFalcon reference implementation

This directory holds the **upstream C reference implementation** of the
triple-word floating-point arithmetic that the Rocq/Coq development in
[`../coq/`](../coq) formalizes.

## Provenance

| | |
|---|---|
| Source repository | [`NXP-Research/TWFalcon`](https://github.com/NXP-Research/TWFalcon) |
| Paper | *TWFalcon: Triple-Word Arithmetic for Falcon — Giving Falcon the Precision to Fly Securely* |
| Original path | `c-fn-dsa-multiple/triple_float.{c,h}` |
| Copyright | © 2025 NXP |
| License | MIT (see `LICENSE`) |

The files `triple_float.c` and `triple_float.h` are copied **verbatim** from the
upstream repository so that the full arithmetic (addition, subtraction,
products, reciprocals, division, square root, conversions, …) is available for
reference next to the formalization.

## Note on precision

The upstream code targets **binary32** (`float`, `u = 2^-24`), because that is
what the Falcon signature scheme uses on embedded targets. The Rocq/Coq
development in `../coq/` instead reasons about **binary64** (`double`,
`u = 2^-53`). The *algorithms* are identical; only the working precision differs.

## Addition only

A trimmed-down, self-contained extraction of just the **triple-word addition**
(`TWSum`, Algorithm 8) — the part currently being formalized — lives in
[`../../code/TWFalcon/`](../../code/TWFalcon), together with a test that probes
what happens when a triple-word input contains zero components.
