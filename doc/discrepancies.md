# Formal verification of *Algorithms for triple-word arithmetic* — what was checked, and where it differs from the paper

This note summarises a complete machine-checked verification of the paper, and
lists every point where the formal proof departs from the printed text. It is
written entirely in the paper's own notation; no knowledge of the proof
assistant is needed to read it.

Everything below has been checked by machine. Counterexamples are exact and
reproducible; where a constant differs, both values are proved.

---

## 1. What has been verified

Algorithms 1–15, together with the appendix Algorithms 18 and 20, and
Theorems 1–11. Radix 2, precision `p`, round to nearest ties-to-even.

| | published | verified |
|---|---|---|
| Thm 1, Cor 1 (VecSum) | — | as stated |
| Thm 2 (VSEB) | — | as stated |
| Thm 3 (keep first `k`) | `2uᵏ + 4.2u^{k+1}` | as stated, for general `k` |
| Thm 4 (ToTW) | `p ≥ 4` | as stated |
| Thm 5 (RoundTW) | `RoundTW(x̄) = RN(x̄)` | as stated, **after correcting Algorithm 7** (§2.1) |
| Thm 6 (TWSum) | `p ≥ 4` | as stated (**its proof has a false step**, §2.3) |
| Thm 7 (Alg 9) | `28u³ + 107u⁴` | as stated |
| Thm 8 (Alg 11) | `10.5u³ + 39u⁴` | as stated (**gap in the case analysis**, §2.4) |
| Thm 9 (Alg 13) | `11.5u³ + 1465u⁴` / `19u³ + 1502u⁴` | `11.5u³ + 1830u⁴` / `19u³ + 1870u⁴` (§2.6) |
| Thm 10 (Alg 14) | `24u³ + 1509u⁴` / `39u³ + 1582u⁴` | `27u³ + 2500u⁴` / `42u³ + 2575u⁴` (§3.1) |
| Thm 11 (Alg 15) | `24u³ + 10260u⁴` / `39u³ + 10333u⁴` | **as stated** (§4.1) |

Two of the `u³` constants move (Theorem 10) and two of the `u⁴` constants move
(Theorem 9). **Every other `u³` constant in the paper is confirmed exactly** —
including `11.5 = 10.5 + 1` and `19 = 18 + 1`, and all of Theorem 11.

Not formalised: Algorithms 16, 17, 19 (the sign-folded variants — they save one
operation each and change no bound).

---

## 2. Points that need a correction

### 2.1 Algorithm 7 (RoundTW): the inner test has the wrong polarity

As printed, the first `if` returns `RN(x₀+x₁)` when

>  `RN(x₀ + 2x₁)` is inexact **or** `RN(−(3/2 u − 2u²)·x₀) ≠ x₁`.

The second disjunct should be `=`, not `≠`.

At a genuine midpoint `x₁ = ±½ulp(x₀)`, the quantity `RN(−(3/2 u − 2u²)·x₀)`
has magnitude `≈ (3/2)u|x₀|` and, for positive `x₁`, the opposite sign — so it
never equals `x₁`, the printed test is true, and the algorithm returns
`RN(x₀+x₁)`, **ignoring `x₂` exactly when `x₂` decides the rounding**.
Conversely, the paper's own "special case" `x₀ = 1+2u`, `x₁ = −3/2 u` is
precisely where `RN(−(3/2 u − 2u²)·x₀) = x₁`, so the printed condition takes
the directional branch there — also the wrong way round.

**Counterexample (binary64).** `x̄ = (1, u, u²)` is a valid triple word and
`x₀+x₁` is exactly the midpoint of `[1, 1+2⁻⁵²]`.

| | |
|---|---|
| `RN(x̄)` | `1 + 2⁻⁵²` |
| Algorithm 7 as printed | `1` — wrong |
| Algorithm 7 with `=` | `1 + 2⁻⁵²` |

An exact sweep over random valid triple words fails on about 0.3 % of inputs
(all midpoints) for `p = 4, 6, 8, 10`. Theorem 5 is true of the corrected
algorithm, and the proof text then reads correctly as written.

### 2.2 Lemma 1: two missing hypotheses

Lemma 1 (`½ulp(x)` divides `RN(x+y)`, used in the proof of Theorem 7) needs
`y` to be a floating-point number and `x ≠ 0`. It is false without them.

### 2.3 Theorem 6: an intermediate claim of the proof is false

The proof asserts that the output of VecSum is F-nonoverlapping. It is not:

>  `[15, 15, 15/16, 15/16]` at `p = 4`

is a legal input whose VecSum output violates the definition. **Theorem 6
itself is true** — VSEB repairs the defect — but the argument has to go through
VSEB rather than through VecSum alone.

### 2.4 Theorem 8: a gap in the case analysis

The case analysis splits on `x̄ȳ ≥ 3/2 − 5u` and `x̄ȳ < 3/2 − 6u`, leaving the
interval between the two uncovered. Using the single threshold `3/2 − 7u`
closes it and the proof goes through unchanged. **The statement is unaffected.**

### 2.5 §8.3: the tail bound needs `ulp`, not `uls`

The argument that the leading limb of `3Prod₂,₃(b̄, x̄)` equals `1` bounds the
tail using F-nonoverlapping, i.e. `uls`. That is not enough:

>  `[16, −8, −4, −2, −1]`

is F-nonoverlapping, sums to `1`, and has leading limb `16`. What the argument
actually needs is the **`ulp`-scale** separation of the two leading limbs —
which the 2Sum structure of the inner VecSum does supply, so the conclusion
`e₀ = 1` stands. Only the justification has to change.

### 2.6 δ₂ (Algorithm 18) is `u³ + 620u⁴`, not `u³ + 260u⁴`

Two distinct issues.

**(a) Remark 10 is false.** Algorithm 18 uses `Fast2Sum(b₁, z₀₁⁺)` without
establishing the ordering, on the grounds that when the condition fails `b₁` is
negligible. But the condition fails exactly when `|b₁| < |z₀₁⁺|`, and the worst
case `|b₁| ≈ ulp(z₀₁⁺)` loses `≈ u|z₀₁⁺| ≈ 41u³` — not `O(u⁴)`. Legal binary64
inputs reach **32u³**, i.e. 32 times the announced `δ₂`. The last line,
`Fast2Sum(e₁, e₂)`, has the same hole (`|e₁| < |e₂|` is legal, and costs
`≈ 3u³`).

*This is repairable at no arithmetic cost*: sort the two arguments first. A
Fast2Sum preceded by one test is error-free unconditionally, so Algorithm 18
keeps its 20 operations and gains 2 tests.

**(b) The `u⁴` term.** With the repair in place we prove `δ₂ = u³ + 620u⁴`.
The `u³` term is exactly the announced one; the `u⁴` term is not. Consequence
for Theorem 9:

|  | published | verified |
|---|---|---|
| accurate | `11.5u³ + 1465u⁴` | `11.5u³ + 1830u⁴` |
| fast | `19u³ + 1502u⁴` | `19u³ + 1870u⁴` |

### 2.7 The exponent range

All the results are proved with an unbounded exponent range — the model the
paper works in implicitly. This is worth stating in the text, because
Theorem 1 and Corollary 1 are genuinely false near the underflow threshold.

---

## 3. One place where our bound is weaker, and we believe the paper is right

### 3.1 δ₃ (Algorithm 20) and Theorem 10

We can only prove `δ₃ = 6u³ + 1250u⁴` against the announced `3u³ + 264u⁴`,
whence Theorem 10 at `27u³ + 2500u⁴` and `42u³ + 2575u⁴` instead of
`24u³ + 1509u⁴` and `39u³ + 1582u⁴`.

The reason is that a *triple* word only gives `|x₁| < ulp(x₀)` and
`|x₂| < ulp(x₁)`, i.e. twice a double word's separation, so the two neglected
roundings cost `2u³` and `4u³` instead of `1u³` and `2u³`. The announced `3u³`
is what the double-word separations would give.

**We do not claim this is an error.** A numerical search over legal inputs
reaches only about `2.5u³`, so `3u³` does look attained and the remaining
factor of two is very likely slack in our proof, not in yours. We record it
only so the discrepancy is not mistaken for a disagreement.

### 3.2 A hypothesis that is implicit in Algorithm 20

Worth making explicit in the appendix: `δ₃` depends on **how close the second
factor is to `1`**, not merely on its leading limb being `1`. Algorithm 14
supplies a second factor within `40u²` of `1`; Algorithm 15 can only supply one
within `≈ 101u²`, because there the seed error enters undamped (see §4.1). Our
bound is therefore stated as a function of that tolerance `c`:

>  `δ₃(c) = 6u³ + (31c + 10)u⁴`   for a second factor within `cu²` of `1`.

The `u³` term does not depend on `c` at all.

---

## 4. Theorem 11 (Algorithm 15)

### 4.1 It holds exactly as published

`24u³ + 10260u⁴` and `39u³ + 10333u⁴` at `p ≥ 11`, verified — and this is the
only theorem in the paper for which the printed constants survive despite
*every* intermediate constant of ours being worse (`δ₃` above; and we could
only reach `100u²` for the seed where the supplementary proves `81u² + 622u³`).

That is not luck. **Our proof takes a different route**, and has to. The
supplementary bounds `|δ₁ − (δ₁+δ₂)/2|` by the triangle inequality, which gives
`δ₁` the weight `1.5`. That discards a real cancellation: `i⁽¹⁾` occurs twice —
once as a factor of the result, once inside `i⁽²⁾` — with opposite signs.
Keeping it gives `δ₁` the weight `1/2`, and the total becomes

>  `|y − √x̄| ≤ (½δ₁ + ½δ₂ + δ₃ + 15200u⁴)·√x̄`

which is what leaves enough `u³` room to absorb our worse `u⁴` terms. Done
termwise, with our `δ₃`, Theorem 11 would come out at `29u³` / `44u³` and the
published bound would fail on both terms at once.

This suggests the supplementary's weight `1.5` on `δ₁` is simply loose, and
that the true first-order sensitivity of Algorithm 15 to its first product is
half, not one and a half.

### 4.2 `p ≥ 11` is confirmed, and confirmed sharp

The supplementary's `9916u⁴` residual is exactly `E²(3+E)/2` evaluated at
`E = 81u² + 622u³`: that is `9915.5u⁴` at `p = 11` and `9989.9u⁴` at `p = 10`,
where it exceeds the stated value. So the precision requirement is real, the
constant is what it is announced to be, and the two are consistent.

---

## 5. In one line

The published statements stand, with four amendments: **Algorithm 7's inner
test must be inverted**, **Algorithm 18's two `Fast2Sum` calls must sort their
arguments**, **`δ₂`'s `u⁴` term is `620`, not `260`** (hence Theorem 9's
`1830` / `1870`), and **Lemma 1 needs two hypotheses**. Three further points
(§2.3, §2.4, §2.5) are gaps in proofs whose statements are correct. Theorem 11
holds verbatim.
