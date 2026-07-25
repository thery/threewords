(* ---------------------------------------------------------------------------*)
(* Algorithm 12 (3Prod^fast_{2,3}): the FAST product of a DOUBLE word by a    *)
(* triple word, and its two correctness results -- the result is a triple     *)
(* word                                                                       *)
(* ([ThreeProdDWFast_isTW]) and the relative error bound [18u^3 + 75u^4]      *)
(* ([ThreeProdDWFast_error]) -- paper doc/paper3.pdf, Section 7.2 (see        *)
(* doc/alg12.md).  Generic over the precision [p] (FLX, no [emin]); needs     *)
(* [p >= 6].                                                                  *)
(*                                                                            *)
(* Algorithm 12 is to Algorithm 11 ([ThreeProdDW.v]) what Algorithm 10 is to  *)
(* Algorithm 9: the last 2Sum becomes a single rounding [s3 = RN(c + z3)] and *)
(* the low word [e4] is dropped.  Equivalently it IS Algorithm 10             *)
(* ([ThreeProdFast.v]) with [x2 = 0], which is how correctness is inherited;  *)
(* the error bound is not -- taking [x2 = 0] into account gives               *)
(* [18u^3 + 75u^4] instead of [44u^3 + 176u^4].                               *)
(*                                                                            *)
(* STATUS: SKELETON.  The definition transcribes Algorithm 12 verbatim on top *)
(* of [TwoProd] (Alg 3), [vecSum] (Alg 4) and [vsebK] (Alg 5); the two        *)
(* theorems are stated and [Admitted].  As for Theorem 8, doc/paper3.pdf      *)
(* gives                                                                      *)
(* no proof of the error bound; it is recovered from doc/old-triplewors.pdf   *)
(* Section 7.5 -- see doc/alg12.md for the full plan.                         *)
(* ---------------------------------------------------------------------------*)

From Stdlib Require Import ZArith Reals Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
Require Import Nmore Rmore Fmore Rstruct MULTmore prelim.
From Flocq Require Import Pff.Pff2Flocq.
Require Import Uls.
Require Import TwoSum.
Require Import Nonoverlap.
Require Import TWR.
Require Import Merge.
Require Import VecSum.
Require Import VSEB.
Require Import Thm6.
Require Import ThreeProd.
Require Import ThreeProdFast.
Require Import ThreeProdDW.
Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SecThreeProdDWFast.

Variable p : Z.
Hypothesis Hp2 : (1 < p)%Z.
(* Algorithm 12, like Algorithms 9-11, needs [p >= 6] (paper Section 7.2).    *)
Hypothesis Hp6 : (6 <= p)%Z.

Local Notation beta := radix2.
Local Notation pow e := (bpow beta e).

Local Instance p_gt_0 : Prec_gt_0 p.
Proof. now apply Z.lt_trans with (2 := Hp2). Qed.

Open Scope R_scope.

Local Notation u := (u p beta).

Variable choice : Z -> bool.
Hypothesis choice_sym : forall x, choice x = ~~ choice (- (x + 1))%Z.
Local Notation rnd := (Znearest choice).
Local Instance valid_rnd : Valid_rnd rnd := valid_rnd_N choice.

Local Notation float := (float radix2).
Local Notation fexp := (FLX_exp p).
Local Notation format := (generic_format beta fexp).
Local Notation cexp := (cexp beta fexp).
Local Notation RND := (round beta fexp rnd).
Local Notation ulp := (ulp beta fexp).
Local Notation uls := (uls p).

(* Building blocks, with this format's [p]/[choice] hidden.                   *)
Local Notation TwoProd := (TwoProd p radix2 rnd).
Local Notation TwoSum := (TwoSum p choice).
Local Notation vecSumAux := (vecSumAux p choice).
Local Notation vecSum := (vecSum p choice).
Local Notation vsebAux := (vsebAux p choice).
Local Notation vseb := (vseb p choice).
Local Notation vsebK := (vsebK p choice).
Local Notation Pnonoverlap := (Pnonoverlap p).
Local Notation Fnonoverlap := (Fnonoverlap p).
Local Notation isTW := (isTW p).

(* Algorithm 10, of which Algorithm 12 is the [x2 = 0] case, and the          *)
(* double-word predicates and normalisation of Algorithm 11.                  *)
Local Notation ThreeProdFast := (ThreeProdFast p choice).
Local Notation isDW := (isDW p).
Local Notation dw_norm := (dw_norm p).
Local Notation dw_normP := (dw_normP p).
Local Notation tw_norm := (tw_norm p).
Local Notation tw_normP := (tw_normP p).

(* ===========================================================================*)
(*  Algorithm 12 -- 3Prod^fast_{2,3}(x, y)                                    *)
(*  (37 operations & 1 test; paper Section 7.2).                              *)
(*                                                                            *)
(*  Algorithm 11 with [s3 = RN(c + z3)] in place of the last 2Sum: its error  *)
(*  term [e4] is NOT computed, so the final VecSum has four inputs and        *)
(*  [(r1, r2) = VSEB(2)(e1, e2, e3)].  The third limb of the first argument   *)
(*  is                                                                        *)
(*  ignored -- it is [0] for an [isDW] input.                                 *)
(* ===========================================================================*)
Definition ThreeProdDWFast (x y : twR) : twR :=
  let: TWR x0 x1 _ := x in
  let: TWR y0 y1 y2 := y in
  let: (z00p, z00m) := TwoProd x0 y0 in
  let: (z01p, z01m) := TwoProd x0 y1 in
  let: (z10p, z10m) := TwoProd x1 y0 in
  let b := vecSum [:: z00m; z01p; z10p] in
  let b0 := nth 0 b 0 in
  let b1 := nth 0 b 1 in
  let b2 := nth 0 b 2 in
  let c   := RND (b2 + x1 * y1) in
  let z31 := RND (z10m + x0 * y2) in
  let z3  := RND (z31 + z01m) in
  let s3  := RND (c + z3) in
  let e := vecSum [:: z00p; b0; b1; s3] in
  let e0 := nth 0 e 0 in
  match vsebK 2 [:: nth 0 e 1; nth 0 e 2; nth 0 e 3] with
  | [:: r1, r2 & _] => TWR e0 r1 r2
  | [:: r1]         => TWR e0 r1 0
  | [::]            => TWR e0 0 0
  end.

(* ===========================================================================*)
(*  Correctness, part 1: [ThreeProdDWFast x y] is a triple-word number.       *)
(*                                                                            *)
(*  As in Section 7.1, this is inherited: Algorithm 12 is Algorithm 10 at     *)
(*  [x2 = 0] (the only difference, [RN(z01- + 0 * y0) = z01-], is             *)
(*  [round_generic] on a rounded value) and a DW is a TW with a zero third    *)
(*  limb.                                                                     *)
(* ===========================================================================*)
Lemma ThreeProdDWFast_isTW x y :
  ties_to_even choice ->
  isDW x -> isTW y -> isTW (ThreeProdDWFast x y).
Proof.
Admitted.

(* ===========================================================================*)
(*  The error bound: [<= 18u^3 + 75u^4] (paper Section 7.2).                  *)
(*                                                                            *)
(*  Proof OMITTED in doc/paper3.pdf, recovered from doc/old-triplewors.pdf    *)
(*  Section 7.5 -- see doc/alg12.md.  The five sources of Theorem 8 are       *)
(*  unchanged (no [eps2], and [eps0 = x1 y2 <= 2u^3 - 2u^4]) and there is one *)
(*  more, the term Algorithm 12 drops:                                        *)
(*                                                                            *)
(*    |eps4'| = |(c + z3) - s3| <= u ufp(6u^2 + 7u^2) <= 8u^3                 *)
(*                                                                            *)
(*  so the naive numerator is [22u^3 - 2u^4].  Three cases then suffice --    *)
(*  the case study is SHORTER than Theorem 8's because it works with [s3]     *)
(*  instead of [c] and [z3]:                                                  *)
(*                                                                            *)
(*    x*y >= 1.5 - 7u          : K = 22u^3 - 2u^4 (naive), with eps5          *)
(*    x*y < 1.5 - 7u, eps5 = 0 : K = 18u^3 - 2u^4 ([eps1], [eps4] halved)     *)
(*    x*y < 1.5 - 7u, eps5 <> 0: K = 16u^3 + 2u^4 (one more source shrinks)   *)
(* ===========================================================================*)
Lemma ThreeProdDWFast_error x y :
  ties_to_even choice ->
  isDW x -> isTW y ->
  Rabs (TWval (ThreeProdDWFast x y) - TWval x * TWval y) <=
     (18 * (u * u * u) + 75 * (u * u * u * u)) * Rabs (TWval x * TWval y).
Proof.
Admitted.

End SecThreeProdDWFast.
