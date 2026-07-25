(* ---------------------------------------------------------------------------*)
(* Algorithm 10 (3Prod^fast_{3,3}): the FAST product of two triple-word       *)
(* numbers, and its two correctness results -- the result is a triple word    *)
(* ([ThreeProdFast_isTW]) and the relative error bound [44u^3 + 176u^4]       *)
(* ([ThreeProdFast_error]) -- paper doc/paper3.pdf, Section 6.4 (see          *)
(* doc/alg10.md).  Generic over the precision [p] (FLX, no [emin]); needs     *)
(* [p >= 6].                                                                  *)
(*                                                                            *)
(* Algorithm 10 is Algorithm 9 ([ThreeProd.v]) with the last 2Sum replaced by *)
(* a single rounding: [s3 = RN(c + z3)] is computed WITHOUT its error term    *)
(* [e4 = (c + z3) - s3], which is simply dropped.  That saves 8 operations    *)
(* and one test, at the price of one extra error source [|e4| <= 16u^3],      *)
(* whence [44u^3 = 28u^3 + 16u^3] instead of [28u^3].                         *)
(*                                                                            *)
(* STATUS: SKELETON.  The definition transcribes Algorithm 10 verbatim on top *)
(* of [TwoProd] (Alg 3), [vecSum] (Alg 4) and [vsebK] (Alg 5); the two        *)
(* theorems are stated and [Admitted].  The proofs re-instantiate the         *)
(* Algorithm-9 skeleton of [ThreeProd.v]: the head [VecSum(z00+, b0, b1, s3)] *)
(* is LITERALLY the one of Algorithm 9 (so [inner_head_Fnonoverlap] applies   *)
(* unchanged, and no [e4] tail has to be handled), and the error analysis     *)
(* reuses [eps0..eps5] with the extra source [eps4' = (c + z3) - s3].  See    *)
(* doc/alg10.md for the full plan.                                            *)
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
Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SecThreeProdFast.

Variable p : Z.
Hypothesis Hp2 : (1 < p)%Z.
(* Algorithm 10, like Algorithm 9, needs [p >= 6] (paper Section 6.4).        *)
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
Local Notation vecSum := (vecSum p choice).
Local Notation vseb := (vseb p choice).
Local Notation vsebK := (vsebK p choice).
Local Notation Pnonoverlap := (Pnonoverlap p).
Local Notation Fnonoverlap := (Fnonoverlap p).
Local Notation isTW := (isTW p).

(* ===========================================================================*)
(*  Algorithm 10 -- 3Prod^fast_{3,3}(x, y)                                    *)
(*  (38 operations & 1 test; paper Section 6.4).                              *)
(*                                                                            *)
(*  The first five lines are those of Algorithm 9 ([ThreeProd]); then         *)
(*  [s3 = RN(c + z3)] replaces the 2Sum of Algorithm 9 -- its error term      *)
(*  [e4] is NOT computed -- and the final VecSum has four inputs instead of   *)
(*  five, so [(r1, r2) = VSEB(2)(e1, e2, e3)].                                *)
(*  The three [RN(_ + _ * _)] terms ([c], [z31], [z32]) are FMAs (a single    *)
(*  rounding).                                                                *)
(* ===========================================================================*)
Definition ThreeProdFast (x y : twR) : twR :=
  let: TWR x0 x1 x2 := x in
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
  let z32 := RND (z01m + x2 * y0) in
  let z3  := RND (z31 + z32) in
  let s3  := RND (c + z3) in
  let e := vecSum [:: z00p; b0; b1; s3] in
  let e0 := nth 0 e 0 in
  match vsebK 2 [:: nth 0 e 1; nth 0 e 2; nth 0 e 3] with
  | [:: r1, r2 & _] => TWR e0 r1 r2
  | [:: r1]         => TWR e0 r1 0
  | [::]            => TWR e0 0 0
  end.

(* ===========================================================================*)
(*  Correctness, part 1: [ThreeProdFast x y] is a triple-word number.         *)
(*                                                                            *)
(*  Paper Section 6.4: correctness is still ensured for the same reasons,     *)
(*  provided that [p >= 6].  Concretely (doc/alg10.md), the Section-6.2       *)
(*  part-1 argument of Algorithm 9 applies with LESS work:                    *)
(*  - the head [VecSum(z00+, b0, b1, s3)] is exactly the one of Algorithm 9   *)
(*    (same [z00+], [b0], [b1], and [s3 = RN(c + z3)]), so its                *)
(*    F-nonoverlapping is [ThreeProd.inner_head_Fnonoverlap] verbatim -- the  *)
(*    four-case [I]-set study of Theorem 1 does not have to be redone;        *)
(*  - the [e4] tail of Algorithm 9 is absent, so the [vecSum_split5] /        *)
(*    [Fnonoverlap_rcons] step and the [e4]-divisibility item (b) disappear;  *)
(*  - Theorem 2 ([vseb_Pnonoverlap]) then gives P-nonoverlapping of           *)
(*    [vseb (z00+, b0, b1, s3)], and the [r0 = e0] optimisation is the same   *)
(*    star identity ([vseb_star] / [vseb_head3_e1zero]).                      *)
(*  The general statement will reduce to a normalised one (paper WLOG         *)
(*  [1 <= x0, y0 < 2]) by the scale/sign equivariance of Algorithm 10, the    *)
(*  twin of [ThreeProd_scale] / [ThreeProd_opp].                              *)
(* ===========================================================================*)
Lemma ThreeProdFast_isTW x y :
  ties_to_even choice ->
  isTW x -> isTW y -> isTW (ThreeProdFast x y).
Proof.
Admitted.

(* ===========================================================================*)
(*  Correctness, part 2: relative error of [ThreeProdFast] is                 *)
(*  [<= 44u^3 + 176u^4].                                                      *)
(*                                                                            *)
(*  Paper Section 6.4 (details in doc/old-triplewors.pdf Section 6.6; see     *)
(*  doc/alg10.md).  The six error sources [eps0..eps5] of Theorem 7 are       *)
(*  unchanged, and there is ONE more, the term Algorithm 10 drops:            *)
(*                                                                            *)
(*     |eps4'| := |(c + z3) - s3| <= u ufp(c + z3) <= u ufp(12u^2 + 8u^2)     *)
(*             <= 16u^3                                                       *)
(*                                                                            *)
(*  so the numerator becomes [(28u^3 - 11.9u^4) + 16u^3 = 44u^3 - 11.9u^4],   *)
(*  and dividing by [x*y >= 1 - 4u] gives [44u^3 + 176u^4].  As for           *)
(*  Algorithm 9, the [eps5 <> 0] case is handled by showing that when all the *)
(*  other terms are big [eps5 = 0] ([ThreeProd.eps5_zero_all_big]).           *)
(* ===========================================================================*)
Lemma ThreeProdFast_error x y :
  ties_to_even choice ->
  isTW x -> isTW y ->
  Rabs (TWval (ThreeProdFast x y) - TWval x * TWval y) <=
     (44 * (u * u * u) + 176 * (u * u * u * u)) * Rabs (TWval x * TWval y).
Proof.
Admitted.

End SecThreeProdFast.
