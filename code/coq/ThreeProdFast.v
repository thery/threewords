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
(* STATUS: [ThreeProdFast_isTW] is PROVED; [ThreeProdFast_error] is still     *)
(* [Admitted].  The definition transcribes Algorithm 10 verbatim on top of    *)
(* [TwoProd] (Alg 3), [vecSum] (Alg 4) and [vsebK] (Alg 5).  The correctness  *)
(* proof re-instantiates the Algorithm-9 skeleton of [ThreeProd.v]: the head  *)
(* [VecSum(z00+, b0, b1, s3)] is LITERALLY the one of Algorithm 9, so         *)
(* [inner_head_Fnonoverlap] (the four-case [I]-set study) applies unchanged   *)
(* and no [e4] tail has to be handled; every Section-6.1 term bound is reused *)
(* as is.  The error proof will reuse [eps0..eps5] plus the extra source      *)
(* [eps4' = (c + z3) - s3].  See doc/alg10.md for the full plan.              *)
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
Local Notation vecSumAux := (vecSumAux p choice).
Local Notation vecSum := (vecSum p choice).
Local Notation vsebAux := (vsebAux p choice).
Local Notation vseb := (vseb p choice).
Local Notation vsebK := (vsebK p choice).
Local Notation Pnonoverlap := (Pnonoverlap p).
Local Notation Fnonoverlap := (Fnonoverlap p).
Local Notation isTW := (isTW p).

(* The paper's normalisation [1 <= x0, y0 < 2] and its triple-word packing,   *)
(* both from ThreeProd.v.                                                     *)
Local Notation tw_norm := (tw_norm p).
Local Notation tw_normP := (tw_normP p).

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
(*  The FLX WLOG for Algorithm 10 -- scale- and sign-equivariance and the     *)
(*  degenerate zero-factor cases, the twins of [ThreeProd_scale] /            *)
(*  [ThreeProd_opp] / [ThreeProd_opp_r] / [ThreeProd_0l] / [ThreeProd_0r].    *)
(*  Every generic ingredient ([round_scale], [vecSum_scale], [vsebK_scale],   *)
(*  [TwoProd_scale] and their [_opp] twins, [vsebAux_zeros], ...) is reused   *)
(*  from ThreeProd.v -- only these five wrappers are algorithm-specific.      *)
(* ===========================================================================*)
Lemma ThreeProdFast_scale a b x y :
  ThreeProdFast (scaleTW a x) (scaleTW b y) =
    scaleTW (a + b) (ThreeProdFast x y).
Proof.
case: x => x0 x1 x2; case: y => y0 y1 y2.
rewrite /ThreeProdFast /scaleTW.
have P1 : x1 * pow a * (y1 * pow b) = x1 * y1 * pow (a + b) by rewrite
  bpow_plus; ring.
have P2 : x0 * pow a * (y2 * pow b) = x0 * y2 * pow (a + b) by rewrite
  bpow_plus; ring.
have P3 : x2 * pow a * (y0 * pow b) = x2 * y0 * pow (a + b) by rewrite
  bpow_plus; ring.
rewrite !P1 !P2 !P3 !TwoProd_scale.
case: (TwoProd x0 y0) => w00p w00m.
case: (TwoProd x0 y1) => w01p w01m.
case: (TwoProd x1 y0) => w10p w10m.
have F1 : forall u v : R, (u, v).1 = u by [].
have F2 : forall u v : R, (u, v).2 = v by [].
rewrite !F1 !F2.
have Eb : forall i, nth 0 (vecSum [:: w00m * pow (a+b); w01p * pow (a+b); w10p *
  pow (a+b)]) i = nth 0 (vecSum [:: w00m; w01p; w10p]) i * pow (a+b).
  move=> i.
  have -> : [:: w00m * pow (a+b); w01p * pow (a+b); w10p * pow (a+b)] = [seq z *
    pow (a+b) | z <- [:: w00m; w01p; w10p]] by [].
  by rewrite vecSum_scale nth_map_scale.
rewrite !Eb.
set bb := vecSum [:: w00m; w01p; w10p].
have E4 : forall t : R, RND (t * pow (a+b) + x1 * y1 * pow (a+b)) = RND (t + x1
  * y1) * pow (a+b).
  move=> t.
  have -> : t * pow (a+b) + x1 * y1 * pow (a+b) = (t + x1 * y1) * pow (a+b) by
    ring.
  by rewrite round_scale.
have E5 : RND (RND (w10m * pow (a+b) + x0 * y2 * pow (a+b)) + RND (w01m * pow
  (a+b) + x2 * y0 * pow (a+b))) = RND (RND (w10m + x0 * y2) + RND (w01m + x2 *
  y0)) * pow (a+b).
  have -> : w10m * pow (a+b) + x0 * y2 * pow (a+b) = (w10m + x0 * y2) * pow
    (a+b) by ring.
  have -> : w01m * pow (a+b) + x2 * y0 * pow (a+b) = (w01m + x2 * y0) * pow
    (a+b) by ring.
  rewrite !round_scale.
  have -> : RND (w10m + x0 * y2) * pow (a+b) + RND (w01m + x2 * y0) * pow (a+b)
    = (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)) * pow (a+b) by ring.
  by rewrite round_scale.
rewrite !E4 !E5.
(* The extra line of Algorithm 10: [s3 = RN(c + z3)] scales as well.          *)
have E6 : RND (RND (nth 0 bb 2 + x1 * y1) * pow (a+b)
             + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)) * pow (a+b))
        = RND (RND (nth 0 bb 2 + x1 * y1)
             + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))) * pow (a+b).
  have -> : RND (nth 0 bb 2 + x1 * y1) * pow (a+b)
          + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)) * pow (a+b)
          = (RND (nth 0 bb 2 + x1 * y1)
           + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))) * pow (a+b) by
    ring.
  by rewrite round_scale.
rewrite !E6.
have Ee : forall i, nth 0 (vecSum [:: w00p * pow (a+b); nth 0 bb 0 * pow (a+b);
  nth 0 bb 1 * pow (a+b); RND (RND (nth 0 bb 2 + x1 * y1)
     + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))) * pow (a+b)]) i
  = nth 0 (vecSum [:: w00p; nth 0 bb 0; nth 0 bb 1;
      RND (RND (nth 0 bb 2 + x1 * y1)
         + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)))]) i * pow (a+b).
  move=> i.
  have -> : [:: w00p * pow (a+b); nth 0 bb 0 * pow (a+b); nth 0 bb 1 * pow
    (a+b); RND (RND (nth 0 bb 2 + x1 * y1)
       + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))) * pow (a+b)]
    = [seq z * pow (a+b) | z <- [:: w00p; nth 0 bb 0; nth 0 bb 1;
        RND (RND (nth 0 bb 2 + x1 * y1)
           + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)))]] by [].
  by rewrite vecSum_scale nth_map_scale.
rewrite !Ee.
set ee := vecSum [:: w00p; nth 0 bb 0; nth 0 bb 1;
  RND (RND (nth 0 bb 2 + x1 * y1)
     + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)))].
have Ev : vsebK 2 [:: nth 0 ee 1 * pow (a+b); nth 0 ee 2 * pow (a+b); nth 0 ee 3
  * pow (a+b)] = [seq z * pow (a+b) | z <- vsebK 2 [::
  nth 0 ee 1; nth 0 ee 2; nth 0 ee 3]].
  have -> : [:: nth 0 ee 1 * pow (a+b); nth 0 ee 2 * pow (a+b); nth 0 ee 3 * pow
    (a+b)] = [seq z * pow (a+b) | z <- [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3]]
    by [].
  by rewrite vsebK_scale.
rewrite Ev.
set V := vsebK 2 [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3].
by case: V => [|r1 [|r2 rr]] //=; congr TWR; ring.
Qed.

Lemma ThreeProdFast_opp x y :
  ThreeProdFast (negTW x) y = negTW (ThreeProdFast x y).
Proof.
case: x => x0 x1 x2; case: y => y0 y1 y2.
rewrite /ThreeProdFast /negTW.
have P1 : (- x1) * y1 = - (x1 * y1) by ring.
have P2 : (- x0) * y2 = - (x0 * y2) by ring.
have P3 : (- x2) * y0 = - (x2 * y0) by ring.
rewrite !P1 !P2 !P3 !(@TwoProd_opp_l p choice choice_sym).
case: (TwoProd x0 y0) => w00p w00m.
case: (TwoProd x0 y1) => w01p w01m.
case: (TwoProd x1 y0) => w10p w10m.
have F1 : forall u v : R, (u, v).1 = u by [].
have F2 : forall u v : R, (u, v).2 = v by [].
rewrite !F1 !F2.
have Eb : forall i, nth 0 (vecSum [:: - w00m; - w01p; - w10p]) i = - nth 0
  (vecSum [:: w00m; w01p; w10p]) i.
  move=> i.
  have -> : [:: - w00m; - w01p; - w10p] = [seq - z | z <- [:: w00m; w01p; w10p]]
    by [].
  by rewrite (@vecSum_opp p choice choice_sym) nth_map_opp.
rewrite !Eb.
set bb := vecSum [:: w00m; w01p; w10p].
have E4 : forall t : R, RND (- t + - (x1 * y1)) = - RND (t + x1 * y1).
  move=> t.
  have -> : - t + - (x1 * y1) = - (t + x1 * y1) by ring.
  by rewrite (@round_opp p choice choice_sym).
have E5 : RND (RND (- w10m + - (x0 * y2)) + RND (- w01m + - (x2 * y0))) = - RND
  (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)).
  have -> : - w10m + - (x0 * y2) = - (w10m + x0 * y2) by ring.
  have -> : - w01m + - (x2 * y0) = - (w01m + x2 * y0) by ring.
  rewrite !(@round_opp p choice choice_sym).
  have -> : - RND (w10m + x0 * y2) + - RND (w01m + x2 * y0) = - (RND (w10m + x0
    * y2) + RND (w01m + x2 * y0)) by ring.
  by rewrite (@round_opp p choice choice_sym).
rewrite !E4 !E5.
(* The extra line of Algorithm 10: [s3 = RN(c + z3)] is odd as well.          *)
have E6 : RND (- RND (nth 0 bb 2 + x1 * y1)
             + - RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)))
        = - RND (RND (nth 0 bb 2 + x1 * y1)
             + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))).
  have -> : - RND (nth 0 bb 2 + x1 * y1)
          + - RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))
          = - (RND (nth 0 bb 2 + x1 * y1)
             + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))) by ring.
  by rewrite (@round_opp p choice choice_sym).
rewrite !E6.
have Ee : forall i, nth 0 (vecSum [:: - w00p; - nth 0 bb 0; - nth 0 bb 1;
  - RND (RND (nth 0 bb 2 + x1 * y1)
       + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)))]) i
  = - nth 0 (vecSum [:: w00p; nth 0 bb 0; nth 0 bb 1;
      RND (RND (nth 0 bb 2 + x1 * y1)
         + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)))]) i.
  move=> i.
  have -> : [:: - w00p; - nth 0 bb 0; - nth 0 bb 1;
    - RND (RND (nth 0 bb 2 + x1 * y1)
         + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)))]
    = [seq - z | z <- [:: w00p; nth 0 bb 0; nth 0 bb 1;
        RND (RND (nth 0 bb 2 + x1 * y1)
           + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)))]] by [].
  by rewrite (@vecSum_opp p choice choice_sym) nth_map_opp.
rewrite !Ee.
set ee := vecSum [:: w00p; nth 0 bb 0; nth 0 bb 1;
  RND (RND (nth 0 bb 2 + x1 * y1)
     + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)))].
have Ev : vsebK 2 [:: - nth 0 ee 1; - nth 0 ee 2; - nth 0 ee 3] =
  [seq - z | z <- vsebK 2 [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3]].
  have -> : [:: - nth 0 ee 1; - nth 0 ee 2; - nth 0 ee 3] = [seq -
    z | z <- [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3]] by [].
  by rewrite (@vsebK_opp p choice choice_sym).
rewrite Ev.
set V := vsebK 2 [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3].
by case: V => [|r1 [|r2 rr]] //=; congr TWR; ring.
Qed.

Lemma ThreeProdFast_opp_r x y :
  ThreeProdFast x (negTW y) = negTW (ThreeProdFast x y).
Proof.
case: x => x0 x1 x2; case: y => y0 y1 y2.
rewrite /ThreeProdFast /negTW.
have P1 : x1 * (- y1) = - (x1 * y1) by ring.
have P2 : x0 * (- y2) = - (x0 * y2) by ring.
have P3 : x2 * (- y0) = - (x2 * y0) by ring.
rewrite !P1 !P2 !P3 !(@TwoProd_opp_r p choice choice_sym).
case: (TwoProd x0 y0) => w00p w00m.
case: (TwoProd x0 y1) => w01p w01m.
case: (TwoProd x1 y0) => w10p w10m.
have F1 : forall u v : R, (u, v).1 = u by [].
have F2 : forall u v : R, (u, v).2 = v by [].
rewrite !F1 !F2.
have Eb : forall i, nth 0 (vecSum [:: - w00m; - w01p; - w10p]) i = - nth 0
  (vecSum [:: w00m; w01p; w10p]) i.
  move=> i.
  have -> : [:: - w00m; - w01p; - w10p] = [seq - z | z <- [:: w00m; w01p; w10p]]
    by [].
  by rewrite (@vecSum_opp p choice choice_sym) nth_map_opp.
rewrite !Eb.
set bb := vecSum [:: w00m; w01p; w10p].
have E4 : forall t : R, RND (- t + - (x1 * y1)) = - RND (t + x1 * y1).
  move=> t.
  have -> : - t + - (x1 * y1) = - (t + x1 * y1) by ring.
  by rewrite (@round_opp p choice choice_sym).
have E5 : RND (RND (- w10m + - (x0 * y2)) + RND (- w01m + - (x2 * y0))) = - RND
  (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)).
  have -> : - w10m + - (x0 * y2) = - (w10m + x0 * y2) by ring.
  have -> : - w01m + - (x2 * y0) = - (w01m + x2 * y0) by ring.
  rewrite !(@round_opp p choice choice_sym).
  have -> : - RND (w10m + x0 * y2) + - RND (w01m + x2 * y0) = - (RND (w10m + x0
    * y2) + RND (w01m + x2 * y0)) by ring.
  by rewrite (@round_opp p choice choice_sym).
rewrite !E4 !E5.
have E6 : RND (- RND (nth 0 bb 2 + x1 * y1)
             + - RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)))
        = - RND (RND (nth 0 bb 2 + x1 * y1)
             + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))).
  have -> : - RND (nth 0 bb 2 + x1 * y1)
          + - RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))
          = - (RND (nth 0 bb 2 + x1 * y1)
             + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))) by ring.
  by rewrite (@round_opp p choice choice_sym).
rewrite !E6.
have Ee : forall i, nth 0 (vecSum [:: - w00p; - nth 0 bb 0; - nth 0 bb 1;
  - RND (RND (nth 0 bb 2 + x1 * y1)
       + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)))]) i
  = - nth 0 (vecSum [:: w00p; nth 0 bb 0; nth 0 bb 1;
      RND (RND (nth 0 bb 2 + x1 * y1)
         + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)))]) i.
  move=> i.
  have -> : [:: - w00p; - nth 0 bb 0; - nth 0 bb 1;
    - RND (RND (nth 0 bb 2 + x1 * y1)
         + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)))]
    = [seq - z | z <- [:: w00p; nth 0 bb 0; nth 0 bb 1;
        RND (RND (nth 0 bb 2 + x1 * y1)
           + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)))]] by [].
  by rewrite (@vecSum_opp p choice choice_sym) nth_map_opp.
rewrite !Ee.
set ee := vecSum [:: w00p; nth 0 bb 0; nth 0 bb 1;
  RND (RND (nth 0 bb 2 + x1 * y1)
     + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)))].
have Ev : vsebK 2 [:: - nth 0 ee 1; - nth 0 ee 2; - nth 0 ee 3] =
  [seq - z | z <- vsebK 2 [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3]].
  have -> : [:: - nth 0 ee 1; - nth 0 ee 2; - nth 0 ee 3] = [seq -
    z | z <- [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3]] by [].
  by rewrite (@vsebK_opp p choice choice_sym).
rewrite Ev.
set V := vsebK 2 [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3].
by case: V => [|r1 [|r2 rr]] //=; congr TWR; ring.
Qed.

Lemma ThreeProdFast_0l y : ThreeProdFast (TWR 0 0 0) y = TWR 0 0 0.
Proof.
case: y => y0 y1 y2.
rewrite /ThreeProdFast !TwoProd00l /=.
rewrite !Rmult_0_l !Rplus_0_r !round_0.
do 40! (rewrite ?round_0 ?Rplus_0_r ?Rplus_0_l ?Rminus_0_r ?Rminus_0_l ?Ropp_0).
rewrite /vsebK /vseb.
have -> : [:: 0; 0] = nseq 1.+1 0 by [].
by rewrite vsebAux_zeros.
Qed.

Lemma ThreeProdFast_0r x : ThreeProdFast x (TWR 0 0 0) = TWR 0 0 0.
Proof.
case: x => x0 x1 x2.
rewrite /ThreeProdFast !TwoProd00r /=.
rewrite !Rmult_0_r !Rplus_0_l !round_0.
do 40! (rewrite ?round_0 ?Rplus_0_r ?Rplus_0_l ?Rminus_0_r ?Rminus_0_l ?Ropp_0).
rewrite /vsebK /vseb.
have -> : [:: 0; 0] = nseq 1.+1 0 by [].
by rewrite vsebAux_zeros.
Qed.

(* ===========================================================================*)
(*  The paper's star identity for Algorithm 10, [e1 = 0] half: the head of    *)
(*  [vseb e] is [e0] and the next two limbs are those of [vseb (behead e)].   *)
(*  The Algorithm-9 twin is [vseb_head3_e1zero]; here [e] has FOUR limbs      *)
(*  (the last one is [s3 = RN(c + z3)], no [e4]).                             *)
(* ===========================================================================*)
Lemma vsebFast_head3_e1zero x0 x1 x2 y0 y1 y2 :
  ties_to_even choice -> tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  let bb := vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)] in
  let e := vecSum
    [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
        RND (RND (nth 0 bb 2 + x1 * y1)
           + RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
                + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)))] in
  nth 0 e 1 = 0 ->
  nth 0 (vseb e) 0 = nth 0 e 0 /\
  nth 0 (vseb e) 1 = nth 0 (vseb (behead e)) 0 /\
  nth 0 (vseb e) 2 = nth 0 (vseb (behead e)) 1.
Proof.
move=> Hc Nx Ny bb e He1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := @u_le_64 p Hp6.
have Hp4 : (4 <= p)%Z by lia.
have [[Fx0 Fx1 Fx2] _ _ _ _] := Nx.
have [[Fy0 Fy1 Fy2] _ _ _ _] := Ny.
(* Section 6.1 term bounds -- reused verbatim from ThreeProd.v (Algorithm 10  *)
(* shares every term of Algorithm 9 up to [s3]).                              *)
have Hz10m2 : Rabs (RND (x1 * y0 - RND (x1 * y0))) <= 2 * (u * u).
  rewrite round_generic;
    first by apply: (@z10m_bound p Hp2 choice x0 x1 x2 y0 y1 y2 Nx Ny).
  rewrite (_ : x1 * y0 - RND (x1 * y0) = -(RND (x1 * y0) - x1 * y0));
    last by ring.
  by apply: generic_format_opp; exact: format_err_mul.
have Hz01m2 : Rabs (RND (x0 * y1 - RND (x0 * y1))) <= 2 * (u * u).
  rewrite round_generic;
    first by apply: (@z01m_bound p Hp2 choice x0 x1 x2 y0 y1 y2 Nx Ny).
  rewrite (_ : x0 * y1 - RND (x0 * y1) = -(RND (x0 * y1) - x0 * y1));
    last by ring.
  by apply: generic_format_opp; exact: format_err_mul.
have Hx0y2 := @x0y2_bound p Hp2 x0 x1 x2 y0 y1 y2 Nx Ny.
have Hx2y0 := @x2y0_bound p Hp2 x0 x1 x2 y0 y1 y2 Nx Ny.
have Hx1y1 := @x1y1_bound p x0 x1 x2 y0 y1 y2 Nx Ny.
have Hz31 := @z31_bound p Hp2 Hp6 choice _ _ _ Hz10m2 Hx0y2.
have Hz32 := @z32_bound p Hp2 Hp6 choice _ _ _ Hz01m2 Hx2y0.
have Hz3 := @z3_bound p Hp2 Hp6 choice _ _ Hz31 Hz32.
have Fbb : {in bb, forall z, format z}.
  apply: (@format_vecSum p Hp2 choice) => z; rewrite !inE.
  by move=> /orP[/eqP->|/orP[/eqP->|/eqP->]]; apply: generic_format_round.
have Fnthbb : forall i, format (nth 0 bb i).
  move=> i; case: (ltnP i (size bb)) => Hi;
    last by rewrite nth_default //; exact: generic_format_0.
  by apply: Fbb; apply: mem_nth.
have Hz00m : Rabs (RND (x0 * y0 - RND (x0 * y0))) <= 2 * u.
  rewrite round_generic;
    first by apply: (@z00m_bound p Hp2 choice x0 x1 x2 y0 y1 y2 Nx Ny).
  rewrite (_ : x0 * y0 - RND (x0 * y0) = -(RND (x0 * y0) - x0 * y0));
    last by ring.
  by apply: generic_format_opp; exact: format_err_mul.
have Hz01p := @z01p_bound p Hp2 choice x0 x1 x2 y0 y1 y2 Nx Ny.
have Hz10p := @z10p_bound p Hp2 choice x0 x1 x2 y0 y1 y2 Nx Ny.
have Hb2 : Rabs (nth 0 bb 2) <= 4 * (u * u).
  have Hb2eq : nth 0 bb 2 = RND (x0 * y1) + RND (x1 * y0)
      - RND (RND (x0 * y1) + RND (x1 * y0)).
    rewrite /bb (@vecSum3 p Hp2 choice choice_sym _ _ _
      (generic_format_round _ _ _ _) (generic_format_round _ _ _ _)
      (generic_format_round _ _ _ _)) /=; ring.
  by rewrite Hb2eq;
     apply: (@b2_bound p Hp2 choice x0 x1 x2 y0 y1 y2 Nx Ny).
have Hc8 : Rabs (RND (nth 0 bb 2 + x1 * y1)) <= 8 * (u * u)
  by apply: (@c_bound p Hp2 Hp6 choice _ _ _ Hb2 Hx1y1).
have Fku : forall k : Z, (Z.abs k < 2 ^ p)%Z -> format (IZR k * u)
  by move=> k Hk; rewrite u_pow; apply: format_mult_pow.
have F8u : format (8 * u) by rewrite -pow_3mp; apply: format_pow.
have Hb0 : Rabs (nth 0 bb 0) <= 10 * u.
  have Heq : nth 0 bb 0
      = RND (RND (x0 * y0 - RND (x0 * y0)) + RND (RND (x0 * y1) + RND (x1 *
        y0))).
    by rewrite /bb vecSum_nth0 vecSumAux_run_cons; congr RND; congr (_ + _).
  rewrite Heq.
  have F10 : format (10 * u) by apply: Fku; have := @two_p_ge_64 p Hp6; simpl;
    lia.
  apply: Rabs_round_le_r => //.
  have Hin : Rabs (RND (RND (x0 * y1) + RND (x1 * y0))) <= 8 * u.
    apply: Rabs_round_le_r => //.
    by have := Rabs_triang (RND (x0 * y1)) (RND (x1 * y0)); lra.
  by have := Rabs_triang (RND (x0 * y0 - RND (x0 * y0)))
       (RND (RND (x0 * y1) + RND (x1 * y0))); lra.
have Flbb : {in [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 *
  y0)],
    forall z, format z}.
  by move=> z; rewrite !inE => /orP[/eqP->|/orP[/eqP->|/eqP->]];
     apply: generic_format_round.
have Hb1 : Rabs (nth 0 bb 1) <= 8 * (u * u).
  have Hle := @vecSum_err_le_half_ulp_run p Hp2 choice choice_sym
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)] 0 isT Flbb.
  move: Hle; rewrite drop0.
  have -> : (vecSumAux [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1);
       RND (x1 * y0)]).2 = nth 0 bb 0 by rewrite /bb vecSum_nth0.
  have -> : nth 0 (vecSum [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1);
       RND (x1 * y0)]) 1 = nth 0 bb 1 by rewrite /bb.
  move=> Hle.
  have Hub : ulp (nth 0 bb 0) <= 16 * (u * u).
    rewrite -pow_4m2p; apply: bound_ulp_FLX; first exact: Hp2.
    have -> : (4 - 2 * p + p = 4 - p)%Z by lia.
    have -> : pow (4 - p) = 16 * u.
      rewrite (_ : (4 - p = (3 - p) + 1)%Z); last by lia.
      rewrite bpow_plus pow_3mp.
      have -> : pow 1 = 2 by rewrite /= /Z.pow_pos /=; lra.
      ring.
    by have := Hb0; lra.
  lra.
have P16 : pow (4 - p) = 16 * u.
  rewrite (_ : (4 - p = (3 - p) + 1)%Z); last by lia.
  rewrite bpow_plus pow_3mp.
  have -> : pow 1 = 2 by rewrite /= /Z.pow_pos /=; lra.
  ring.
have Hulp16 : forall z, Rabs z < 16 * u -> ulp z <= 16 * (u * u).
  move=> z Hz; rewrite -pow_4m2p; apply: bound_ulp_FLX; first exact: Hp2.
  by rewrite (_ : (4 - 2 * p + p = 4 - p)%Z) ?P16 //; lia.
have Hs3 : Rabs (RND (RND (nth 0 bb 2 + x1 * y1)
    + RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
         + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)))) <= 20 * (u * u)
  by apply: (@s3_bound p Hp2 Hp6 choice _ _ Hc8 Hz3).
set c := RND (nth 0 bb 2 + x1 * y1).
set z3v := RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
       + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)).
set s3 := RND (c + z3v).
(* The running sums of the four-limb VecSum: [|s3| <= 20u^2],                 *)
(* [|RN(b1 + s3)| <= 32u^2], [|RN(b0 + ...)| <= 11u].  One step shorter than  *)
(* Algorithm 9's, whose last two inputs are [c] and [z3].                     *)
have Hr3' : Rabs ((vecSumAux [:: s3]).2) <= 20 * (u * u) by exact: Hs3.
have Hr2 : Rabs ((vecSumAux [:: nth 0 bb 1; s3]).2) <= 32 * (u * u).
  rewrite vecSumAux_run_cons.
  have F32 : format (32 * (u * u))
    by apply: (@format_imul_u2 p Hp2 32); have := @two_p_ge_64 p Hp6; lia.
  apply: Rabs_round_le_r => //.
  have Ht := Rabs_triang (nth 0 bb 1) ((vecSumAux [:: s3]).2).
  move: Hb1 Hr3' Ht; nra.
have Hr1 : Rabs ((vecSumAux [:: nth 0 bb 0; nth 0 bb 1; s3]).2) <= 11 * u.
  rewrite vecSumAux_run_cons.
  have F11 : format (11 * u) by apply: Fku; have := @two_p_ge_64 p Hp6; simpl;
    lia.
  apply: Rabs_round_le_r => //.
  have Ht := Rabs_triang (nth 0 bb 0) ((vecSumAux [:: nth 0 bb 1; s3]).2).
  move: Hb0 Hr2 Ht Hu0 Hu64; nra.
have He0 : 3 / 4 <= nth 0 e 0.
  rewrite /e vecSum_nth0 vecSumAux_run_cons.
  have F34 : format (3 / 4).
    have -> : 3 / 4 = IZR 3 * pow (-2) by rewrite /= /Z.pow_pos /=; lra.
    by apply: format_mult_pow; have := @two_p_ge_64 p Hp6; simpl; lia.
  apply: round_le_l => //.
  have Hz00p1 : 1 <= RND (x0 * y0)
    by apply: (@z00p_lb p Hp2 choice x0 x1 x2 y0 y1 y2 Nx Ny).
  rewrite -/c -/z3v -/s3.
  set r1 := (vecSumAux [:: nth 0 bb 0; nth 0 bb 1; s3]).2.
  set z := RND (x0 * y0).
  move: Hr1 Hz00p1; rewrite -/r1 -/z => Hr1 Hz00p1.
  have Hr1c := Rabs_le_inv _ _ Hr1.
  lra.
have HL4f : {in [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; s3],
    forall z, format z}.
  move=> z; rewrite !inE
    => /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]];
    try exact: generic_format_round; exact: Fnthbb.
have Ee : e = vecSum [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; s3]
  by rewrite /e -/c -/z3v -/s3.
(* Every non-head limb is [< 1/2 u]: it is [<= 1/2 ulp] of a running sum      *)
(* smaller than [16u] ([vecSum_err_le_half_ulp_run] + [Hulp16]).              *)
have Hstep : forall k : nat, (k.+1 < 4)%N ->
    Rabs ((vecSumAux
      (drop k [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; s3])).2) < 16 * u ->
    2 * Rabs (nth 0 e k.+1) < u.
  move=> k Hk Hrk.
  have Hle := @vecSum_err_le_half_ulp_run p Hp2 choice choice_sym
    [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; s3] k Hk HL4f.
  rewrite -Ee in Hle.
  have Hw := Hulp16 _ Hrk.
  move: Hle Hw.
  set n := Rabs (nth 0 e k.+1).
  set w := ulp _.
  move=> Hle Hw.
  move: Hle Hw Hu64 Hu0; nra.
have Hdom : forall i, (0 < i)%N -> (i < 4)%N -> 2 * Rabs (nth 0 e i) < u.
  move=> i Hi0 Hi4.
  case: i Hi0 Hi4 => [|[|[|[|i]]]] // _ _.
  - by rewrite He1 Rabs_R0; nra.
  - apply: (Hstep 1%N) => //.
    have -> : drop 1 [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; s3]
      = [:: nth 0 bb 0; nth 0 bb 1; s3] by [].
    by move: Hr1 Hu0; lra.
  - apply: (Hstep 2%N) => //.
    have -> : drop 2 [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; s3]
      = [:: nth 0 bb 1; s3] by [].
    by move: Hr2 Hu0 Hu64; nra.
have Hsz4 : size e = 4%N by rewrite /e size_vecSum.
have Fe : {in e, forall z, format z}
  by rewrite Ee; apply: (@format_vecSum p Hp2 choice); exact: HL4f.
have He0e : e = nth 0 e 0 :: behead e by case: (e) Hsz4 => [|a l].
have Hbeh_dom : forall x, x \in behead e -> 2 * Rabs x < u.
  move=> x xI.
  have [i Hi Hnth] : exists2 i, (i < size (behead e))%N & nth 0 (behead e) i = x
    by apply/(nthP 0).
  have Hnth' : nth 0 (behead e) i = nth 0 e i.+1 by rewrite He0e /=.
  rewrite -Hnth Hnth'.
  have Hi4 : (i.+1 < 4)%N by move: Hi; rewrite size_behead Hsz4.
  case: i Hi Hnth Hnth' Hi4 => [|i'] Hi Hnth Hnth' Hi4.
    by rewrite He1 Rabs_R0; have := u_gt_0; move=> H; nra.
  by apply: Hdom.
by apply: vseb_head3_dom => //; rewrite Hsz4.
Qed.

(* ===========================================================================*)
(*  The star identity [(r0, VSEB(2)) = VSEB(3)] for Algorithm 10: the output  *)
(*  is the first three limbs of [vseb e], with [e = VecSum(z00+, b0, b1, s3)] *)
(*  the pre-truncation VecSum output.  [e1 <> 0] uses [vseb_star]             *)
(*  (structural, reused from ThreeProd.v), [e1 = 0] uses                      *)
(*  [vsebFast_head3_e1zero].                                                  *)
(* ===========================================================================*)
Lemma ThreeProdFast_norm_eq x0 x1 x2 y0 y1 y2 :
  ties_to_even choice -> tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  let bb := vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)] in
  let e := vecSum
    [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
        RND (RND (nth 0 bb 2 + x1 * y1)
           + RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
                + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)))] in
  ThreeProdFast (TWR x0 x1 x2) (TWR y0 y1 y2) =
    TWR (nth 0 (vseb e) 0) (nth 0 (vseb e) 1) (nth 0 (vseb e) 2).
Proof.
move=> Hc Nx' Ny'.
rewrite /ThreeProdFast /TwoProd.
set bb := vecSum [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 *
  y0)].
set e := vecSum [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
  RND (RND (nth 0 bb 2 + x1 * y1)
     + RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
          + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)))].
set el := [:: nth 0 e 1; nth 0 e 2; nth 0 e 3].
have Hmatch : match vsebK 2 el with
    | [::] => TWR (nth 0 e 0) 0 0
    | [:: r1] => TWR (nth 0 e 0) r1 0
    | [:: r1, r2 & _] => TWR (nth 0 e 0) r1 r2
    end = TWR (nth 0 e 0) (nth 0 (vseb el) 0) (nth 0 (vseb el) 1).
  by rewrite /vsebK; case: (vseb el) => [|r1 [|r2 rl]].
rewrite Hmatch.
have Hsz4 : size e = 4%N by rewrite /e size_vecSum.
have Fbb : {in bb, forall z, format z}.
  apply: (@format_vecSum p Hp2 choice) => z; rewrite !inE.
  by move=> /orP[/eqP->|/orP[/eqP->|/eqP->]]; apply: generic_format_round.
have Fnthbb : forall i, format (nth 0 bb i).
  move=> i; case: (ltnP i (size bb)) => Hi;
    last by rewrite nth_default //; exact: generic_format_0.
  by apply: Fbb; apply: mem_nth.
have Hbeh : el = behead e.
  have gen : forall s : seq R, size s = 4%N ->
      behead s = [:: nth 0 s 1; nth 0 s 2; nth 0 s 3].
    by move=> s; case: s => [|a[|b[|c[|d[|f r]]]]].
  by rewrite /el (gen e Hsz4).
have [H0 [H1 H2]] : nth 0 (vseb e) 0 = nth 0 e 0 /\
    nth 0 (vseb e) 1 = nth 0 (vseb (behead e)) 0 /\
    nth 0 (vseb e) 2 = nth 0 (vseb (behead e)) 1.
  case: (Req_dec (nth 0 e 1) 0) => [He1|He1].
    by apply: (vsebFast_head3_e1zero Hc Nx' Ny').
  have FL4 : {in [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
      RND (RND (nth 0 bb 2 + x1 * y1)
         + RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
              + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)))],
      forall z, format z}.
    move=> z; rewrite !inE.
    move=> /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]];
      try apply: generic_format_round; apply: Fnthbb.
  have Hstar := @vseb_star p Hp2 choice choice_sym _ FL4 (isT : (1 < 4)%N) He1.
  have Hs : vseb e = nth 0 e 0 :: vseb (behead e) by exact: Hstar.
  rewrite Hs; split; [exact: erefl | split; exact: erefl].
by rewrite Hbeh H0 H1 H2.
Qed.

(* ===========================================================================*)
(*  Correctness, part 1, normalised (paper WLOG [1 <= x0, y0 < 2]).  The head *)
(*  VecSum is F-nonoverlapping -- and it is LITERALLY Algorithm 9's inner     *)
(*  list, so [inner_head_Fnonoverlap] applies verbatim (its [s3] is           *)
(*  [dwh (TwoSum c z3)], which is [RN(c + z3)] by [TwoSum_hi]) -- hence       *)
(*  [vseb e] is P-nonoverlapping (Theorem 2) and its first three limbs, which *)
(*  are the output by [ThreeProdFast_norm_eq], form a triple word.            *)
(* ===========================================================================*)
Lemma ThreeProdFast_isTW_norm x y :
  ties_to_even choice -> tw_normP x -> tw_normP y -> isTW (ThreeProdFast x y).
Proof.
move=> Hc Nx Ny.
case: x Nx => x0 x1 x2 Nx.
case: y Ny => y0 y1 y2 Ny.
have Nx' : tw_norm x0 x1 x2 by exact: Nx.
have Ny' : tw_norm y0 y1 y2 by exact: Ny.
rewrite (ThreeProdFast_norm_eq Hc Nx' Ny').
set bb := vecSum [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 *
  y0)].
set e := vecSum [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
  RND (RND (nth 0 bb 2 + x1 * y1)
     + RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
          + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)))].
have Hsz4 : size e = 4%N by rewrite /e size_vecSum.
have Fbb : {in bb, forall z, format z}.
  apply: (@format_vecSum p Hp2 choice) => z; rewrite !inE.
  by move=> /orP[/eqP->|/orP[/eqP->|/eqP->]]; apply: generic_format_round.
have Fnthbb : forall i, format (nth 0 bb i).
  move=> i; case: (ltnP i (size bb)) => Hi;
    last by rewrite nth_default //; exact: generic_format_0.
  by apply: Fbb; apply: mem_nth.
have Fe : {in e, forall z, format z}.
  apply: (@format_vecSum p Hp2 choice) => z; rewrite !inE.
  move=> /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]];
    try apply: generic_format_round; apply: Fnthbb.
(* The head VecSum is Algorithm 9's inner list: [inner_head_Fnonoverlap]      *)
(* applies verbatim, its [dwh (TwoSum c z3)] being [RN(c + z3)] ([TwoSum_hi]).*)
have Fno : Fnonoverlap e.
  have H := @inner_head_Fnonoverlap p Hp2 Hp6 choice choice_sym
    x0 x1 x2 y0 y1 y2 Hc Nx' Ny'.
  have H2 : Fnonoverlap (vecSum
    [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
        dwh (TwoSum (RND (nth 0 bb 2 + x1 * y1))
             (RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
                 + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0))))]) by
    exact: H.
  rewrite TwoSum_hi in H2.
  by rewrite /e.
have Pno : Pnonoverlap (vseb e).
  have Hle : (Z.of_nat (size e) <= p + 1)%Z by rewrite Hsz4; lia.
  by have [] := @vseb_Pnonoverlap p Hp2 choice choice_sym e Hle Fe Fno.
apply: Pnonoverlap_isTW3; first exact: Pno.
by apply: (@format_vseb p Hp2 choice e Fe).
Qed.

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
move=> Hc Hx Hy.
case: (Req_dec (tw0 x) 0) => [x0z | x0n].
  rewrite (@isTW_zero_lead p Hp2 x Hx x0z) ThreeProdFast_0l.
  by exact: isTW_TWR000.
case: (Req_dec (tw0 y) 0) => [y0z | y0n].
  rewrite (@isTW_zero_lead p Hp2 y Hy y0z) ThreeProdFast_0r.
  by exact: isTW_TWR000.
have [cx _ [Hxp Hxn]] := @isTW_normalize p Hp2 choice x Hx x0n.
have [cy _ [Hyp Hyn]] := @isTW_normalize p Hp2 choice y Hy y0n.
have Hxsg : 0 < tw0 x \/ tw0 x < 0 by lra.
have Hysg : 0 < tw0 y \/ tw0 y < 0 by lra.
case: Hxsg => Hxs; case: Hysg => Hys.
- rewrite -(@isTW_scale p Hp2 choice (cx + cy)) -ThreeProdFast_scale.
  by apply: ThreeProdFast_isTW_norm => //; [apply: Hxp | apply: Hyp].
- rewrite -(@isTW_opp p (ThreeProdFast x y)).
  rewrite -(@isTW_scale p Hp2 choice (cx + cy)).
  rewrite -ThreeProdFast_opp_r -ThreeProdFast_scale.
  by apply: ThreeProdFast_isTW_norm => //; [apply: Hxp | apply: Hyn].
- rewrite -(@isTW_opp p (ThreeProdFast x y)).
  rewrite -(@isTW_scale p Hp2 choice (cx + cy)).
  rewrite -ThreeProdFast_opp -ThreeProdFast_scale.
  by apply: ThreeProdFast_isTW_norm => //; [apply: Hxn | apply: Hyp].
- rewrite -(@isTW_scale p Hp2 choice (cx + cy)).
  have <- : ThreeProdFast (negTW x) (negTW y) = ThreeProdFast x y.
    by rewrite ThreeProdFast_opp ThreeProdFast_opp_r negTW_id.
  rewrite -ThreeProdFast_scale.
  by apply: ThreeProdFast_isTW_norm => //; [apply: Hxn | apply: Hyn].
Qed.

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
