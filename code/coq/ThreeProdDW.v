(* ---------------------------------------------------------------------------*)
(* Algorithm 11 (3Prod^acc_{2,3}): the product of a DOUBLE word by a triple   *)
(* word, and its two correctness results -- the result is a triple word       *)
(* ([ThreeProdDW_isTW]) and the relative error bound [10.5u^3 + 39u^4]        *)
(* ([ThreeProdDW_error]) -- paper Theorem 8 (doc/paper3.pdf, Section 7; see   *)
(* doc/thm8.md).  Generic over the precision [p] (FLX, no [emin]); needs      *)
(* [p >= 6].                                                                  *)
(*                                                                            *)
(* Algorithm 11 IS Algorithm 9 ([ThreeProd.v]) with [x2 = 0]: the FMA         *)
(* [z32 = RN(z01- + x2 y0)] collapses to [z01-] (a float), saving one         *)
(* operation.  Correctness is therefore inherited from Theorem 7; the error   *)
(* bound is not -- taking [x2 = 0] into account gives [10.5u^3 + 39u^4]       *)
(* instead of [28u^3 + 107u^4].                                               *)
(*                                                                            *)
(* STATUS: [ThreeProdDW_isTW] is PROVED (it is Theorem 7 at [x2 = 0]);        *)
(* [ThreeProdDW_error] is still [Admitted].  The definition transcribes       *)
(* Algorithm 11 verbatim on top of [TwoProd] (Alg 3), [vecSum] (Alg 4) and    *)
(* [vsebK] (Alg 5).  doc/paper3.pdf omits the proof of Theorem 8 altogether;  *)
(* it is recovered from doc/old-triplewors.pdf Section 7.4 -- see             *)
(* doc/thm8.md for the full plan.                                             *)
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

Section SecThreeProdDW.

Variable p : Z.
Hypothesis Hp2 : (1 < p)%Z.
(* Algorithm 11, like Algorithm 9, needs [p >= 6] (paper Section 7).          *)
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

(* Algorithm 9, of which Algorithm 11 is the [x2 = 0] case.                   *)
Local Notation ThreeProd := (ThreeProd p choice).

(* The paper's normalisation [1 <= x0, y0 < 2] and its triple-word packing,   *)
(* both from ThreeProd.v.                                                     *)
Local Notation tw_norm := (tw_norm p).
Local Notation tw_normP := (tw_normP p).

(* ===========================================================================*)
(*  Double-word numbers (paper Definition 3): a pair of floats with           *)
(*  [2|x1| <= ulp x0] -- the standard [x0 = RN(x0 + x1)] separation, STRICTER *)
(*  than the P-nonoverlapping [|x1| < ulp x0] of a triple word.  It is        *)
(*  packaged as a [twR] with a zero third limb, so that Algorithm 9's         *)
(*  machinery (scaling, sign, [isTW]) applies unchanged.                      *)
(* ===========================================================================*)
Definition isDW (x : twR) : Prop :=
  let: TWR x0 x1 x2 := x in
  [/\ format x0, format x1, x2 = 0 & x1 = 0 \/ 2 * Rabs x1 <= ulp x0].

(* ===========================================================================*)
(*  Algorithm 11 -- 3Prod^acc_{2,3}(x, y)                                     *)
(*  (45 operations & 2 tests; paper Section 7).                               *)
(*                                                                            *)
(*  The first five lines are those of Algorithm 9 ([ThreeProd]); then         *)
(*  [z3 = RN(z31 + z01-)] replaces Algorithm 9's [RN(z31 + z32)], since       *)
(*  [z32 = RN(z01- + x2 y0) = z01-] when [x2 = 0].  The third limb of the     *)
(*  first argument is ignored -- it is [0] for a [isDW] input.                *)
(* ===========================================================================*)
Definition ThreeProdDW (x y : twR) : twR :=
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
  let e := vecSum [:: z00p; b0; b1; c; z3] in
  let e0 := nth 0 e 0 in
  match vsebK 2 [:: nth 0 e 1; nth 0 e 2; nth 0 e 3; nth 0 e 4] with
  | [:: r1, r2 & _] => TWR e0 r1 r2
  | [:: r1]         => TWR e0 r1 0
  | [::]            => TWR e0 0 0
  end.

(* A double word is a triple word with a zero third limb: the DW separation   *)
(* [2|x1| <= ulp x0] is stronger than the P-nonoverlapping [|x1| < ulp x0].   *)
Lemma isDW_isTW x : isDW x -> isTW x.
Proof.
case: x => x0 x1 x2 [F0 F1 -> Hsep].
split=> //; first exact: generic_format_0.
- case: Hsep => [->|Hs]; first by left.
  case: (Req_dec x1 0) => [->|Hx1n]; first by left.
  by right; have := Rabs_pos_lt _ Hx1n; lra.
- by left.
Qed.

(* ===========================================================================*)
(*  Algorithm 11 IS Algorithm 9 at [x2 = 0]: the only difference is           *)
(*  [z32 = RN(z01- + 0 * y0) = z01-], since [z01-] is a rounded value, hence  *)
(*  a float ([round_generic]).  This is the paper's                           *)
(*  "Algorithm 11 is a particular case of Algorithm 9".                       *)
(* ===========================================================================*)
Lemma ThreeProdDW_eq x y :
  ThreeProdDW x y = ThreeProd (TWR (tw0 x) (tw1 x) 0) y.
Proof.
case: x => x0 x1 x2; case: y => y0 y1 y2.
rewrite /ThreeProdDW /ThreeProd.
have F01m : format (TwoProd x0 y1).2 by apply: generic_format_round.
case E00 : (TwoProd x0 y0) => [z00p z00m].
case E01 : (TwoProd x0 y1) => [z01p z01m].
case E10 : (TwoProd x1 y0) => [z10p z10m].
have F01 : format z01m by move: F01m; rewrite E01.
by rewrite Rmult_0_l Rplus_0_r (round_generic _ _ _ _ F01).
Qed.

(* ===========================================================================*)
(*  Correctness, part 1: [ThreeProdDW x y] is a triple-word number.           *)
(*                                                                            *)
(*  Paper Section 7.1: since Algorithm 11 is a particular case of Algorithm   *)
(*  9, correctness is directly ensured for [p >= 6].  Formally                *)
(*  [ThreeProdDW x y = ThreeProd (TWR (tw0 x) (tw1 x) 0) y] -- the only       *)
(*  difference, [RN(z01- + 0 * y0) = z01-], is [round_generic] on             *)
(*  [format_err_mul] -- and a DW is a TW with a zero third limb.              *)
(* ===========================================================================*)
Lemma ThreeProdDW_isTW x y :
  ties_to_even choice ->
  isDW x -> isTW y -> isTW (ThreeProdDW x y).
Proof.
move=> Hc Hx Hy.
rewrite ThreeProdDW_eq.
apply: (@ThreeProd_isTW p Hp2 Hp6 choice choice_sym) => //.
have Hx' := isDW_isTW Hx.
by case: x Hx Hx' => x0 x1 x2 [_ _ -> _].
Qed.

(* ===========================================================================*)
(*  Theorem 8: relative error of [ThreeProdDW] is [<= 10.5u^3 + 39u^4].       *)
(*                                                                            *)
(*  Proof OMITTED in doc/paper3.pdf; recovered from doc/old-triplewors.pdf    *)
(*  Section 7.4 (Theorem 11) -- see doc/thm8.md.  With [x2 = 0] the error     *)
(*  sources shrink to                                                         *)
(*                                                                            *)
(*    |eps0| = |x1 y2| <= 2u^3 - 2u^4     (and [|x1| <= u], a DW)             *)
(*    |eps1| = |(z10- + x0 y2) - z31| <= 4u^3                                 *)
(*    |eps3| = |(z31 + z01-) - z3|    <= 4u^3       (there is NO eps2)        *)
(*    |eps4| = |(b2 + x1 y1) - c|     <= 4u^3                                 *)
(*    |eps5| <= (2u^3 + 4.2u^4)|z00+ + b0 + b1 + c + z3|                      *)
(*                                                                            *)
(*  giving a naive [16u^3 + 62u^4]; the paper's [10.5u^3 + 39u^4] needs two   *)
(*  refinements (a large [eps1] or [eps4] forces [x*y >= 1.5 - 6u], and       *)
(*  [eps5 <> 0] forces one of the terms below [u^2]) and a five-case          *)
(*  assembly.                                                                 *)
(* ===========================================================================*)
Lemma ThreeProdDW_error x y :
  ties_to_even choice ->
  isDW x -> isTW y ->
  Rabs (TWval (ThreeProdDW x y) - TWval x * TWval y) <=
     (105 / 10 * (u * u * u) + 39 * (u * u * u * u)) *
       Rabs (TWval x * TWval y).
Proof.
Admitted.

End SecThreeProdDW.
