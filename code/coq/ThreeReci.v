(* ---------------------------------------------------------------------------*)
(* Algorithm 13 (3Reci): the RECIPROCAL of a triple word, computed by one     *)
(* Newton-Raphson step, and its two correctness results -- the result is a    *)
(* triple word ([ThreeReci_isTW]) and the relative error bounds               *)
(* [11.5u^3 + 1465u^4] (accurate variant, [ThreeReci_error]) and              *)
(* [19u^3 + 1502u^4] (fast variant, [ThreeReciFast_error]) -- paper           *)
(* doc/paper3.pdf, Section 8 and Theorem 9 (see doc/thm9.md).  Generic over   *)
(* the precision [p] (FLX, no [emin]); needs [p >= 10].                       *)
(*                                                                            *)
(* The Newton iteration for [1/x] is [r_{n+1} = r_n (2 - r_n x)].  Algorithm  *)
(* 13 starts from [a = RN((1 + 2u)/x0)] -- NOT [RN(1/x0)] -- so that          *)
(* [RN(x0 * a) = 1 + 2u] exactly, which makes the head of                     *)
(* [2 - a * (x0 + x1)] the CONSTANT [h0 = 2 - (1 + 2u) = 1 - 2u] (a virtual   *)
(* word: no operation).  One step in double-word arithmetic gives             *)
(* [b = (b0, b1) ~ 1/x], and one step in triple-word arithmetic, through the  *)
(* DW x TW products of Algorithm 11 or Algorithm 12, gives the result.        *)
(*                                                                            *)
(* Both variants share the definition [ThreeReciAux], parameterised by the    *)
(* [3Prod_{2,3}] it calls: [ThreeReci] uses Algorithm 11 (accurate) and       *)
(* [ThreeReciFast] uses Algorithm 12 (fast).                                  *)
(*                                                                            *)
(* STATUS: SKELETON.  The definition transcribes Algorithm 13 verbatim on top *)
(* of [TwoProd] (Alg 3), [Fast2Sum] (Alg 1) and [ThreeProdDW]/                *)
(* [ThreeProdDWFast] (Alg 11/12); the four theorems are stated and            *)
(* [Admitted].  doc/paper3.pdf gives no proof of Theorem 9 (it is in the      *)
(* supplementary material, which we do not have); the plan is recovered from  *)
(* doc/old-triplewors.pdf Section 8 -- see doc/thm9.md for the full chain.    *)
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
Require Import ThreeProdDWFast.
Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SecThreeReci.

Variable p : Z.
Hypothesis Hp2 : (1 < p)%Z.
(* Algorithm 13 needs the stronger [p >= 10] of paper Section 8: it is what   *)
(* forces the leading limb of [3Prod_{2,3}(b, x)] to be exactly [1], so that  *)
(* [2 - 3Prod_{2,3}(b, x)] is exact (old paper Section 8.3, Remark 9).        *)
Hypothesis Hp10 : (10 <= p)%Z.

(* Algorithms 11 and 12, which Algorithm 13 calls, need [p >= 6].             *)
Lemma Hp6 : (6 <= p)%Z. Proof. lia. Qed.

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
Local Notation Fast2Sum := (Fast2Sum p choice).
Local Notation isTW := (isTW p).
Local Notation isDW := (isDW p).

(* The two DW x TW products of Sections 7.1 and 7.2 (Algorithms 11 and 12).   *)
Local Notation ThreeProdDW := (ThreeProdDW p choice).
Local Notation ThreeProdDWFast := (ThreeProdDWFast p choice).

(* ===========================================================================*)
(*  [2 - x] on triple words                                                   *)
(*                                                                            *)
(*  Algorithm 13 subtracts a triple word from [2] ("i <- 2 - 3Prod(b, x)").   *)
(*  Limb by limb this is [(2 - x0, -x1, -x2)]: the two low limbs are just     *)
(*  negated, and the head subtraction [2 - x0] is EXACT by Sterbenz as soon   *)
(*  as [1 <= x0 <= 2] -- in Algorithm 13 the paper proves the much stronger   *)
(*  [x0 = 1] (old paper Section 8.3), so it costs one operation and no error. *)
(*  The paper even folds it into the multiplication (its Algorithms 16-18);   *)
(*  we keep it explicit, exactly as Algorithm 13 is written.                  *)
(* ===========================================================================*)
Definition sub2TW (x : twR) : twR :=
  let: TWR x0 x1 x2 := x in TWR (2 - x0) (- x1) (- x2).

Lemma TWval_sub2TW x : TWval (sub2TW x) = 2 - TWval x.
Proof. by case: x => x0 x1 x2; rewrite /TWval /=; ring. Qed.

(* ===========================================================================*)
(*  Algorithm 13 -- 3Reci(x0, x1, x2)                                         *)
(*  (73 operations & 2 tests with Algorithm 11, 65 operations & 1 test with   *)
(*  Algorithm 12; paper Section 8).                                           *)
(*                                                                            *)
(*    a    <- RN((1 + 2u) / x0)                                               *)
(*    h11  <- RN(a x0 - (1 + 2u))          (FMA; 2Prod2_{(1+2u)}(a, x0))      *)
(*    h1   <- RN(-h11 - a x1)              (FMA)                              *)
(*    (b01, b11) <- 2Prod(a, 1 - 2u)       (1 - 2u is the virtual h0)         *)
(*    b12  <- RN(b11 + a h1)               (FMA)                              *)
(*    b    <- Fast2Sum(b01, b12)           (a DW)                             *)
(*    i    <- 2 - 3Prod_{2,3}(b, x)                                           *)
(*    y    <- 3Prod_{2,3}(b, i)                                               *)
(*                                                                            *)
(*  [h11] is the error of the product [a x0] taken with respect to [1 + 2u]:  *)
(*  since [RN(a x0) = 1 + 2u], it is exactly [a x0 - (1 + 2u)], so            *)
(*  [(1 + 2u, h11)] is an error-free transform of [a x0] and the pair         *)
(*  [h = (h0, h1) = (1 - 2u, h1)] is a double word approximating              *)
(*  [2 - a (x0 + x1)].                                                        *)
(* ===========================================================================*)
Definition ThreeReciAux (mul : twR -> twR -> twR) (x : twR) : twR :=
  let x0  := tw0 x in
  let x1  := tw1 x in
  let a   := RND ((1 + 2 * u) / x0) in
  let h11 := RND (a * x0 - (1 + 2 * u)) in
  let h1  := RND (- h11 - a * x1) in
  let: (b01, b11) := TwoProd a (1 - 2 * u) in
  let b12 := RND (b11 + a * h1) in
  let b   := Fast2Sum b01 b12 in
  let bw  := TWR (dwh b) (dwl b) 0 in
  mul bw (sub2TW (mul bw x)).

(* The accurate variant: [3Prod_{2,3}] is Algorithm 11.                       *)
Definition ThreeReci (x : twR) : twR := ThreeReciAux ThreeProdDW x.

(* The fast variant: [3Prod_{2,3}] is Algorithm 12.                           *)
Definition ThreeReciFast (x : twR) : twR := ThreeReciAux ThreeProdDWFast x.

(* ===========================================================================*)
(*  The starting point [a = RN((1 + 2u)/x0)] (paper Section 8)                *)
(*                                                                            *)
(*  [1 + 2u] is the SUCCESSOR of [1], and that is exactly what makes          *)
(*  [RN(x * RN((1 + 2u)/x)) = 1 + 2u] hold for EVERY nonzero float [x] -- the *)
(*  fact the paper calls straightforward, and which turns [h0] into the       *)
(*  constant [1 - 2u].  Scaling and sign reduce it to [1 <= x < 2], where     *)
(*  there are three cases: [x = 1] and [x = 1 + 2u] are exact, and for        *)
(*  [x >= 1 + 4u] the quotient lies in [[1/2, 1)], so it is rounded with an   *)
(*  error at most [u/2], which [x < 2] turns into a distance STRICTLY below   *)
(*  the half-ulp [u] of [1 + 2u].                                             *)
(* ===========================================================================*)
(* [p >= 10] caps [u] at [2^-10] -- the counterpart, for Algorithm 13, of the *)
(* [u <= 1/64] that the multiplication algorithms spend their [p >= 6] on.    *)
Lemma u_le_1024 : u <= / 1024.
Proof.
have -> : / 1024 = pow (-10) by rewrite /= /Z.pow_pos /=; lra.
by rewrite (u_pow p); apply: bpow_le; lia.
Qed.

Lemma format_1 : format 1.
Proof. exact: generic_format_FLX_1. Qed.

Lemma succ_1 : succ beta fexp 1 = 1 + 2 * u.
Proof.
rewrite succ_FLX_1.
have -> : (- p + 1 = 1 - p)%Z by lia.
by rewrite (pow_1mp p).
Qed.

Lemma format_1p2u : format (1 + 2 * u).
Proof. by rewrite -succ_1; apply: generic_format_succ; apply: format_1. Qed.

Lemma ulp_1p2u : ulp (1 + 2 * u) = 2 * u.
Proof.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu4 : u <= /4 by have := u_le_1024; lra.
have Hne : 1 + 2 * u <> 0 by lra.
have Hmag : (mag beta (1 + 2 * u) = 1%Z :> Z).
  apply: (mag_unique_pos beta (1 + 2 * u) 1); split.
    have E0 : pow (1 - 1) = 1 by [].
    by rewrite E0; lra.
  have E1 : pow 1 = 2 by [].
  by rewrite E1; lra.
by rewrite ulp_neq_0 // /cexp /fexp Hmag (pow_1mp p).
Qed.

Lemma succ_1p2u : succ beta fexp (1 + 2 * u) = 1 + 4 * u.
Proof.
have Hu0 : 0 < u by apply: u_gt_0.
by rewrite succ_eq_pos ?ulp_1p2u; lra.
Qed.

Lemma pred_1p2u : Ulp.pred beta fexp (1 + 2 * u) = 1.
Proof. by rewrite -succ_1 pred_succ //; apply: format_1. Qed.

(* Anything strictly within the half-ulp [u] of [1 + 2u] rounds to it: the    *)
(* two midpoints are [(1 + pred) / 2 = 1 + u] and [(1 + succ) / 2 = 1 + 3u].  *)
Lemma RN_eq_1p2u t : Rabs (t - (1 + 2 * u)) < u -> RND t = 1 + 2 * u.
Proof.
move=> Ht.
have Hu0 : 0 < u by apply: u_gt_0.
have [Ht1 Ht2] := Rabs_def2 _ _ Ht.
apply: Rle_antisym.
  by apply: round_N_le_midp; [apply: format_1p2u | rewrite succ_1p2u; lra].
by apply: round_N_ge_midp; [apply: format_1p2u | rewrite pred_1p2u; lra].
Qed.

(* The normalised case [1 <= x < 2].                                          *)
Lemma round_div_1p2u_norm x :
  format x -> 1 <= x < 2 -> RND (x * RND ((1 + 2 * u) / x)) = 1 + 2 * u.
Proof.
move=> Fx [Hx1 Hx2].
have Hu0 : 0 < u by apply: u_gt_0.
have Hu4 : u <= /4 by have := u_le_1024; lra.
have F1 : format 1 by apply: format_1.
have F12u : format (1 + 2 * u) by apply: format_1p2u.
have [Hxe1 | Hxn1] := Req_dec x 1.
  rewrite Hxe1 Rmult_1_l.
  have -> : (1 + 2 * u) / 1 = 1 + 2 * u by field.
  by rewrite !round_generic.
have Hx12u : 1 + 2 * u <= x by rewrite -succ_1; apply: succ_le_lt => //; lra.
have [Hxe2 | Hxn2] := Req_dec x (1 + 2 * u).
  have -> : (1 + 2 * u) / x = 1 by rewrite Hxe2; field; lra.
  by rewrite [RND 1]round_generic // Rmult_1_r Hxe2 round_generic.
have Hx14u : 1 + 4 * u <= x by rewrite -succ_1p2u; apply: succ_le_lt => //; lra.
set v := (1 + 2 * u) / x.
have Hxn0 : x <> 0 by lra.
have Hv1 : /2 <= v.
  rewrite /v; apply: (Rmult_le_reg_r x) => //; first by lra.
  by rewrite /Rdiv Rmult_assoc Rinv_l //; lra.
have Hv2 : v < 1.
  rewrite /v; apply: (Rmult_lt_reg_r x); first by lra.
  by rewrite /Rdiv Rmult_assoc Rinv_l //; nra.
have Hvn0 : v <> 0 by lra.
have Hmagv : (mag beta v = 0%Z :> Z).
  apply: (mag_unique_pos beta v 0); split.
    have E0 : pow (0 - 1) = /2 by rewrite /= /Z.pow_pos /=; lra.
    by rewrite E0.
  have E1 : pow 0 = 1 by [].
  by rewrite E1.
have Hulpv : ulp v = u.
  by rewrite ulp_neq_0 // /cexp /fexp Hmagv (u_pow p); congr (pow _); lia.
have Herr : Rabs (RND v - v) <= /2 * ulp v by apply: error_le_half_ulp.
rewrite Hulpv in Herr.
apply: RN_eq_1p2u.
have -> : x * RND v - (1 + 2 * u) = x * (RND v - v) by rewrite /v; field.
rewrite Rabs_mult (Rabs_pos_eq x); last by lra.
have := Rabs_pos (RND v - v).
nra.
Qed.

(* The general case, by scaling to [[1, 2)] and by sign symmetry.             *)
Lemma round_div_1p2u x :
  format x -> x <> 0 -> RND (x * RND ((1 + 2 * u) / x)) = 1 + 2 * u.
Proof.
move=> Fx Hxn0.
wlog Hxpos : x Fx Hxn0 / 0 < x => [Hw|].
  have [Hpos|Hneg] := Rlt_le_dec 0 x; first by apply: Hw.
  have Hn : - x <> 0 by lra.
  have Fn : format (- x) by apply: generic_format_opp.
  have H := Hw (- x) Fn Hn ltac:(lra).
  have Hopp2 : (1 + 2 * u) / x = - ((1 + 2 * u) / - x) by field.
  rewrite Hopp2 RN_sym; last by exact: choice_sym.
  have -> : x * - RND ((1 + 2 * u) / - x) = - x * RND ((1 + 2 * u) / - x)
    by ring.
  exact: H.
(* Scale [x] into [[1, 2)]: both the division and the product commute with a  *)
(* power of two ([round_bpow_FLX]), so the normalised case suffices.          *)
set e := (mag beta x - 1)%Z.
have Hep : pow e <= x.
  have := bpow_mag_le beta x Hxn0; rewrite (Rabs_pos_eq x); last by lra.
  by rewrite /e.
have Hes : x < pow (e + 1).
  have -> : (e + 1 = mag beta x)%Z by rewrite /e; lia.
  by have := bpow_mag_gt beta x; rewrite (Rabs_pos_eq x); last by lra.
set y := x * pow (- e).
have Hpe0 : 0 < pow e by apply: bpow_gt_0.
have Hy1 : 1 <= y.
  rewrite /y bpow_opp; apply: (Rmult_le_reg_r (pow e)) => //.
  by rewrite Rmult_1_l Rmult_assoc Rinv_l; lra.
have Hy2 : y < 2.
  rewrite /y bpow_opp; apply: (Rmult_lt_reg_r (pow e)) => //.
  rewrite Rmult_assoc Rinv_l ?Rmult_1_r; last by lra.
  by move: Hes; rewrite bpow_plus; have -> : pow 1 = 2 by []; lra.
have Fy : format y by rewrite /y; apply/format_scale.
have Hxy : x = y * pow e.
  rewrite /y Rmult_assoc -bpow_plus.
  have -> : (- e + e = 0)%Z by lia.
  by have -> : pow 0 = 1 by []; rewrite Rmult_1_r.
have Hyn0 : y <> 0 by lra.
have -> : (1 + 2 * u) / x = ((1 + 2 * u) / y) * pow (- e).
  by rewrite {1}Hxy bpow_opp; field; split; lra.
rewrite round_bpow_FLX.
have -> : x * (RND ((1 + 2 * u) / y) * pow (- e)) = y * RND ((1 + 2 * u) / y).
  by rewrite {1}Hxy bpow_opp; field; lra.
by apply: round_div_1p2u_norm.
Qed.

(* ===========================================================================*)
(*  Correctness, part 1: the result is a triple-word number.                  *)
(*                                                                            *)
(*  Both products are calls to Algorithm 11 (resp. 12), whose result is a TW  *)
(*  ([ThreeProdDW_isTW], [ThreeProdDWFast_isTW]) as soon as the first         *)
(*  argument is a DW and the second one a TW.  So part 1 amounts to:          *)
(*  (i) [b = Fast2Sum(b01, b12)] is a DW -- the Fast2Sum ordering hypothesis  *)
(*      holds because [|b12| <= u |b01|] (doc/thm9.md);                       *)
(*  (ii) [sub2TW] preserves [isTW], which needs [2 - i0] to keep the same     *)
(*      ulp as [i0], i.e. the [i0 = 1] of old paper Section 8.3.              *)
(* ===========================================================================*)
Lemma ThreeReci_isTW x :
  ties_to_even choice ->
  isTW x -> tw0 x <> 0 -> isTW (ThreeReci x).
Proof.
Admitted.

Lemma ThreeReciFast_isTW x :
  ties_to_even choice ->
  isTW x -> tw0 x <> 0 -> isTW (ThreeReciFast x).
Proof.
Admitted.

(* ===========================================================================*)
(*  Correctness, part 2: the relative error (paper Theorem 9).                *)
(*                                                                            *)
(*  Following old paper Section 8.2, with [d1] the relative error of the      *)
(*  first product (taken relatively to [x b]) and [d2] that of the second     *)
(*  one:                                                                      *)
(*                                                                            *)
(*    |y - 1/x| <= (d1 (1 + 71u^2) + d2 (1 + 107u^2) + 1172u^4) |1/x|         *)
(*                                                                            *)
(*  where [1172u^4] is the quadratic Newton residue [|x| (b - 1/x)^2] coming  *)
(*  from [|b - 1/x| <= (34u^2 + 115u^3)|1/x|].  Here [d1] is Theorem 8's      *)
(*  [10.5u^3 + 39u^4] (resp. Algorithm 12's [18u^3 + 75u^4]), while [d2] is   *)
(*  ONE u^3 only -- the second product is [b] times a triple word whose head  *)
(*  is [1] and whose second limb is [O(u^2)], so its error is essentially the *)
(*  final truncation to three limbs.  Whence [11.5 = 10.5 + 1] and            *)
(*  [19 = 18 + 1].                                                            *)
(* ===========================================================================*)
Lemma ThreeReci_error x :
  ties_to_even choice ->
  isTW x -> tw0 x <> 0 ->
  Rabs (TWval (ThreeReci x) - / TWval x) <=
     (115 / 10 * (u * u * u) + 1465 * (u * u * u * u)) *
       Rabs (/ TWval x).
Proof.
Admitted.

Lemma ThreeReciFast_error x :
  ties_to_even choice ->
  isTW x -> tw0 x <> 0 ->
  Rabs (TWval (ThreeReciFast x) - / TWval x) <=
     (19 * (u * u * u) + 1502 * (u * u * u * u)) *
       Rabs (/ TWval x).
Proof.
Admitted.

End SecThreeReci.
