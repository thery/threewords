(* ---------------------------------------------------------------------------*)
(* Algorithms 18 and 20 (3Prod^one): the product of a double word (Alg 18)   *)
(* resp. a TRIPLE word (Alg 20) by a triple word                              *)
(* whose leading limb is exactly [1], and its two correctness results -- the  *)
(* result is a triple word ([ThreeProdOne_isTW]) and the relative error is    *)
(* [u^3 + 260u^4] ([ThreeProdOne_error]), an order of magnitude sharper than  *)
(* Theorem 8's [10.5u^3].  This is the SECOND product of Algorithm 13         *)
(* (doc/paper3.pdf Section 8): there [i = 2 - 3Prod_{2,3}(b, x)] has head [1] *)
(* and tail [O(u^2)], and it is this sharper bound that makes Theorem 9's     *)
(* [11.5 = 10.5 + 1] and [19 = 18 + 1].  See doc/old-triplewors.pdf Section   *)
(* 8.4 and doc/thm9.md.  Generic over the precision [p] (FLX); needs [p >= 6].*)
(*                                                                            *)
(* Why it is so much sharper: [y0 = 1] is VIRTUAL (it costs no operation and  *)
(* no error), the inner VecSum has only THREE entries -- so there is no VSEB  *)
(* truncation, which is [2u^3] of Theorem 8's budget -- and every remaining   *)
(* error source is [O(u^4)] except the rounding of [s3].                      *)
(*                                                                            *)
(* ONE DEVIATION FROM THE PAPER, and it is necessary.  Algorithm 18 sums      *)
(* [b1] and [z01+] with a Fast2Sum, justified by its Remark 10 -- if the      *)
(* condition to be errorless is false, it means that [b1] is very small, so   *)
(* that the global error will be small anyway.  That is FALSE: the           *)
(* condition fails exactly when [|b1| < |z01+|], and the worst case is        *)
(* [|b1| ~ ulp(z01+)], where [b1] is absorbed and what is lost is             *)
(* [~ u|z01+| ~ 41u^3], not [O(u^4)].  doc/alg18_fast2sum_bug.py exhibits     *)
(* legal inputs reaching [32u^3] in binary64, i.e. 32 times the claimed       *)
(* [delta2].  The SAME defect sits in its last line, [Fast2Sum(e1, e2)]:      *)
(* [|e1| < |e2|] is legal (the top 2Sum of the inner VecSum can be exact      *)
(* while the lower one is not) and costs [~3u^3].                             *)
(*                                                                            *)
(* Both are repaired at no operation cost by SORTING the two arguments        *)
(* first: [Fast2SumS] (TwoSum.v) is a Fast2Sum preceded by one test, and is   *)
(* error-free unconditionally.  Algorithm 18 keeps its 20 operations and      *)
(* gains 2 tests -- and the paper's [delta2] then holds.                      *)
(*                                                                            *)
(* STATUS: Algorithm 18 is COMPLETE (zero admits).  Algorithm 20 -- its      *)
(* [3,3] twin, which Theorem 10 (3Div) needs for its final product -- is      *)
(* stated and ADMITTED (skeleton).                                            *)
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
Require Import ThreeProdDW.
Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SecThreeProdOne.

Variable p : Z.
Hypothesis Hp2 : (1 < p)%Z.
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

Local Notation TwoProd := (TwoProd p radix2 rnd).
Local Notation TwoSum := (TwoSum p choice).
Local Notation Fast2Sum := (Fast2Sum p choice).
Local Notation Fast2SumS := (Fast2SumS p choice).
Local Notation vecSumAux := (vecSumAux p choice).
Local Notation vecSum := (vecSum p choice).
Local Notation Pnonoverlap := (Pnonoverlap p).
Local Notation Fnonoverlap := (Fnonoverlap p).
Local Notation isTW := (isTW p).
Local Notation isDW := (isDW p).
Local Notation dw_norm := (dw_norm p).
Local Notation dw_normP := (dw_normP p).
Local Notation tw_norm := (tw_norm p).
Local Notation tw_normP := (tw_normP p).

(* ===========================================================================*)
(*  Algorithm 18 -- 3Prod^one(x, y) with [y0 = 1] VIRTUAL                     *)
(*  (21 operations; old paper Section 8.4).                                   *)
(*                                                                            *)
(*    z01+, z01- <- 2Prod(x0, y1)                                             *)
(*    b'0, b'1   <- Fast2SumS(x1, z01+)     (the paper's Fast2Sum, SORTED)    *)
(*    z31 <- RN(z01- + x1 y1)               (FMA)                             *)
(*    z3  <- RN(z31 + x0 y2)                (FMA)                             *)
(*    s3  <- RN(b'1 + z3)                                                     *)
(*    e0, e1, e2 <- VecSum(x0, b'0, s3)                                       *)
(*    y0 <- e0 ;  y1, y2 <- Fast2SumS(e1, e2)                                 *)
(*                                                                            *)
(*  The leading limb of [y] is IGNORED -- the algorithm is only correct when  *)
(*  it is [1], which is what its callers guarantee.  The third limb of [x] is *)
(*  ignored too: [x] is a double word.                                        *)
(* ===========================================================================*)
(* One definition per line of the algorithm, so that every intermediate      *)
(* quantity can be bounded without ever unfolding [ThreeProdOne] (the same    *)
(* discipline as [reciA]/[reciB] in ThreeReci.v).  [x0], [x1] are the double  *)
(* word, [y1], [y2] the tail of the triple word whose head is [1].            *)
Definition p18z01p (x0 y1 : R) : R := RND (x0 * y1).

Definition p18z01m (x0 y1 : R) : R := RND (x0 * y1 - p18z01p x0 y1).

Definition p18b (x0 x1 y1 : R) : dwR := Fast2SumS x1 (p18z01p x0 y1).

Definition p18z31 (x0 x1 y1 : R) : R := RND (p18z01m x0 y1 + x1 * y1).

Definition p18z3 (x0 x1 y1 y2 : R) : R := RND (p18z31 x0 x1 y1 + x0 * y2).

Definition p18s3 (x0 x1 y1 y2 : R) : R :=
  RND (dwl (p18b x0 x1 y1) + p18z3 x0 x1 y1 y2).

Definition p18e (x0 x1 y1 y2 : R) : seq R :=
  vecSum [:: x0; dwh (p18b x0 x1 y1); p18s3 x0 x1 y1 y2].

(* The three limbs of that VecSum, named so that unfolding [ThreeProdOne]     *)
(* does not force the concrete list to compute.                               *)
Definition p18e0 (x0 x1 y1 y2 : R) : R := nth 0 (p18e x0 x1 y1 y2) 0.
Definition p18e1 (x0 x1 y1 y2 : R) : R := nth 0 (p18e x0 x1 y1 y2) 1.
Definition p18e2 (x0 x1 y1 y2 : R) : R := nth 0 (p18e x0 x1 y1 y2) 2.

Definition ThreeProdOne (x y : twR) : twR :=
  let: TWR x0 x1 _ := x in
  let: TWR _ y1 y2 := y in
  let: DWR r1 r2 :=
     Fast2SumS (p18e1 x0 x1 y1 y2) (p18e2 x0 x1 y1 y2) in
  TWR (p18e0 x0 x1 y1 y2) r1 r2.

(* ===========================================================================*)
(*  The term bounds, relative to [|x0|] -- no normalisation is needed here,   *)
(*  since every quantity is a fixed multiple of [|x0|].  With [|y1| <= 2u]    *)
(*  (the second argument has head [1]) and [|x1| <= u|x0|] (a double word):   *)
(*                                                                            *)
(*    |z01+| <= 3u|x0|      |z01-| <= 2u^2|x0|     |b'0| <= 6u|x0|            *)
(*    |b'1|  <= 6u^2|x0|     |z3,1| <= 7u^2|x0|     |z3|  <= 12u^2|x0|        *)
(*    |s3|   <= 19u^2|x0|    |s3 (Alg 20)| <= 24u^2|x0|                       *)
(*                                                                            *)
(*  The hypothesis on [x1] is the TRIPLE word one, [|x1| <= 2u|x0|], so that  *)
(*  Algorithms 18 and 20 share these bounds; a double word satisfies it a     *)
(*  fortiori.                                                                 *)
(* ===========================================================================*)

Lemma p18z01p_le x0 y1 :
  Rabs y1 <= 2 * u -> Rabs (p18z01p x0 y1) <= 3 * u * Rabs x0.
Proof.
move=> Hy1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := @u_le_64 p Hp6.
apply: Rle_trans (@abs_round_le_rel p Hp2 choice _) _.
rewrite Rabs_mult.
have Hx := Rabs_pos x0.
have Hkey : 0 <= Rabs x0 * (u * (1 - 2 * u)) by apply: Rmult_le_pos; nra.
have H2 : Rabs x0 * Rabs y1 <= Rabs x0 * (2 * u) by apply: Rmult_le_compat_l.
nra.
Qed.

Lemma p18z01m_le x0 y1 :
  format x0 -> format y1 -> Rabs y1 <= 2 * u ->
  Rabs (p18z01m x0 y1) <= 2 * (u * u) * Rabs x0.
Proof.
move=> Fx0 Fy1 Hy1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := @u_le_64 p Hp6.
rewrite /p18z01m /p18z01p round_generic; last first.
  rewrite (_ : x0 * y1 - RND (x0 * y1) = -(RND (x0 * y1) - x0 * y1));
    last by ring.
  by apply: generic_format_opp; apply: format_err_mul.
have He : Rabs (RND (x0 * y1) - x0 * y1) <= u * Rabs (x0 * y1).
  by apply: (@relative_error_le p beta Hp2 choice).
rewrite Rabs_minus_sym Rabs_mult in He *.
have Hx := Rabs_pos x0.
have H2 : Rabs x0 * Rabs y1 <= Rabs x0 * (2 * u) by apply: Rmult_le_compat_l.
nra.
Qed.

Lemma p18b0_le x0 x1 y1 :
  Rabs x1 <= 2 * u * Rabs x0 -> Rabs y1 <= 2 * u ->
  Rabs (dwh (p18b x0 x1 y1)) <= 6 * u * Rabs x0.
Proof.
move=> Hx1 Hy1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := @u_le_64 p Hp6.
have Hz := p18z01p_le x0 Hy1.
rewrite /p18b Fast2SumS_hi.
apply: Rle_trans (@abs_round_le_rel p Hp2 choice _) _.
have T := Rabs_triang x1 (p18z01p x0 y1).
have Hx := Rabs_pos x0.
have Hkey : 0 <= Rabs x0 * (u * (1 - 5 * u)) by apply: Rmult_le_pos; nra.
nra.
Qed.

Lemma p18b1_le x0 x1 y1 :
  format x1 -> Rabs x1 <= 2 * u * Rabs x0 -> Rabs y1 <= 2 * u ->
  Rabs (dwl (p18b x0 x1 y1)) <= 6 * (u * u) * Rabs x0.
Proof.
move=> Fx1 Hx1 Hy1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := @u_le_64 p Hp6.
have Hb0 := p18b0_le Hx1 Hy1.
have Fz : format (p18z01p x0 y1) by apply: generic_format_round.
have Hm : Rabs (dwl (p18b x0 x1 y1)) <= ulp (dwh (p18b x0 x1 y1)) / 2.
  rewrite /p18b.
  have := @magnitude_Fast2SumS p Hp2 choice x1 (p18z01p x0 y1) Fx1 Fz.
  by rewrite /magnitudeDWR; case: TwoSum.Fast2SumS.
have Hulp := @ulp_2u p beta Hp2 (dwh (p18b x0 x1 y1)).
have Hx := Rabs_pos x0.
have Hb0p := Rabs_pos (dwh (p18b x0 x1 y1)).
nra.
Qed.

Lemma p18z31_le x0 x1 y1 :
  format x0 -> format y1 -> Rabs x1 <= 2 * u * Rabs x0 -> Rabs y1 <= 2 * u ->
  Rabs (p18z31 x0 x1 y1) <= 7 * (u * u) * Rabs x0.
Proof.
move=> Fx0 Fy1 Hx1 Hy1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := @u_le_64 p Hp6.
have Hz01m := p18z01m_le Fx0 Fy1 Hy1.
rewrite /p18z31.
apply: Rle_trans (@abs_round_le_rel p Hp2 choice _) _.
have T := Rabs_triang (p18z01m x0 y1) (x1 * y1).
have Hx := Rabs_pos x0.
have Hxy : Rabs (x1 * y1) <= 4 * (u * u) * Rabs x0.
  rewrite Rabs_mult.
  have Hx1p := Rabs_pos x1.
  have H2 : Rabs x1 * Rabs y1 <= (2 * u * Rabs x0) * (2 * u).
    by apply: Rmult_le_compat => //; apply: Rabs_pos.
  nra.
have Hkey : 0 <= Rabs x0 * (u * u * (1 - 6 * u)) by apply: Rmult_le_pos; nra.
nra.
Qed.

Lemma p18z3_le x0 x1 y1 y2 :
  format x0 -> format y1 -> Rabs x1 <= 2 * u * Rabs x0 -> Rabs y1 <= 2 * u ->
  Rabs y2 <= 4 * (u * u) ->
  Rabs (p18z3 x0 x1 y1 y2) <= 12 * (u * u) * Rabs x0.
Proof.
move=> Fx0 Fy1 Hx1 Hy1 Hy2.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := @u_le_64 p Hp6.
have Hz31 := p18z31_le Fx0 Fy1 Hx1 Hy1.
rewrite /p18z3.
apply: Rle_trans (@abs_round_le_rel p Hp2 choice _) _.
have T := Rabs_triang (p18z31 x0 x1 y1) (x0 * y2).
have Hxy : Rabs (x0 * y2) <= 4 * (u * u) * Rabs x0.
  rewrite Rabs_mult.
  have Hx := Rabs_pos x0.
  have H2 : Rabs x0 * Rabs y2 <= Rabs x0 * (4 * (u * u))
    by apply: Rmult_le_compat_l.
  nra.
have Hx := Rabs_pos x0.
have Hkey : 0 <= Rabs x0 * (u * u * (1 - 11 * u)) by apply: Rmult_le_pos; nra.
nra.
Qed.

Lemma p18s3_le x0 x1 y1 y2 :
  format x0 -> format x1 -> format y1 ->
  Rabs x1 <= 2 * u * Rabs x0 -> Rabs y1 <= 2 * u -> Rabs y2 <= 4 * (u * u) ->
  Rabs (p18s3 x0 x1 y1 y2) <= 19 * (u * u) * Rabs x0.
Proof.
move=> Fx0 Fx1 Fy1 Hx1 Hy1 Hy2.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := @u_le_64 p Hp6.
have Hb1 := p18b1_le Fx1 Hx1 Hy1.
have Hz3 := p18z3_le Fx0 Fy1 Hx1 Hy1 Hy2.
rewrite /p18s3.
apply: Rle_trans (@abs_round_le_rel p Hp2 choice _) _.
have T := Rabs_triang (dwl (p18b x0 x1 y1)) (p18z3 x0 x1 y1 y2).
have Hx := Rabs_pos x0.
have Hkey : 0 <= Rabs x0 * (u * u * (1 - 18 * u)) by apply: Rmult_le_pos; nra.
nra.
Qed.

(* Correctness, part 1: the result is a triple word.  The head limb and the   *)
(* pair below it are separated by the inner VecSum's own half-ulp             *)
(* ([vecSum_head_sep]), and the pair itself is a double word ([Fast2Sum]).    *)
Lemma ThreeProdOne_isTW x y :
  ties_to_even choice ->
  isDW x -> isTW y -> tw0 y = 1 -> isTW (ThreeProdOne x y).
Proof.
(* The head of the inner VecSum and its two low limbs, by computation.        *)
have He0 : forall x0 x1 y1 y2, p18e0 x0 x1 y1 y2
    = RND (x0 + RND (dwh (p18b x0 x1 y1) + p18s3 x0 x1 y1 y2)) by [].
have He2 : forall x0 x1 y1 y2, p18e2 x0 x1 y1 y2
    = dwl (TwoSum (dwh (p18b x0 x1 y1)) (p18s3 x0 x1 y1 y2)) by [].
move=> Hc Hx Hy Hy0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := @u_le_64 p Hp6.
case: x Hx => x0 x1 x2 [Fx0 Fx1 Hx2 Hsep].
case: y Hy Hy0 => y0 y1 y2 [Fy0 Fy1 Fy2 Hys1 Hys2] /= Hy0.
rewrite Hy0 in Hys1.
(* What the two arguments give: [|x1| <= u|x0|] (a double word) and, since    *)
(* the second argument has head [1], [|y1| <= 2u] and [|y2| <= 4u^2].         *)
have Hx1 : Rabs x1 <= u * Rabs x0.
  case: Hsep => [->|Hs]; first by rewrite Rabs_R0; have := Rabs_pos x0; nra.
  by have := @ulp_2u p beta Hp2 x0; lra.
have Hy1 : Rabs y1 <= 2 * u.
  case: Hys1 => [->|Hs]; first by rewrite Rabs_R0; lra.
  by move: Hs; rewrite (@ulp_one p); lra.
have Hy2 : Rabs y2 <= 4 * (u * u).
  case: Hys2 => [->|Hs]; first by rewrite Rabs_R0; nra.
  have Hu2 := @ulp_2u p beta Hp2 y1.
  by have := Rabs_pos y1; nra.
have Fb0 : format (dwh (p18b x0 x1 y1)).
  by rewrite /p18b Fast2SumS_hi; apply: generic_format_round.
have Fs3 : format (p18s3 x0 x1 y1 y2) by apply: generic_format_round.
have Fin : {in [:: x0; dwh (p18b x0 x1 y1); p18s3 x0 x1 y1 y2],
             forall z : R, format z}.
  by move=> z; rewrite !inE => /or3P[] /eqP->.
have Fe : forall i, format (nth 0 (p18e x0 x1 y1 y2) i).
  move=> i; case: (ltnP i (size (p18e x0 x1 y1 y2))) => Hi;
    last by rewrite nth_default //; exact: generic_format_0.
  by apply: (@format_vecSum p Hp2 choice) Fin _ _; apply: mem_nth.
(* The genuine HALF ulp between the two leading limbs of a VecSum.            *)
have Hsep1 := @vecSum_head_sep p Hp2 choice choice_sym _ Fin (isT : (1 < 3)%N).
have Hx1' : Rabs x1 <= 2 * u * Rabs x0 by have := Rabs_pos x0; nra.
have Hb0 := p18b0_le Hx1' Hy1.
have Hs3 := p18s3_le Fx0 Fx1 Fy1 Hx1' Hy1 Hy2.
have HX := Rabs_pos x0.
set b0' := dwh (p18b x0 x1 y1) in Fb0 Hb0 *.
set s3 := p18s3 x0 x1 y1 y2 in Fs3 Hs3 *.
set S := RND (b0' + s3).
have HS : Rabs S <= 7 * u * Rabs x0.
  apply: Rle_trans (@abs_round_le_rel p Hp2 choice _) _.
  have T := Rabs_triang b0' s3.
  have Hkey2 : 0 <= Rabs x0 * (u - 25 * (u * u) - 19 * (u * u * u))
    by apply: Rmult_le_pos; nra.
  nra.
(* [e0] is [x0] to within [7u], so its ulp is at least [u(1 - 7u)|x0|].       *)
have He0lb : (1 - 8 * u) * Rabs x0 <= Rabs (p18e0 x0 x1 y1 y2).
  rewrite He0 -/b0' -/s3 -/S.
  have H1 : (1 - 7 * u) * Rabs x0 <= Rabs (x0 + S).
    have T := Rabs_triang_inv x0 (- S).
    have E : x0 - - S = x0 + S by ring.
    by rewrite E Rabs_Ropp in T; lra.
  have Hrel := @relative_error_le p beta Hp2 choice (x0 + S).
  have T3 : Rabs (x0 + S) - Rabs (RND (x0 + S) - (x0 + S))
              <= Rabs (RND (x0 + S)).
    have T4 := Rabs_triang (RND (x0 + S)) (- (RND (x0 + S) - (x0 + S))).
    have E4 : RND (x0 + S) + - (RND (x0 + S) - (x0 + S)) = x0 + S by ring.
    by rewrite E4 Rabs_Ropp in T4; lra.
  have Habs := Rabs_pos (x0 + S).
  nra.
(* [e2] is the low word of the INNER 2Sum, hence [<= u|S| <= 6u^2|x0|].       *)
have He2b : Rabs (p18e2 x0 x1 y1 y2) <= 7 * (u * u) * Rabs x0.
  rewrite He2.
  have Hm := @magnitude_TwoSum p Hp2 choice choice_sym b0' s3 Fb0 Fs3.
  have Hu2 := @ulp_2u p beta Hp2 (dwh (TwoSum b0' s3)).
  have HdE : dwh (TwoSum b0' s3) = S by [].
  move: Hm; rewrite /magnitudeDWR HdE in Hu2 *.
  by case: (TwoSum b0' s3) HdE => h l /= ->; nra.
have He1b : 2 * Rabs (p18e1 x0 x1 y1 y2) <= ulp (p18e0 x0 x1 y1 y2)
  by move: Hsep1; rewrite /p18e1 /p18e0 /p18e -/b0' -/s3.
have Hulp0 := @u_abs_le_ulp p Hp2 (p18e0 x0 x1 y1 y2).
(* so the pair below the head stays under [(1/2 + 7u) ulp e0].                *)
have Hsum : Rabs (p18e1 x0 x1 y1 y2 + p18e2 x0 x1 y1 y2)
    <= (/2 + 8 * u) * ulp (p18e0 x0 x1 y1 y2).
  have T := Rabs_triang (p18e1 x0 x1 y1 y2) (p18e2 x0 x1 y1 y2).
  have Hkey : 7 * (u * u) * Rabs x0 <= 8 * u * ulp (p18e0 x0 x1 y1 y2).
    have H7 : u * ((1 - 8 * u) * Rabs x0) <= u * Rabs (p18e0 x0 x1 y1 y2)
      by apply: Rmult_le_compat_l; lra.
    have Hkey2 : 0 <= Rabs x0 * (u * u * (1 - 64 * u))
      by apply: Rmult_le_pos; nra.
    nra.
  lra.
have Hfmt := @format_Fast2SumS p Hp2 choice (p18e1 x0 x1 y1 y2)
  (p18e2 x0 x1 y1 y2).
have Hmag := @magnitude_Fast2SumS p Hp2 choice (p18e1 x0 x1 y1 y2)
  (p18e2 x0 x1 y1 y2) (Fe 1%N) (Fe 2%N).
have Hhi := @Fast2SumS_hi p choice (p18e1 x0 x1 y1 y2) (p18e2 x0 x1 y1 y2).
case E : (Fast2SumS (p18e1 x0 x1 y1 y2) (p18e2 x0 x1 y1 y2)) => [r1 r2].
rewrite E /= in Hfmt Hmag Hhi.
split.
- exact: (Fe 0%N).
- by case: Hfmt.
- by case: Hfmt.
- have [Hz|Hnz] := Req_dec (p18e0 x0 x1 y1 y2) 0.
    left; rewrite Hhi.
    have Hu00 : ulp (p18e0 x0 x1 y1 y2) = 0 by rewrite Hz ulp_FLX_0.
    rewrite Hu00 Rmult_0_r in Hsum.
    have Habs := Rabs_pos (p18e1 x0 x1 y1 y2 + p18e2 x0 x1 y1 y2).
    have Ez : p18e1 x0 x1 y1 y2 + p18e2 x0 x1 y1 y2 = 0
      by apply: Rabs_eq_R0; lra.
    by rewrite Ez round_0.
  right; rewrite Hhi.
  have Hulpp : 0 < ulp (p18e0 x0 x1 y1 y2)
    by rewrite ulp_neq_0 //; apply: bpow_gt_0.
  apply: Rle_lt_trans (@abs_round_le_rel p Hp2 choice _) _.
  have Hcoef : (1 + u) * (/2 + 8 * u) < 1 by nra.
  have Hstep : (1 + u) * Rabs (p18e1 x0 x1 y1 y2 + p18e2 x0 x1 y1 y2)
      <= (1 + u) * ((/2 + 8 * u) * ulp (p18e0 x0 x1 y1 y2))
    by apply: Rmult_le_compat_l; lra.
  have Hlast : 0 < ulp (p18e0 x0 x1 y1 y2) * (1 - (1 + u) * (/2 + 8 * u))
    by apply: Rmult_lt_0_compat; lra.
  lra.
have [Hz|Hnz] := Req_dec r1 0.
  left; move: Hmag; rewrite Hz ulp_FLX_0.
  have := Rabs_pos r2.
  by move=> H1 H2; apply: Rabs_eq_R0; lra.
right.
have Hulpp : 0 < ulp r1 by rewrite ulp_neq_0 //; apply: bpow_gt_0.
lra.
Qed.

(* Correctness, part 2: the relative error, for a second argument within      *)
(* [40u^2] of [1] -- which is what Algorithm 13's [i = 2 - 3Prod_{2,3}(b, x)] *)
(* satisfies.  Every block being exact, the error is just FOUR terms,         *)
(*                                                                            *)
(*   error = - x1 y2 + eta1 + eta2 + eta3                                     *)
(*                                                                            *)
(* (the neglected product and the three roundings of [z3,1], [z3], [s3]), of  *)
(* which only [eta3] -- the rounding of [s3 = RN(b'1 + z3)], both [O(u^2)] -- *)
(* reaches [u^3].  That is the paper's remark that all errors are negligible  *)
(* except the one committed when computing [s3].                              *)
(*                                                                            *)
(* THE [u^4] TERM IS BIGGER THAN THE PAPER'S.  Section 8.4 claims             *)
(* [delta2 = u^3 + 260u^4]; the honest accounting gives [620u^4], because     *)
(* [|y2| <= 2u|y1| <= 82u^3] feeds [z3] and hence [eta3] (and [eta2]).  Only  *)
(* the [u^4] term is affected -- the published [u^3] is exact -- but Theorem  *)
(* 9's [1465u^4] leaves just [260u^4] here, so its [u^4] constant grows too.  *)
Lemma ThreeProdOne_error x y :
  ties_to_even choice ->
  isDW x -> isTW y -> tw0 y = 1 -> Rabs (TWval y - 1) <= 40 * (u * u) ->
  Rabs (TWval (ThreeProdOne x y) - TWval x * TWval y)
    <= (u * u * u + 620 * (u * u * u * u)) * Rabs (TWval x * TWval y).
Proof.
move=> Hc Hx Hy Hy0 Hy1v.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := @u_le_64 p Hp6.
case: x Hx => x0 x1 x2 [Fx0 Fx1 Hx2 Hsep].
case: y Hy Hy0 Hy1v => y0 y1 y2 [Fy0 Fy1 Fy2 Hys1 Hys2] /= Hy0.
rewrite Hy0 in Hys1 *.
move=> Hy1v.
rewrite Hx2.
(* [|x1| <= u|x0|] (a double word); and since the head is [1] and the whole  *)
(* is within [40u^2] of it, [|y1| <= 42u^2] and [|y2| <= 84u^3].             *)
have Hx1 : Rabs x1 <= u * Rabs x0.
  case: Hsep => [->|Hs]; first by rewrite Rabs_R0; have := Rabs_pos x0; nra.
  by have := @ulp_2u p beta Hp2 x0; lra.
have Hy2u : Rabs y2 <= 2 * u * Rabs y1.
  case: Hys2 => [->|Hs]; first by rewrite Rabs_R0; have := Rabs_pos y1; nra.
  by have := @ulp_2u p beta Hp2 y1; lra.
have Hy1 : Rabs y1 <= 42 * (u * u).
  have T := Rabs_triang_inv y1 (- y2).
  have E : y1 - - y2 = y1 + y2 by ring.
  rewrite E Rabs_Ropp in T.
  have E2 : 1 + y1 + y2 - 1 = y1 + y2 by ring.
  rewrite E2 in Hy1v.
  nra.
have Hy2 : Rabs y2 <= 84 * (u * u * u).
  have Hp := Rabs_pos y1.
  nra.
have HX := Rabs_pos x0.
have Fz : format (p18z01p x0 y1) by apply: generic_format_round.
have Fb0 : format (dwh (p18b x0 x1 y1)).
  by rewrite /p18b Fast2SumS_hi; apply: generic_format_round.
have Fs3 : format (p18s3 x0 x1 y1 y2) by apply: generic_format_round.
have Fin : {in [:: x0; dwh (p18b x0 x1 y1); p18s3 x0 x1 y1 y2],
             forall z : R, format z}.
  by move=> z; rewrite !inE => /or3P[] /eqP->.
have Fe : forall i, format (nth 0 (p18e x0 x1 y1 y2) i).
  move=> i; case: (ltnP i (size (p18e x0 x1 y1 y2))) => Hi;
    last by rewrite nth_default //; exact: generic_format_0.
  by apply: (@format_vecSum p Hp2 choice) Fin _ _; apply: mem_nth.
(* EVERY block is exact -- 2Prod, the two sorted Fast2Sums, VecSum -- so the *)
(* result is just [x0 + b'0 + s3].                                           *)
have Hval : TWval (let: DWR r1 r2 := Fast2SumS (p18e1 x0 x1 y1 y2)
      (p18e2 x0 x1 y1 y2) in TWR (p18e0 x0 x1 y1 y2) r1 r2)
    = x0 + dwh (p18b x0 x1 y1) + p18s3 x0 x1 y1 y2.
  have Hlast := @Fast2SumS_correct p Hp2 choice (p18e1 x0 x1 y1 y2)
    (p18e2 x0 x1 y1 y2) (Fe 1%N) (Fe 2%N).
  have Hsum := @vecSum_sum p Hp2 choice choice_sym _ Fin.
  case E : (Fast2SumS (p18e1 x0 x1 y1 y2) (p18e2 x0 x1 y1 y2)) => [r1 r2].
  rewrite E in Hlast.
  rewrite /TWval.
  move: Hsum; rewrite -/(p18e x0 x1 y1 y2) => Hsum.
  have Hsz : size (p18e x0 x1 y1 y2) = 3%N by rewrite /p18e size_vecSum.
  have HsE : sumR (p18e x0 x1 y1 y2)
      = p18e0 x0 x1 y1 y2 + p18e1 x0 x1 y1 y2 + p18e2 x0 x1 y1 y2.
    rewrite /p18e0 /p18e1 /p18e2.
    by case E3 : (p18e x0 x1 y1 y2) Hsz => [|a [|b [|c [|d l]]]] //= _; ring.
  by move: Hsum; rewrite HsE /=; lra.
rewrite Hval.
have Hb : dwh (p18b x0 x1 y1) + dwl (p18b x0 x1 y1) = x1 + p18z01p x0 y1.
  have H := @Fast2SumS_correct p Hp2 choice x1 (p18z01p x0 y1) Fx1 Fz.
  by move: H; rewrite /p18b; case: TwoSum.Fast2SumS => a b /=; lra.
have Hprod : p18z01p x0 y1 + p18z01m x0 y1 = x0 * y1.
  rewrite /p18z01m round_generic; first by ring.
  rewrite (_ : x0 * y1 - p18z01p x0 y1 = -(p18z01p x0 y1 - x0 * y1));
    last by ring.
  by apply: generic_format_opp; rewrite /p18z01p; apply: format_err_mul.
(* THE ERROR IS FOUR TERMS: the neglected [x1 y2] and the three roundings.   *)
set eta1 := p18z31 x0 x1 y1 - (p18z01m x0 y1 + x1 * y1).
set eta2 := p18z3 x0 x1 y1 y2 - (p18z31 x0 x1 y1 + x0 * y2).
set eta3 := p18s3 x0 x1 y1 y2 - (dwl (p18b x0 x1 y1) + p18z3 x0 x1 y1 y2).
have HE : (x0 + x1 + 0) * (1 + y1 + y2)
    = x0 + x1 + x0 * y1 + x1 * y1 + x0 * y2 + x1 * y2 by ring.
have Hid : x0 + dwh (p18b x0 x1 y1) + p18s3 x0 x1 y1 y2
    - (x0 + x1 + 0) * (1 + y1 + y2) = - (x1 * y2) + eta1 + eta2 + eta3.
  by rewrite HE /eta1 /eta2 /eta3; lra.
rewrite Hid.
(* Three shapes cover every bound below: a product, a rounding, and the      *)
(* error of a rounding, all measured against [|x0|].                         *)
have Hmono : forall c d : R, c <= d -> c * Rabs x0 <= d * Rabs x0
  by move=> c d Hcd; apply: Rmult_le_compat_r.
have Hmul : forall a b ca cb : R, Rabs a <= ca * Rabs x0 -> Rabs b <= cb ->
    0 <= cb -> Rabs (a * b) <= (ca * cb) * Rabs x0.
  move=> a b ca cb Ha Hb' Hcb; rewrite Rabs_mult.
  have H1 : Rabs a * Rabs b <= (ca * Rabs x0) * cb.
    by apply: Rmult_le_compat => //; apply: Rabs_pos.
  by have -> : ca * cb * Rabs x0 = ca * Rabs x0 * cb by ring.
have Hround : forall t c : R, Rabs t <= c * Rabs x0 -> 0 <= c ->
    Rabs (RND t) <= ((1 + u) * c) * Rabs x0.
  move=> t c Ht Hc0.
  apply: Rle_trans (@abs_round_le_rel p Hp2 choice t) _.
  have -> : (1 + u) * c * Rabs x0 = (1 + u) * (c * Rabs x0) by ring.
  by apply: Rmult_le_compat_l => //; lra.
have Herr : forall t c : R, Rabs t <= c * Rabs x0 -> 0 <= c ->
    Rabs (RND t - t) <= (u * c) * Rabs x0.
  move=> t c Ht Hc0.
  apply: Rle_trans (@relative_error_le p beta Hp2 choice t) _.
  have -> : u * c * Rabs x0 = u * (c * Rabs x0) by ring.
  by apply: Rmult_le_compat_l => //; lra.
have Hx0y1 : Rabs (x0 * y1) <= (42 * (u * u)) * Rabs x0.
  have H := Hmul x0 y1 1 (42 * (u * u)) (ltac:(lra)) Hy1 (ltac:(nra)).
  by move: H; rewrite Rmult_1_l.
have Hx1y1 : Rabs (x1 * y1) <= (42 * (u * u * u)) * Rabs x0.
  have H := Hmul x1 y1 u (42 * (u * u)) Hx1 Hy1 (ltac:(nra)).
  by move: H; have -> : u * (42 * (u * u)) = 42 * (u * u * u) by ring.
have Hx0y2 : Rabs (x0 * y2) <= (84 * (u * u * u)) * Rabs x0.
  have H := Hmul x0 y2 1 (84 * (u * u * u)) (ltac:(lra)) Hy2 (ltac:(nra)).
  by move: H; rewrite Rmult_1_l.
have Hx1y2 : Rabs (x1 * y2) <= (84 * (u * u * u * u)) * Rabs x0.
  have H := Hmul x1 y2 u (84 * (u * u * u)) Hx1 Hy2 (ltac:(nra)).
  by move: H; have -> : u * (84 * (u * u * u)) = 84 * (u * u * u * u) by ring.
have Hz01p : Rabs (p18z01p x0 y1) <= (43 * (u * u)) * Rabs x0.
  apply: Rle_trans (Hround (x0 * y1) (42 * (u * u)) Hx0y1 (ltac:(nra))) _.
  by apply: Hmono; nra.
have Hz01m : Rabs (p18z01m x0 y1) <= (42 * (u * u * u)) * Rabs x0.
  rewrite /p18z01m round_generic; last first.
    rewrite (_ : x0 * y1 - p18z01p x0 y1 = -(p18z01p x0 y1 - x0 * y1));
      last by ring.
    by apply: generic_format_opp; rewrite /p18z01p; apply: format_err_mul.
  have E : x0 * y1 - p18z01p x0 y1 = - (RND (x0 * y1) - x0 * y1)
    by rewrite /p18z01p; ring.
  rewrite E Rabs_Ropp.
  apply: Rle_trans (Herr (x0 * y1) (42 * (u * u)) Hx0y1 (ltac:(nra))) _.
  by apply: Hmono; nra.
have Ht1 : Rabs (p18z01m x0 y1 + x1 * y1) <= (84 * (u * u * u)) * Rabs x0.
  by have T := Rabs_triang (p18z01m x0 y1) (x1 * y1); lra.
have Heta1 : Rabs eta1 <= (84 * (u * u * u * u)) * Rabs x0.
  rewrite /eta1 /p18z31.
  apply: Rle_trans (Herr _ (84 * (u * u * u)) Ht1 (ltac:(nra))) _.
  by apply: Hmono; nra.
have Hz31 : Rabs (p18z31 x0 x1 y1) <= (86 * (u * u * u)) * Rabs x0.
  rewrite /p18z31.
  apply: Rle_trans (Hround _ (84 * (u * u * u)) Ht1 (ltac:(nra))) _.
  by apply: Hmono; nra.
have Ht2 : Rabs (p18z31 x0 x1 y1 + x0 * y2) <= (170 * (u * u * u)) * Rabs x0.
  by have T := Rabs_triang (p18z31 x0 x1 y1) (x0 * y2); lra.
have Heta2 : Rabs eta2 <= (170 * (u * u * u * u)) * Rabs x0.
  rewrite /eta2 /p18z3.
  apply: Rle_trans (Herr _ (170 * (u * u * u)) Ht2 (ltac:(nra))) _.
  by apply: Hmono; nra.
have Hz3 : Rabs (p18z3 x0 x1 y1 y2) <= (173 * (u * u * u)) * Rabs x0.
  rewrite /p18z3.
  apply: Rle_trans (Hround _ (170 * (u * u * u)) Ht2 (ltac:(nra))) _.
  by apply: Hmono; nra.
have Hb0v : dwh (p18b x0 x1 y1) = RND (x1 + p18z01p x0 y1)
  by rewrite /p18b Fast2SumS_hi.
have Htb : Rabs (x1 + p18z01p x0 y1) <= (u + 43 * (u * u)) * Rabs x0.
  by have T := Rabs_triang x1 (p18z01p x0 y1); lra.
have Hb0 : Rabs (dwh (p18b x0 x1 y1)) <= (u + 45 * (u * u)) * Rabs x0.
  rewrite Hb0v.
  apply: Rle_trans (Hround _ (u + 43 * (u * u)) Htb (ltac:(nra))) _.
  by apply: Hmono; nra.
have Hb1 : Rabs (dwl (p18b x0 x1 y1)) <= (u * u + 45 * (u * u * u)) * Rabs x0.
  have Hm : Rabs (dwl (p18b x0 x1 y1)) <= ulp (dwh (p18b x0 x1 y1)) / 2.
    rewrite /p18b.
    have := @magnitude_Fast2SumS p Hp2 choice x1 (p18z01p x0 y1) Fx1 Fz.
    by rewrite /magnitudeDWR; case: TwoSum.Fast2SumS.
  have Hulp := @ulp_2u p beta Hp2 (dwh (p18b x0 x1 y1)).
  have Hstep : u * Rabs (dwh (p18b x0 x1 y1))
      <= u * ((u + 45 * (u * u)) * Rabs x0) by apply: Rmult_le_compat_l; lra.
  by nra.
have Ht3 : Rabs (dwl (p18b x0 x1 y1) + p18z3 x0 x1 y1 y2)
    <= (u * u + 218 * (u * u * u)) * Rabs x0.
  by have T := Rabs_triang (dwl (p18b x0 x1 y1)) (p18z3 x0 x1 y1 y2); lra.
(* ... and THIS is the only one that reaches [u^3].                          *)
have Heta3 : Rabs eta3 <= (u * u * u + 218 * (u * u * u * u)) * Rabs x0.
  rewrite /eta3 /p18s3.
  apply: Rle_trans (Herr _ (u * u + 218 * (u * u * u)) Ht3 (ltac:(nra))) _.
  by apply: Hmono; nra.
have Hfin : Rabs (- (x1 * y2) + eta1 + eta2 + eta3)
    <= (u * u * u + 556 * (u * u * u * u)) * Rabs x0.
  have T1 := Rabs_triang (- (x1 * y2) + eta1 + eta2) eta3.
  have T2 := Rabs_triang (- (x1 * y2) + eta1) eta2.
  have T3 := Rabs_triang (- (x1 * y2)) eta1.
  rewrite Rabs_Ropp in T3.
  lra.
(* Finally, the product itself is at least [(1 - 2u)|x0|].                   *)
have Hxy : (1 - 2 * u) * Rabs x0 <= Rabs ((x0 + x1 + 0) * (1 + y1 + y2)).
  have E : x0 + x1 + 0 = x0 + x1 by ring.
  rewrite E Rabs_mult.
  have H1 : (1 - u) * Rabs x0 <= Rabs (x0 + x1).
    have T := Rabs_triang_inv x0 (- x1).
    have E2 : x0 - - x1 = x0 + x1 by ring.
    by rewrite E2 Rabs_Ropp in T; lra.
  have H2 : 1 - 44 * (u * u) <= Rabs (1 + y1 + y2).
    have T := Rabs_triang_inv (1 + y1) (- y2).
    have E2 : 1 + y1 - - y2 = 1 + y1 + y2 by ring.
    rewrite E2 Rabs_Ropp in T.
    have T2 := Rabs_triang_inv 1 (- y1).
    have E3 : 1 - - y1 = 1 + y1 by ring.
    rewrite E3 Rabs_Ropp Rabs_R1 in T2.
    have Hup : 0 <= u * u by apply: Rle_0_sqr.
    have Hu3 : u * u * u <= /64 * (u * u).
      have -> : /64 * (u * u) = (u * u) * /64 by ring.
      by apply: Rmult_le_compat_l.
    lra.
  have Hxp := Rabs_pos (x0 + x1).
  have Hyp := Rabs_pos (1 + y1 + y2).
  have Hp1 : 0 <= u - 44 * (u * u) + 44 * (u * u * u).
    have -> : u - 44 * (u * u) + 44 * (u * u * u)
        = u * (1 - 44 * u + 44 * (u * u)) by ring.
    have Hup : 0 <= u * u by apply: Rle_0_sqr.
    by apply: Rmult_le_pos; lra.
  have Hstep : (1 - u) * Rabs x0 * (1 - 44 * (u * u))
      <= Rabs (x0 + x1) * Rabs (1 + y1 + y2).
    apply: Rmult_le_compat => //; try lra.
      by apply: Rmult_le_pos; lra.
    have Hu2 : u * u <= u * /64 by apply: Rmult_le_compat_l; lra.
    by lra.
  have Hexp : (1 - u) * Rabs x0 * (1 - 44 * (u * u))
      = (1 - u - 44 * (u * u) + 44 * (u * u * u)) * Rabs x0 by ring.
  rewrite Hexp in Hstep.
  apply: Rle_trans Hstep.
  by apply: Hmono; lra.
apply: Rle_trans Hfin _.
have Hpos : 0 <= u * u * u + 620 * (u * u * u * u).
  have Hup : 0 <= u * u by apply: Rle_0_sqr.
  have H3 : 0 <= u * u * u by apply: Rmult_le_pos; lra.
  have H4 : 0 <= u * u * u * u by apply: Rmult_le_pos; lra.
  by lra.
apply: Rle_trans (_ : (u * u * u + 620 * (u * u * u * u))
    * ((1 - 2 * u) * Rabs x0) <= _); last first.
  by apply: Rmult_le_compat_l.
have Hexp2 : (u * u * u + 620 * (u * u * u * u)) * ((1 - 2 * u) * Rabs x0)
    = ((u * u * u + 620 * (u * u * u * u)) * (1 - 2 * u)) * Rabs x0 by ring.
rewrite Hexp2.
apply: Hmono.
have H5 : u * u * u * u * u <= u * u * u * u * / 64.
  apply: Rmult_le_compat_l; last by lra.
  have Hup : 0 <= u * u by apply: Rle_0_sqr.
  have H3 : 0 <= u * u * u by apply: Rmult_le_pos; lra.
  by apply: Rmult_le_pos; lra.
have -> : (u * u * u + 620 * (u * u * u * u)) * (1 - 2 * u)
    = u * u * u + 618 * (u * u * u * u) - 1240 * (u * u * u * u * u) by ring.
have Hup : 0 <= u * u by apply: Rle_0_sqr.
have H3 : 0 <= u * u * u by apply: Rmult_le_pos; lra.
have H4 : 0 <= u * u * u * u by apply: Rmult_le_pos; lra.
lra.
Qed.

(* ===========================================================================*)
(*  Algorithm 20 -- 3Prod^one_{3,3}(x, y) with [y0 = 1] VIRTUAL               *)
(*  (21 operations + 2 tests; old paper Section 9).                           *)
(*                                                                            *)
(*  Algorithm 18 with a TRIPLE word as first argument.  Two changes: the      *)
(*  chain gains one line for [x2] (which is [0] for a double word), and the   *)
(*  first limb separation is the WEAKER [|x1| < ulp x0 <= 2u|x0|] of a triple *)
(*  word instead of the double word's [u|x0|].                                *)
(*                                                                            *)
(*    z01+, z01- <- 2Prod(x0, y1)                                             *)
(*    b'0, b'1   <- Fast2SumS(x1, z01+)     (the paper's Fast2Sum, SORTED)    *)
(*    z31 <- RN(z01- + x1 y1)               (FMA)                             *)
(*    z3  <- RN(z31 + x0 y2)                (FMA)                             *)
(*    s3' <- RN(b'1 + z3)                   (Algorithm 18's [s3])             *)
(*    s3  <- RN(s3' + x2)                   (the one new line)                *)
(*    e0, e1, e2 <- VecSum(x0, b'0, s3)                                       *)
(*    y0 <- e0 ;  y1, y2 <- Fast2SumS(e1, e2)                                 *)
(* ===========================================================================*)
(* Everything up to [s3] is Algorithm 18's; the third limb of the first       *)
(* argument adds exactly one line.                                            *)
Definition p20s3 (x0 x1 x2 y1 y2 : R) : R := RND (p18s3 x0 x1 y1 y2 + x2).

Definition p20e (x0 x1 x2 y1 y2 : R) : seq R :=
  vecSum [:: x0; dwh (p18b x0 x1 y1); p20s3 x0 x1 x2 y1 y2].

Definition p20e0 (x0 x1 x2 y1 y2 : R) : R := nth 0 (p20e x0 x1 x2 y1 y2) 0.
Definition p20e1 (x0 x1 x2 y1 y2 : R) : R := nth 0 (p20e x0 x1 x2 y1 y2) 1.
Definition p20e2 (x0 x1 x2 y1 y2 : R) : R := nth 0 (p20e x0 x1 x2 y1 y2) 2.

Definition ThreeProdOneTW (x y : twR) : twR :=
  let: TWR x0 x1 x2 := x in
  let: TWR _ y1 y2 := y in
  let: DWR r1 r2 :=
     Fast2SumS (p20e1 x0 x1 x2 y1 y2) (p20e2 x0 x1 x2 y1 y2) in
  TWR (p20e0 x0 x1 x2 y1 y2) r1 r2.

Lemma p20s3_le x0 x1 x2 y1 y2 :
  format x0 -> format x1 -> format y1 ->
  Rabs x1 <= 2 * u * Rabs x0 -> Rabs x2 <= 4 * (u * u) * Rabs x0 ->
  Rabs y1 <= 2 * u -> Rabs y2 <= 4 * (u * u) ->
  Rabs (p20s3 x0 x1 x2 y1 y2) <= 24 * (u * u) * Rabs x0.
Proof.
move=> Fx0 Fx1 Fy1 Hx1 Hx2 Hy1 Hy2.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := @u_le_64 p Hp6.
have Hs3 := p18s3_le Fx0 Fx1 Fy1 Hx1 Hy1 Hy2.
rewrite /p20s3.
apply: Rle_trans (@abs_round_le_rel p Hp2 choice _) _.
have T := Rabs_triang (p18s3 x0 x1 y1 y2) x2.
have Hx := Rabs_pos x0.
have Hkey : 0 <= Rabs x0 * (u * u * (1 - 23 * u)) by apply: Rmult_le_pos; nra.
nra.
Qed.

(* Correctness, part 1.  Same shape as [ThreeProdOne_isTW]: the head and the  *)
(* pair below it are separated by the inner VecSum's half-ulp                 *)
(* ([vecSum_head_sep]), and that pair is a double word ([Fast2SumS]).  Only   *)
(* the term bounds change ([|x1| <= 2u|x0|], and [x2] joins [s3]).            *)
Lemma ThreeProdOneTW_isTW x y :
  ties_to_even choice ->
  isTW x -> isTW y -> tw0 y = 1 -> isTW (ThreeProdOneTW x y).
Proof.
have He0 : forall x0 x1 x2 y1 y2, p20e0 x0 x1 x2 y1 y2
    = RND (x0 + RND (dwh (p18b x0 x1 y1) + p20s3 x0 x1 x2 y1 y2)) by [].
have He2 : forall x0 x1 x2 y1 y2, p20e2 x0 x1 x2 y1 y2
    = dwl (TwoSum (dwh (p18b x0 x1 y1)) (p20s3 x0 x1 x2 y1 y2)) by [].
move=> Hc Hx Hy Hy0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := @u_le_64 p Hp6.
case: x Hx => x0 x1 x2 [Fx0 Fx1 Fx2 Hxs1 Hxs2].
case: y Hy Hy0 => y0 y1 y2 [Fy0 Fy1 Fy2 Hys1 Hys2] /= Hy0.
rewrite Hy0 in Hys1.
(* A triple word gives the WEAKER [|x1| <= 2u|x0|], and its third limb is    *)
(* [O(u^2)] -- that is the whole difference with Algorithm 18.               *)
have Hx1 : Rabs x1 <= 2 * u * Rabs x0.
  case: Hxs1 => [->|Hs]; first by rewrite Rabs_R0; have := Rabs_pos x0; nra.
  by have := @ulp_2u p beta Hp2 x0; lra.
have Hx2 : Rabs x2 <= 4 * (u * u) * Rabs x0.
  case: Hxs2 => [->|Hs]; first by rewrite Rabs_R0; have := Rabs_pos x0; nra.
  have Hu2 := @ulp_2u p beta Hp2 x1.
  by have := Rabs_pos x1; nra.
have Hy1 : Rabs y1 <= 2 * u.
  case: Hys1 => [->|Hs]; first by rewrite Rabs_R0; lra.
  by move: Hs; rewrite (@ulp_one p); lra.
have Hy2 : Rabs y2 <= 4 * (u * u).
  case: Hys2 => [->|Hs]; first by rewrite Rabs_R0; nra.
  have Hu2 := @ulp_2u p beta Hp2 y1.
  by have := Rabs_pos y1; nra.
have Fb0 : format (dwh (p18b x0 x1 y1)).
  by rewrite /p18b Fast2SumS_hi; apply: generic_format_round.
have Fs3 : format (p20s3 x0 x1 x2 y1 y2) by apply: generic_format_round.
have Fin : {in [:: x0; dwh (p18b x0 x1 y1); p20s3 x0 x1 x2 y1 y2],
             forall z : R, format z}.
  by move=> z; rewrite !inE => /or3P[] /eqP->.
have Fe : forall i, format (nth 0 (p20e x0 x1 x2 y1 y2) i).
  move=> i; case: (ltnP i (size (p20e x0 x1 x2 y1 y2))) => Hi;
    last by rewrite nth_default //; exact: generic_format_0.
  by apply: (@format_vecSum p Hp2 choice) Fin _ _; apply: mem_nth.
have Hsep1 := @vecSum_head_sep p Hp2 choice choice_sym _ Fin (isT : (1 < 3)%N).
have Hb0 := p18b0_le Hx1 Hy1.
have Hs3 := p20s3_le Fx0 Fx1 Fy1 Hx1 Hx2 Hy1 Hy2.
have HX := Rabs_pos x0.
set b0' := dwh (p18b x0 x1 y1) in Fb0 Hb0 *.
set s3 := p20s3 x0 x1 x2 y1 y2 in Fs3 Hs3 *.
set S := RND (b0' + s3).
have HS : Rabs S <= 8 * u * Rabs x0.
  apply: Rle_trans (@abs_round_le_rel p Hp2 choice _) _.
  have T := Rabs_triang b0' s3.
  have Hkey2 : 0 <= Rabs x0 * (2 * u - 30 * (u * u) - 24 * (u * u * u))
    by apply: Rmult_le_pos; nra.
  nra.
have He0lb : (1 - 9 * u) * Rabs x0 <= Rabs (p20e0 x0 x1 x2 y1 y2).
  rewrite He0 -/b0' -/s3 -/S.
  have H1 : (1 - 8 * u) * Rabs x0 <= Rabs (x0 + S).
    have T := Rabs_triang_inv x0 (- S).
    have E : x0 - - S = x0 + S by ring.
    by rewrite E Rabs_Ropp in T; lra.
  have Hrel := @relative_error_le p beta Hp2 choice (x0 + S).
  have T3 : Rabs (x0 + S) - Rabs (RND (x0 + S) - (x0 + S))
              <= Rabs (RND (x0 + S)).
    have T4 := Rabs_triang (RND (x0 + S)) (- (RND (x0 + S) - (x0 + S))).
    have E4 : RND (x0 + S) + - (RND (x0 + S) - (x0 + S)) = x0 + S by ring.
    by rewrite E4 Rabs_Ropp in T4; lra.
  have Habs := Rabs_pos (x0 + S).
  nra.
have He2b : Rabs (p20e2 x0 x1 x2 y1 y2) <= 8 * (u * u) * Rabs x0.
  rewrite He2.
  have Hm := @magnitude_TwoSum p Hp2 choice choice_sym b0' s3 Fb0 Fs3.
  have Hu2 := @ulp_2u p beta Hp2 (dwh (TwoSum b0' s3)).
  have HdE : dwh (TwoSum b0' s3) = S by [].
  move: Hm; rewrite /magnitudeDWR HdE in Hu2 *.
  by case: (TwoSum b0' s3) HdE => h l /= ->; nra.
have He1b : 2 * Rabs (p20e1 x0 x1 x2 y1 y2) <= ulp (p20e0 x0 x1 x2 y1 y2)
  by move: Hsep1; rewrite /p20e1 /p20e0 /p20e -/b0' -/s3.
have Hulp0 := @u_abs_le_ulp p Hp2 (p20e0 x0 x1 x2 y1 y2).
have Hsum : Rabs (p20e1 x0 x1 x2 y1 y2 + p20e2 x0 x1 x2 y1 y2)
    <= (/2 + 10 * u) * ulp (p20e0 x0 x1 x2 y1 y2).
  have T := Rabs_triang (p20e1 x0 x1 x2 y1 y2) (p20e2 x0 x1 x2 y1 y2).
  have Hkey : 8 * (u * u) * Rabs x0 <= 10 * u * ulp (p20e0 x0 x1 x2 y1 y2).
    have H7 : u * ((1 - 9 * u) * Rabs x0) <= u * Rabs (p20e0 x0 x1 x2 y1 y2)
      by apply: Rmult_le_compat_l; lra.
    have Hkey2 : 0 <= Rabs x0 * (u * u * (2 - 90 * u))
      by apply: Rmult_le_pos; nra.
    nra.
  lra.
have Hfmt := @format_Fast2SumS p Hp2 choice (p20e1 x0 x1 x2 y1 y2)
  (p20e2 x0 x1 x2 y1 y2).
have Hmag := @magnitude_Fast2SumS p Hp2 choice (p20e1 x0 x1 x2 y1 y2)
  (p20e2 x0 x1 x2 y1 y2) (Fe 1%N) (Fe 2%N).
have Hhi := @Fast2SumS_hi p choice (p20e1 x0 x1 x2 y1 y2)
  (p20e2 x0 x1 x2 y1 y2).
case E : (Fast2SumS (p20e1 x0 x1 x2 y1 y2) (p20e2 x0 x1 x2 y1 y2)) => [r1 r2].
rewrite E /= in Hfmt Hmag Hhi.
split.
- exact: (Fe 0%N).
- by case: Hfmt.
- by case: Hfmt.
- have [Hz|Hnz] := Req_dec (p20e0 x0 x1 x2 y1 y2) 0.
    left; rewrite Hhi.
    have Hu00 : ulp (p20e0 x0 x1 x2 y1 y2) = 0 by rewrite Hz ulp_FLX_0.
    rewrite Hu00 Rmult_0_r in Hsum.
    have Habs := Rabs_pos (p20e1 x0 x1 x2 y1 y2 + p20e2 x0 x1 x2 y1 y2).
    have Ez : p20e1 x0 x1 x2 y1 y2 + p20e2 x0 x1 x2 y1 y2 = 0
      by apply: Rabs_eq_R0; lra.
    by rewrite Ez round_0.
  right; rewrite Hhi.
  have Hulpp : 0 < ulp (p20e0 x0 x1 x2 y1 y2)
    by rewrite ulp_neq_0 //; apply: bpow_gt_0.
  apply: Rle_lt_trans (@abs_round_le_rel p Hp2 choice _) _.
  have Hcoef : (1 + u) * (/2 + 10 * u) < 1 by nra.
  have Hstep : (1 + u) * Rabs (p20e1 x0 x1 x2 y1 y2 + p20e2 x0 x1 x2 y1 y2)
      <= (1 + u) * ((/2 + 10 * u) * ulp (p20e0 x0 x1 x2 y1 y2))
    by apply: Rmult_le_compat_l; lra.
  have Hlast : 0 < ulp (p20e0 x0 x1 x2 y1 y2) * (1 - (1 + u) * (/2 + 10 * u))
    by apply: Rmult_lt_0_compat; lra.
  lra.
have [Hz|Hnz] := Req_dec r1 0.
  left; move: Hmag; rewrite Hz ulp_FLX_0.
  have := Rabs_pos r2.
  by move=> H1 H2; apply: Rabs_eq_R0; lra.
right.
have Hulpp : 0 < ulp r1 by rewrite ulp_neq_0 //; apply: bpow_gt_0.
lra.
Qed.

(* Correctness, part 2.  Every block is exact here too, so the error is again *)
(* a handful of terms,                                                        *)
(*                                                                            *)
(*   error = - x1 y2 - x2 y1 - x2 y2 + eta1 + eta2 + eta3 + eta4              *)
(*                                                                            *)
(* the three neglected products and the roundings of [z31], [z3], [s3'],      *)
(* [s3].                                                                      *)
(*                                                                            *)
(* THE PAPER'S [u^3] IS TOO SMALL.  Old paper Section 9 calls this "Algorithm *)
(* 18's analysis with an additional [2u^3]", i.e. [delta3 = 3u^3 + 264u^4].   *)
(* The honest bound is [8u^3 + 1330u^4], and the gap is structural, not       *)
(* slack: a TRIPLE word only gives [|x1| < ulp x0 <= 2u|x0|] and              *)
(* [|x2| < ulp x1 <= 4u^2|x0|], TWICE a double word's separation at each      *)
(* level.  So                                                                 *)
(*                                                                            *)
(*   eta3 = u |b'1 + z3|  with  |b'1| <= u|b'0| <= 2u^2|x0|   ->  2u^3        *)
(*   eta4 = u |s3' + x2|  with  |x2| <= 4u^2|x0|              ->  6u^3        *)
(*                                                                            *)
(* against Algorithm 18's [1u^3] and the paper's announced [2u^3].  Its       *)
(* [3u^3] is what the double-word separations [|x1| <= u|x0|],                *)
(* [|x2| <= u^2|x0|] would give.  Consequence: Theorem 10's leading term is   *)
(* [29u^3] / [44u^3], not [24u^3] / [39u^3] -- see doc/thm10.md, which also   *)
(* records the tightening (to [6u^3]) that recording "the last two limbs of   *)
(* the multipliers' output form a double word" would buy.                     *)
Lemma ThreeProdOneTW_error x y :
  ties_to_even choice ->
  isTW x -> isTW y -> tw0 y = 1 -> Rabs (TWval y - 1) <= 40 * (u * u) ->
  Rabs (TWval (ThreeProdOneTW x y) - TWval x * TWval y)
    <= (8 * (u * u * u) + 1330 * (u * u * u * u)) * Rabs (TWval x * TWval y).
Proof.
move=> Hc Hx Hy Hy0 Hy1v.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := @u_le_64 p Hp6.
case: x Hx => x0 x1 x2 [Fx0 Fx1 Fx2 Hxs1 Hxs2].
case: y Hy Hy0 Hy1v => y0 y1 y2 [Fy0 Fy1 Fy2 Hys1 Hys2] /= Hy0.
rewrite Hy0 in Hys1 *.
move=> Hy1v.
(* A triple word gives [|x1| <= 2u|x0|] and [|x2| <= 4u^2|x0|] -- TWICE       *)
(* Algorithm 18's double-word bounds, and that is where [delta3] grows.       *)
have Hx1 : Rabs x1 <= 2 * u * Rabs x0.
  case: Hxs1 => [->|Hs]; first by rewrite Rabs_R0; have := Rabs_pos x0; nra.
  by have := @ulp_2u p beta Hp2 x0; lra.
have Hx2 : Rabs x2 <= 4 * (u * u) * Rabs x0.
  case: Hxs2 => [->|Hs]; first by rewrite Rabs_R0; have := Rabs_pos x0; nra.
  have Hu2 := @ulp_2u p beta Hp2 x1.
  by have := Rabs_pos x1; nra.
have Hy2u : Rabs y2 <= 2 * u * Rabs y1.
  case: Hys2 => [->|Hs]; first by rewrite Rabs_R0; have := Rabs_pos y1; nra.
  by have := @ulp_2u p beta Hp2 y1; lra.
have Hy1 : Rabs y1 <= 42 * (u * u).
  have T := Rabs_triang_inv y1 (- y2).
  have E : y1 - - y2 = y1 + y2 by ring.
  rewrite E Rabs_Ropp in T.
  have E2 : 1 + y1 + y2 - 1 = y1 + y2 by ring.
  rewrite E2 in Hy1v.
  nra.
have Hy2 : Rabs y2 <= 84 * (u * u * u).
  have Hp := Rabs_pos y1.
  nra.
have HX := Rabs_pos x0.
have Fz : format (p18z01p x0 y1) by apply: generic_format_round.
have Fb0 : format (dwh (p18b x0 x1 y1)).
  by rewrite /p18b Fast2SumS_hi; apply: generic_format_round.
have Fs3 : format (p20s3 x0 x1 x2 y1 y2) by apply: generic_format_round.
have Fin : {in [:: x0; dwh (p18b x0 x1 y1); p20s3 x0 x1 x2 y1 y2],
             forall z : R, format z}.
  by move=> z; rewrite !inE => /or3P[] /eqP->.
have Fe : forall i, format (nth 0 (p20e x0 x1 x2 y1 y2) i).
  move=> i; case: (ltnP i (size (p20e x0 x1 x2 y1 y2))) => Hi;
    last by rewrite nth_default //; exact: generic_format_0.
  by apply: (@format_vecSum p Hp2 choice) Fin _ _; apply: mem_nth.
(* EVERY block is exact, exactly as in Algorithm 18.                          *)
have Hval : TWval (let: DWR r1 r2 := Fast2SumS (p20e1 x0 x1 x2 y1 y2)
      (p20e2 x0 x1 x2 y1 y2) in TWR (p20e0 x0 x1 x2 y1 y2) r1 r2)
    = x0 + dwh (p18b x0 x1 y1) + p20s3 x0 x1 x2 y1 y2.
  have Hlast := @Fast2SumS_correct p Hp2 choice (p20e1 x0 x1 x2 y1 y2)
    (p20e2 x0 x1 x2 y1 y2) (Fe 1%N) (Fe 2%N).
  have Hsum := @vecSum_sum p Hp2 choice choice_sym _ Fin.
  case E : (Fast2SumS (p20e1 x0 x1 x2 y1 y2) (p20e2 x0 x1 x2 y1 y2)) => [r1 r2].
  rewrite E in Hlast.
  rewrite /TWval.
  move: Hsum; rewrite -/(p20e x0 x1 x2 y1 y2) => Hsum.
  have Hsz : size (p20e x0 x1 x2 y1 y2) = 3%N by rewrite /p20e size_vecSum.
  have HsE : sumR (p20e x0 x1 x2 y1 y2)
      = p20e0 x0 x1 x2 y1 y2 + p20e1 x0 x1 x2 y1 y2 + p20e2 x0 x1 x2 y1 y2.
    rewrite /p20e0 /p20e1 /p20e2.
    by case E3 : (p20e x0 x1 x2 y1 y2) Hsz => [|a [|b [|c [|d l]]]] //= _; ring.
  by move: Hsum; rewrite HsE /=; lra.
rewrite Hval.
have Hb : dwh (p18b x0 x1 y1) + dwl (p18b x0 x1 y1) = x1 + p18z01p x0 y1.
  have H := @Fast2SumS_correct p Hp2 choice x1 (p18z01p x0 y1) Fx1 Fz.
  by move: H; rewrite /p18b; case: TwoSum.Fast2SumS => a b /=; lra.
have Hprod : p18z01p x0 y1 + p18z01m x0 y1 = x0 * y1.
  rewrite /p18z01m round_generic; first by ring.
  rewrite (_ : x0 * y1 - p18z01p x0 y1 = -(p18z01p x0 y1 - x0 * y1));
    last by ring.
  by apply: generic_format_opp; rewrite /p18z01p; apply: format_err_mul.
(* THE ERROR IS SEVEN TERMS: three neglected products and four roundings.    *)
set eta1 := p18z31 x0 x1 y1 - (p18z01m x0 y1 + x1 * y1).
set eta2 := p18z3 x0 x1 y1 y2 - (p18z31 x0 x1 y1 + x0 * y2).
set eta3 := p18s3 x0 x1 y1 y2 - (dwl (p18b x0 x1 y1) + p18z3 x0 x1 y1 y2).
set eta4 := p20s3 x0 x1 x2 y1 y2 - (p18s3 x0 x1 y1 y2 + x2).
have HE : (x0 + x1 + x2) * (1 + y1 + y2)
    = x0 + x1 + x2 + x0 * y1 + x1 * y1 + x2 * y1 + x0 * y2 + x1 * y2
      + x2 * y2 by ring.
have Hid : x0 + dwh (p18b x0 x1 y1) + p20s3 x0 x1 x2 y1 y2
    - (x0 + x1 + x2) * (1 + y1 + y2)
    = - (x1 * y2) - (x2 * y1) - (x2 * y2) + eta1 + eta2 + eta3 + eta4.
  by rewrite HE /eta1 /eta2 /eta3 /eta4; lra.
rewrite Hid.
(* Three shapes cover every bound below: a product, a rounding, and the      *)
(* error of a rounding, all measured against [|x0|].                         *)
have Hmono : forall c d : R, c <= d -> c * Rabs x0 <= d * Rabs x0
  by move=> c d Hcd; apply: Rmult_le_compat_r.
have Hmul : forall a b ca cb : R, Rabs a <= ca * Rabs x0 -> Rabs b <= cb ->
    0 <= cb -> Rabs (a * b) <= (ca * cb) * Rabs x0.
  move=> a b ca cb Ha Hb' Hcb; rewrite Rabs_mult.
  have H1 : Rabs a * Rabs b <= (ca * Rabs x0) * cb.
    by apply: Rmult_le_compat => //; apply: Rabs_pos.
  by have -> : ca * cb * Rabs x0 = ca * Rabs x0 * cb by ring.
have Hround : forall t c : R, Rabs t <= c * Rabs x0 -> 0 <= c ->
    Rabs (RND t) <= ((1 + u) * c) * Rabs x0.
  move=> t c Ht Hc0.
  apply: Rle_trans (@abs_round_le_rel p Hp2 choice t) _.
  have -> : (1 + u) * c * Rabs x0 = (1 + u) * (c * Rabs x0) by ring.
  by apply: Rmult_le_compat_l => //; lra.
have Herr : forall t c : R, Rabs t <= c * Rabs x0 -> 0 <= c ->
    Rabs (RND t - t) <= (u * c) * Rabs x0.
  move=> t c Ht Hc0.
  apply: Rle_trans (@relative_error_le p beta Hp2 choice t) _.
  have -> : u * c * Rabs x0 = u * (c * Rabs x0) by ring.
  by apply: Rmult_le_compat_l => //; lra.
have Hu2p : 0 <= u * u by apply: Rle_0_sqr.
have Hu3p : 0 <= u * u * u by apply: Rmult_le_pos; lra.
have Hx0y1 : Rabs (x0 * y1) <= (42 * (u * u)) * Rabs x0.
  have Hc1 : 0 <= 42 * (u * u) by lra.
  have Hc2 : Rabs x0 <= 1 * Rabs x0 by lra.
  have H := Hmul x0 y1 1 (42 * (u * u)) Hc2 Hy1 Hc1.
  by move: H; rewrite Rmult_1_l.
have Hx1y1 : Rabs (x1 * y1) <= (84 * (u * u * u)) * Rabs x0.
  have Hc1 : 0 <= 42 * (u * u) by lra.
  have H := Hmul x1 y1 (2 * u) (42 * (u * u)) Hx1 Hy1 Hc1.
  by move: H; have -> : 2 * u * (42 * (u * u)) = 84 * (u * u * u) by ring.
have Hx0y2 : Rabs (x0 * y2) <= (84 * (u * u * u)) * Rabs x0.
  have Hc1 : 0 <= 84 * (u * u * u) by lra.
  have Hc2 : Rabs x0 <= 1 * Rabs x0 by lra.
  have H := Hmul x0 y2 1 (84 * (u * u * u)) Hc2 Hy2 Hc1.
  by move: H; rewrite Rmult_1_l.
have Hx1y2 : Rabs (x1 * y2) <= (168 * (u * u * u * u)) * Rabs x0.
  have Hc1 : 0 <= 84 * (u * u * u) by lra.
  have H := Hmul x1 y2 (2 * u) (84 * (u * u * u)) Hx1 Hy2 Hc1.
  by move: H;
     have -> : 2 * u * (84 * (u * u * u)) = 168 * (u * u * u * u) by ring.
have Hx2y1 : Rabs (x2 * y1) <= (168 * (u * u * u * u)) * Rabs x0.
  have Hc1 : 0 <= 42 * (u * u) by lra.
  have H := Hmul x2 y1 (4 * (u * u)) (42 * (u * u)) Hx2 Hy1 Hc1.
  by move: H;
     have -> : 4 * (u * u) * (42 * (u * u)) = 168 * (u * u * u * u) by ring.
(* [x2 y2] is [336u^5], which [u <= 1/64] absorbs into [6u^4].              *)
have Hx2y2 : Rabs (x2 * y2) <= (6 * (u * u * u * u)) * Rabs x0.
  have Hc1 : 0 <= 84 * (u * u * u) by lra.
  have H := Hmul x2 y2 (4 * (u * u)) (84 * (u * u * u)) Hx2 Hy2 Hc1.
  have Hstep : 4 * (u * u) * (84 * (u * u * u)) * Rabs x0
      <= 6 * (u * u * u * u) * Rabs x0 by apply: Hmono; nra.
  by lra.
have Hz01p : Rabs (p18z01p x0 y1) <= (43 * (u * u)) * Rabs x0.
  have Hc1 : 0 <= 42 * (u * u) by lra.
  apply: Rle_trans (Hround (x0 * y1) (42 * (u * u)) Hx0y1 Hc1) _.
  by apply: Hmono; nra.
have Hz01m : Rabs (p18z01m x0 y1) <= (42 * (u * u * u)) * Rabs x0.
  have Hc1 : 0 <= 42 * (u * u) by lra.
  rewrite /p18z01m round_generic; last first.
    rewrite (_ : x0 * y1 - p18z01p x0 y1 = -(p18z01p x0 y1 - x0 * y1));
      last by ring.
    by apply: generic_format_opp; rewrite /p18z01p; apply: format_err_mul.
  have E : x0 * y1 - p18z01p x0 y1 = - (RND (x0 * y1) - x0 * y1)
    by rewrite /p18z01p; ring.
  rewrite E Rabs_Ropp.
  apply: Rle_trans (Herr (x0 * y1) (42 * (u * u)) Hx0y1 Hc1) _.
  by apply: Hmono; nra.
have Ht1 : Rabs (p18z01m x0 y1 + x1 * y1) <= (126 * (u * u * u)) * Rabs x0.
  by have T := Rabs_triang (p18z01m x0 y1) (x1 * y1); lra.
have Hc126 : 0 <= 126 * (u * u * u) by lra.
have Heta1 : Rabs eta1 <= (126 * (u * u * u * u)) * Rabs x0.
  rewrite /eta1 /p18z31.
  apply: Rle_trans (Herr _ (126 * (u * u * u)) Ht1 Hc126) _.
  by apply: Hmono; nra.
have Hz31 : Rabs (p18z31 x0 x1 y1) <= (128 * (u * u * u)) * Rabs x0.
  rewrite /p18z31.
  apply: Rle_trans (Hround _ (126 * (u * u * u)) Ht1 Hc126) _.
  by apply: Hmono; nra.
have Ht2 : Rabs (p18z31 x0 x1 y1 + x0 * y2) <= (212 * (u * u * u)) * Rabs x0.
  by have T := Rabs_triang (p18z31 x0 x1 y1) (x0 * y2); lra.
have Hc212 : 0 <= 212 * (u * u * u) by lra.
have Heta2 : Rabs eta2 <= (212 * (u * u * u * u)) * Rabs x0.
  rewrite /eta2 /p18z3.
  apply: Rle_trans (Herr _ (212 * (u * u * u)) Ht2 Hc212) _.
  by apply: Hmono; nra.
have Hz3 : Rabs (p18z3 x0 x1 y1 y2) <= (216 * (u * u * u)) * Rabs x0.
  rewrite /p18z3.
  apply: Rle_trans (Hround _ (212 * (u * u * u)) Ht2 Hc212) _.
  by apply: Hmono; nra.
have Hb0v : dwh (p18b x0 x1 y1) = RND (x1 + p18z01p x0 y1)
  by rewrite /p18b Fast2SumS_hi.
have Htb : Rabs (x1 + p18z01p x0 y1) <= (2 * u + 43 * (u * u)) * Rabs x0.
  by have T := Rabs_triang x1 (p18z01p x0 y1); lra.
have Hcb : 0 <= 2 * u + 43 * (u * u) by lra.
have Hb0 : Rabs (dwh (p18b x0 x1 y1)) <= (2 * u + 46 * (u * u)) * Rabs x0.
  rewrite Hb0v.
  apply: Rle_trans (Hround _ (2 * u + 43 * (u * u)) Htb Hcb) _.
  by apply: Hmono; nra.
have Hb1 : Rabs (dwl (p18b x0 x1 y1))
    <= (2 * (u * u) + 46 * (u * u * u)) * Rabs x0.
  have Hm : Rabs (dwl (p18b x0 x1 y1)) <= ulp (dwh (p18b x0 x1 y1)) / 2.
    rewrite /p18b.
    have := @magnitude_Fast2SumS p Hp2 choice x1 (p18z01p x0 y1) Fx1 Fz.
    by rewrite /magnitudeDWR; case: TwoSum.Fast2SumS.
  have Hulp := @ulp_2u p beta Hp2 (dwh (p18b x0 x1 y1)).
  have Hstep : u * Rabs (dwh (p18b x0 x1 y1))
      <= u * ((2 * u + 46 * (u * u)) * Rabs x0)
    by apply: Rmult_le_compat_l; lra.
  by nra.
have Ht3 : Rabs (dwl (p18b x0 x1 y1) + p18z3 x0 x1 y1 y2)
    <= (2 * (u * u) + 262 * (u * u * u)) * Rabs x0.
  by have T := Rabs_triang (dwl (p18b x0 x1 y1)) (p18z3 x0 x1 y1 y2); lra.
have Hc3 : 0 <= 2 * (u * u) + 262 * (u * u * u) by lra.
(* [eta3] is Algorithm 18's [u^3] term, DOUBLED by [|b'1| <= 2u^2|x0|].      *)
have Heta3 : Rabs eta3
    <= (2 * (u * u * u) + 262 * (u * u * u * u)) * Rabs x0.
  rewrite /eta3 /p18s3.
  apply: Rle_trans (Herr _ (2 * (u * u) + 262 * (u * u * u)) Ht3 Hc3) _.
  by apply: Hmono; nra.
have Hs3' : Rabs (p18s3 x0 x1 y1 y2)
    <= (2 * (u * u) + 269 * (u * u * u)) * Rabs x0.
  rewrite /p18s3.
  apply: Rle_trans (Hround _ (2 * (u * u) + 262 * (u * u * u)) Ht3 Hc3) _.
  by apply: Hmono; nra.
have Ht4 : Rabs (p18s3 x0 x1 y1 y2 + x2)
    <= (6 * (u * u) + 269 * (u * u * u)) * Rabs x0.
  by have T := Rabs_triang (p18s3 x0 x1 y1 y2) x2; lra.
have Hc4 : 0 <= 6 * (u * u) + 269 * (u * u * u) by lra.
(* ... and [eta4], the new line, is the DOMINANT [6u^3]: [|x2| <= 4u^2|x0|]. *)
have Heta4 : Rabs eta4
    <= (6 * (u * u * u) + 269 * (u * u * u * u)) * Rabs x0.
  rewrite /eta4 /p20s3.
  apply: Rle_trans (Herr _ (6 * (u * u) + 269 * (u * u * u)) Ht4 Hc4) _.
  by apply: Hmono; nra.
have Hfin : Rabs (- (x1 * y2) - (x2 * y1) - (x2 * y2)
                  + eta1 + eta2 + eta3 + eta4)
    <= (8 * (u * u * u) + 1211 * (u * u * u * u)) * Rabs x0.
  have E : - (x1 * y2) - (x2 * y1) - (x2 * y2) + eta1 + eta2 + eta3 + eta4
      = - (x1 * y2) + - (x2 * y1) + - (x2 * y2) + eta1 + eta2 + eta3 + eta4
    by ring.
  rewrite E.
  have T6 := Rabs_triang (- (x1 * y2)) (- (x2 * y1)).
  have T5 := Rabs_triang (- (x1 * y2) + - (x2 * y1)) (- (x2 * y2)).
  have T4 := Rabs_triang (- (x1 * y2) + - (x2 * y1) + - (x2 * y2)) eta1.
  have T3 := Rabs_triang
    (- (x1 * y2) + - (x2 * y1) + - (x2 * y2) + eta1) eta2.
  have T2 := Rabs_triang
    (- (x1 * y2) + - (x2 * y1) + - (x2 * y2) + eta1 + eta2) eta3.
  have T1 := Rabs_triang
    (- (x1 * y2) + - (x2 * y1) + - (x2 * y2) + eta1 + eta2 + eta3) eta4.
  rewrite !Rabs_Ropp in T6.
  rewrite Rabs_Ropp in T5.
  lra.
(* Finally, the product itself is at least [(1 - 3u)|x0|].                   *)
have Hxy : (1 - 4 * u) * Rabs x0 <= Rabs ((x0 + x1 + x2) * (1 + y1 + y2)).
  rewrite Rabs_mult.
  have H1 : (1 - 3 * u) * Rabs x0 <= Rabs (x0 + x1 + x2).
    have T := Rabs_triang_inv (x0 + x1) (- x2).
    have E2 : x0 + x1 - - x2 = x0 + x1 + x2 by ring.
    rewrite E2 Rabs_Ropp in T.
    have T2 := Rabs_triang_inv x0 (- x1).
    have E3 : x0 - - x1 = x0 + x1 by ring.
    rewrite E3 Rabs_Ropp in T2.
    have Hslack : 4 * (u * u) * Rabs x0 <= u * Rabs x0
      by apply: Hmono; clear -Hu0 Hu64; nra.
    lra.
  have H2 : 1 - 44 * (u * u) <= Rabs (1 + y1 + y2).
    have T := Rabs_triang_inv (1 + y1) (- y2).
    have E2 : 1 + y1 - - y2 = 1 + y1 + y2 by ring.
    rewrite E2 Rabs_Ropp in T.
    have T2 := Rabs_triang_inv 1 (- y1).
    have E3 : 1 - - y1 = 1 + y1 by ring.
    rewrite E3 Rabs_Ropp Rabs_R1 in T2.
    have Hu3 : u * u * u <= /64 * (u * u).
      have -> : /64 * (u * u) = (u * u) * /64 by ring.
      by apply: Rmult_le_compat_l.
    lra.
  have Hxp := Rabs_pos (x0 + x1 + x2).
  have Hyp := Rabs_pos (1 + y1 + y2).
  have Hstep : (1 - 3 * u) * Rabs x0 * (1 - 44 * (u * u))
      <= Rabs (x0 + x1 + x2) * Rabs (1 + y1 + y2).
    apply: Rmult_le_compat => //; try lra.
      by apply: Rmult_le_pos; lra.
    by nra.
  have Hexp : (1 - 3 * u) * Rabs x0 * (1 - 44 * (u * u))
      = (1 - 3 * u - 44 * (u * u) + 132 * (u * u * u)) * Rabs x0 by ring.
  rewrite Hexp in Hstep.
  apply: Rle_trans Hstep.
  apply: Hmono.
  have Hkey : 0 <= u * (1 - 44 * u + 132 * (u * u))
    by apply: Rmult_le_pos; nra.
  by nra.
apply: Rle_trans Hfin _.
have Hpos : 0 <= 8 * (u * u * u) + 1330 * (u * u * u * u).
  have H4 : 0 <= u * u * u * u by apply: Rmult_le_pos; lra.
  by lra.
apply: Rle_trans (_ : (8 * (u * u * u) + 1330 * (u * u * u * u))
    * ((1 - 4 * u) * Rabs x0) <= _); last first.
  by apply: Rmult_le_compat_l.
have Hexp2 :
    (8 * (u * u * u) + 1330 * (u * u * u * u)) * ((1 - 4 * u) * Rabs x0)
    = ((8 * (u * u * u) + 1330 * (u * u * u * u)) * (1 - 4 * u)) * Rabs x0
  by ring.
rewrite Hexp2.
apply: Hmono.
have H4 : 0 <= u * u * u * u by apply: Rmult_le_pos; lra.
have H5 : u * u * u * u * u <= u * u * u * u * / 64
  by apply: Rmult_le_compat_l; lra.
have -> : (8 * (u * u * u) + 1330 * (u * u * u * u)) * (1 - 4 * u)
    = 8 * (u * u * u) + 1298 * (u * u * u * u)
      - 5320 * (u * u * u * u * u) by ring.
lra.
Qed.


End SecThreeProdOne.
