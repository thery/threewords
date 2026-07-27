(* ---------------------------------------------------------------------------*)
(* Algorithm 18 (3Prod^one): the product of a DOUBLE word by a triple word    *)
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
(* STATUS: skeleton -- both results are [Admitted].                           *)
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
(*    |z01+| <= 3u|x0|      |z01-| <= 2u^2|x0|     |b'0| <= 5u|x0|            *)
(*    |b'1|  <= 5u^2|x0|    |z3,1| <= 5u^2|x0|     |z3|  <= 10u^2|x0|         *)
(*    |s3|   <= 16u^2|x0|                                                     *)
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
  Rabs x1 <= u * Rabs x0 -> Rabs y1 <= 2 * u ->
  Rabs (dwh (p18b x0 x1 y1)) <= 5 * u * Rabs x0.
Proof.
move=> Hx1 Hy1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := @u_le_64 p Hp6.
have Hz := p18z01p_le x0 Hy1.
rewrite /p18b Fast2SumS_hi.
apply: Rle_trans (@abs_round_le_rel p Hp2 choice _) _.
have T := Rabs_triang x1 (p18z01p x0 y1).
have Hx := Rabs_pos x0.
have Hkey : 0 <= Rabs x0 * (u * (1 - 4 * u)) by apply: Rmult_le_pos; nra.
nra.
Qed.

Lemma p18b1_le x0 x1 y1 :
  format x1 -> Rabs x1 <= u * Rabs x0 -> Rabs y1 <= 2 * u ->
  Rabs (dwl (p18b x0 x1 y1)) <= 5 * (u * u) * Rabs x0.
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
  format x0 -> format y1 -> Rabs x1 <= u * Rabs x0 -> Rabs y1 <= 2 * u ->
  Rabs (p18z31 x0 x1 y1) <= 5 * (u * u) * Rabs x0.
Proof.
move=> Fx0 Fy1 Hx1 Hy1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := @u_le_64 p Hp6.
have Hz01m := p18z01m_le Fx0 Fy1 Hy1.
rewrite /p18z31.
apply: Rle_trans (@abs_round_le_rel p Hp2 choice _) _.
have T := Rabs_triang (p18z01m x0 y1) (x1 * y1).
have Hxy : Rabs (x1 * y1) <= 2 * (u * u) * Rabs x0.
  rewrite Rabs_mult.
  have Hx := Rabs_pos x0; have Hx1p := Rabs_pos x1.
  have H2 : Rabs x1 * Rabs y1 <= (u * Rabs x0) * (2 * u).
    apply: Rmult_le_compat => //; apply: Rabs_pos.
  nra.
have Hx := Rabs_pos x0.
have Hkey : 0 <= Rabs x0 * (u * u * (1 - 4 * u)) by apply: Rmult_le_pos; nra.
nra.
Qed.

Lemma p18z3_le x0 x1 y1 y2 :
  format x0 -> format y1 -> Rabs x1 <= u * Rabs x0 -> Rabs y1 <= 2 * u ->
  Rabs y2 <= 4 * (u * u) ->
  Rabs (p18z3 x0 x1 y1 y2) <= 10 * (u * u) * Rabs x0.
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
have Hkey : 0 <= Rabs x0 * (u * u * (1 - 9 * u)) by apply: Rmult_le_pos; nra.
nra.
Qed.

Lemma p18s3_le x0 x1 y1 y2 :
  format x0 -> format x1 -> format y1 ->
  Rabs x1 <= u * Rabs x0 -> Rabs y1 <= 2 * u -> Rabs y2 <= 4 * (u * u) ->
  Rabs (p18s3 x0 x1 y1 y2) <= 16 * (u * u) * Rabs x0.
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
have Hkey : 0 <= Rabs x0 * (u * u * (1 - 15 * u)) by apply: Rmult_le_pos; nra.
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
have Hb0 := p18b0_le Hx1 Hy1.
have Hs3 := p18s3_le Fx0 Fx1 Fy1 Hx1 Hy1 Hy2.
have HX := Rabs_pos x0.
set b0' := dwh (p18b x0 x1 y1) in Fb0 Hb0 *.
set s3 := p18s3 x0 x1 y1 y2 in Fs3 Hs3 *.
set S := RND (b0' + s3).
have HS : Rabs S <= 6 * u * Rabs x0.
  apply: Rle_trans (@abs_round_le_rel p Hp2 choice _) _.
  have T := Rabs_triang b0' s3.
  have Hkey2 : 0 <= Rabs x0 * (u - 21 * (u * u) - 16 * (u * u * u))
    by apply: Rmult_le_pos; nra.
  nra.
(* [e0] is [x0] to within [7u], so its ulp is at least [u(1 - 7u)|x0|].       *)
have He0lb : (1 - 7 * u) * Rabs x0 <= Rabs (p18e0 x0 x1 y1 y2).
  rewrite He0 -/b0' -/s3 -/S.
  have H1 : (1 - 6 * u) * Rabs x0 <= Rabs (x0 + S).
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
have He2b : Rabs (p18e2 x0 x1 y1 y2) <= 6 * (u * u) * Rabs x0.
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
    <= (/2 + 7 * u) * ulp (p18e0 x0 x1 y1 y2).
  have T := Rabs_triang (p18e1 x0 x1 y1 y2) (p18e2 x0 x1 y1 y2).
  have Hkey : 6 * (u * u) * Rabs x0 <= 7 * u * ulp (p18e0 x0 x1 y1 y2).
    have H7 : u * ((1 - 7 * u) * Rabs x0) <= u * Rabs (p18e0 x0 x1 y1 y2)
      by apply: Rmult_le_compat_l; lra.
    have Hkey2 : 0 <= Rabs x0 * (u * u * (1 - 49 * u))
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
  have Hcoef : (1 + u) * (/2 + 7 * u) < 1 by nra.
  have Hstep : (1 + u) * Rabs (p18e1 x0 x1 y1 y2 + p18e2 x0 x1 y1 y2)
      <= (1 + u) * ((/2 + 7 * u) * ulp (p18e0 x0 x1 y1 y2))
    by apply: Rmult_le_compat_l; lra.
  have Hlast : 0 < ulp (p18e0 x0 x1 y1 y2) * (1 - (1 + u) * (/2 + 7 * u))
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

(* Correctness, part 2: the relative error is [u^3 + 260u^4] (old paper       *)
(* Section 8.4) as soon as the second argument is within [40u^2] of [1] --    *)
(* which is what Algorithm 13's [i = 2 - 3Prod_{2,3}(b, x)] satisfies.        *)
Lemma ThreeProdOne_error x y :
  ties_to_even choice ->
  isDW x -> isTW y -> tw0 y = 1 -> Rabs (TWval y - 1) <= 40 * (u * u) ->
  Rabs (TWval (ThreeProdOne x y) - TWval x * TWval y)
    <= (u * u * u + 260 * (u * u * u * u)) * Rabs (TWval x * TWval y).
Proof.
Admitted.

End SecThreeProdOne.
