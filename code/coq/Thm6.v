(* ---------------------------------------------------------------------------*)
(* Paper Theorem 6 = the draft's Theorem 7 (doc/old-triplewors.pdf, 5.1):     *)
(* [VSEB (VecSum x_0 .. x_5)] is P-nonoverlapping, for [p >= 4].              *)
(*                                                                            *)
(* This is the ONE open result of the development.  It needs both [VecSum]    *)
(* and [VSEB] and nothing else, so it lives in its own file rather than in    *)
(* [TWSum.v] -- [Merge]/[TWR] are not on its path.                            *)
(*                                                                            *)
(* THE PROOF TO FOLLOW IS [doc/thm6.md] SECTION 5, not the published sketch.  *)
(* The published paper states Theorem 6 with only a five-line sketch and      *)
(* "for space constraints, the proof is not detailed"; the earlier draft      *)
(* proves the same statement in full as Theorem 7.  Beware: the sketch is not *)
(* a faithful compression of the draft (doc/thm6.md 5.6) -- it uses the wrong *)
(* index ([i] for the draft's [i_1]) and the wrong constant ([1/2 uls(e_j)]   *)
(* for the draft's [5/8 u]).                                                  *)
(* ---------------------------------------------------------------------------*)

From Stdlib Require Import ZArith Reals Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
Require Import Nmore Rmore Fmore Rstruct MULTmore prelim.
From Flocq Require Import Pff.Pff2Flocq.
Require Import Uls.
Require Import TwoSum.
Require Import Nonoverlap.
Require Import VecSum.
Require Import VSEB.

Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SecThm6.

Variable p : Z.
Hypothesis Hp2 : (1 < p)%Z.
(* The draft uses [p >= 4] explicitly, in the [|e_{i_1}| > 1/2 u] case of the *)
(* VSEB analysis ("this part uses p >= 4, and ties-to-even for p = 4").       *)
Hypothesis Hp4 : (4 <= p)%Z.

Local Notation beta := radix2.
Local Notation pow e := (bpow beta e).

Local Instance p_gt_0 : Prec_gt_0 p.
Proof. now apply Z.lt_trans with (2 := Hp2). Qed.

Open Scope R_scope.

Local Notation u := (u p beta).
Local Notation uE := (@uE p).

Variable choice : Z -> bool.
Hypothesis choice_sym : forall x, choice x = ~~ choice (- (x + 1))%Z.
Local Notation rnd := (Znearest choice).
Local Instance valid_rnd : Valid_rnd rnd := valid_rnd_N choice.

Local Notation fexp := (FLX_exp p).
Local Notation format := (generic_format beta fexp).
Local Notation ulp := (ulp beta fexp).
Local Notation uls := (uls p).

Local Notation Pnonoverlap := (Pnonoverlap p).
Local Notation pairwise_ulp := (pairwise_ulp p).

Local Notation vecSum := (vecSum p choice).
Local Notation vecSumAux := (vecSumAux p choice).
Local Notation vseb := (vseb p choice).
Local Notation vsebAux := (vsebAux p choice).
Local Notation vecSum_run_ufp := (vecSum_run_ufp Hp2 choice_sym).
Local Notation vecSum_err_ufp := (vecSum_err_ufp Hp2 choice_sym).

Local Notation RND := (round beta fexp rnd).
Local Notation magnitudeDWR := (magnitudeDWR p).
Local Notation TwoSum_hi := (@TwoSum_hi p choice).
Local Notation TwoSum_correct_loc := (TwoSum_correct_loc Hp2 choice_sym).
Local Notation format_TwoSum := (@format_TwoSum p Hp2 choice).
Local Notation magnitude_TwoSum := (magnitude_TwoSum Hp2 choice_sym).
Local Notation vsebAux_head_lt_mass := (vsebAux_head_lt_mass Hp2 choice_sym).
Local Notation uls_gt_0 := (@uls_gt_0 p).
Local Notation uls_le_abs := (@uls_le_abs p).
Local Notation format_vecSum := (format_vecSum Hp2).
Local Notation size_vecSum := (@size_vecSum p choice).

(* ===========================================================================*)
(*  Theorem 6 / draft Theorem 7.                                              *)
(*                                                                            *)
(*  NOTE what is NOT here, compared with the FLT statement on [main]: there is*)
(*  no no-underflow hypothesis [emin + p <= mag z].  FLX IS the paper's model *)
(*  (unlimited exponent range), so this is the paper's statement, unpatched.  *)
(*  That is not just cosmetic: the draft's proof WLOGs [uls(e_j) = u] and     *)
(*  [uls(e_{i_0}) = u] and states every constant relative to that             *)
(*  normalisation.  Rescaling is invalid under FLT with a real [emin] -- which*)
(*  is why [vecSum_sep] had to be done scaling-free with a symbolic carry.    *)
(*  Under FLX the WLOG is legitimate, so the draft's proof is transcribable.  *)
(*                                                                            *)
(*  ROADMAP (doc/thm6.md 5.1-5.3).  Available (Qed, ported from main):        *)
(*   *1 run bound   [vecSum_run_ufp] : |s_j| <= 4 ufp(x_j), <= 2 ufp(x_{j-1}) *)
(*      err bound   [vecSum_err_ufp] : |e_{i+1}| <= 2u ufp(x_i)               *)
(*      the tie     [RN_midpoint_even], [ties_to_even]                        *)
(*   To do:                                                                   *)
(*   *2 (5.2) Assume [uls(e_j) = u] (WLOG) and [e_i >= 5/8 u] for some j < i. *)
(*      Force: |s_{i-1}| >= 1; then [2u | s_{i-1}] but [2u  |  e_j] gives some*)
(*      i' <= i-2 with [~(2u | x_i')], so |x_{i-2}| < 1; hence |x_i| < u,     *)
(*      |s_i| <= 2u, |x_{i-1}| <= 1-u.  With |s_{i-1} + e_i| >= 1 + 5/8 u this*)
(*      pins [s_{i-1} = 1], [x_{i-1} = 1-u], [s_i = u+e_i], and [2u^2 | e_i]. *)
(*      Then the right-of-i and left-of-i case analyses.                      *)
(*   *3 (5.3) VSEB: take [i_0] with [y_j = r_{i_0-1}] (so [eps_{i_0} <> 0]),  *)
(*      and [i_1] the first nonzero [e_i] after [e_{i_0}]; WLOG               *)
(*      [uls(e_{i_0}) = u], so [|eps_{i_0}| >= u] and [ulp(y_j) >= 2u].  Then *)
(*      three cases: [i_1 <= 3 /\ e_{i_1} >= 5/8 u]; [i_1 >= 4 /\ e_{i_1} >=  *)
(*      5/8 u]; [0 < e_{i_1} < 5/8 u] (itself split on 1/2 u and 1/4 u).      *)
(*                                                                            *)
(*  The [<= 6] bound is paid for in *3, via the counting: "we are adding at   *)
(*  most 3 of them", and the final [|e_4| = |e_3|] / [|e_5| <= uls(e_4)] step.*)
(*  It is necessary: Theorem 6 is FALSE for 7 inputs (doc/thm6.md 3).         *)
(* ===========================================================================*)
(* ===========================================================================*)
(*  The VSEB block-mass invariant.                                            *)
(*                                                                            *)
(*  The engine of Theorem 2 is [vsebAux_head_lt_mass]: the first term VSEB    *)
(*  emits from a nonzero remainder [eps] over a tail [l] has [|.| < 2 |eps|],  *)
(*  needing ONLY the mass bound [sum|l| <= uls(eps)(1 - 2^{-|l|})] and the     *)
(*  block-length bound [|l| + 2 <= p + 1] -- NOT F-nonoverlap.  Paired with    *)
(*  the always-true [2 |et| <= ulp(r)] ([magnitude_TwoSum]), P-nonoverlap of  *)
(*  each emitted step follows.  [vsebMass] records exactly those two           *)
(*  obligations at every VSEB emit along the walk, so that [vseb] of any list *)
(*  satisfying it is P-nonoverlapping (the [vsebAux_Pnonoverlap_mass] driver   *)
(*  below).  This is the interface the draft's Theorem-7 proof feeds: it is    *)
(*  weaker than F-nonoverlap (the VecSum output is not F-nonoverlapping), and  *)
(*  the [<= 6] bound enters through the per-emit block-length obligation.      *)
(* ===========================================================================*)
Fixpoint vsebMass (eps : R) (l : seq R) : Prop :=
  match l with
  | [::]    => True
  | [:: _]  => True
  | e :: l' =>
      let: DWR r et := TwoSum p choice eps e in
      if Req_EM_T et 0 then vsebMass r l'
      else [/\ (Z.of_nat (size l').+2 <= p + 1)%Z,
               sumRabs l' <= uls et * (1 - (/ 2) ^ size l') &
               vsebMass et l']
  end.

(* One-step unfolding (by reflexivity), exposing [TwoSum eps e] the way        *)
(* [vsebAux_consS] does, so a following [case] captures it.                     *)
Lemma vsebMass_consS eps e e2 l :
  vsebMass eps [:: e, e2 & l] =
  (let: DWR r et := TwoSum p choice eps e in
   if Req_EM_T et 0 then vsebMass r (e2 :: l)
   else [/\ (Z.of_nat (size (e2 :: l)).+2 <= p + 1)%Z,
            sumRabs (e2 :: l) <= uls et * (1 - (/ 2) ^ size (e2 :: l)) &
            vsebMass et (e2 :: l)]).
Proof. by []. Qed.

(* The driver: [vseb] of a list carrying the block-mass invariant is           *)
(* P-nonoverlapping.  Same induction as [VSEB.vsebAux_Pnonoverlap], but the    *)
(* emitted-head bound comes from [vsebAux_head_lt_mass] (mass) instead of      *)
(* F-nonoverlap, and the invariant transported to the recursion is [vsebMass]. *)
Lemma vsebAux_Pnonoverlap_mass eps l :
  format eps -> {in l, forall z, format z} ->
  vsebMass eps l -> Pnonoverlap (vsebAux eps l).
Proof.
elim: l eps => [|e l' IH] eps epsF lF Hm.
  by move=> i; rewrite /= ltnS ltn0.
have Fe : format e by apply: lF; rewrite inE eqxx.
case: l' IH lF Hm => [|e2 l''] IH lF Hm.
  (* Last step: [vsebAux eps [:: e] = [:: y0; y1]], [|y1| < ulp y0].           *)
  rewrite vsebAux_1; case E1 : (TwoSum p choice eps e) => [y0 y1].
  move=> [|i] /= Hi; last by move: Hi; rewrite ltnS ltnS ltn0.
  have Hmag := magnitude_TwoSum epsF Fe; rewrite E1 /= in Hmag.
  case: (Req_dec y1 0) => [y10|y1n0]; first by left.
  right.
  have y0n0 : y0 <> 0.
    by move=> y00; apply: y1n0; move: Hmag;
       rewrite y00 ulp_FLX_0; split_Rabs; lra.
  have Hy : 0 < ulp y0 by rewrite ulp_neq_0 //; apply: bpow_gt_0.
  by lra.
(* General step: [2Sum(eps, e) = (r, et)].                                    *)
rewrite vsebAux_consS; case E1 : (TwoSum p choice eps e) => [r et].
have Hr : r = RND (eps + e) by have := TwoSum_hi eps e; rewrite E1.
move: Hm; rewrite vsebMass_consS E1.
case: (Req_EM_T et 0) => [et0|etn0] Hm.
  (* [et = 0]: nothing emitted; carry [r] and recurse.                        *)
  apply: IH => //.
  - by rewrite Hr; apply: generic_format_round.
  by move=> z zI; apply: lF; rewrite inE zI orbT.
(* [et <> 0]: emit [r], recurse on the new remainder [et].                    *)
have Fet : format et
  by have H := format_TwoSum epsF Fe; rewrite E1 /= in H; case: H.
have Fl' : {in e2 :: l'', forall z, format z}
  by move=> z zI; apply: lF; rewrite inE zI orbT.
case: Hm => Hszl' Hmass Hmrec.
have Hrec : Pnonoverlap (vsebAux et (e2 :: l'')) by apply: IH.
move=> [|i] /= Hi.
  right.
  have Hulp : 2 * Rabs et <= ulp r.
    by have Hmag := magnitude_TwoSum epsF Fe; rewrite E1 /= in Hmag; lra.
  have Hnext : Rabs (nth 0 (vsebAux et (e2 :: l'')) 0) < 2 * Rabs et.
    by apply: vsebAux_head_lt_mass.
  by apply: (Rlt_le_trans _ _ _ Hnext Hulp).
by apply: (Hrec i); move: Hi; rewrite ltnS.
Qed.

(* ===========================================================================*)
(*  THE HARD CORE (the draft's Theorem 7 proof, doc/thm6.md 5.2-5.3): the      *)
(*  VecSum output supplies the block-mass invariant.  This is where steps      *)
(*  *2 (the conditions forced by a violation) and *3 (the VSEB case study)     *)
(*  live, and where the [<= 6] bound and [p >= 4] are consumed.                *)
(* ===========================================================================*)
Lemma vecSum_vsebMass (l : seq R) :
  ties_to_even choice ->
  (size l <= 6)%N ->
  {in l, forall z, format z} ->
  (forall i, (i < size l)%N -> nth (0:R) l i <> 0) ->
  sorted_mag l -> pairwise_ulp l ->
  vsebMass (head 0 (vecSum l)) (behead (vecSum l)).
Proof.
Admitted.

(* ===========================================================================*)
(*  LAYER 2 (the draft's Theorem 7 proper): the ZERO-FREE case.               *)
(*                                                                            *)
(*  This is what doc/thm6.md 5.1-5.3 actually proves.  The draft's [x_i] are  *)
(*  nonzero throughout -- it takes [uls(e_j)] and divides by it -- and our    *)
(*  [vecSum_run_ufp] / [vecSum_err_ufp] likewise need [Hnz].  Zeros are OUR   *)
(*  obligation, discharged in layer 1 below.                                  *)
(* ===========================================================================*)
Lemma vecSum_vseb_Pnonoverlap_nz (l : seq R) :
  ties_to_even choice ->
  (size l <= 6)%N ->
  {in l, forall z, format z} ->
  (forall i, (i < size l)%N -> nth (0:R) l i <> 0) ->
  sorted_mag l -> pairwise_ulp l ->
  Pnonoverlap (vseb (vecSum l)).
Proof.
move=> Heven Hsz Hfmt Hnz Hsort Hpair.
have HfV : {in vecSum l, forall z, format z} by apply: format_vecSum.
have HM := vecSum_vsebMass Heven Hsz Hfmt Hnz Hsort Hpair.
rewrite /vseb; case E : (vecSum l) HfV HM => [|e0 tl] HfV HM.
  by move=> i; rewrite /= ltn0.
apply: vsebAux_Pnonoverlap_mass => //.
- by apply: HfV; rewrite inE eqxx.
by move=> z zI; apply: HfV; rewrite inE zI orbT.
Qed.

(* ===========================================================================*)
(*  LAYER 1: zeros.  Under [sorted_mag] the zeros of [l] form a SUFFIX, so a  *)
(*  list is either zero-free (layer 2) or ends in a zero, which we peel.      *)
(* ===========================================================================*)

(* [sorted_mag] makes the zeros a suffix: a nonzero LAST entry forces every   *)
(* entry nonzero, since [|nth i| >= |last| > 0] along the chain.              *)
Lemma sorted_mag_last_nz (m : seq R) (x : R) :
  sorted_mag (rcons m x) -> x <> 0 ->
  forall i, (i < size (rcons m x))%N -> nth (0:R) (rcons m x) i <> 0.
Proof.
move=> Hsort xn0 i Hi.
have Hlast : nth (0:R) (rcons m x) (size m) = x by rewrite nth_rcons ltnn eqxx.
have Hsz : size (rcons m x) = (size m).+1 by rewrite size_rcons.
(* Walk down from the last index, using one [sorted_mag] step at a time.      *)
have Hdown : forall d, (d <= size m)%N ->
    nth (0:R) (rcons m x) (size m - d) <> 0.
  elim=> [_|d IH Hd]; first by rewrite subn0 Hlast.
  have Hd' : (d <= size m)%N by apply: ltnW.
  have Hlt : (size m - d.+1).+1 = (size m - d)%N by rewrite subnSK.
  have Hin : ((size m - d.+1).+1 < size (rcons m x))%N.
    by rewrite Hlt Hsz ltnS leq_subr.
  move=> Hz; apply: (IH Hd').
  have := Hsort _ Hin; rewrite Hlt Hz Rabs_R0 => Habs.
  by apply/Rabs_eq_R0/Rle_antisym => //; apply: Rabs_pos.
have -> : i = (size m - (size m - i))%N by rewrite subKn // -ltnS -Hsz.
by apply: Hdown; apply: leq_subr.
Qed.

(* [vecSumAux] on a list with a trailing zero: the deepest step is            *)
(* [2Sum(x_{n-1}, 0) = (x_{n-1}, 0)] (exact, since [x_{n-1}] is a float), so   *)
(* the running sum is unchanged and the emitted error is a trailing zero.      *)
Lemma vecSumAux_rcons0 (m : seq R) :
  (0 < size m)%N -> {in m, forall z, format z} ->
  vecSumAux (rcons m 0) =
    (rcons (vecSumAux m).1 0, (vecSumAux m).2).
Proof.
case: m => [//|a m _]; elim: m a => [a aF|b m IH a abF].
  have Fa : format a by apply: aF; rewrite inE eqxx.
  have -> : rcons [:: a] 0 = [:: a, 0 & [::]] by [].
  rewrite vecSumAux_cons.
  have E0 : vecSumAux [:: 0] = ([::], 0) by [].
  have Ea : vecSumAux [:: a] = ([::], a) by [].
  rewrite E0 Ea; case E : (TwoSum p choice a 0) => [si ei1].
  have := @dwh_TwoSum_r0 p choice a Fa; rewrite E /= => ->.
  by have := @dwl_TwoSum_r0 p Hp2 choice choice_sym a Fa; rewrite E /= => ->.
have Hbm : {in b :: m, forall z, format z}.
  by move=> z zI; apply: abF; rewrite inE zI orbT.
have IH' := IH b Hbm; rewrite rcons_cons in IH'.
rewrite rcons_cons vecSumAux_cons rcons_cons vecSumAux_cons IH'.
by case: (vecSumAux (b :: m)) => es s /=; case: (TwoSum p choice a s).
Qed.

(* VecSum carries a trailing zero through untouched: the running sum entering *)
(* the last step is [s = 0], so [2Sum(x_{n-2}, 0) = (x_{n-2}, 0)] and the     *)
(* emitted error is [0].                                                      *)
Lemma vecSum_rcons0 (m : seq R) :
  (0 < size m)%N -> {in m, forall z, format z} ->
  vecSum (rcons m 0) = rcons (vecSum m) 0.
Proof.
move=> Hs Hf; rewrite /vecSum vecSumAux_rcons0 //.
by case: (vecSumAux m) => es s /=.
Qed.

(* VSEB absorbs a trailing zero at the [vsebAux] level: the terminal step is  *)
(* [2Sum(_, 0) = (_, 0)], whose zero error either is dropped (output           *)
(* unchanged) or, at the very last position, emitted as a trailing zero.       *)
Lemma vsebAux_rcons0 (l : seq R) (eps : R) :
  format eps -> {in l, forall z, format z} ->
  vsebAux eps (rcons l 0) = vsebAux eps l \/
  vsebAux eps (rcons l 0) = rcons (vsebAux eps l) 0.
Proof.
(* [vsebAux w [:: 0] = [:: w; 0]]: a trailing zero is an exact merge.         *)
have vseb0 : forall w : R, format w -> vsebAux w [:: 0] = [:: w; 0].
  move=> w wF; rewrite vsebAux_1; case Ew : (TwoSum p choice w 0) => [z0 z1].
  have := @dwh_TwoSum_r0 p choice w wF; rewrite Ew /= => ->.
  by have := @dwl_TwoSum_r0 p Hp2 choice choice_sym w wF; rewrite Ew /= => ->.
elim: l eps => [|e l' IH] eps epsF lF.
  by right; rewrite (vseb0 _ epsF).
have eF : format e by apply: lF; rewrite inE eqxx.
have Fl' : {in l', forall z, format z}.
  by move=> z zI; apply: lF; rewrite inE zI orbT.
have [rF etF] : format (dwh (TwoSum p choice eps e)) /\
                format (dwl (TwoSum p choice eps e))
  by apply: format_TwoSum.
rewrite rcons_cons.
case: l' IH lF Fl' rF etF => [|e2 l2] IH lF Fl' rF etF.
  (* One remaining term: the trailing zero is either dropped or emitted last. *)
  have -> : e :: rcons [::] 0 = [:: e, 0 & [::]] by [].
  rewrite vsebAux_consS vsebAux_1.
  case E : (TwoSum p choice eps e) => [r et].
  have rF' : format r by move: rF; rewrite E.
  have etF' : format et by move: etF; rewrite E.
  case: (Req_EM_T et 0) => [et0|etn0].
    by left; rewrite [is_left _]/= (vseb0 r rF') et0.
  by right; rewrite [is_left _]/= (vseb0 et etF').
(* Two or more terms: recurse, the zero travelling to the tail.               *)
have -> : e :: rcons (e2 :: l2) 0 = [:: e, e2 & rcons l2 0] by rewrite rcons_cons.
rewrite !vsebAux_consS.
case E : (TwoSum p choice eps e) => [r et].
have rF' : format r by move: rF; rewrite E.
have etF' : format et by move: etF; rewrite E.
case: (Req_EM_T et 0) => [et0|etn0]; rewrite [is_left _]/= -rcons_cons.
  exact: (IH r rF' Fl').
have [->|->] := IH et etF' Fl'; first by left.
by right; rewrite rcons_cons.
Qed.

(* VSEB absorbs a trailing zero: [2Sum(eps, 0) = (eps, 0)] has zero error, so *)
(* nothing is emitted and the remainder is carried.  The output therefore     *)
(* either is unchanged or gains a single trailing zero.                       *)
Lemma vseb_rcons0 (X : seq R) :
  (0 < size X)%N -> {in X, forall z, format z} ->
  vseb (rcons X 0) = vseb X \/ vseb (rcons X 0) = rcons (vseb X) 0.
Proof.
case: X => [//|e0 l'] _ Hf.
have e0F : format e0 by apply: Hf; rewrite inE eqxx.
have l'F : {in l', forall z, format z}.
  by move=> z zI; apply: Hf; rewrite inE zI orbT.
rewrite rcons_cons /vseb.
exact: vsebAux_rcons0.
Qed.

(* ===========================================================================*)
(*  Theorem 6 / draft Theorem 7 -- the target.                                *)
(* ===========================================================================*)
Lemma vecSum_vseb_Pnonoverlap (l : seq R) :
  ties_to_even choice ->
  (size l <= 6)%N ->
  {in l, forall z, format z} -> sorted_mag l -> pairwise_ulp l ->
  Pnonoverlap (vseb (vecSum l)).
Proof.
elim/last_ind: l => [_ _ _ _ _ i|m x IH Heven Hsz Hfmt Hsort Hpair].
  by rewrite /vseb /vecSum /= ltnS ltn0.
(* A nonzero last entry means the whole list is zero-free: layer 2 applies.   *)
case: (Req_dec x 0) => [x0|xn0]; last first.
  apply: vecSum_vseb_Pnonoverlap_nz => //.
  exact: sorted_mag_last_nz Hsort xn0.
(* Otherwise peel the trailing zero: VecSum passes it through, VSEB absorbs   *)
(* it, and the guard makes whatever trailing zero survives harmless.          *)
case: (posnP (size m)) => [/eqP|Hm].
  by rewrite size_eq0 => /eqP-> i; rewrite x0 /vseb /vecSum /= ltnS ltn0.
have Hfm : {in m, forall z, format z}.
  by move=> z zIm; apply: Hfmt; rewrite mem_rcons inE zIm orbT.
have Hrec : Pnonoverlap (vseb (vecSum m)).
  apply: IH => //.
  - by apply: leq_trans Hsz; rewrite size_rcons leqW.
  - exact: sorted_mag_rcons Hsort.
  exact: pairwise_ulp_rcons Hpair.
rewrite x0 vecSum_rcons0 //.
have Hsz0 : (0 < size (vecSum m))%N by rewrite size_vecSum.
have HfV : {in vecSum m, forall z, format z} by apply: format_vecSum.
have [->|->] := vseb_rcons0 Hsz0 HfV; first exact: Hrec.
exact: Pnonoverlap_rcons0.
Qed.

End SecThm6.
