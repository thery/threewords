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
Local Notation cexp := (cexp beta fexp).
Local Notation mant := (scaled_mantissa beta fexp).
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
Local Notation TwoSum := (TwoSum.TwoSum p choice).
Local Notation vecSumAux_cons := (@vecSumAux_cons p choice).
Local Notation vecSumAux_nth1 := (@vecSumAux_nth1 p choice).
Local Notation format_vecSumAux := (@format_vecSumAux p Hp2 choice).
Local Notation dwh_TwoSum_r0 := (@dwh_TwoSum_r0 p choice).
Local Notation dwl_TwoSum_r0 := (@dwl_TwoSum_r0 p Hp2 choice choice_sym).
Local Notation TwoSum_err_uls_ge := (@TwoSum_err_uls_ge p Hp2 choice choice_sym).
Local Notation TwoSum_hi := (@TwoSum_hi p choice).
Local Notation TwoSum_correct_loc := (TwoSum_correct_loc Hp2 choice_sym).
Local Notation format_TwoSum := (@format_TwoSum p Hp2 choice).
Local Notation magnitude_TwoSum := (magnitude_TwoSum Hp2 choice_sym).
Local Notation vsebAux_head_lt_mass := (vsebAux_head_lt_mass Hp2 choice_sym).
Local Notation vsebAux_head_leB := (vsebAux_head_leB Hp2 choice_sym).
Local Notation uls_gt_0 := (@uls_gt_0 p).
Local Notation uls_le_abs := (@uls_le_abs p).
Local Notation format_vecSum := (format_vecSum Hp2).
Local Notation size_vecSum := (@size_vecSum p choice).
Local Notation vecSumAux_imul := (@vecSumAux_imul p Hp2 choice choice_sym).
Local Notation vecSumAux_split := (@vecSumAux_split p choice).

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
(* Length-free variant of [vsebAux_head_lt_mass]: the block bound             *)
(* [|head| < 2|eps|] from a mass bound WITHOUT the block-length hypothesis.    *)
(* The length was only needed in the power-of-two ([uls eps = |eps|]) case of  *)
(* [vsebAux_head_lt_mass], to keep [pred(2|eps|)] above the tail mass; the      *)
(* stronger margin [(1 - 2u)] here supplies exactly that slack directly.  This *)
(* matters because a VecSum output can emit over a long (mostly-zero) tail     *)
(* whose length exceeds [p - 1] (e.g. at [p = 4], a size-6 output), so the     *)
(* length bound is genuinely unavailable -- but the tail mass is tiny.         *)
Lemma vsebAux_head_lt_massU eps l :
  format eps -> {in l, forall z, format z} -> eps <> 0 ->
  sumRabs l <= uls eps * (1 - 2 * u) ->
  Rabs (nth 0 (vsebAux eps l) 0) < 2 * Rabs eps.
Proof.
move=> epsF lF epsn0 Hsum.
have Hu0 : 0 < uls eps by apply: uls_gt_0.
have Hae : uls eps <= Rabs eps by apply: uls_le_abs.
have He0 : 0 < Rabs eps by apply: Rabs_pos_lt.
have Hupos : 0 < u by rewrite /Fmore.u; have := bpow_gt_0 beta (1 - p); lra.
have Hg : uls eps = pow (cexp eps + Z.of_nat (trZ (Ztrunc (mant eps)))).
  by rewrite /uls; case: Req_bool_spec => // eps0; case: (epsn0 eps0).
set g := (cexp eps + Z.of_nat (trZ (Ztrunc (mant eps))))%Z.
have HmB : (Z.abs (Ztrunc (mant eps)) < beta ^ p)%Z.
  apply: lt_IZR; rewrite abs_IZR -scaled_mantissa_generic // IZR_Zpower;
    last lia.
  apply: Rlt_le_trans (_ : pow (mag beta eps - cexp eps) <= _)%R.
    exact: scaled_mantissa_lt_bpow.
  by apply: bpow_le; rewrite /cexp /FLX_exp; lia.
have Heps : Rabs eps = IZR (Z.abs (Ztrunc (mant eps))) * pow (cexp eps).
  by rewrite {1}epsF /F2R /= Rabs_mult -abs_IZR Rabs_pow.
have Hcu : pow (cexp eps) <= uls eps.
  by rewrite Hg; apply: bpow_le; rewrite /g;
     have := Zle_0_nat (trZ (Ztrunc (mant eps))); lia.
suff [B [FB HVB HBlt]] :
    exists B, [/\ format B, Rabs eps + sumRabs l <= B & B < 2 * Rabs eps].
  by apply: Rle_lt_trans (vsebAux_head_leB epsF lF FB HVB) HBlt.
have [HM|HM] := Rle_lt_or_eq_dec _ _ Hae.
- (* [uls eps < Rabs eps] (mantissa > 1): [B = |eps| + uls eps] is a float in *)
  (* range, and [< 2|eps|] since [uls eps < |eps|].                           *)
  exists (Rabs eps + uls eps).
  have Huim : is_imul (uls eps) (pow g) by rewrite Hg; exists 1%Z;
    rewrite Rmult_1_l.
  have Heim : is_imul (Rabs eps) (pow g).
    have Him : is_imul eps (pow g) by rewrite -Hg; exact: uls_imul epsF.
    case: (Rle_lt_dec 0 eps) => He.
      by rewrite Rabs_pos_eq.
    by rewrite Rabs_left //; apply: is_imul_opp.
  split.
  + apply: (imul_format Hp2 (e := g) (b := Rabs eps + uls eps)) => //.
    * by apply: is_imul_add.
    * by rewrite Rabs_pos_eq; lra.
    rewrite bpow_plus.
    have Hub : Rabs eps <= (pow p - 1) * uls eps.
      rewrite Heps.
      apply: Rle_trans (_ : (pow p - 1) * pow (cexp eps) <= _).
        apply: Rmult_le_compat_r; first by apply: bpow_ge_0.
        have -> : pow p - 1 = IZR (beta ^ p - 1).
          by rewrite minus_IZR IZR_Zpower //; lia.
        by apply: IZR_le; lia.
      apply: Rmult_le_compat_l; last exact: Hcu.
      by rewrite -(pow0E beta); have := bpow_le beta 0 p ltac:(lia); lra.
    have -> : pow g = uls eps by rewrite Hg.
    nra.
  + by nra.
  + by lra.
(* [uls eps = Rabs eps] (a power of two): [B = pred(2|eps|)].  Here the       *)
(* [(1 - 2u)] margin -- not a block-length bound -- keeps [B] above the tail  *)
(* mass, which is the whole point of this length-free variant.                *)
have HgF : pow g = uls eps by rewrite Hg.
have H3 : pow (g + 1) = 2 * pow g by rewrite bpow_plus bpow_1 /=; lra.
have H2 : 2 * Rabs eps = pow (g + 1) by rewrite H3 -HM Hg.
exists (pred beta fexp (2 * Rabs eps)); split.
+ by apply: generic_format_pred; rewrite H2;
     apply: generic_format_bpow; rewrite /FLX_exp; lia.
+ rewrite H2 pred_bpow.
  have Hpm : pow (fexp (g + 1)) = uls eps * (2 * u).
    have Hueq : u = pow (- p).
      rewrite /Fmore.u (_ : (- p = 1 + - p - 1)%Z); last lia.
      by rewrite !bpow_plus bpow_1 /=; lra.
    rewrite /fexp /FLX_exp -HgF Hueq.
    rewrite (_ : (g + 1 - p = g + (1 - p))%Z); last lia.
    rewrite bpow_plus; congr (_ * _).
    rewrite (_ : (1 - p = 1 + - p)%Z); last lia.
    by rewrite bpow_plus bpow_1 /=; lra.
  rewrite -H2 Hpm; nra.
+ by apply: pred_lt_id; rewrite H2; have := bpow_gt_0 beta (g + 1); lra.
Qed.

(* ===========================================================================*)
(*  The VSEB block-mass invariant.                                            *)
(*                                                                            *)
(*  The engine of Theorem 2 is [vsebAux_head_lt_massU]: the first term VSEB   *)
(*  emits from a nonzero remainder [eps] over a tail [l] has [|.| < 2 |eps|],  *)
(*  needing ONLY the mass bound [sum|l| <= uls(eps)(1 - 2u)] -- NOT            *)
(*  F-nonoverlap, and NOT any block-length bound (a VecSum output can emit     *)
(*  over a long, mostly-zero tail; e.g. at [p = 4] a size-6 output emits with  *)
(*  a 4-term tail, so [|l| + 2 <= p + 1] genuinely fails).  Paired with the    *)
(*  always-true [2 |et| <= ulp(r)] ([magnitude_TwoSum]), P-nonoverlap of each  *)
(*  emitted step follows.  [vsebMass] records exactly this mass obligation at  *)
(*  every VSEB emit along the walk, so that [vseb] of any list satisfying it   *)
(*  is P-nonoverlapping (the [vsebAux_Pnonoverlap_mass] driver below).  This   *)
(*  is the interface the draft's Theorem-7 proof feeds: it is weaker than      *)
(*  F-nonoverlap (the VecSum output is not F-nonoverlapping).  The [<= 6]      *)
(*  bound and [p >= 4] enter through the per-emit mass bound (draft 5.3: the   *)
(*  emitted-tail errors are [<= u^2] and there are "at most 3 of them").       *)
(* ===========================================================================*)
Fixpoint vsebMass (eps : R) (l : seq R) : Prop :=
  match l with
  | [::]    => True
  | [:: _]  => True
  | e :: l' =>
      let: DWR r et := TwoSum eps e in
      if Req_EM_T et 0 then vsebMass r l'
      else sumRabs l' <= uls et * (1 - 2 * u) /\ vsebMass et l'
  end.

(* One-step unfolding (by reflexivity), exposing [TwoSum eps e] the way        *)
(* [vsebAux_consS] does, so a following [case] captures it.                     *)
Lemma vsebMass_consS eps e e2 l :
  vsebMass eps [:: e, e2 & l] =
  (let: DWR r et := TwoSum eps e in
   if Req_EM_T et 0 then vsebMass r (e2 :: l)
   else sumRabs (e2 :: l) <= uls et * (1 - 2 * u) /\ vsebMass et (e2 :: l)).
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
  rewrite vsebAux_1; case E1 : (TwoSum eps e) => [y0 y1].
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
rewrite vsebAux_consS; case E1 : (TwoSum eps e) => [r et].
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
case: Hm => Hmass Hmrec.
have Hrec : Pnonoverlap (vsebAux et (e2 :: l'')) by apply: IH.
move=> [|i] /= Hi.
  right.
  have Hulp : 2 * Rabs et <= ulp r.
    by have Hmag := magnitude_TwoSum epsF Fe; rewrite E1 /= in Hmag; lra.
  have Hnext : Rabs (nth 0 (vsebAux et (e2 :: l'')) 0) < 2 * Rabs et.
    by apply: vsebAux_head_lt_massU.
  by apply: (Rlt_le_trans _ _ _ Hnext Hulp).
by apply: (Hrec i); move: Hi; rewrite ltnS.
Qed.

(* Paper core tool (doc/thm6.md 5.4): each VecSum error is at most half an     *)
(* ulp of the running high word it is dropped from, [|e_{i+1}| <= 1/2 ulp(s_i)]*)
(* -- directly [magnitude_TwoSum] on the step [2Sum(x_i, s_{i+1}) = (s_i,      *)
(* e_{i+1})].  This is the draft's recurring [|e_i| <= 1/2 ulp(s_{i-1})].      *)
Lemma vecSum_err_le_half_ulp_run (l : seq R) i :
  (i.+1 < size l)%N -> {in l, forall z, format z} ->
  Rabs (nth 0 (vecSum l) i.+1) <= / 2 * ulp ((vecSumAux (drop i l)).2).
Proof.
move=> Hi Hf.
have iLl : (i < size l)%N by apply: ltn_trans (ltnSn i) Hi.
have Fx : format (nth 0 l i) by apply: Hf; apply: mem_nth.
have Hdf : {in drop i.+1 l, forall z, format z}
  by move=> z /mem_drop zI; apply: Hf.
have [Fs _] := format_vecSumAux Hdf.
have -> : nth 0 (vecSum l) i.+1 = nth 0 (vecSumAux l).1 i
  by rewrite /vecSum; case: (vecSumAux l).
rewrite (vecSumAux_nth1 Hi).
have Hs : (vecSumAux (drop i l)).2
        = dwh (TwoSum (nth 0 l i) (vecSumAux (drop i.+1 l)).2).
  have Hdne : (0 < size (drop i.+1 l))%N by rewrite size_drop subn_gt0.
  rewrite (drop_nth 0 iLl).
  case Hd : (drop i.+1 l) Hdne => [//|b l0] _.
  rewrite vecSumAux_cons; case E : (vecSumAux (b :: l0)) => [es s].
  by case: (TwoSum (nth 0 l i) s).
rewrite Hs; have Hm := magnitude_TwoSum Fx Fs.
by move: Hm;
   case: (TwoSum (nth 0 l i) (vecSumAux (drop i.+1 l)).2) => hi lo /=;
   lra.
Qed.

(* ===========================================================================*)
(*  Step *2 forcing (doc/thm6.md 5.2), scale-invariant: [uls(e_j)] is kept    *)
(*  symbolic (as [pow k]) instead of the paper's WLOG [uls(e_j) = u], which is *)
(*  the FLX-legal reading of the WLOG rescaling.                              *)
(* ===========================================================================*)

(* An ulp lower bound forces a magnitude lower bound.  From                    *)
(* [5/8 pow k <= 1/2 ulp s] we get [ulp s >= 2 pow k] (the next power of two   *)
(* above [5/4 pow k]) and hence [|s| >= ufp s = 2^(p-1) ulp s >= pow(k+p)].    *)
(* This is the draft's "[|e_i| <= 1/2 ulp(s_{i-1})] gives [|s_{i-1}| >= 1]"    *)
(* (with [1 = 2^p uls(e_j)] after the [uls(e_j) = u] normalisation).           *)
Lemma abs_ge_of_ulp_lb (s : R) (k : Z) :
  5 / 8 * pow k <= / 2 * ulp s -> pow (k + p) <= Rabs s.
Proof.
move=> H.
have Hk : 0 < pow k by apply: bpow_gt_0.
have Hs0 : s <> 0 by move=> s0; move: H; rewrite s0 ulp_FLX_0; lra.
have Hulp : ulp s = pow (cexp s) by rewrite ulp_neq_0.
have Hce : (k < cexp s)%Z by apply: (lt_bpow beta); rewrite -Hulp; lra.
have Hcexp : cexp s = (mag beta s - p)%Z by rewrite /cexp /FLX_exp.
apply: Rle_trans (bpow_mag_le beta s Hs0).
apply: bpow_le; lia.
Qed.

(* Draft 5.2, first step: a violation forces the preceding running sum large. *)
(* If a VecSum error [e_{i+1}] reaches [5/8 uls(e_j)] (with [uls(e_j) = pow k])*)
(* then [|s_i| >= 2^p uls(e_j) = pow(k+p)] -- the draft's [|s_{i-1}| >= 1].     *)
(* Combines [vecSum_err_le_half_ulp_run] ([|e_{i+1}| <= 1/2 ulp(s_i)]) with    *)
(* [abs_ge_of_ulp_lb].                                                         *)
Lemma vecSum_run_ge_of_violation (l : seq R) (i : nat) (k : Z) :
  (i.+1 < size l)%N -> {in l, forall z, format z} ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  pow (k + p) <= Rabs (vecSumAux (drop i l)).2.
Proof.
move=> Hi Hf Hviol.
apply: abs_ge_of_ulp_lb; apply: Rle_trans Hviol _.
exact: vecSum_err_le_half_ulp_run.
Qed.

(* Draft 5.2, divisibility: since [|s_i| >= 2^p uls(e_j)], the running sum is  *)
(* a multiple of [2 uls(e_j) = pow(k+1)] -- the draft's "[2u | s_{i-1}]" (with *)
(* [uls(e_j) = u]).  A float of magnitude [>= pow(k+p)] lies on a grid at      *)
(* least as coarse as [pow(k+1)] ([is_imul_bound_pow_format]).                 *)
Lemma vecSum_run_imul_of_violation (l : seq R) (i : nat) (k : Z) :
  (i.+1 < size l)%N -> {in l, forall z, format z} ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  is_imul (vecSumAux (drop i l)).2 (pow (k + 1)).
Proof.
move=> Hi Hf Hviol.
have Fs : format (vecSumAux (drop i l)).2.
  have Hdf : {in drop i l, forall z, format z} by move=> z /mem_drop; apply: Hf.
  by have [Fs _] := format_vecSumAux Hdf.
have Hge := vecSum_run_ge_of_violation Hi Hf Hviol.
have H := is_imul_bound_pow_format Hge Fs.
by rewrite (_ : (k + 1 = k + p - p + 1)%Z); last lia.
Qed.

(* Divisibility propagates from inputs to the VecSum output: if every input   *)
(* lies on the grid [pow g], so does every output ([vecSumAux_imul] packaged   *)
(* for [vecSum]).                                                              *)
Lemma vecSum_imul_forward (l : seq R) (g : Z) :
  {in l, forall z, format z} -> {in l, forall z, is_imul z (pow g)} ->
  {in vecSum l, forall z, is_imul z (pow g)}.
Proof.
move=> Hf Hm z; rewrite /vecSum.
have [H2 H1] := vecSumAux_imul Hf Hm.
case E : (vecSumAux l) => [es s0]; rewrite E /= in H2 H1.
by rewrite inE => /orP[/eqP->//|]; apply: H1.
Qed.

(* Draft 5.2, the propagation step: [2u | s_{i-1}] but [~ 2u | e_j] (j < i)    *)
(* forces some INPUT [x_{i'}] off the grid, with [i' < t] when the offending   *)
(* output sits in the prefix [j <= t] and the running sum [s_t] is on grid.    *)
(* Via [vecSumAux_split]: [vecSum (take t l ++ [s_t])] is the [t+1]-prefix of  *)
(* [vecSum l], and its inputs are [x_0..x_{t-1}] plus the (on-grid) [s_t].     *)
Lemma vecSum_not_imul_prefix (l : seq R) (t j : nat) (g : Z) :
  (t < size l)%N -> {in l, forall z, format z} -> (j <= t)%N ->
  is_imul (vecSumAux (drop t l)).2 (pow g) ->
  ~ is_imul (nth 0 (vecSum l) j) (pow g) ->
  exists2 i', (i' < t)%N & ~ is_imul (nth 0 l i') (pow g).
Proof.
move=> Ht Hf Hjt Hs Hnj.
set st := (vecSumAux (drop t l)).2.
set L := take t l ++ [:: st].
have Fst : format st.
  have Hdf : {in drop t l, forall z, format z} by move=> z /mem_drop; apply: Hf.
  by have [F _] := format_vecSumAux Hdf.
have HvL : vecSum L = (vecSumAux l).2 :: take t (vecSumAux l).1
  by rewrite /vecSum /L vecSumAux_split.
have Hnthj : nth 0 (vecSum L) j = nth 0 (vecSum l) j.
  rewrite HvL /vecSum; case: (vecSumAux l) => es s0.
  rewrite [(es, s0).1]/= [(es, s0).2]/=.
  by rewrite -[s0 :: take t es]/(take t.+1 (s0 :: es)) nth_take.
have HszL : size L = t.+1.
  by rewrite /L size_cat size_take_min /= addn1 (minn_idPl (ltnW Ht)).
apply: Classical_Prop.NNPP => Hnex.
have Hall : {in L, forall z, is_imul z (pow g)}.
  move=> z; rewrite /L mem_cat inE => /orP[|/eqP->]; last exact: Hs.
  move=> /(nthP 0)[i' Hi' <-].
  move: Hi'; rewrite size_take_min ltn_min => /andP[Hi't _].
  rewrite nth_take //.
  apply: Classical_Prop.NNPP => Hni'.
  by apply: Hnex; exists i'.
have HfL : {in L, forall z, format z}.
  by move=> z; rewrite /L mem_cat inE => /orP[/mem_take/Hf //|/eqP->//].
have Him := vecSum_imul_forward HfL Hall.
apply: Hnj; rewrite -Hnthj; apply: Him; apply: mem_nth.
by rewrite size_vecSum HszL.
Qed.

(* Draft 5.2, "[exists i' <= i-2, ~(2u | x_{i'})]": at a violation, with a     *)
(* reference error [e_j] ([j <= i]) whose [uls(e_j) = pow k] (so [e_j] is an   *)
(* odd multiple of the grid, [~ 2u | e_j] by [not_imul_uls_succ]), some input  *)
(* [x_{i'}] with [i' < i] is off the [2 uls(e_j) = pow(k+1)] grid.             *)
Lemma vecSum_exists_offgrid_input (l : seq R) (i j : nat) (k : Z) :
  (i.+1 < size l)%N -> {in l, forall z, format z} -> (j <= i)%N ->
  nth 0 (vecSum l) j <> 0 -> uls (nth 0 (vecSum l) j) = pow k ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  exists2 i', (i' < i)%N & ~ is_imul (nth 0 l i') (pow (k + 1)).
Proof.
move=> Hi Hf Hji Hej0 Huls Hviol.
have Hilt : (i < size l)%N by apply: ltn_trans (ltnSn i) Hi.
have Hjs : (j < size (vecSum l))%N.
  rewrite size_vecSum prednK; last by apply: ltn_trans Hi.
  by apply: leq_ltn_trans Hji Hilt.
have Fej : format (nth 0 (vecSum l) j)
  by apply: (format_vecSum Hf); apply: mem_nth.
have Hnej : ~ is_imul (nth 0 (vecSum l) j) (pow (k + 1))
  by exact: not_imul_uls_succ Fej Hej0 Huls.
apply: (vecSum_not_imul_prefix Hilt Hf Hji _ Hnej).
exact: vecSum_run_imul_of_violation Hi Hf Hviol.
Qed.

(* ===========================================================================*)
(*  Reduction of [vecSum_vsebMass] to two STATIC properties of the VecSum     *)
(*  error sequence [E = vecSum l].  Both are verified true by exhaustive       *)
(*  [p = 4, 5, 6] simulation; each isolates one half of draft 5.2-5.3.        *)
(*                                                                            *)
(*   (A) [suffMass E]: every error's [uls] dominates the total mass of all    *)
(*       LATER errors, with the [(1 - 2u)] margin.  This is the block-mass     *)
(*       estimate (draft 5.3: the emitted-tail errors are tiny, "at most 3").  *)
(*   (C) [ulsMono E]: [uls] is non-increasing along the nonzero errors.  Via  *)
(*       [TwoSum_err_uls_ge] this lifts the tail-mass bound from [uls(e_k)] to *)
(*       [uls(et)], the actual VSEB remainder.                                 *)
(* ===========================================================================*)

(* Each nonzero entry's [uls] bounds the mass of the strict suffix after it.  *)
Definition suffMass (L : seq R) : Prop :=
  forall k, (k < size L)%N -> nth 0 L k <> 0 ->
    sumRabs (drop k.+1 L) <= uls (nth 0 L k) * (1 - 2 * u).

(* [uls] is non-increasing on the nonzero entries.                            *)
Definition ulsMono (L : seq R) : Prop :=
  forall i j, (i < j)%N -> (j < size L)%N ->
    nth 0 L i <> 0 -> nth 0 L j <> 0 -> uls (nth 0 L j) <= uls (nth 0 L i).

(* A remainder [rho] whose [uls] dominates every nonzero entry of [L].        *)
Definition dominates (rho : R) (L : seq R) : Prop :=
  forall z, z \in L -> z <> 0 -> uls z <= uls rho.

Lemma suffMass_cons e L :
  suffMass (e :: L) -> (e <> 0 -> sumRabs L <= uls e * (1 - 2 * u)) /\ suffMass L.
Proof.
move=> Hs; split=> [en0|k Hk kn0].
  by have := Hs 0%N isT en0; rewrite drop1.
by have := Hs k.+1 Hk kn0; rewrite -[drop _ (e :: L)]/(drop k.+1 L).
Qed.

Lemma ulsMono_cons e L :
  ulsMono (e :: L) -> ulsMono L /\ (e <> 0 -> dominates e L).
Proof.
move=> Hm; split=> [i j Hij Hj ni nj|en0 z /(nthP 0)[j Hj <-] nj].
  by have := Hm i.+1 j.+1 Hij Hj ni nj.
by have := Hm 0%N j.+1 isT Hj en0 nj.
Qed.

Lemma dominates_cons rho e L : dominates rho (e :: L) -> dominates rho L.
Proof. by move=> Hd z zL; apply: Hd; rewrite inE zL orbT. Qed.

(* The walk induction: [vsebMass rho L] follows from the two static facts on   *)
(* [L] plus the running [uls]-domination invariant.  At an emit the tail mass  *)
(* bound comes from [suffMass] and is lifted to [uls et] by                    *)
(* [TwoSum_err_uls_ge] (needs [uls e <= uls rho], the invariant); the          *)
(* invariant is transported to the new remainder by [ulsMono].                 *)
Lemma vsebMass_gen rho L :
  format rho -> {in L, forall z, format z} ->
  (rho = 0 \/ dominates rho L) -> ulsMono L -> suffMass L ->
  vsebMass rho L.
Proof.
elim: L rho => [|e L' IH] rho Frho FL Hdom HM HS; first by [].
case: L' IH FL Hdom HM HS => [|e2 L''] IH FL Hdom HM HS; first by [].
have Fe : format e by apply: FL; rewrite inE eqxx.
have FL' : {in e2 :: L'', forall z, format z}
  by move=> z zI; apply: FL; rewrite inE zI orbT.
have [rF etF] : format (dwh (TwoSum rho e)) /\
                format (dwl (TwoSum rho e)) by apply: format_TwoSum.
have [HSe HSL'] := suffMass_cons HS.
have [HML' Hdome] := ulsMono_cons HM.
rewrite vsebMass_consS; case E : (TwoSum rho e) => [r et].
rewrite E /= in rF etF.
have Hc : dwh (TwoSum rho e) + dwl (TwoSum rho e) = rho + e
  by exact: TwoSum_correct_loc Frho Fe.
rewrite E /= in Hc.
have Hr : r = RND (rho + e) by have := TwoSum_hi rho e; rewrite E.
case: (Req_dec e 0) => [e0|en0].
  have Eet : et = 0.
    by have := dwl_TwoSum_r0 Frho; rewrite -e0 E /=.
  have Er : r = rho.
    by have := dwh_TwoSum_r0 Frho; rewrite -e0 E /=.
  rewrite Eet Er; move: (Req_EM_T (0:R) 0); case=> [E0|E0]; last by case: E0.
  rewrite [is_left _]/=.
  apply: IH => //.
  case: Hdom => [rho0|Hd]; [by left | by right; apply: dominates_cons Hd].
move: (Req_EM_T et 0); case=> [et0|etn0]; rewrite [is_left _]/=.
  have Hre : r = rho + e by move: Hc; rewrite et0 Rplus_0_r.
  apply: IH => //.
  case: (Req_dec r 0) => [r0|rn0]; first by left.
  right => z zI zn0.
  have Hze : uls z <= uls e by apply: Hdome.
  have Hg_e : uls e = pow (cexp e + Z.of_nat (trZ (Ztrunc (mant e)))).
    by rewrite /uls; case: Req_bool_spec => // e_0; case: en0.
  have Him_e : is_imul e (uls e) by apply: uls_imul.
  have Him_rho : is_imul rho (uls e).
    case: (Req_dec rho 0) => [rho0|rhon0].
      by rewrite rho0; exists 0%Z; rewrite Rmult_0_l.
    have Hler : uls e <= uls rho.
      case: Hdom => [rho0|Hd]; first by case: rhon0.
      by apply: Hd; [rewrite inE eqxx | exact: en0].
    have Hg_rho : uls rho = pow (cexp rho + Z.of_nat (trZ (Ztrunc (mant rho)))).
      by rewrite /uls; case: Req_bool_spec => // rho_0; case: rhon0.
    have Hle_exp : (cexp e + Z.of_nat (trZ (Ztrunc (mant e))) <=
                    cexp rho + Z.of_nat (trZ (Ztrunc (mant rho))))%Z.
      by apply: (le_bpow beta); rewrite -Hg_e -Hg_rho.
    have := uls_imul Frho; rewrite Hg_rho => Him_rho0.
    by rewrite Hg_e; apply: is_imul_pow_le Him_rho0 Hle_exp.
  have Him_r : is_imul r (uls e) by rewrite Hre; apply: is_imul_add.
  have Her : uls e <= uls r.
    by rewrite Hg_e; apply: is_imul_uls_ge => //; rewrite -Hg_e; exact: Him_r.
  apply: Rle_trans Hze Her.
have rhon0 : rho <> 0.
  move=> rho0; apply: etn0.
  have Hre0 : r = e by rewrite Hr rho0 Rplus_0_l round_generic.
  by move: Hc; rewrite Hre0 rho0 Rplus_0_l; lra.
have Hler : uls e <= uls rho.
  case: Hdom => [rho0|Hd]; first by case: rhon0.
  by apply: Hd; [rewrite inE eqxx|exact: en0].
have Huls_e_et : uls e <= uls et.
  have H := TwoSum_err_uls_ge Frho Fe rhon0 en0 Hler.
  by move: H; rewrite E /=; apply.
have H12u : 0 <= 1 - 2 * u.
  have -> : 2 * u = pow (1 - p) by rewrite /Fmore.u; lra.
  by have := bpow_le beta (1 - p) 0 ltac:(lia); rewrite (pow0E beta); lra.
split; last first.
  apply: IH => //.
  right => z zI zn0.
  apply: Rle_trans Huls_e_et.
  by apply: (Hdome en0).
apply: Rle_trans (HSe en0) _.
by apply: Rmult_le_compat_r.
Qed.

(* (A) -- draft 5.3 block-mass estimate.  SIMULATION-verified (p = 4, 5, 6).  *)
Lemma vecSum_suffMass (l : seq R) :
  ties_to_even choice ->
  (size l <= 6)%N ->
  {in l, forall z, format z} ->
  (forall i, (i < size l)%N -> nth (0:R) l i <> 0) ->
  sorted_mag l -> pairwise_ulp l ->
  suffMass (vecSum l).
Proof.
Admitted.

(* (C) -- [uls] non-increasing on the nonzero errors.  SIMULATION-verified.   *)
Lemma vecSum_ulsMono (l : seq R) :
  ties_to_even choice ->
  (size l <= 6)%N ->
  {in l, forall z, format z} ->
  (forall i, (i < size l)%N -> nth (0:R) l i <> 0) ->
  sorted_mag l -> pairwise_ulp l ->
  ulsMono (vecSum l).
Proof.
Admitted.

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
move=> Heven Hsz Hfmt Hnz Hsort Hpair.
have HfV : {in vecSum l, forall z, format z} by apply: format_vecSum.
have HA := vecSum_suffMass Heven Hsz Hfmt Hnz Hsort Hpair.
have HC := vecSum_ulsMono Heven Hsz Hfmt Hnz Hsort Hpair.
case E : (vecSum l) HfV HA HC => [|e0 L] HfV HA HC; first by [].
have [_ HAL] := suffMass_cons HA.
have [HCL Hdom] := ulsMono_cons HC.
apply: vsebMass_gen => //.
- by apply: HfV; rewrite inE eqxx.
- by move=> z zL; apply: HfV; rewrite inE zL orbT.
case: (Req_dec e0 0) => [->|e0n0]; first by left.
by right; apply: Hdom.
Qed.

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
  rewrite E0 Ea; case E : (TwoSum a 0) => [si ei1].
  have := dwh_TwoSum_r0 Fa; rewrite E /= => ->.
  by have := dwl_TwoSum_r0 Fa; rewrite E /= => ->.
have Hbm : {in b :: m, forall z, format z}.
  by move=> z zI; apply: abF; rewrite inE zI orbT.
have IH' := IH b Hbm; rewrite rcons_cons in IH'.
rewrite rcons_cons vecSumAux_cons rcons_cons vecSumAux_cons IH'.
by case: (vecSumAux (b :: m)) => es s /=; case: (TwoSum a s).
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
  move=> w wF; rewrite vsebAux_1; case Ew : (TwoSum w 0) => [z0 z1].
  have := dwh_TwoSum_r0 wF; rewrite Ew /= => ->.
  by have := dwl_TwoSum_r0 wF; rewrite Ew /= => ->.
elim: l eps => [|e l' IH] eps epsF lF.
  by right; rewrite (vseb0 _ epsF).
have eF : format e by apply: lF; rewrite inE eqxx.
have Fl' : {in l', forall z, format z}.
  by move=> z zI; apply: lF; rewrite inE zI orbT.
have [rF etF] : format (dwh (TwoSum eps e)) /\
                format (dwl (TwoSum eps e))
  by apply: format_TwoSum.
rewrite rcons_cons.
case: l' IH lF Fl' rF etF => [|e2 l2] IH lF Fl' rF etF.
  (* One remaining term: the trailing zero is either dropped or emitted last. *)
  have -> : e :: rcons [::] 0 = [:: e, 0 & [::]] by [].
  rewrite vsebAux_consS vsebAux_1.
  case E : (TwoSum eps e) => [r et].
  have rF' : format r by move: rF; rewrite E.
  have etF' : format et by move: etF; rewrite E.
  case: (Req_EM_T et 0) => [et0|etn0].
    by left; rewrite [is_left _]/= (vseb0 r rF') et0.
  by right; rewrite [is_left _]/= (vseb0 et etF').
(* Two or more terms: recurse, the zero travelling to the tail.               *)
have -> : e :: rcons (e2 :: l2) 0 = [:: e, e2 & rcons l2 0] by rewrite rcons_cons.
rewrite !vsebAux_consS.
case E : (TwoSum eps e) => [r et].
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
