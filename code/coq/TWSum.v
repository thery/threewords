(* ---------------------------------------------------------------------------*)
(* Algorithm 8 (TWSum): the sum of two triple-word numbers, and its two main  *)
(* correctness results -- the result is a triple word ([TWSum_isTW]) and the  *)
(* relative error bound ([TWSum_error]).  Generic over the precision [p] and  *)
(* over the precision [p] alone -- FLX, no [emin] (binary64 is fixed only in *)
(* [TwoSum], [Nonoverlap], [TWR], [Merge], [VecSum] and [VSEB].               *)
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
Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SecTWSum.

Variable p : Z.
Hypothesis Hp2 : (1 < p)%Z.
(* The correctness of triple-word addition needs enough precision (paper      *)
(* Section 5: [p >= 4] for Theorem 6, [p >= 6] for the Theorem-3 truncation   *)
(* and [size < p + 1] for six merged terms).  [p >= 6] covers all of them;    *)
(* binary64 ([p = 53]) satisfies it in [addition.v].                          *)
Hypothesis Hp6 : (6 <= p)%Z.

(* [Thm6.v] is stated for [4 <= p]; here [6 <= p].                           *)
Fact Hp4 : (4 <= p)%Z. Proof. by lia. Qed.

Local Notation beta := radix2.
Local Notation pow e := (bpow beta e).

Local Instance p_gt_0 : Prec_gt_0 p.
Proof. now apply Z.lt_trans with (2 := Hp2). Qed.

Open Scope R_scope.

Local Notation u := (u p beta).
Local Notation u_gt_0 := (u_gt_0 p beta).
Local Notation uE := (@uE p).

Variable choice : Z -> bool.
Hypothesis choice_sym : forall x, choice x = ~~ choice (- (x + 1))%Z.
Local Notation rnd := (Znearest choice).
Local Instance valid_rnd : Valid_rnd rnd := valid_rnd_N choice.

Local Notation float := (float radix2).
Local Notation fexp := (FLX_exp p).
Local Notation format := (generic_format beta fexp).
Local Notation cexp := (cexp beta fexp).
Local Notation mant := (scaled_mantissa beta fexp).
Local Notation RND := (round beta fexp rnd).
Local Notation RU := (round beta fexp Zceil).
Local Notation RD := (round beta fexp Zfloor).
Local Notation ulp := (ulp beta fexp).
Local Notation uls := (uls p).
Local Notation error_le_half_ulp_RN :=
  (@error_le_half_ulp_round beta (FLX_exp p)
     (FLX_exp_valid p) (FLX_exp_monotone p) choice).
Local Notation TwoSum_correct_RN :=
  (@TwoSum_correct p choice Hp2 choice_sym).

Local Notation TwoSum := (TwoSum p choice).
Local Notation TwoSum_hi := (TwoSum_hi p choice).
Local Notation formatDWR := (formatDWR p).
Local Notation magnitudeDWR := (magnitudeDWR p).
Local Notation format_TwoSum := (format_TwoSum Hp2 choice).
Local Notation TwoSum_correct_loc :=
  (TwoSum_correct_loc Hp2 choice_sym).
Local Notation magnitude_TwoSum :=
  (magnitude_TwoSum Hp2 choice_sym).
Local Notation TwoSum_err_imul := (TwoSum_err_imul Hp2 choice_sym).
Local Notation TwoSum_err_uls_ge :=
  (TwoSum_err_uls_ge Hp2 choice_sym).

Local Notation Pnonoverlap := (Pnonoverlap p).
Local Notation pairwise_ulp := (pairwise_ulp p).
Local Notation Fnonoverlap := (Fnonoverlap p).
Local Notation format_lt_ulp_le := (@format_lt_ulp_le p Hp2).
Local Notation Pnonoverlap_imp_pairwise_ul :=
  (Pnonoverlap_imp_pairwise_ul Hp2).
Local Notation abs_le_ufp_norm := (abs_le_ufp_norm Hp2).
Local Notation small_head_zero := (@small_head_zero p Hp2).
Local Notation sumR_ufp_bound := (@sumR_ufp_bound p Hp2).
Local Notation nth_step_zero := (@nth_step_zero p Hp2).

(* Triple-word type and merge from [TWR.v]/[Merge.v]; fix [p].               *)
Local Notation isTW := (isTW p).
Local Notation isTW_sorted_mag := (isTW_sorted_mag Hp2).
Local Notation Merge_pairwise_ulp := (Merge_pairwise_ulp Hp2).

(* [VecSum.v] / [VSEB.v] / [Thm6.v] entry points; re-hide this format's      *)
(* [p]/[choice] (and the [Hp2]/[choice_sym] proofs).                         *)
Local Notation vecSum := (vecSum p choice).
Local Notation vseb := (vseb p choice).
Local Notation vsebK := (vsebK p choice).
Local Notation size_vecSum := (size_vecSum p choice).
Local Notation format_vecSum := (format_vecSum Hp2).
Local Notation format_vseb := (format_vseb Hp2).
Local Notation format_vsebK := (format_vsebK Hp2).
Local Notation vecSum_sum := (vecSum_sum Hp2 choice_sym).
Local Notation vseb_sum := (vseb_sum Hp2 choice_sym).
Local Notation vecSum_run_ufp := (vecSum_run_ufp Hp2 choice_sym).
Local Notation vecSum_err_ufp := (vecSum_err_ufp Hp2 choice_sym).
Local Notation vseb_Pnonoverlap :=
  (vseb_Pnonoverlap Hp2 choice_sym).
Local Notation vecSum_vseb_Pnonoverlap :=
  (vecSum_vseb_Pnonoverlap Hp2 Hp4 choice_sym).

(* ===========================================================================*)
(*  Algorithm 6 (ToTW): three FP numbers to a triple word (paper Thm 4).      *)
(*  ToTW a b c = VSEB(VecSum(d0, d1, c)) with (d0,d1) = 2Sum(a,b).  Unlike    *)
(*  TWSum this does NOT go through Theorem 6: the special input [d0; d1; c]   *)
(*  (a DW followed by one FP) makes VecSum's output already F-nonoverlapping, *)
(*  so Theorem 2 ([vseb_Pnonoverlap]) suffices.  See doc/thm4.md.             *)
(* ===========================================================================*)
Definition ToTW (a b c : R) : twR :=
  let: DWR d0 d1 := TwoSum a b in
  match vsebK 3 (vecSum [:: d0; d1; c]) with
  | [:: r0, r1, r2 & _] => TWR r0 r1 r2
  | [:: r0; r1]         => TWR r0 r1 0
  | [:: r0]             => TWR r0 0 0
  | [::]                => TWR 0 0 0
  end.

(* THE content of Theorem 4 (doc/thm4.md, the [(e1,e2)] argument): the        *)
(* VecSum of [d0; d1; c] is F-nonoverlapping.  [(e0,e1)] is free from the     *)
(* 2Sum half-ulp bound; [(e1,e2)] is a divisibility/ulp contradiction.        *)
(* Theorem 4 core (paper p.5), case [e_1 <> 0]: the last VecSum error [e_2] =  *)
(* error of [2Sum(d1,c)] is [<= 1/2 uls(e_1)].  [Rabs d1 <= 1/2 ulp d0] is the *)
(* DW property of [(d0,d1) = 2Sum(a,b)].                                       *)
Lemma ToTW_e1e2 (d0 d1 c s1 s0 e1 e2 : R) :
  ties_to_even choice -> format d0 -> format d1 -> format c ->
  TwoSum d1 c = DWR s1 e2 -> TwoSum d0 s1 = DWR s0 e1 ->
  Rabs d1 <= / 2 * ulp d0 -> e1 <> 0 ->
  Rabs e2 <= / 2 * uls e1.
Proof.
move=> Heven Fd0 Fd1 Fc E2 E1 Hd1 e1n0.
apply: Rnot_lt_le => Hgt.
have Fs1 : format s1 by have := format_TwoSum Fd1 Fc; rewrite E2; case.
have Fe1 : format e1 by have := format_TwoSum Fd0 Fs1; rewrite E1; case.
have Hs1v : s1 = RND (d1 + c) by have := TwoSum_hi d1 c; rewrite E2.
have Hc2 : s1 + e2 = d1 + c.
  move: E2 (TwoSum_correct_loc Fd1 Fc); case: (TwoSum d1 c) => sX eX.
  by case=> <- <- /= ->.
have Hm2 : Rabs e2 <= / 2 * ulp s1.
  have := magnitude_TwoSum Fd1 Fc; rewrite E2 /magnitudeDWR; lra.
have [k Hk] : exists e, uls e1 = pow e by apply: uls_pow.
rewrite Hk in Hgt.
have Hpk := bpow_gt_0 beta k.
(* Step 1 (paper's [s >= 1, 2u | s]): [cexp s1 >= k+1]                       *)
have Hulps1 : pow k < ulp s1 by lra.
have s1n0 : s1 <> 0 by move=> H0; move: Hulps1; rewrite H0 ulp_FLX_0; lra.
have Hcexp_s1 : (k < cexp s1)%Z.
  apply: (lt_bpow beta); apply: Rlt_le_trans Hulps1 _.
  rewrite ulp_neq_0 //; apply: Rle_refl.
(* Step 2 (paper's [e1 not div 2u, so d0 < 1]): [cexp d0 <= k]              *)
have Himul_e1 := TwoSum_err_imul Fd0 Fs1; rewrite E1 /= in Himul_e1.
have Hmin_le : (Z.min (cexp d0) (cexp s1) <= k)%Z.
  by apply: (le_bpow beta); rewrite -Hk; apply: is_imul_uls_ge.
have Hcexp_d0 : (cexp d0 <= k)%Z by move: Hmin_le Hcexp_s1; lia.
have d0n0 : d0 <> 0.
  move=> H0.
  have d1z : d1 = 0.
    by move: Hd1; rewrite H0 ulp_FLX_0 Rmult_0_r; split_Rabs; lra.
  have s1c : s1 = c by rewrite Hs1v d1z Rplus_0_l round_generic.
  by move: Hgt Hc2; rewrite d1z s1c; split_Rabs; lra.
(* Hence [|d1| <= 1/2 pow k] (paper's [|d1| <= 1/2 u])                       *)
have Hd1_le : Rabs d1 <= / 2 * pow k.
  apply: Rle_trans Hd1 _.
  rewrite ulp_neq_0 //.
  have : pow (cexp d0) <= pow k by apply: bpow_le.
  lra.
(* Finish: a 2Sum error never exceeds the OTHER operand ([c] is a float),   *)
(* so [|e2| <= |d1|] -- this is the paper's [s = c, e2 = d1], but immediate *)
(* from the nearest-float property (no [|c| >= 1] / tie analysis needed).   *)
have He2_le : Rabs e2 <= Rabs d1.
  have [_ Hnear] := round_N_pt beta fexp choice (d1 + c).
  have Hb := Hnear c Fc.
  have -> : Rabs e2 = Rabs (RND (d1 + c) - (d1 + c)).
    by rewrite -Hs1v; move: Hc2; split_Rabs; lra.
  apply: Rle_trans Hb _.
  have -> : c - (d1 + c) = - d1 by lra.
  rewrite Rabs_Ropp; apply: Rle_refl.
lra.
Qed.

(* Theorem 4 core, case [e_1 = 0]: the same bound against the surviving high  *)
(* word [s_0 = e_0] ("the same reasoning with [e_0] instead of [e_1]").        *)
Lemma ToTW_e1zero (d0 d1 c s1 s0 e1 e2 : R) :
  ties_to_even choice -> format d0 -> format d1 -> format c ->
  TwoSum d1 c = DWR s1 e2 -> TwoSum d0 s1 = DWR s0 e1 ->
  Rabs d1 <= / 2 * ulp d0 -> s0 <> 0 -> e1 = 0 ->
  Rabs e2 <= / 2 * uls s0.
Proof.
move=> Heven Fd0 Fd1 Fc E2 E1 Hd1 s0n0 e1z.
apply: Rnot_lt_le => Hgt.
have Fs1 : format s1 by have := format_TwoSum Fd1 Fc; rewrite E2; case.
have Fs0 : format s0 by have := format_TwoSum Fd0 Fs1; rewrite E1; case.
have Hs1v : s1 = RND (d1 + c) by have := TwoSum_hi d1 c; rewrite E2.
have Hc2 : s1 + e2 = d1 + c.
  move: E2 (TwoSum_correct_loc Fd1 Fc); case: (TwoSum d1 c) => sX eX.
  by case=> <- <- /= ->.
have Hc1 : s0 + e1 = d0 + s1.
  move: E1 (TwoSum_correct_loc Fd0 Fs1); case: (TwoSum d0 s1) => sX eX.
  by case=> <- <- /= ->.
have Hs0v : s0 = d0 + s1 by move: Hc1; rewrite e1z; lra.
have Hm2 : Rabs e2 <= / 2 * ulp s1.
  have := magnitude_TwoSum Fd1 Fc; rewrite E2 /magnitudeDWR; lra.
have [k Hk] : exists e, uls s0 = pow e by apply: uls_pow.
rewrite Hk in Hgt.
have Hpk := bpow_gt_0 beta k.
have Hulps1 : pow k < ulp s1 by lra.
have s1n0 : s1 <> 0 by move=> H0; move: Hulps1; rewrite H0 ulp_FLX_0; lra.
have Hcexp_s1 : (k < cexp s1)%Z.
  apply: (lt_bpow beta); apply: Rlt_le_trans Hulps1 _.
  rewrite ulp_neq_0 //; apply: Rle_refl.
(* Step 2 via [s0 = d0 + s1]: if [cexp d0 >= k+1] then [pow(k+1) | s0],      *)
(* contradicting [uls s0 = pow k] (the paper's "same reasoning with e0").    *)
have Hs1_imul : is_imul s1 (pow (k + 1)).
  by apply: is_imul_pow_le (format_imul_cexp Fs1) _; lia.
have Hcexp_d0 : (cexp d0 <= k)%Z.
  case: (Z_le_gt_dec (cexp d0) k) => // Hgt_d0.
  have Hd0_imul : is_imul d0 (pow (k + 1)).
    by apply: is_imul_pow_le (format_imul_cexp Fd0) _; lia.
  have Hs0_imul : is_imul s0 (pow (k + 1)) by rewrite Hs0v; apply: is_imul_add.
  have := is_imul_uls_ge Fs0 s0n0 Hs0_imul; rewrite Hk.
  by move/(le_bpow beta); lia.
have d0n0 : d0 <> 0.
  move=> H0.
  have d1z : d1 = 0.
    by move: Hd1; rewrite H0 ulp_FLX_0 Rmult_0_r; split_Rabs; lra.
  have s1c : s1 = c by rewrite Hs1v d1z Rplus_0_l round_generic.
  by move: Hgt Hc2; rewrite d1z s1c; split_Rabs; lra.
have Hd1_le : Rabs d1 <= / 2 * pow k.
  apply: Rle_trans Hd1 _.
  rewrite ulp_neq_0 //.
  have : pow (cexp d0) <= pow k by apply: bpow_le.
  lra.
have He2_le : Rabs e2 <= Rabs d1.
  have [_ Hnear] := round_N_pt beta fexp choice (d1 + c).
  have Hb := Hnear c Fc.
  have -> : Rabs e2 = Rabs (RND (d1 + c) - (d1 + c)).
    by rewrite -Hs1v; move: Hc2; split_Rabs; lra.
  apply: Rle_trans Hb _.
  have -> : c - (d1 + c) = - d1 by lra.
  rewrite Rabs_Ropp; apply: Rle_refl.
lra.
Qed.

Lemma ToTW_vecSum_Fnonoverlap a b c :
  ties_to_even choice -> format a -> format b -> format c ->
  Fnonoverlap (vecSum [:: dwh (TwoSum a b); dwl (TwoSum a b); c]).
Proof.
move=> Heven Fa Fb Fc.
have Fd0 : format (dwh (TwoSum a b))
  by have := format_TwoSum Fa Fb; case: (TwoSum a b) => ? ? [].
have Fd1 : format (dwl (TwoSum a b))
  by have := format_TwoSum Fa Fb; case: (TwoSum a b) => ? ? [].
have Hd1 : Rabs (dwl (TwoSum a b)) <= / 2 * ulp (dwh (TwoSum a b)).
  have := magnitude_TwoSum Fa Fb.
  by case: (TwoSum a b) => sh sl; rewrite /magnitudeDWR /dwh /dwl; lra.
set d0 := dwh (TwoSum a b).
set d1 := dwl (TwoSum a b).
have Hvs : vecSum [:: d0; d1; c] =
  let: DWR s1 e2 := TwoSum d1 c in
  let: DWR s0 e1 := TwoSum d0 s1 in [:: s0; e1; e2].
  rewrite /vecSum !vecSumAux_cons /=.
  by case: (TwoSum d1 c) => s1 e2; case: (TwoSum d0 s1) => s0 e1.
rewrite Hvs.
case E2 : (TwoSum d1 c) => [s1 e2].
case E1 : (TwoSum d0 s1) => [s0 e1].
have Fs1 : format s1 by have := format_TwoSum Fd1 Fc; rewrite E2; case.
have Fe1 : format e1 by have := format_TwoSum Fd0 Fs1; rewrite E1; case.
have Hm1 : Rabs e1 <= / 2 * ulp s0.
  have := magnitude_TwoSum Fd0 Fs1; rewrite E1 /magnitudeDWR; lra.
have HA : s0 <> 0 -> Rabs e1 <= / 2 * uls s0.
  move=> _; apply: Rle_trans Hm1 _.
  suff : ulp s0 <= uls s0 by lra.
  exact: ulp_le_ulps.
have HI : e1 <> 0 -> Rabs e2 <= / 2 * uls e1
  by move=> H; apply: (ToTW_e1e2 Heven Fd0 Fd1 Fc E2 E1 Hd1 H).
have HII : s0 <> 0 -> e1 = 0 -> Rabs e2 <= / 2 * uls s0
  by move=> H H0; apply: (ToTW_e1zero Heven Fd0 Fd1 Fc E2 E1 Hd1 H H0).
have Huls_mono : e1 <> 0 -> uls e1 <= uls s0.
  move=> e1n0.
  apply: Rle_trans (uls_le_abs Fe1 e1n0) _.
  apply: Rle_trans Hm1 _.
  have Hx : ulp s0 <= uls s0 by exact: ulp_le_ulps.
  have Hu0 : 0 <= ulp s0 by apply: ulp_ge_0.
  lra.
apply: Fnonoverlap_allpairs => i j iLj jLs ni0.
move: iLj jLs ni0.
case: i => [|[|[|i']]]; case: j => [|[|[|j']]] //= _ _ ni0.
case: (Req_dec e1 0) => [e1z|e1n0]; first by apply: HII.
apply: Rle_trans (HI e1n0) _.
have := Huls_mono e1n0; lra.
Qed.

(* Paper Theorem 4: [ToTW a b c] is a triple word (p >= 4; here p >= 6).      *)
(* Reduction to Theorem 2, mirroring [TWSum_isTW].                            *)
Lemma ToTW_isTW a b c :
  ties_to_even choice -> format a -> format b -> format c -> isTW (ToTW a b c).
Proof.
move=> Hceven Fa Fb Fc.
have HzF := ToTW_vecSum_Fnonoverlap Hceven Fa Fb Fc.
have [Fd0 Fd1] : format (dwh (TwoSum a b)) /\ format (dwl (TwoSum a b)).
  by have := format_TwoSum Fa Fb; case: (TwoSum a b) => h l [].
move: HzF Fd0 Fd1; rewrite /ToTW; case: (TwoSum a b) => d0 d1 /= HzF Fd0 Fd1.
pose z := [:: d0; d1; c].
have Hzf : {in z, forall t, format t}.
  by move=> t; rewrite !inE => /or3P[] /eqP->.
have Hsz : (Z.of_nat (size (vecSum z)) <= p + 1)%Z.
  by rewrite size_vecSum /=; move: Hp6; lia.
have Hr_nonover : Pnonoverlap (vsebK 3 (vecSum z)).
  apply/Pnonoverlap_take.
  by case: (vseb_Pnonoverlap Hsz (format_vecSum Hzf) HzF).
have Hr_format : {in vsebK 3 (vecSum z), forall t, format t}.
  by apply/format_vsebK/format_vecSum.
rewrite -/z.
move: Hr_nonover Hr_format;
  case: (vsebK 3 (vecSum z)) => [|r0 [|r1 [|r2 tl]]] Hno Hfmt.
- by split; try exact: generic_format_0; left.
- by split; try exact: generic_format_0;
     [apply: Hfmt; rewrite !inE eqxx | left | left].
- by split; [apply: Hfmt; rewrite !inE eqxx | apply: Hfmt; rewrite !inE eqxx orbT
           | exact: generic_format_0 | apply: (Hno 0%N) | left].
by split; [apply: Hfmt; rewrite !inE eqxx | apply: Hfmt; rewrite !inE eqxx orbT
         | apply: Hfmt; rewrite !inE eqxx !orbT | apply: (Hno 0%N)
         | apply: (Hno 1%N)].
Qed.

(* ===========================================================================*)
(*  Algorithm 7 (RoundTW): round a triple word to the nearest float           *)
(*  (paper Theorem 5).  See doc/thm5.md.                                      *)
(* ===========================================================================*)

(* [x0+x1] sits exactly halfway between its two nearest floats.               *)
Definition is_midpoint (m : R) : Prop :=
  m - round beta fexp Zfloor m = / 2 * ulp (round beta fexp Zfloor m).

Definition RoundTW (x0 x1 x2 : R) : R :=
  if Req_EM_T (RND (x0 + 2 * x1)) (x0 + 2 * x1) then
    if Req_EM_T (RND (- (3 / 2 * u - 2 * (u * u)) * x0)) x1 then
      if Rlt_le_dec 0 x2 then RU (x0 + x1)
      else if Rlt_le_dec x2 0 then RD (x0 + x1)
      else RND (x0 + x1)
    else RND (x0 + x1)
  else RND (x0 + x1).

(* Helper A (paper's "if [x0+x1] is a FP number ..."): a float plus a tail    *)
(* below half its ulp rounds back to the float.                               *)
Lemma RoundTW_add_float x0 x1 x2 :
  format x0 -> format x1 -> format x2 -> format (x0 + x1) ->
  Rabs x2 < ulp x1 -> RND (x0 + x1 + x2) = x0 + x1.
Proof.
Admitted.

(* Helper B (non-midpoint): a tail below the distance to the midpoint cannot  *)
(* change the rounding, so [RN(m + d) = RN m].                                *)
Lemma RN_add_notmid (m d : R) :
  ~ is_midpoint m -> ~ format m -> Rabs d < ulp m -> RND (m + d) = RND m.
Proof.
Admitted.

(* Helper C (midpoint): at a midpoint the sign of the tail decides the        *)
(* rounding -- [RU] when positive, [RD] when negative, [RN] when zero.        *)
Lemma RN_add_mid (m d : R) :
  is_midpoint m -> ~ format m -> Rabs d < ulp m ->
  RND (m + d) = if Rlt_le_dec 0 d then RU m
                else if Rlt_le_dec d 0 then RD m else RND m.
Proof.
Admitted.

(* The tie-detector (the core of Algorithm 7): with [isTW]'s separation, the  *)
(* algorithm's first condition is FALSE exactly when [x0+x1] is a midpoint   *)
(* the special case [x0 = 1+2u, x1 = -3/2 u] being caught by [star].            *)
Lemma RoundTW_cond x0 x1 :
  format x0 -> format x1 -> (x1 = 0 \/ Rabs x1 < ulp x0) -> ~ format (x0 + x1) ->
  (RND (x0 + 2 * x1) = x0 + 2 * x1 /\
   RND (- (3 / 2 * u - 2 * (u * u)) * x0) = x1) <-> is_midpoint (x0 + x1).
Proof.
Admitted.

(* Paper Theorem 5. *)
Lemma RoundTW_correct x0 x1 x2 :
  isTW (TWR x0 x1 x2) -> RoundTW x0 x1 x2 = RND (x0 + x1 + x2).
Proof.
Admitted.

(* ===========================================================================*)
(*  Algorithm 8: TWSum -- the sum of two triple-word numbers.                 *)
(* ===========================================================================*)
Definition TWSum (x y : twR) : twR :=
  let: TWR x0 x1 x2 := x in
  let: TWR y0 y1 y2 := y in
  let z := Merge [:: x0; x1; x2] [:: y0; y1; y2] in
  let e := vecSum z in
  match vsebK 3 e with
  | [:: r0, r1, r2 & _] => TWR r0 r1 r2
  | [:: r0; r1]         => TWR r0 r1 0
  | [:: r0]             => TWR r0 0 0
  | [::]                => TWR 0 0 0
  end.

(* The relative-error coefficient of the "Ensure" clause of Alg. 8.           *)
Local Notation errc := (2 * (u * u * u) + 42 / 10 * (u * u * u * u)).

(* ===========================================================================*)
(*  Correctness: TWSum returns a triple-word number (Theorem 6).              *)
(*                                                                            *)
(*  Sketch (paper, Section 5.1, p >= 4):                                      *)
(*   - Merge keeps floating-point numbers, magnitude-sorted, with the         *)
(*     pairwise-ulp separation, i.e. the hypotheses of Theorem 6.             *)
(*   - [VSEB (VecSum ...)] is P-nonoverlapping with the same exact sum         *)
(*     ([vecSum_vseb_Pnonoverlap], paper Theorem 6), so its first three        *)
(*     terms form a TW number.                                                *)
(*                                                                            *)
(*  NB.  The intermediate "[VecSum ...] is F-nonoverlapping" is NOT used any   *)
(*  more, because it is FALSE for merges of near-equal odd leaders (see the    *)
(*  note in [VecSum.v] and the machine-checked [CEThm6.v]).  Theorem 6 is a    *)
(*  DIRECT statement about [VSEB (VecSum ...)]: VSEB repairs the overlap that  *)
(*  VecSum can leave behind.                                                   *)
(* ===========================================================================*)
(* Merging two triples and running VecSum yields exactly six terms, so the    *)
(* [size <= p + 1] side condition of [vseb_Pnonoverlap] holds once [6 <= p].  *)
Lemma size_vecSum_Merge x0 x1 x2 y0 y1 y2 :
  (Z.of_nat
     (size (vecSum (Merge [:: x0; x1; x2] [:: y0; y1; y2]))) <= p + 1)%Z.
Proof. by rewrite size_vecSum size_Merge /=; lia. Qed.

(* Paper Theorem 6 (the statement [TWSum] actually needs).  For at most SIX    *)
(* magnitude-sorted, pairwise-ulp-separated floating-point inputs (with no     *)
(* underflow: nonzero terms normal), running VecSum and then VSEB yields a     *)
(* P-nonoverlapping sequence.  Round-to-nearest must be TIES-TO-EVEN.          *)
(*                                                                            *)
(* This is DIRECT: the raw [vecSum l] is generally NOT F-nonoverlapping        *)
(* ([CEThm6.v]), so it does NOT factor through [vecSum_Fnonoverlap]/           *)
(* [vseb_Pnonoverlap].  The proof (paper Section 5.1, undetailed there) uses   *)
(* the run-bound [vecSum_run_ufp] and error-bound [vecSum_err_ufp], then a     *)
(* case study on how VSEB's Fast2Sum steps collapse the (few) overlaps VecSum  *)

Lemma TWSum_isTW x y :
  ties_to_even choice ->
  isTW x -> isTW y -> isTW (TWSum x y).
Proof.
case: x => x0 x1 x2; case: y => y0 y1 y2 => Hceven Hx Hy.
pose z := Merge [:: x0; x1; x2] [:: y0; y1; y2].
pose e := vecSum z.
(* Merge keeps the six terms floating-point ...                               *)
have Hz_format : {in z, forall t, format t}.
  apply: format_Merge.
    by case: Hx => x0F x1F x2F _ _ z1; rewrite !inE => /or3P[] /eqP->.
  by case: Hy => y0F y1F y2F _ _ z1; rewrite !inE => /or3P[] /eqP->.
(* ... magnitude-sorted ...                                                   *)
have Hz_sorted : sorted_mag z.
  apply: Merge_sorted_mag; first by apply: isTW_sorted_mag Hx.
  by apply: isTW_sorted_mag Hy.
(* ... and pairwise ulp-separated: the hypotheses of Theorem 6.               *)
have Hz_ulp : pairwise_ulp z.
  apply: Merge_pairwise_ulp=> [u|u||].
  - by rewrite !inE => /or3P[] /eqP->; case: Hx.
  - by rewrite !inE => /or3P[] /eqP->; case: Hy.
  - by apply: isTW_Pnonoverlap Hx.
  by apply: isTW_Pnonoverlap Hy.
(* VecSum preserves the exact sum (Algorithm 4 is error-free).                *)
have He_sum : sumR e = sumR z by apply: vecSum_sum.
(* VSEB(3) of VecSum is P-nonoverlapping.  The chain (see the lemmas above):  *)
(*   - [vecSum_Fnonoverlap] (Thm 1): [e = vecSum z] is F-nonoverlapping (its  *)
(*     [.1]), using [Hz_format], [Hz_sorted] and [Hz_ulp];                    *)
(*   - [vseb_Pnonoverlap]  (Thm 2): hence [vseb e] is P-nonoverlapping (its   *)
(*     [.1]); its side conditions are [size e = 6 <= p + 1] and the formatness*)
(*     [format_vecSum Hz_format];                                             *)
(*   - [Pnonoverlap_take]         : [vsebK 3 e = take 3 (vseb e)] is a prefix,*)
(*     so it is P-nonoverlapping too.                                         *)
(* i.e. once the three lemmas are proved this closes with (writing [Hsz] for  *)
(* [Z.of_nat (size e) <= p + 1] -- here [size e = 6] as VecSum and Merge      *)
(* preserve length, and [p = 53])                                             *)
(*   [rewrite /vsebK; apply: Pnonoverlap_take;                                *)
(*    apply: (vseb_Pnonoverlap Hsz (format_vecSum Hz_format)                  *)
(*             (vecSum_Fnonoverlap Hz_format Hz_sorted Hz_ulp).1).1].         *)
have Hr_nonover : Pnonoverlap (vsebK 3 e).
  apply/Pnonoverlap_take.
  rewrite /e; apply: vecSum_vseb_Pnonoverlap.
  - exact: Hceven.
  - by rewrite /z size_Merge.
  - exact: Hz_format.
  - exact: Hz_sorted.
  exact: Hz_ulp.
(* and its terms are floating-point numbers.                                  *)
have Hr_format : {in vsebK 3 e, forall t, format t}.
  by apply/format_vsebK/format_vecSum.
(* Reading the first three terms off the P-nonoverlapping sequence            *)
(* yields a triple-word number.  Case on the (<=3, zero-padded) list [vsebK   *)
(* 3 e]; formats come from [Hr_format], the strict ulp bounds from either     *)
(* [Hr_nonover] (real terms) or [0 < ulp _] (the padding zeros).              *)
rewrite /TWSum -/z -/e.
move: Hr_nonover Hr_format; case: (vsebK 3 e) => [|r0 [|r1 [|r2 tl]]] Hno Hfmt.
- by split; try exact: generic_format_0; left.
- by split; try exact: generic_format_0;
     [apply: Hfmt; rewrite !inE eqxx | left | left].
- by split; [apply: Hfmt; rewrite !inE eqxx | apply: Hfmt; rewrite !inE eqxx orbT
           | exact: generic_format_0 | apply: (Hno 0%N) | left].
by split; [apply: Hfmt; rewrite !inE eqxx | apply: Hfmt; rewrite !inE eqxx orbT
         | apply: Hfmt; rewrite !inE eqxx !orbT | apply: (Hno 0%N)
         | apply: (Hno 1%N)].
Qed.

(* A float is at most [(2 - 2u) ufp] of itself (max-mantissa bound).  Holds   *)
(* also at 0 and in the subnormal range, so no no-underflow hypothesis.       *)
Lemma TWSum_error x y :
  ties_to_even choice ->
  isTW x -> isTW y ->
  Rabs (TWval (TWSum x y) - (TWval x + TWval y)) <=
     errc * Rabs (TWval x + TWval y).
Proof.
case: x => x0 x1 x2; case: y => y0 y1 y2 => Hceven Hx Hy.
pose z := Merge [:: x0; x1; x2] [:: y0; y1; y2].
pose e := vecSum z.
(* Merge is a permutation: it preserves the exact sum.                        *)
have Hmerge_sum : sumR z = (x0 + x1 + x2) + (y0 + y1 + y2).
  by rewrite Merge_sumR /=; lra.
(* VecSum is error-free.                                                      *)
have Hvec_sum : sumR e = sumR z.
  rewrite vecSum_sum //; apply: format_Merge; first by apply: (isTW_format Hx).
  by apply: isTW_format Hy.

(* VSEB is error-free on the full output.                                     *)
have Hvseb_sum : sumR (vseb e) = sumR e.
  apply: vseb_sum; apply: format_vecSum; apply: format_Merge.
  - by apply: (isTW_format Hx).
  by apply: isTW_format Hy.
(* Truncating to the first three terms loses at most errc of the sum          *)
(* (Theorem 3 with k = 3).                                                    *)
have Htrunc :
  Rabs (sumR (vseb e) - sumR (vsebK 3 e)) <= errc * Rabs (sumR e).
  have Hzf : {in z, forall t, format t}.
    apply: format_Merge.
      by case: Hx => x0F x1F x2F _ _ t; rewrite !inE => /or3P[] /eqP->.
    by case: Hy => y0F y1F y2F _ _ t; rewrite !inE => /or3P[] /eqP->.
  have Hzs : sorted_mag z.
    by apply: Merge_sorted_mag;
      [apply: isTW_sorted_mag Hx | apply: isTW_sorted_mag Hy].
  have Hzu : pairwise_ulp z.
    apply: Merge_pairwise_ulp => [t|t||].
    - by rewrite !inE => /or3P[] /eqP->; case: Hx.
    - by rewrite !inE => /or3P[] /eqP->; case: Hy.
    - by apply: isTW_Pnonoverlap Hx.
    by apply: isTW_Pnonoverlap Hy.
  have Fe : {in e, forall t, format t} by apply: format_vecSum.
  have Py : Pnonoverlap (vseb e).
    rewrite /e; apply: vecSum_vseb_Pnonoverlap.
    - exact: Hceven.
    - by rewrite /z size_Merge.
    - exact: Hzf.
    - exact: Hzs.
    exact: Hzu.
  have Fy : {in vseb e, forall t, format t} by apply: format_vseb.
  set y := vseb e.
  have Hsplit : sumR (vseb e) - sumR (vsebK 3 e) = sumR (drop 3 y).
    by rewrite /vsebK -/y -{1}(cat_take_drop 3 y) sumR_cat; ring.
  rewrite Hsplit -Hvseb_sum -/y.
  (* The dropped tail is bounded by Theorem 3 (general k), at k = 3.          *)
  have Hu0 : 0 < u by rewrite uE; apply: bpow_gt_0.
  have Hu64 : u <= / 64.
    rewrite uE; have -> : (/ 64 = bpow beta (-6))%R
      by rewrite /= /Z.pow_pos /=; lra.
    by apply: bpow_le; lia.
  have -> : 2 * (u * u * u) + 42 / 10 * (u * u * u * u) =
            2 * u ^ 3 + 42 / 10 * u ^ 3.+1 by rewrite /=; ring.
  case: (Req_dec (nth 0 y 0) 0) => [Hy0z|Hy0n]; last first.
    by apply: Pnonoverlap_truncate_error.
  have H1 := nth_step_zero Py Fy Hy0z.
  have H2 := nth_step_zero Py Fy H1.
  have H3 := nth_step_zero Py Fy H2.
  have -> : sumR (drop 3 y) = 0.
    apply: small_head_zero; [by apply: Pnonoverlap_drop
      | by move=> t /mem_drop; apply: Fy | by rewrite nth_drop addn0].
  rewrite Rabs_R0; apply: Rmult_le_pos; last exact: Rabs_pos.
  have H4 : 0 <= u ^ 3 by apply: pow_le; lra.
  have H5 : 0 <= u ^ 3.+1 by apply: pow_le; lra.
  lra.
(* The result of TWSum is exactly the value of those three terms.  [vsebK 3 e]*)
(* has length <= 3 (it is a [take 3]); TWSum reads its (zero-padded) first    *)
(* three entries, whose sum is exactly [sumR (vsebK 3 e)].                    *)
have Hres : TWval (TWSum (TWR x0 x1 x2) (TWR y0 y1 y2)) = sumR (vsebK 3 e).
  have Hsz : (size (vsebK 3 e) <= 3)%N.
    rewrite /vsebK size_take; case: ifP => [_|Hf]; first by [].
    by rewrite leqNgt Hf.
  rewrite /TWSum -/z -/e.
  move: Hsz; case: (vsebK 3 e) => [|r0 [|r1 [|r2 [|r3 l]]]] /= H; try by lra.
  by exfalso; move/leP: H; lia.
(* Chaining the equalities and the truncation bound concludes.  Both operands *)
(* sum to [sumR (vseb e)] (Merge/VecSum/VSEB preserve the sum), the result is *)
(* [sumR (vsebK 3 e)] (Hres), so the error is the dropped tail bounded by     *)
(* [Htrunc].                                                                  *)
have E1 : TWval (TWR x0 x1 x2) + TWval (TWR y0 y1 y2) = sumR (vseb e).
  by rewrite /= Hvseb_sum Hvec_sum Hmerge_sum.
rewrite Hres E1 Rabs_minus_sym {2}Hvseb_sum.
exact: Htrunc.
Qed.


End SecTWSum.
