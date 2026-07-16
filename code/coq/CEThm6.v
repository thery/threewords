(* Counterexample: vecSum_Thm6 as currently stated (Fnonoverlap of the raw    *)
(* VecSum output) is FALSE.  Input [15;15;15/16;15/16] at p=4 satisfies       *)
(* sorted_mag + pairwise_ulp + size<=6 + normal + ties-to-even, yet           *)
(* VecSum = [32;-1;7/8;0], which is NOT F-nonoverlapping (|7/8| > 1/2 uls(-1) *)
(* = 1/2).  The paper's real Theorem 6 concludes P-nonoverlap of VSEB(VecSum),*)
(* a strictly weaker statement.                                               *)
From Stdlib Require Import ZArith Reals Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
Require Import Nmore Rmore Fmore Rstruct MULTmore prelim.
From Flocq Require Import Pff.Pff2Flocq.
Require Import Uls.
Require Import TwoSum.
Require Import Nonoverlap.
Require Import VecSum.

Open Scope R_scope.

Definition p : Z := 4.
Definition emin : Z := (-20).
Definition choice (z : Z) : bool := negb (Z.even z).

Local Notation beta := radix2.
Local Notation pow e := (bpow beta e).
Local Notation fexp := (FLT_exp emin p).
Local Notation format := (generic_format beta fexp).
Local Notation rnd := (Znearest choice).
Local Notation RND := (round beta fexp rnd).

Lemma Hp2 : (1 < p)%Z. Proof. by []. Qed.
Lemma emin_le_0 : (emin <= 0)%Z. Proof. by []. Qed.
Instance p_gt_0 : Prec_gt_0 p. Proof. by []. Qed.
Instance valid_rnd : Valid_rnd rnd := valid_rnd_N choice.

(* the input list                                                             *)
Definition l : seq R := [:: 15; 15; 15/16; 15/16].

Local Notation TwoSum := (TwoSum p emin choice).
Local Notation vecSum := (VecSum.vecSum p emin choice).
Local Notation vecSumAux := (VecSum.vecSumAux p emin choice).
Local Notation Fnonoverlap := (Nonoverlap.Fnonoverlap p emin).
Local Notation uls := (Uls.uls p emin).

Lemma choice_sym : forall x, choice x = ~~ choice (- (x + 1))%Z.
Proof.
move=> x; rewrite /choice; congr negb.
have -> : (- (x + 1) = - x - 1)%Z by lia.
by rewrite Z.even_sub Z.even_opp /=; case: Z.even.
Qed.

(* format facts                                                               *)
Lemma Ffloat (m e : Z) : (Z.abs m < 2 ^ p)%Z -> (emin <= e)%Z ->
  format (IZR m * pow e).
Proof.
move=> Hm He; apply: generic_format_FLT.
by exists (Float beta m e); [rewrite /F2R | | ].
Qed.

Lemma Ffloat' (v : R) (m e : Z) : v = IZR m * pow e ->
  (Z.abs m < 2 ^ p)%Z -> (emin <= e)%Z -> format v.
Proof. by move=> ->; apply: Ffloat. Qed.

Lemma F15 : format 15.
Proof. by apply: (Ffloat' _ 15 0); rewrite /= ?Rmult_1_r. Qed.

Lemma F15_16 : format (15 / 16).
Proof.
by apply: (Ffloat' _ 15 (-4)); rewrite //= /Z.pow_pos /=; lra.
Qed.

Lemma F15_8 : format (15 / 8).
Proof.
by apply: (Ffloat' _ 15 (-3)); rewrite //= /Z.pow_pos /=; lra.
Qed.

Lemma F7_8 : format (7 / 8).
Proof.
by apply: (Ffloat' _ 7 (-3)); rewrite //= /Z.pow_pos /=; lra.
Qed.

Lemma F16 : format 16.
Proof. apply: (Ffloat' _ 1 4); [rewrite /= /Z.pow_pos /=; lra | | ]; by []. Qed.

Lemma F32 : format 32.
Proof. apply: (Ffloat' _ 1 5); [rewrite /= /Z.pow_pos /=; lra | | ]; by []. Qed.

Lemma Fm1 : format (-1).
Proof.
apply: generic_format_opp; apply: (Ffloat' _ 1 0); rewrite /= ?Rmult_1_r; by [].
Qed.

Lemma RND_15_8 : RND (15 / 8) = 15 / 8.
Proof. by apply: round_generic; apply: F15_8. Qed.

(* 15 + 15/8 = 135/8 = 16.875 rounds to 16 (nearest float; 18 is farther).    *)
Lemma RND_16875 : RND (15 + 15 / 8) = 16.
Proof.
have V := FLT_exp_valid emin p.
have E16 : (16 = pow 4) by rewrite /= /Z.pow_pos /=; lra.
have E18 : (18 = 9 * pow 1) by rewrite /= /Z.pow_pos /=; lra.
have Vd := V p_gt_0.
have U16 : ulp beta fexp 16 = 2.
  rewrite E16 ulp_bpow /FLT_exp Z.max_l /=; last by [].
  by rewrite /= /Z.pow_pos /=; lra.
have Hd : round beta fexp Zfloor (15 + 15 / 8) = 16.
  apply: round_DN_eq => //; first exact: F16.
  rewrite succ_eq_pos; last by lra.
  rewrite U16; lra.
have F18 : format 18 by rewrite E18; apply: (Ffloat 9 1).
have Hu : round beta fexp Zceil (15 + 15 / 8) = 18.
  have -> : (15 + 15 / 8 = 16 + 7 / 8) by lra.
  rewrite (@round_UP_plus_eps beta fexp Vd 16 F16 (7/8)); last first.
    rewrite Rle_bool_true; last by lra.
    rewrite U16; lra.
  rewrite succ_eq_pos; last by lra.
  rewrite U16; lra.
rewrite (@round_N_eq_DN beta fexp Vd choice (15 + 15/8)); first by rewrite Hd.
rewrite Hd Hu; lra.
Qed.

(* 15 + 16 = 31 is the exact midpoint of [30,32]; ties-to-even -> 32.         *)
Lemma RND_31 : RND (15 + 16) = 32.
Proof.
have V := FLT_exp_valid emin p.
have Vd := V p_gt_0.
have E30 : (30 = 15 * pow 1) by rewrite /= /Z.pow_pos /=; lra.
have F30 : format 30 by rewrite E30; apply: (Ffloat 15 1).
have U30 : ulp beta fexp 30 = 2.
  rewrite ulp_neq_0; last by lra.
  rewrite /cexp /FLT_exp Z.max_l.
    rewrite (mag_unique beta 30 5) /=; [by rewrite /Z.pow_pos /=; lra | ].
    rewrite /= /Z.pow_pos /= Rabs_pos_eq; lra.
  have Hm30 : (mag beta 30 = 5%Z :> Z)
    by apply: mag_unique_pos; rewrite /= /Z.pow_pos /=; lra.
  rewrite /p /emin; lia.
have Hd : round beta fexp Zfloor (15 + 16) = 30.
  apply: round_DN_eq => //.
  rewrite succ_eq_pos; last by lra.
  rewrite U30; lra.
have Hu : round beta fexp Zceil (15 + 16) = 32.
  have -> : (15 + 16 = 30 + 1) by lra.
  rewrite (@round_UP_plus_eps beta fexp Vd 30 F30 1); last first.
    rewrite Rle_bool_true; last by lra.
    rewrite U30; lra.
  rewrite succ_eq_pos; last by lra.
  rewrite U30; lra.
rewrite (@round_N_middle beta fexp choice (15 + 16));
  last by rewrite Hd Hu; lra.
rewrite Hd Hu.
have Hm31 : (mag beta (15 + 16) = 5%Z :> Z)
  by apply: mag_unique_pos; rewrite /= /Z.pow_pos /=; lra.
have Hsm : scaled_mantissa beta fexp (15 + 16) = 31 / 2.
  rewrite /scaled_mantissa /cexp Hm31 /FLT_exp Z.max_l /p /emin //.
  rewrite /= /Z.pow_pos /=; lra.
rewrite Hsm.
have Hzf : Zfloor (31 / 2) = 15%Z.
  apply: Zfloor_imp; rewrite (_ : (15 + 1)%Z = 16%Z) //= /Z.pow_pos /=; lra.
by rewrite Hzf /choice /=.
Qed.

(* Any 2Sum with format operands is fully determined by its rounded sum.      *)
Lemma TwoSum_eq a b : format a -> format b ->
  TwoSum a b = DWR (RND (a + b)) (a + b - RND (a + b)).
Proof.
move=> Fa Fb.
have Hc := TwoSum_correct_loc Hp2 emin_le_0 choice_sym Fa Fb.
rewrite {1}/TwoSum.TwoSum; congr DWR; lra.
Qed.

Local Notation pairwise_ulp := (Nonoverlap.pairwise_ulp p emin).

(* VecSum processes right-to-left:                                            *)
(*   TwoSum(15/16, 15/16) = (15/8, 0);   TwoSum(15, 15/8) = (16, 7/8);        *)
(*   TwoSum(15, 16)       = (32, -1).                                         *)
Lemma vecSum_l : vecSum l = [:: 32; -1; 7/8; 0].
Proof.
have E1 : vecSumAux [:: 15/16] = ([::], 15/16) by [].
have E2 : vecSumAux [:: 15/16; 15/16] = ([:: 0], 15/8).
  rewrite vecSumAux_cons E1 (TwoSum_eq _ _ F15_16 F15_16).
  have -> : (15/16 + 15/16 = 15/8 :> R) by lra.
  rewrite RND_15_8.
  by congr (_, _); congr (_ :: _); lra.
have E3 : vecSumAux [:: 15; 15/16; 15/16] = ([:: 7/8; 0], 16).
  rewrite vecSumAux_cons E2 (TwoSum_eq _ _ F15 F15_8) RND_16875.
  by congr (_, _); congr (_ :: _); lra.
have E4 : vecSumAux l = ([:: -1; 7/8; 0], 32).
  rewrite /l vecSumAux_cons E3 (TwoSum_eq _ _ F15 F16) RND_31.
  by congr (_, _); congr (_ :: _); lra.
by rewrite /vecSum E4.
Qed.

(* [mag (-1) = 1]: [2^0 <= |-1| < 2^1].                                       *)
Lemma mag_m1 : (mag beta (-1) = 1%Z :> Z).
Proof.
apply: mag_unique.
rewrite Rabs_Ropp Rabs_R1 /= /Z.pow_pos /=; lra.
Qed.

(* [uls (-1) = 1]: [cexp (-1) = -3], mantissa [-8] has three trailing zeros,  *)
(* so the rightmost nonzero bit sits at [2^(-3+3) = 2^0].                     *)
Lemma uls_m1 : uls (-1) = 1.
Proof.
rewrite /Uls.uls; case: Req_bool_spec => [|_]; first by lra.
have Hce : cexp beta fexp (-1) = (-3)%Z.
  rewrite /cexp mag_m1 /FLT_exp /p /emin; lia.
have Hsm : Ztrunc (scaled_mantissa beta fexp (-1)) = (-8)%Z.
  rewrite /scaled_mantissa Hce.
  have -> : (-1 * pow (- (-3)) = -8) by rewrite /= /Z.pow_pos /=; lra.
  by apply: Ztrunc_IZR.
by rewrite Hce Hsm /= /Z.pow_pos /=; lra.
Qed.

(* ===========================================================================*)
(*  The counterexample                                                        *)
(* ===========================================================================*)
(* Every hypothesis of the (deleted) [vecSum_Thm6] holds for [l], yet its     *)
(* conclusion [Fnonoverlap (vecSum l)] fails: the raw VecSum output           *)
(* [[32; -1; 7/8; 0]] has [|7/8| > 1/2 uls(-1) = 1/2].                        *)
Theorem vecSum_Thm6_is_false :
  [/\ VecSum.ties_to_even choice,
      (size l <= 6)%N,
      {in l, forall z, format z},
      sorted_mag l & pairwise_ulp l] /\
  (forall z, z \in l -> z <> 0 -> (emin + p <= mag beta z)%Z) /\
  ~ Fnonoverlap (vecSum l).
Proof.
have Hmag15 : (mag beta 15 = 4%Z :> Z).
  apply: mag_unique_pos; rewrite /= /Z.pow_pos /=; lra.
have Hmag1516 : (mag beta (15/16) = 0%Z :> Z).
  apply: mag_unique_pos; rewrite /= /Z.pow_pos /=; lra.
have Hulp15 : ulp beta fexp 15 = 1.
  rewrite ulp_neq_0; last by lra.
  by rewrite /cexp Hmag15 /FLT_exp /p /emin /=; lra.
split; last split.
- split.
  + by move=> z; rewrite /choice.
  + by [].
  + by move=> z; rewrite /l !inE => /or4P[] /eqP->;
      [exact: F15 | exact: F15 | exact: F15_16 | exact: F15_16].
  + by move=> [|[|[|i]]] Hi //=; rewrite ?Rabs_pos_eq; lra.
  by move=> [|[|i]] Hi //=; rewrite Hulp15 Rabs_pos_eq; lra.
- by move=> z; rewrite /l !inE => /or4P[] /eqP-> _;
    rewrite ?Hmag15 ?Hmag1516 /p /emin; lia.
(* [vecSum l = [32; -1; 7/8; 0]]: the zeros are filtered out, and the second  *)
(* surviving pair demands [|7/8| <= 1/2 uls(-1) = 1/2], which is false.       *)
rewrite vecSum_l /Nonoverlap.Fnonoverlap.
have H32 : (32 != 0 :> R) by apply/eqP; lra.
have Hm1 : (-1 != 0 :> R) by apply/eqP; lra.
have H78 : (7/8 != 0 :> R) by apply/eqP; lra.
have H0 : ((0:R) != 0 :> R) = false by apply/negbTE; rewrite negbK.
rewrite /= H32 Hm1 H78 H0 /=.
have Hne : is_left (Req_EM_T (-1) 0) = false.
  by case: Req_EM_T => // H; lra.
rewrite Hne uls_m1.
move=> [_ [H _]].
have := H (ltac:(lra) : (7/8 <> 0)).
rewrite Rabs_pos_eq; lra.
Qed.
