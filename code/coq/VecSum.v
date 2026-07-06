(* ---------------------------------------------------------------------------*)
(* Algorithm 4 (VecSum) and the paper's Theorem 1 (its output is              *)
(* F-nonoverlapping).  A general round-to-nearest building block, generic     *)
(* over the precision [p] and minimal exponent [emin] (binary64 is fixed      *)
(* only in [addition.v]); built on [TwoSum] and [Nonoverlap].                 *)
(* ---------------------------------------------------------------------------*)

From Stdlib Require Import ZArith Reals Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
Require Import Nmore Rmore Fmore Rstruct MULTmore prelim.
From Flocq Require Import Pff.Pff2Flocq.
Require Import Uls.
Require Import TwoSum.
Require Import Nonoverlap.

Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SecVecSum.

Variable p : Z.
Variable emin : Z.
Hypothesis Hp2 : (1 < p)%Z.
Hypothesis emin_le_0 : (emin <= 0)%Z.

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
Local Notation fexp := (FLT_exp emin p).
Local Notation format := (generic_format beta fexp).
Local Notation cexp := (cexp beta fexp).
Local Notation mant := (scaled_mantissa beta fexp).
Local Notation RND := (round beta fexp rnd).
Local Notation ulp := (ulp beta fexp).
Local Notation uls := (uls p emin).
Local Notation error_le_half_ulp_RN :=
  (@error_le_half_ulp_round beta (FLT_exp emin p)
     (FLT_exp_valid emin p) (FLT_exp_monotone emin p) choice).
Local Notation TwoSum_correct_RN :=
  (@TwoSum_correct emin p choice Hp2 emin_le_0 choice_sym).

Local Notation TwoSum := (TwoSum p emin choice).
Local Notation TwoSum_hi := (TwoSum_hi p emin choice).
Local Notation formatDWR := (formatDWR p emin).
Local Notation magnitudeDWR := (magnitudeDWR p emin).
Local Notation format_TwoSum := (format_TwoSum Hp2 choice).
Local Notation TwoSum_correct_loc :=
  (TwoSum_correct_loc Hp2 emin_le_0 choice_sym).
Local Notation magnitude_TwoSum :=
  (magnitude_TwoSum Hp2 emin_le_0 choice_sym).
Local Notation TwoSum_err_imul := (TwoSum_err_imul Hp2 emin_le_0 choice_sym).
Local Notation TwoSum_err_uls_ge :=
  (TwoSum_err_uls_ge Hp2 emin_le_0 choice_sym).

Local Notation Pnonoverlap := (Pnonoverlap p emin).
Local Notation pairwise_ulp := (pairwise_ulp p emin).
Local Notation Fnonoverlap := (Fnonoverlap p emin).
Local Notation format_lt_ulp_0 := (@format_lt_ulp_0 p emin Hp2).
Local Notation format_lt_ulp_le := (@format_lt_ulp_le p emin Hp2).
Local Notation Pnonoverlap_imp_pairwise_ul :=
  (Pnonoverlap_imp_pairwise_ul Hp2).
Local Notation abs_le_ufp_norm := (abs_le_ufp_norm Hp2).
Local Notation nu_of_lt_ulp := (nu_of_lt_ulp Hp2).
Local Notation small_head_zero := (@small_head_zero p emin Hp2).
Local Notation sumR_ufp_bound := (@sumR_ufp_bound p emin Hp2).
Local Notation nth_step_zero := (@nth_step_zero p emin Hp2).

(* === BODY PLACEHOLDER === *)

End SecVecSum.
