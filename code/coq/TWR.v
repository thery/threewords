(* ---------------------------------------------------------------------------*)
(* Triple-word numbers [twR] (paper Def. 5): a triplet of floats that is      *)
(* P-nonoverlapping.  The record, its projectors [tw0]/[tw1]/[tw2] and value  *)
(* [TWval], the predicate [isTW], the list view [TW2l], and that an [isTW] is *)
(* magnitude-sorted / P-nonoverlapping / made of floats.  Generic over the    *)
(* precision [p] and minimal exponent [emin]; built on [Nonoverlap].          *)
(* ---------------------------------------------------------------------------*)

From Stdlib Require Import ZArith Reals Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
Require Import Nmore Rmore Fmore Rstruct MULTmore prelim.
From Flocq Require Import Pff.Pff2Flocq.
Require Import Nonoverlap.

Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section TWR.

Variable p : Z.
Variable emin : Z.
Hypothesis Hp2 : (1 < p)%Z.

Let beta := radix2.

Open Scope R_scope.

Local Instance p_gt_0 : Prec_gt_0 p.
Proof. now apply Z.lt_trans with (2 := Hp2). Qed.

Local Notation fexp := (FLT_exp emin p).
Local Notation format := (generic_format beta fexp).
Local Notation ulp := (ulp beta fexp).
Local Notation Pnonoverlap := (Pnonoverlap p emin).
Local Notation pairwise_ulp := (pairwise_ulp p emin).
Local Notation format_lt_ulp_le := (@format_lt_ulp_le p emin Hp2).

Inductive twR := TWR (x0 x1 x2 : R).

(* Named projectors for the triple-word record [twR], mirroring [dwh]/[dwl].  *)
Definition tw0 (t : twR) : R := let: TWR x0 _ _ := t in x0.
Definition tw1 (t : twR) : R := let: TWR _ x1 _ := t in x1.
Definition tw2 (t : twR) : R := let: TWR _ _ x2 := t in x2.

Lemma tw0E x0 x1 x2 : tw0 (TWR x0 x1 x2) = x0. Proof. by []. Qed.
Lemma tw1E x0 x1 x2 : tw1 (TWR x0 x1 x2) = x1. Proof. by []. Qed.
Lemma tw2E x0 x1 x2 : tw2 (TWR x0 x1 x2) = x2. Proof. by []. Qed.

Definition TWval (x : twR) : R := let: TWR x0 x1 x2 := x in x0 + x1 + x2.


(* Definition 5: a triple-word number is a P-nonoverlapping triplet           *)
(* of floating-point numbers.                                                 *)
Definition isTW (x : twR) : Prop :=
  let: TWR x0 x1 x2 := x in
  [/\ format x0, format x1, format x2, Rabs x1 < ulp x0 & Rabs x2 < ulp x1].

(* ===========================================================================*)
(*  Triple-word numbers as 3-element sequences                                *)
(* ===========================================================================*)
Definition TW2l x := let: TWR x0 x1 x2 := x in [:: x0; x1; x2].

(* The merge precondition for a single TW: its three limbs are magnitude-     *)
(* sorted.  Two applications of [format_lt_ulp_le] to the [isTW] conjuncts.   *)
Lemma isTW_sorted_mag x : isTW x -> sorted_mag (TW2l x).
Proof.
by case : x => x0 x1 x2 [x0F x1F x2F x1Lux0 x2Lux1] [|[|//]] _; 
   apply: format_lt_ulp_le.
Qed.

(* A triple-word, viewed as a 3-element list, is P-nonoverlapping (Def. 5).   *)
Lemma isTW_Pnonoverlap x : isTW x -> Pnonoverlap (TW2l x).
Proof.
by case : x => x0 x1 x2 [x0F x1F x2F x1Lux0 x2Lux1] [|[|[]]].
Qed.

(* The three limbs of a triple-word are floats (part of Def. 5).              *)
Lemma isTW_format x : isTW x -> {in (TW2l x), forall z, format z}.
Proof.
by case : x => x0 x1 x2 [x0F x1F x2F _ _] z; rewrite !inE => /or3P[] /eqP->.
Qed.

End TWR.
