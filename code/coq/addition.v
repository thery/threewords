(* ---------------------------------------------------------------------------*)
(* Triple-word addition (Algorithm 8, "TWSum") of                             *)
(*   N. Fabiano, J.-M. Muller, J. Picot,                                      *)
(*   "Algorithms for triple-word arithmetic", IEEE TC, 2019.                  *)
(*   (doc/paper3.pdf, Section 5).                                             *)
(*                                                                            *)
(* This file starts the Flocq/Rocq formalisation, in the same style           *)
(* as algoExp1.v / algoLog1.v (mathcomp + the [prelim] infrastructure).       *)
(* The algorithm is defined faithfully; the correctness and error             *)
(* theorems are stated and their proofs are only *sketched* with              *)
(* [have name : formula] steps, the intermediate steps being [admit]ed.       *)
(* Filling those steps is the goal of the formalisation.                      *)
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
Require Import TWSum.

Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section TWAdd.

Let p := 53%Z.
Let emax := 1024%Z.
Let emin := (3 - emax - p)%Z.

Local Notation beta := radix2.

Hypothesis Hp2 : Z.lt 1 p.
Local Notation pow e := (bpow beta e).

Local Instance p_gt_0 : Prec_gt_0 p.
now apply Z.lt_trans with (2 := Hp2).
Qed.

Open Scope R_scope.

(* [u] is the round-to-nearest unit roundoff; [errc] below is the paper's     *)
(* relative-error constant [2u^3 + 4.2u^4].                                   *)
Local Notation u := (u p beta).

(* Following paper3, the whole development is under round-to-nearest (ties    *)
(* broken by [choice] to even, [RN(-t) = -RN(t)]); see [TwoSum.v].            *)
Variable choice : Z -> bool.
Hypothesis choice_sym : forall x, choice x = ~~ choice (- (x + 1))%Z.

Lemma emin_le_0 : (emin <= 0)%Z.
Proof. by rewrite /emin /emax /p; lia. Qed.

(* The triple-word predicate from [TWR.v], specialised to binary64.           *)
Local Notation isTW := (isTW p emin).

(* Triple-word addition (Algorithm 8) and its two theorems now live in        *)
(* [TWSum.v], generic over [p]/[emin] under the precision bound [6 <= p].     *)
(* At binary64 ([p = 53]) that bound is immediate, so we discharge it and     *)
(* re-state the headline results with everything specialised.                 *)
Lemma Hp6 : (6 <= p)%Z. Proof. by rewrite /p; lia. Qed.

Local Notation TWSum := (TWSum p emin choice).
Local Notation errc :=
  (2 * (u * u * u) + 42 / 10 * (u * u * u * u)).

(* The sum of two triple words is a triple word (paper Theorem, Section 5.1). *)
Theorem TWSum_isTW x y : isTW x -> isTW y -> isTW (TWSum x y).
Proof. exact: (TWSum_isTW Hp2 emin_le_0 Hp6 choice_sym). Qed.

(* Its relative error is at most [errc = 2u^3 + 4.2u^4] (Ensure of Alg. 8).   *)
Theorem TWSum_error x y : isTW x -> isTW y ->
  Rabs (TWval (TWSum x y) - (TWval x + TWval y)) <=
    errc * Rabs (TWval x + TWval y).
Proof. exact: (TWSum_error Hp2 emin_le_0 Hp6 choice_sym). Qed.

End TWAdd.
