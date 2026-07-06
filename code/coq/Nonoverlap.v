(* ---------------------------------------------------------------------------*)
(* Separation predicates on sequences of floats and the list-sum [sumR],      *)
(* split out of [addition.v]: P-nonoverlapping (Priest, Def. 1), magnitude    *)
(* order [sorted_mag], and the pairwise-ulp separation, with their head/tail  *)
(* manipulation lemmas.  Generic over the precision [p] and minimal exponent  *)
(* [emin]; binary64 is fixed only in [addition.v].                            *)
(* ---------------------------------------------------------------------------*)

From Stdlib Require Import ZArith Reals Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
Require Import Nmore Rmore Fmore Rstruct MULTmore prelim.
From Flocq Require Import Pff.Pff2Flocq.

Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Nonoverlap.

Variable p : Z.
Variable emin : Z.

Let beta := radix2.

Open Scope R_scope.

Local Notation fexp := (FLT_exp emin p).
Local Notation ulp := (ulp beta fexp).

(* Sum of a sequence, used to state exactness of the building blocks.         *)
Fixpoint sumR (l : seq R) : R := if l is a :: l' then a + sumR l' else 0.

(* P-nonoverlapping (Priest, Definition 1): |x_{i+1}| < ulp (x_i).            *)
Definition Pnonoverlap (l : seq R) : Prop :=
  forall i, (i.+1 < size l)%N -> Rabs (nth 0 l i.+1) < ulp (nth 0 l i).

(* Dropping the head of a P-nonoverlapping sequence keeps it P-nonoverlapping.*)
Lemma Pnonoverlap_cons a l : Pnonoverlap (a :: l) -> Pnonoverlap l.
Proof. by move=> alP i iLs; apply: (alP i.+1). Qed.

(* The two preconditions of Theorem 6 on the merged sequence.                 *)

(* --- magnitude order -----------------------------------------------------  *)
(* [sorted_mag l]: the sequence is non-increasing in magnitude.               *)
Definition sorted_mag (l : seq R) : Prop :=
  forall i, (i.+1 < size l)%N -> Rabs (nth 0 l i.+1) <= Rabs (nth 0 l i).

(* Peel the head of a [sorted_mag] sequence: the first step plus the tail.    *)
Lemma sorted_mag_cons a1 a2 l :
  sorted_mag [:: a1,  a2 & l] -> Rabs a2 <= Rabs a1 /\ sorted_mag (a2 :: l).
Proof.
move=> a1a2lM; split; first by apply: (a1a2lM 0%N).
by move=> n Hn; apply: (a1a2lM n.+1).
Qed.

(* Cons a larger-magnitude head onto a [sorted_mag] sequence.                 *)
Lemma sorted_mag_cons_inv a1 a2 l :
  Rabs a2 <= Rabs a1 -> sorted_mag (a2 :: l) -> sorted_mag [:: a1,  a2 & l].
Proof. by move=> a2La1 a2lN [//|i Hi]; apply: (a2lN i). Qed.

(* Replace the head by an even larger one (still [sorted_mag]).               *)
Lemma sorted_mag_le a1 a2 l :
  sorted_mag (a1 :: l) -> Rabs a1 <= Rabs a2 -> sorted_mag (a2 :: l).
Proof.
case: l => // a3 l /sorted_mag_cons[a1La3 a3lS] a1La2.
by apply: sorted_mag_cons_inv => //; lra.
Qed.

(* --- pairwise ulp separation ---------------------------------------------  *)
(* [pairwise_ulp l]: each term is below ulp of the term two positions before; *)
(* this tolerates a single overlap but never two in a row.                    *)
Definition pairwise_ulp (l : seq R) : Prop :=
  forall i, (i.+2 < size l)%N -> Rabs (nth 0 l i.+2) < ulp (nth 0 l i).

(* Peel the head: the third-term bound [Rabs a3 < ulp a1] plus the tail.      *)
Lemma pairwise_ulp_cons a1 a2 a3 l :
  pairwise_ulp [:: a1, a2, a3 & l] ->
  Rabs a3 < ulp a1 /\ pairwise_ulp [::a2, a3 & l].
Proof.
move=> a1a2a3lU; split; last by move=> n Hn; apply: (a1a2a3lU n.+1).
by apply: (a1a2a3lU 0%N).
Qed.

(* Cons a head given its bound against the third term.                        *)
Lemma pairwise_ulp_cons_inv a1 a2 a3 l :
  Rabs a3 < ulp a1 ->
  pairwise_ulp (a2 :: a3 :: l) -> pairwise_ulp [:: a1, a2, a3 & l].
Proof. by move=> a2La1 a2lN [//|i Hi]; apply: (a2lN i). Qed.

(* Cons a head onto any tail: the only new obligation is the third-term bound.*)
Lemma pairwise_ulp_cons1_inv a l :
  pairwise_ulp l  -> ((1 < size l)%N -> Rabs(nth 0 l 1) < ulp a) ->
  pairwise_ulp (a :: l).
Proof.
case: l => // b [|c l] //= bclP /(_ isT) cLua.
by apply: pairwise_ulp_cons_inv.
Qed.

End Nonoverlap.
