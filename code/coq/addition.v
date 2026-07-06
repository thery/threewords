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

Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section TWAdd.

Let p := 53%Z.
Let emax := 1024%Z.
Let emin := (3 - emax - p)%Z.

(* [beta]/[rnd] are concrete notations (not [Let]s) so goals show [radix2] /  *)
(* [Znearest choice] literally, matching the (inlined) statements of imported *)
(* [TwoSum]/[Uls] lemmas -- so [lra] sees the same atoms across files.  [p] / *)
(* [emin] stay [Let]s: the imported lemmas are generic in them and instantiate*)
(* at these values.                                                           *)
Local Notation beta := radix2.

Hypothesis Hp2 : Z.lt 1 p.
Local Notation pow e := (bpow beta e).

Local Instance p_gt_0 : Prec_gt_0 p.
now apply Z.lt_trans with (2 := Hp2).
Qed.

Open Scope R_scope.

Local Notation u := (u p beta).
Local Notation u_gt_0 := (u_gt_0 p beta).

Lemma uE : u = pow (- p).
Proof. by rewrite /u /= /Z.pow_pos /=; lra. Qed.

(* Following paper3, the whole development is under round-to-nearest          *)
(* (ties broken by [choice]): the paper sets RN(.) as its standing rounding   *)
(* mode in the preliminaries and writes every operation as RN(...).  This     *)
(* is needed for the error-free transforms (e.g. 2Sum is exact and its low    *)
(* word is bounded by half an ulp) -- a generic [Valid_rnd] is too weak.      *)
Variable choice : Z -> bool.
(* Ties broken to even (the symmetry [RN(-t) = -RN(t)]); required by          *)
(* Flocq's [TwoSum_correct].                                                  *)
Hypothesis choice_sym : forall x, choice x = ~~ choice (- (x + 1))%Z.
Local Notation rnd := (Znearest choice).
Local Instance valid_rnd : Valid_rnd rnd := valid_rnd_N choice.

Lemma emin_le_0 : (emin <= 0)%Z.
Proof. by rewrite /emin /emax /p; lia. Qed.

Local Notation float := (float radix2).
Local Notation fexp := (FLT_exp emin p).
Local Notation format := (generic_format beta fexp).
Local Notation cexp := (cexp beta fexp).
Local Notation mant := (scaled_mantissa beta fexp).
Local Notation RND := (round beta fexp rnd).
Local Notation ulp := (ulp beta fexp).
(* [uls] (from [Uls.v]) is generic over [p]/[emin]; fix them to this format.  *)
Local Notation uls := (uls p emin).
Local Notation fastTwoSum := (fastTwoSum beta emin p rnd).
(* Round-to-nearest half-ulp error bound with this section's format and tie-  *)
(* breaking pre-applied: [error_le_half_ulp_RN x : Prec_gt_0 p -> ...].       *)
Local Notation error_le_half_ulp_RN :=
  (@error_le_half_ulp_round beta (FLT_exp emin p)
     (FLT_exp_valid emin p) (FLT_exp_monotone emin p) choice).
(* Flocq's [TwoSum_correct] with this section's parameters and hypotheses     *)
(* pre-applied: [TwoSum_correct_RN x y : format x -> format y -> ...].        *)
Local Notation TwoSum_correct_RN :=
  (@TwoSum_correct emin p choice Hp2 emin_le_0 choice_sym).

(* [TwoSum] and its lemmas now live in [TwoSum.v], generic over [p]/[emin];   *)
(* re-hide this format's [p], [emin], [choice] (and the [Hp2]/[emin_le_0]/    *)
(* [choice_sym] proofs) so the names read exactly as before.                  *)
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

(* ===========================================================================*)
(*  Algorithm 4: VecSum                                                       *)
(*  On [x0; ...; x_{n-1}] returns [e0; ...; e_{n-1}] with the same            *)
(*  exact sum, processing from the least significant term.                    *)
(* ===========================================================================*)
Fixpoint vecSumAux (l : seq R) : seq R * R :=
  match l with
  | [::]    => ([::], 0)
  | [:: x]  => ([::], x)
  | x :: l' => let: (es, s) := vecSumAux l' in
               let: DWR si ei1 := TwoSum x s in
               (ei1 :: es, si)
  end.

Definition vecSum (l : seq R) : seq R :=
  let: (es, s0) := vecSumAux l in s0 :: es.

Lemma format_vecSum l :
  {in l, forall z, format z} -> {in vecSum l, forall z, format z}.
Proof.
move=> Hl /= z.
suff Hf ll a : vecSumAux l = (ll, a) -> 
                {in ll, forall z, format z}  /\ format a.
  case E : (vecSumAux l) => [ll a].
  have [llF aF] := Hf _ _ E.
  by rewrite /vecSum E inE => /orP[/eqP->|zIll] //; apply: llF.
elim: l ll a Hl => /= [ll a _ [<- <-]| b [| c l] IH ll a blF].
- split; first by move=> ?; rewrite in_nil.
  by apply: generic_format_0.
- case => <- <-; split; first by move=> ?; rewrite in_nil.
  by apply: blF; rewrite inE eqxx.
case E1 : (vecSumAux (c :: l)) => [ll1 d].
case => <- <-; split; last by apply: generic_format_round.
move=> z1; rewrite inE => /orP[/eqP->|z1Ill1].
  by apply: generic_format_round.
have cF : format c by apply: blF; rewrite !inE eqxx orbT.
case: (IH ll1 d) => // [z2 z2Icl|].
  by apply: blF; rewrite inE z2Icl orbT.
by move=> ll1F dF; apply: ll1F.
Qed.

Lemma vecSumAux_cons a b l :
  vecSumAux [::a, b & l] =
  let '(es, s) := vecSumAux (b :: l) in 
  let 'DWR si ei1 := TwoSum a s in (ei1 :: es, si).
Proof. by []. Qed.

Lemma size_vecSumAux l : size (vecSumAux l).1 = (size l).-1.
Proof.
elim: l => // a [//| b l].
rewrite vecSumAux_cons.
case : vecSumAux => c l1.
by case TwoSum => a3 b3 /= ->.
Qed.

Lemma size_vecSum l : size (vecSum l) = (size l).-1.+1.
Proof.
case: l => //= a l.
rewrite /vecSum.
by case: vecSumAux (size_vecSumAux (a :: l)) => ? ? /= ->.
Qed.

(* ===========================================================================*)
(*  Algorithm 5: VecSumErrBranch (VSEB)                                       *)
(*  Returns the full normalised output; zero error terms are dropped.         *)
(* ===========================================================================*)
Fixpoint vsebAux (eps : R) (l : seq R) : seq R :=
  match l with
  | [::]       => [:: eps]
  | [:: elast] => let: DWR y0 y1 := TwoSum eps elast in [:: y0; y1]
  | e :: l'    => let: DWR r et := TwoSum eps e in
                  if Req_EM_T et 0 then vsebAux r l'
                  else r :: vsebAux et l'
  end.

Lemma format_vsebAux e l :
  format e -> {in l, forall z, format z} -> 
   {in vsebAux e l, forall z, format z}.
Proof.
move=> eF lF /= z.
elim: l z e eF lF => /= [z e eF lF|a [| b l] IH z e eF lF].
- by rewrite !inE => /eqP->.
- by rewrite !inE => /orP[/eqP->|/eqP->]; apply: generic_format_round.
case: Req_EM_T => HH.
  apply: IH; first by apply: generic_format_round.
  by move=> z1 z1Ibl; apply: lF; rewrite inE z1Ibl orbT.
rewrite inE => /orP[/eqP->|]; first by apply: generic_format_round.
apply: IH; first by apply: generic_format_round.
by move=> z1 z1Ibl; apply: lF; rewrite inE z1Ibl orbT.
Qed.

Definition vseb (l : seq R) : seq R :=
  if l is e0 :: l' then vsebAux e0 l' else [::].

Lemma format_vseb l :
  {in l, forall z, format z} -> {in vseb l, forall z, format z}.
Proof.
case: l => //= a l alF; apply: format_vsebAux => [|z zIl].
  by apply: alF; rewrite inE eqxx.
by apply: alF; rewrite inE zIl orbT.
Qed.

(* VSEB(k): keep only the first k terms (the dropped tail is the error).      *)
Definition vsebK (k : nat) (l : seq R) : seq R := take k (vseb l).

Lemma format_vsebK k l :
  {in l, forall z, format z} -> {in vsebK k l, forall z, format z}.
Proof.
move=> lF /= z /mem_take zIl.
by apply: format_vseb lF _ zIl.
Qed.

(* ===========================================================================*)
(*  Merge two magnitude-sorted sequences into a magnitude-sorted one.         *)
(* ===========================================================================*)

Fixpoint Merge (l1 : seq R) : seq R -> seq R :=
  fix Merge_aux (l2 : seq R) : seq R :=
    match l1, l2 with
    | [::], _ => l2
    | _, [::] => l1
    | a1 :: l1', a2 :: l2' =>
        if Rle_bool (Rabs a2) (Rabs a1)
        then a1 :: Merge l1' l2
        else a2 :: Merge_aux l2'
    end.

Lemma format_Merge l1 l2 :
  {in l1, forall z, format z} -> {in l2, forall z, format z} -> 
  {in Merge l1 l2, forall z, format z}.
Proof.
elim: l1 l2 => /= [|a l1 IH l2 al1F]; first by elim.
have aF : format a by apply: al1F; rewrite !inE eqxx.
set u := (X in _ -> {in X l2, _}).
elim: l2 IH => /= [IH _ z| b l2 IH1 IH2 bl2F].
  rewrite inE => /orP[/eqP->|zIl1] //.
  by apply: al1F; rewrite inE zIl1 orbT.
case: Rle_bool => z; rewrite inE => /orP[/eqP->|zIl] //.
- apply: (IH2 (b :: l2)) => // z1 z1Il1.
  by apply: al1F; rewrite inE z1Il1 orbT.
- by apply: bl2F; rewrite inE eqxx.
apply: IH1 => // z1 z1Il2.
by apply: bl2F; rewrite inE z1Il2 orbT.
Qed.

Lemma size_Merge l1 l2 : size (Merge l1 l2) = (size l1 + size l2)%N.
Proof.
elim: l1 l2 => /= [|a1 l1 IH1]; first by elim.
elim => [/=|a2 l2 IH2]; first by rewrite addn0.
case: Rle_bool => /=; first by rewrite IH1.
by rewrite IH2 addnS.
Qed.

(* ===========================================================================*)
(*  Triple-word numbers                                                       *)
(* ===========================================================================*)
Inductive twR := TWR (x0 x1 x2 : R).

(* Named projectors for the triple-word record [twR], mirroring [dwh]/[dwl].  *)
Definition tw0 (t : twR) : R := let: TWR x0 _ _ := t in x0.
Definition tw1 (t : twR) : R := let: TWR _ x1 _ := t in x1.
Definition tw2 (t : twR) : R := let: TWR _ _ x2 := t in x2.

Lemma tw0E x0 x1 x2 : tw0 (TWR x0 x1 x2) = x0. Proof. by []. Qed.
Lemma tw1E x0 x1 x2 : tw1 (TWR x0 x1 x2) = x1. Proof. by []. Qed.
Lemma tw2E x0 x1 x2 : tw2 (TWR x0 x1 x2) = x2. Proof. by []. Qed.

Definition TWval (x : twR) : R := let: TWR x0 x1 x2 := x in x0 + x1 + x2.

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

(* Definition 5: a triple-word number is a P-nonoverlapping triplet           *)
(* of floating-point numbers.                                                 *)
Definition isTW (x : twR) : Prop :=
  let: TWR x0 x1 x2 := x in
  [/\ format x0, format x1, format x2, Rabs x1 < ulp x0 & Rabs x2 < ulp x1].

(* ===========================================================================*)
(*  From P-nonoverlap to magnitude order, with the zero case.                 *)
(*                                                                            *)
(*  [isTW] is P-nonoverlapping (Def. 1/5): the separation is the *strict*     *)
(*  [Rabs x_{i+1} < ulp x_i].  To feed [Merge] (which orders by [Rabs]) we    *)
(*  need the magnitude order [Rabs x_{i+1} <= Rabs x_i].  The usual argument  *)
(*  [ulp x_i <= Rabs x_i] breaks at x_i = 0, since in FLT                     *)
(*    ulp 0 = bpow emin > 0 = Rabs 0      (Flocq: [ulp_FLT_0]).               *)
(*  But that very value is what forces a zero limb to be *trailing*: a        *)
(*  nonzero float has [bpow emin <= Rabs y], so [Rabs y < ulp 0] gives y = 0. *)
(* ===========================================================================*)


(* A format number strictly below the smallest positive float is 0.           *)
(* Depends on (all from Flocq.Core, already imported via [Core]):             *)
(*   - [ulp_FLT_0]    : ulp 0 = bpow emin   (Flocq.Core.FLT)                  *)
(*   - [ulp_ge_ulp_0] : Exp_not_FTZ fexp -> ulp 0 <= ulp y   (Flocq.Core.Ulp) *)
(*   - [ulp_le_abs]   : y <> 0 -> format y -> ulp y <= Rabs y (Flocq.Core.Ulp)*)
(*   the [Exp_not_FTZ (FLT_exp emin p)] instance comes from                   *)
(*   [FLT_exp_monotone] + [monotone_exp_not_FTZ].                             *)
Lemma format_lt_ulp_0 y : format y -> Rabs y < ulp 0 -> y = 0.
Proof.
move=> yF yLu.
suff : ~ (0 < Rabs y) by split_Rabs; lra.
move=> ay_gt0.
have ayF : format (Rabs y) by apply: generic_format_abs.
have pLw : pow emin <= Rabs y by apply: alpha_LB ayF _.
rewrite ulp_FLT_0 in yLu; lra.
Qed.

(* P-nonoverlap separation implies magnitude order, zeros included.           *)
(* Depends on:                                                                *)
(*   - [ulp_le_abs] : x <> 0 -> format x -> ulp x <= Rabs x  (Flocq.Core.Ulp) *)
(*     for the x <> 0 case (then Rabs y < ulp x <= Rabs x);                   *)
(*   - [ulp_FLT_0] + [format_lt_ulp_0] above for the x = 0 case (then y = 0). *)
Lemma format_lt_ulp_le x y :
  format x -> format y -> Rabs y < ulp x -> Rabs y <= Rabs x.
Proof.
move=> xF yF yLux.
have [x_eq0|x_neq0 ]:= Req_dec x 0; last first.
  apply: Rle_trans (Rlt_le _ _ yLux) _.
  by apply: ulp_le_abs.
have -> : y = 0 by apply: format_lt_ulp_0 => //; rewrite -x_eq0.
split_Rabs; lra.
Qed.

(* P-nonoverlap implies pairwise-ulp separation on a single (format) list,    *)
(* zeros included: |x_{i+2}| < ulp x_{i+1} <= ulp x_i, the last step via      *)
(* [ulp_le_abs] (and [format_lt_ulp_0] when x_{i+1} = 0).                     *)
Lemma Pnonoverlap_imp_pairwise_ul l :
  {in l,  forall z : R, format z} -> Pnonoverlap l -> pairwise_ulp l.
Proof.
elim: l => //= a [|b [|c l]] // IH abclF abclP.
apply: pairwise_ulp_cons_inv.
  have /= bLua := abclP 0%N isT.
  apply: Rle_lt_trans bLua.
  have /= := abclP 1%N isT.
  have [->/format_lt_ulp_0->//|y_neq0 cLub] := Req_dec b 0; try lra.
    by apply: abclF; rewrite !inE eqxx !orbT.
  apply: Rle_trans (Rlt_le _ _ cLub) _.
  apply: ulp_le_abs => //.
  by apply: abclF; rewrite !inE eqxx !orbT.
apply: IH.
  by move=> z zIl; apply: abclF; rewrite inE zIl orbT.
by move=> i iLs; apply: (abclP i.+1).
Qed.

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

(* ===========================================================================*)
(*  Merge lemmas (beyond [format_Merge] above): a common magnitude bound, and *)
(*  the two preconditions of Theorem 6 -- magnitude order and pairwise ulp.   *)
(* ===========================================================================*)

(* Merge propagates a common upper bound on the elements: if every element of *)
(* [l1] and of [l2] is below [a], so is every element of the merge.  This is  *)
(* the key tool for [pairwise_ulp] of the merge -- once the global maximum    *)
(* (the larger head) is removed, all remaining elements are below ulp of the  *)
(* head, hence so is the element two positions on.                            *)
Lemma Merge_head_lt l1 l2 a :
  {in l1, forall z, Rabs z < a} -> {in l2, forall z, Rabs z < a} ->
  {in Merge l1 l2, forall z, Rabs z < a}.
Proof.
elim: l1 l2 a => /= [|a1 l1 IH1]; first by elim.
elim => // a2 l2 IH2 a a1l1S a2l2S.
case: Rle_bool_spec => [a2La1|a1La2] x.
  rewrite inE => /orP[/eqP->|]; first by apply: a1l1S; rewrite !inE eqxx.
  by apply: IH1 => [z zIl1|//]; apply: a1l1S; rewrite !inE zIl1 orbT.
rewrite inE => /orP[/eqP->|]; first by apply: a2l2S; rewrite !inE eqxx.
apply: IH2 => // z zIl2.
by apply: a2l2S; rewrite !inE zIl2 orbT.
Qed.

(* Merge under a common dominating head [a]: if [a] tops both lists, it still *)
(* tops the merge, and the merge stays magnitude-sorted.  (Helper for         *)
(* [Merge_sorted_mag].)                                                       *)
Lemma Merge_asorted_mag a l1 l2 :
  sorted_mag (a :: l1) -> sorted_mag (a :: l2) -> sorted_mag (a :: Merge l1 l2).
Proof.
elim: l1 l2 a => /= [|a1 l1 IH1]; first by elim.
elim => // a2 l2 IH2 a a1l1S a2l2S.
case: Rle_bool_spec => [a2La1|a1La2].
  apply: sorted_mag_cons_inv.
    by case: (sorted_mag_cons a1l1S).
  apply: IH1; first by case: (sorted_mag_cons a1l1S).
  apply: sorted_mag_cons_inv => //.
  by case: (sorted_mag_cons a2l2S).
apply: sorted_mag_cons_inv => //.
  by case: (sorted_mag_cons a2l2S).
apply: IH2.
  apply: sorted_mag_cons_inv; first by apply: Rlt_le.
  by case: (sorted_mag_cons a1l1S).
by case: (sorted_mag_cons a2l2S).
Qed.

(* [Merge] picks the larger-magnitude head at each step, so it turns two      *)
(* magnitude-sorted sequences into a magnitude-sorted one.  Combined with     *)
(* [isTW_sorted_mag] on each input triple, this discharges [Hz_sorted] in     *)
(* [TWSum_isTW].                                                              *)
Lemma Merge_sorted_mag l1 l2 :
  sorted_mag l1 -> sorted_mag l2 -> sorted_mag (Merge l1 l2).
Proof.
elim: l1 l2 => /= [|a l1 IH1]; first by elim.
elim => // b l2 IH2 al1S bl2S.
case: Rle_bool_spec => [bLa|aLb].
  apply: Merge_asorted_mag => //.
  by apply: sorted_mag_cons_inv.
move : bl2S.
have: sorted_mag (b :: l1).
  case: (l1) al1S => // a3 l3 H.
  case: (sorted_mag_cons H) => H1 H2.
  by apply: sorted_mag_cons_inv => //; lra.
elim: (l2) (b) aLb => 
    /= [b1 aLb1 b1l1S _|b3 l3 IH3 b4 aLb4 b4l1S /sorted_mag_cons[b4Lb3 b3l3S]].
  by apply: sorted_mag_cons_inv => //; lra.
case: Rle_bool_spec => [b3La|aLb3].
  apply: sorted_mag_cons_inv; first by lra.
  apply: Merge_asorted_mag => //.
  by apply: sorted_mag_cons_inv.
apply: sorted_mag_cons_inv => //.
apply: IH3 => //.
by apply: sorted_mag_le al1S _; lra.
Qed.

(* The main Merge result for Theorem 6: merging two P-nonoverlapping (format) *)
(* lists yields a [pairwise_ulp] sequence.  The merge's own magnitude tests   *)
(* supply the ordering, so no [sorted_mag] hypothesis is needed -- among any  *)
(* three consecutive outputs, two come from the same input list and are       *)
(* consecutive there, giving the [Pnonoverlap] step; the mixed cases use the  *)
(* merge's comparison plus ulp monotonicity ([ulp_le]).                       *)
Lemma Merge_pairwise_ulp (l1 l2 : seq R) :
  {in l1, forall z, format z} ->   {in l2, forall z, format z} ->
  Pnonoverlap l1 -> Pnonoverlap l2 -> pairwise_ulp (Merge l1 l2).
Proof.
elim: l1 l2 => /= [|a l1 IH1].
  elim => // b [|c [|d l2]] IH _ bl2F _ bl2P //.
  apply: pairwise_ulp_cons_inv.
    have /= cLub := bl2P 0%N isT.
    apply: Rle_lt_trans cLub.
    have /= := bl2P 1%N isT.
    have [->/format_lt_ulp_0->//|y_neq0 dLuc] := Req_dec c 0; try lra.
      by apply: bl2F; rewrite !inE eqxx !orbT.
    apply: Rle_trans (Rlt_le _ _ dLuc) _.
    apply: ulp_le_abs => //.
    by apply: bl2F; rewrite !inE eqxx !orbT.
  apply: IH => //.
    by move=> z zIl; apply: bl2F; rewrite inE zIl orbT.
  by apply: Pnonoverlap_cons bl2P.
elim => [al1F _ al1P _|b l2 IH2 al1F bl2F al1P bl2P].
  by apply: Pnonoverlap_imp_pairwise_ul.
case: Rle_bool_spec => [bLa|aLb].
  apply: pairwise_ulp_cons1_inv.
    apply: IH1 => //.
      by move=> z zIl; apply: al1F; rewrite inE zIl orbT.
    by apply: Pnonoverlap_cons al1P.
  case: (l1) al1P al1F => //.
    case: (l2) bl2P bl2F => //= c l3 /(_ 0%N isT) /= cLub _ _ _ _.
    apply: Rlt_le_trans cLub _.
    by apply: (ulp_le beta fexp _ _ bLa).
  move=> a1 l3.
  rewrite /=; case: Rle_bool_spec => /=.
    case: l3 => //=.
      move=> bLa1 /(_ 0%N isT) /= a1Lua _ _.
      by apply: Rle_lt_trans bLa1 a1Lua.
    move=> a2 l3 bLa1 aa1a2l3P aa1a2l3F _.
    case: Rle_bool_spec => [bLa2|a2Lb] /=.
      have /(_ 0%N isT)/= a1Lua :=  aa1a2l3P.
      apply: Rle_lt_trans (a1Lua).
      have /(_ 1%N isT)/= a2Lua1 :=  aa1a2l3P.
      move: a2Lua1.
      have [->/format_lt_ulp_0->|a1_neq0 a2Lua1] := Req_dec a1 0; try lra.
        by apply: aa1a2l3F; rewrite !inE eqxx !orbT.
      apply: Rle_trans (Rlt_le _ _ a2Lua1) _.
      apply: ulp_le_abs => //.
      by apply: aa1a2l3F; rewrite !inE eqxx !orbT.
    have /(_ 0%N isT)/= a1Lua :=  aa1a2l3P.
    by apply: Rle_lt_trans (a1Lua).
  move=> a1Lb aa1l3P aa1l3F.
  case: (l2) bl2F bl2P => /= [_ _ _|b1 l4 bb1F bb1P _] /=.
    by apply: (aa1l3P 0%N).
  case: Rle_bool_spec => [b1La1|a1Lb1] /=.
    by apply: (aa1l3P 0%N).
  have /(_ 0%N isT)/= b1Lub :=  bb1P.
  apply: Rlt_le_trans b1Lub _.
  by apply: (ulp_le beta fexp _ _ bLa).
apply: pairwise_ulp_cons1_inv.
  apply: IH2 => //.
    by move=> z zIl; apply: bl2F; rewrite inE zIl orbT.
  by apply: Pnonoverlap_cons bl2P.
case: (l2) bl2F bl2P al1F al1P => /=.
  case: (l1) => // a1 l3 bF bP aa1l3F aa1l3P /= _.
  have /(_ 0%N isT)/= a1Lua :=  aa1l3P.
  apply: Rlt_le_trans a1Lua _.
  by apply: (ulp_le beta fexp _ _ (Rlt_le _ _ aLb)).
move=> b1 l3.
case: Rle_bool_spec => [b1La|aLb1] /=.
  case: (l1) => //= [_ /(_ 0%N isT) //|a1 l4].
  case: Rle_bool_spec => [b1La1|a1Lb1]//=.  
    move=> bb1l3F bb1l3P aa1l4F aa1l4P _.
    have /(_ 0%N isT)/= a1Lua :=  aa1l4P.
    apply: Rlt_le_trans a1Lua _.
    by apply: (ulp_le beta fexp _ _ (Rlt_le _ _ aLb)).
  case: l3 => /= [bb1F bb1P aa1l4F aa1l4P _|
                  b2 l3 bb1b2l3F bb1b2l3P aa1l4F aa1l4P _].
    by apply: (bb1P 0%N).
  by apply: (bb1b2l3P 0%N).
case: l3 => /= [bb1F bb1P al1F al1P _|b2 l3 bb1b2l3F bb1b2l3P al1F al1P _].
  apply: Rlt_trans aLb1 _.
  by apply: (bb1P 0%N).
case: Rle_bool_spec => [b2La|aLb2]//=.
  apply: Rlt_trans aLb1 _.
  by apply: (bb1b2l3P 0%N).
have /(_ 1%N isT)/= b2Lub1 := bb1b2l3P.
  apply: Rlt_le_trans b2Lub1 _.
apply: (ulp_le beta fexp).
apply: Rlt_le.
have /(_ 0%N isT)/= b1Lub := bb1b2l3P.
apply: Rlt_le_trans b1Lub _.
apply: ulp_le_abs.
  move=> b_eq0; move: aLb; rewrite b_eq0; split_Rabs; lra.
by apply: bb1b2l3F; rewrite !inE eqxx.
Qed.

(* Merge is a permutation of its two inputs, so it preserves the exact sum.   *)
Lemma Merge_sumR (l1 l2 : seq R) : sumR (Merge l1 l2) = sumR l1 + sumR l2.
 Proof.
elim: l1 l2 => /= [|a l1 IH1]; first by elim => [/=| b l2] //; lra.
elim =>  [/=|b l2 IH2]; first by lra.
case: Rle_bool_spec => [bLa|aLb].
  by rewrite /= IH1 /=; lra.
by rewrite /= IH2; lra.
Qed.


Lemma format_vecSumAux l : 
  {in l, forall z, format z} ->
  format (vecSumAux l).2 /\ {in (vecSumAux l).1, forall z, format z}.
Proof.
elim: l => [_|a [|b l] // IH ablF]; split => //.
- by apply: generic_format_0.
- by apply: ablF; rewrite inE eqxx.
- rewrite vecSumAux_cons.
  have /IH[] :  {in b :: l,  forall z : R, format z}.
    by move=> z zIl; apply: ablF; rewrite inE zIl orbT.
  case E : vecSumAux => [es s].
  case E1 : (TwoSum a s) => [si ei1] => sF esF.
  have Fa : format a by apply: ablF; rewrite inE eqxx.
  have [Hsi Hei1] : format (dwh (TwoSum a s)) /\ format (dwl (TwoSum a s))
    by exact: format_TwoSum Fa sF.
  rewrite E1 /= in Hsi Hei1.
  by first [exact: Hsi | exact: Hei1].
have /IH[] :  {in b :: l,  forall z : R, format z}.
  by move=> z zIl; apply: ablF; rewrite inE zIl orbT.
  rewrite vecSumAux_cons.
case E : vecSumAux => [es s].
case E1 : (TwoSum a s) => [si ei1] => sF esF.
move=> z; rewrite inE => /orP[/eqP->|zIes].
  have Fa : format a by apply: ablF; rewrite inE eqxx.
  have [Hsi Hei1] : format (dwh (TwoSum a s)) /\ format (dwl (TwoSum a s))
    by exact: format_TwoSum Fa sF.
  rewrite E1 /= in Hsi Hei1.
  by first [exact: Hsi | exact: Hei1].
by apply: esF.
Qed.

Lemma vecSum_sum l : 
  {in l, forall z, format z} -> sumR (vecSum l) = sumR l.
Proof.
rewrite /vecSum; elim: l => [|a [|b l] // IH ablF]; first by rewrite /=; lra.
rewrite vecSumAux_cons.
have : sumR (let '(es, s0) := vecSumAux (b :: l) in s0 :: es) = sumR (b :: l).
  by apply: IH => z zIl; apply: ablF; rewrite inE zIl orbT.
case E : vecSumAux => [es s] ssE; rewrite /= in ssE.
case E1 : (TwoSum a s) => [si ei1] /=.
have Fa : format a by apply: ablF; rewrite inE eqxx.
have Fs : format s.
  have [Hs _] :
      format (vecSumAux (b :: l)).2 /\
      {in (vecSumAux (b :: l)).1, forall z, format z}.
    by apply: format_vecSumAux => z zIl; apply: ablF; rewrite inE zIl !orbT.
  by move: Hs; rewrite E.
have Hc : dwh (TwoSum a s) + dwl (TwoSum a s) = a + s
  by exact: TwoSum_correct_loc Fa Fs.
rewrite E1 /= in Hc.
lra.
Qed.

(* Divisibility propagation -- the induction step of paper Thm 1 ("if         *)
(* 2^k | s_i, x_{i-1}, ..., x_0 then 2^k | e_i, ..., e_0").  If every input   *)
(* lies on the grid [pow e], so does the running high word and every error:   *)
(* [2Sum] preserves it, the rounded sum via [is_imul_pow_round] and the exact *)
(* error via [is_imul_minus].  [format] is only used for the error identity.  *)
Lemma vecSumAux_imul e l :
  {in l, forall z, format z} -> {in l, forall z, is_imul z (pow e)} ->
  is_imul (vecSumAux l).2 (pow e) /\
  {in (vecSumAux l).1, forall z, is_imul z (pow e)}.
Proof.
elim: l => [_ _|a [|b l] // IH ablF ablM]; split => //.
- by exists 0%Z; rewrite Rmult_0_l.
- by apply: ablM; rewrite inE eqxx.
- rewrite vecSumAux_cons.
  have Ma : is_imul a (pow e) by apply: ablM; rewrite inE eqxx.
  have [sM _] : is_imul (vecSumAux (b :: l)).2 (pow e) /\
                {in (vecSumAux (b :: l)).1, forall z, is_imul z (pow e)}.
    apply: IH.
      by move=> z zIl; apply: ablF; rewrite inE zIl orbT.
    by move=> z zIl; apply: ablM; rewrite inE zIl orbT.
  move: sM; case E : vecSumAux => [es s] sM.
  case E1 : (TwoSum a s) => [si ei1] /=.
  have := TwoSum_hi a s; rewrite E1 /= => ->.
  by apply: is_imul_pow_round; apply: is_imul_add.
rewrite vecSumAux_cons.
have Ma : is_imul a (pow e) by apply: ablM; rewrite inE eqxx.
have Fa : format a by apply: ablF; rewrite inE eqxx.
have [sM esM] : is_imul (vecSumAux (b :: l)).2 (pow e) /\
                {in (vecSumAux (b :: l)).1, forall z, is_imul z (pow e)}.
  apply: IH.
    by move=> z zIl; apply: ablF; rewrite inE zIl orbT.
  by move=> z zIl; apply: ablM; rewrite inE zIl orbT.
have [Fs _] : format (vecSumAux (b :: l)).2 /\
              {in (vecSumAux (b :: l)).1, forall z, format z}.
  apply: format_vecSumAux.
  by move=> z zIl; apply: ablF; rewrite inE zIl orbT.
move: sM esM Fs; case E : vecSumAux => [es s] sM esM Fs.
case E1 : (TwoSum a s) => [si ei1] /=.
move=> z; rewrite inE => /orP[/eqP->|zIes]; last by apply: esM.
have Hsi : si = RND (a + s) by have := TwoSum_hi a s; rewrite E1.
have Hc : si + ei1 = a + s.
  have Hcc : dwh (TwoSum a s) + dwl (TwoSum a s) = a + s
    by exact: TwoSum_correct_loc Fa Fs.
  by move: Hcc; rewrite E1 /= => ->.
have -> : ei1 = (a + s) - si by lra.
apply: is_imul_minus; first by apply: is_imul_add.
by rewrite Hsi; apply: is_imul_pow_round; apply: is_imul_add.
Qed.

(* Two definitional unfoldings of [vsebAux] (by reflexivity), mirroring       *)
(* [vecSumAux_cons]: they expose [TwoSum eps e] so the following [case] can   *)
(* capture it in the goal, keeping the low words as the very variables that   *)
(* [TwoSum_correct_loc] talks about (otherwise [simpl] re-expands them to     *)
(* [RND ...] and the correctness fact no longer applies).                     *)
Lemma vsebAux_1 eps e :
  vsebAux eps [:: e] = let: DWR y0 y1 := TwoSum eps e in [:: y0; y1].
Proof. by []. Qed.

Lemma vsebAux_consS eps e e2 l :
  vsebAux eps [:: e, e2 & l] =
  let: DWR r et := TwoSum eps e in
  if Req_EM_T et 0 then vsebAux r (e2 :: l) else r :: vsebAux et (e2 :: l).
Proof. by []. Qed.

(* VSEB is error-free: [vsebAux] preserves the exact sum, prefix [eps]        *)
(* included.  Each step is a [TwoSum] (exact by [TwoSum_correct_loc]); whether*)
(* the error [et] is dropped ([et = 0], so [r = eps + e]) or emitted, the sum *)
(* [eps + sumR l] is preserved.                                               *)
Lemma vsebAux_sum eps l :
  format eps -> {in l, forall z, format z} ->
  sumR (vsebAux eps l) = eps + sumR l.
Proof.
elim: l eps => [|e l IH] eps epsF lF.
  by rewrite /=; lra.
have eF : format e by apply: lF; rewrite inE eqxx.
case: l IH lF => [|e2 l'] IH lF.
  rewrite vsebAux_1; case E1 : (TwoSum eps e) => [y0 y1].
  have Cc : dwh (TwoSum eps e) + dwl (TwoSum eps e) = eps + e
    by exact: TwoSum_correct_loc epsF eF.
  rewrite E1 /= in Cc.
  by rewrite /=; lra.
rewrite vsebAux_consS; case E1 : (TwoSum eps e) => [r et].
have Cc : dwh (TwoSum eps e) + dwl (TwoSum eps e) = eps + e
  by exact: TwoSum_correct_loc epsF eF.
have [rF etF] : format (dwh (TwoSum eps e)) /\ format (dwl (TwoSum eps e))
  by exact: format_TwoSum epsF eF.
rewrite E1 /= in Cc rF etF.
have l'F : {in e2 :: l', forall z, format z}.
  by move=> z zIl; apply: lF; rewrite inE zIl orbT.
case: Req_EM_T => [et0|etn0].
  by rewrite (IH r rF l'F) /=; lra.
by rewrite /= (IH et etF l'F) /=; lra.
Qed.

(* VSEB preserves the exact sum (Theorem 2, sum part): [sumR(vseb l)=sumR l]. *)
Lemma vseb_sum l :
  {in l, forall z, format z} -> sumR (vseb l) = sumR l.
Proof.
case: l => [_|e0 l' e0l'F]; first by rewrite /vseb.
have e0F : format e0 by apply: e0l'F; rewrite inE eqxx.
have l'F : {in l', forall z, format z}.
  by move=> z zIl; apply: e0l'F; rewrite inE zIl orbT.
by rewrite /vseb /= (vsebAux_sum e0F l'F) /=.
Qed.

(* ===========================================================================*)
(*  Normalisation: VecSum then VSEB (paper Theorems 1 and 2)                  *)
(*                                                                            *)
(*  This is the machinery behind the [Hr_nonover] step of [TWSum_isTW]: it    *)
(*  turns the merged six-term sequence into a P-nonoverlapping triple.  The   *)
(*  chain is  VecSum (Thm 1) -> VSEB (Thm 2) -> take the first 3 terms.       *)
(* ===========================================================================*)





(* [ufp x] -- "unit in the first place": the weight [2^(mag x - 1)] of the    *)
(* leftmost bit, i.e. the largest power of two <= |x| (for x <> 0).  Paper    *)
(* Theorem 1 / Corollary 1 (p.3) state the VecSum input conditions with it.   *)
Definition ufp (x : R) : R := pow (mag beta x - 1).

Lemma ufp_gt_0 x : 0 < ufp x.
Proof. by apply: bpow_gt_0. Qed.

(* [ufp x <= |x| < 2 * ufp x]: |x| lies in one binade above [ufp x].          *)
Lemma ufp_le_abs x : x <> 0 -> ufp x <= Rabs x.
Proof. exact: bpow_mag_le. Qed.

Lemma abs_lt_2ufp x : Rabs x < 2 * ufp x.
Proof.
rewrite /ufp; set m := mag beta x.
have := bpow_mag_gt beta x; rewrite -/m => H.
suff -> : (2 * bpow beta (m - 1) = bpow beta m)%R by [].
have -> : (2 = IZR beta)%R by rewrite /=; lra.
by rewrite -bpow_plus_1; congr bpow; lia.
Qed.

(* One P-nonoverlap step makes [ufp] shrink by a factor [u]: if [|y| < ulp x] *)
(* (Priest's [Pnonoverlap]) and [x] is not near underflow, then               *)
(* [ufp y <= u * ufp x].  This is the geometric decay behind Theorem 3's tail *)
(* bound [2 u^3 + 4.2 u^4] (each kept term is [u] times finer than the last). *)
Lemma ufp_ulp_step x y : x <> 0 -> y <> 0 -> Rabs y < ulp x ->
  (emin <= mag beta x - p)%Z -> ufp y <= u * ufp x.
Proof.
move=> xn0 yn0 Hxy Hx1.
have Hmagy : (mag beta y <= mag beta x - p)%Z.
  apply: mag_le_bpow => //.
  apply: Rlt_le_trans Hxy _.
  rewrite ulp_neq_0 //.
  by rewrite /cexp /FLT_exp; apply: bpow_le; lia.
by rewrite /ufp uE -bpow_plus; apply: bpow_le; lia.
Qed.

(* Definition 2 (Fabiano): [l] is F-nonoverlapping when each term is at most  *)
(* half the [uls] of its predecessor.  This is Fabiano's separation (more     *)
(* restrictive than Shewchuk's ulp-nonoverlapping); it is the invariant that  *)
(* VecSum establishes (Thm 1) and that VSEB consumes (Thm 2) to yield a       *)
(* P-nonoverlapping output.                                                   *)
(* This is the "with interleaving zeros" form (paper Def. 3): the bound is    *)
(* required only across a NONZERO predecessor [nth 0 l i <> 0], so a zero     *)
(* error term (e.g. an exact [2Sum]) imposes no constraint on its successor.  *)
(* Without this guard the statement is false: at a zero predecessor the RHS   *)
(* would be [/2 * uls 0 = 2^(emin-1)], unreachable by a normal-sized term.    *)
Definition Fnonoverlap (l : seq R) : Prop :=
  forall i, (i.+1 < size l)%N -> nth 0 l i <> 0 ->
    Rabs (nth 0 l i.+1) <= / 2 * uls (nth 0 l i).

(* A prefix of a P-nonoverlapping sequence is P-nonoverlapping.  Since        *)
(* [vsebK k = take k \o vseb], this is what turns "VSEB is P-nonoverlapping"  *)
(* into "VSEB(k) is P-nonoverlapping".                                        *)
(* Proof: [take k] leaves the [nth]s at indices < k unchanged and only        *)
(* shortens the list, so every instance of the [Pnonoverlap] condition on     *)
(* [take k l] is an instance already available on [l].                        *)
Lemma Pnonoverlap_take k l : Pnonoverlap l -> Pnonoverlap (take k l).
Proof.
elim: l k => //= a [| b l] IH [|[|k]] //=.
move=> ablP [|i] /= iLs; first by apply: (ablP 0%N).
apply: (IH k.+1 _ i) => // z zLs.
by apply: (ablP z.+1).
Qed.

(* ===========================================================================*)
(*  Theorem 1 (VecSum), faithful to paper3 Section 2.1                        *)
(*                                                                            *)
(*  The current [vecSum_Fnonoverlap] below uses the simplified inputs         *)
(*  [sorted_mag]+[pairwise_ulp]; this block states Theorem 1 with the paper's *)
(*  actual [k_i] exponent hypotheses, and the proof steps it goes through.    *)
(* ===========================================================================*)

(* Paper representation: [x = M * 2^(k-p+1)] with [|M| < 2^p], [M] an integer *)
(* and the exponent [k] chosen (not necessarily canonical).  We also require  *)
(* [emin <= k - p + 1] so that [x] genuinely lands on the FLT grid -- without *)
(* it [x = 2^(emin-1)] (M = 1, k = emin+p-2) satisfies the equation but is not*)
(* a float.  The paper's x_i are floats, so this is the intended reading.     *)
Definition repr (k : Z) (x : R) : Prop :=
  (emin <= k - p + 1)%Z /\
  exists2 M : Z, (Z.abs M < 2 ^ p)%Z & x = IZR M * pow (k - p + 1)%Z.

(* Being [repr]-esentable at [k] makes [x] an FLT float: it is [F2R] of the   *)
(* integer float [Float M (k-p+1)], whose mantissa is < 2^p and whose exponent*)
(* is >= emin.                                                                *)
Lemma repr_format k x : repr k x -> format x.
Proof.
move=> [Hemin [M Mlt ->]].
apply: generic_format_FLT; exists (Float beta M (k - p + 1)%Z).
- by rewrite /F2R.
- exact: Mlt.
exact: Hemin.
Qed.

(* Hypotheses of Theorem 1 on inputs [l] with a chosen exponent map [k]:      *)
(*  - every [x_i] is representable at exponent [k_i];                         *)
(*  - [k_{i-1} >= k_i + 1] for every pair but the last (strict exponent gap); *)
(*  - [k_{n-2} >= k_{n-1}] for the last pair (weak gap: allowed overlap).     *)
Definition Thm1_hyp (k : nat -> Z) (l : seq R) : Prop :=
  [/\ forall i, (i < size l)%N -> repr (k i) (nth 0 l i),
      forall i, (i.+2 < size l)%N -> (k i.+1 + 1 <= k i)%Z &
      forall i, i.+2 = size l -> (k i.+1 <= k i)%Z ].

(* "Firstly": the running high word [s_{i+1} = (vecSumAux (drop i.+1 l)).2]   *)
(* is bounded by [(2-2u) 2^(k_i)].  (paper: |s_i| <= (2-2u)2^(k_{i-1});       *)
(* we index by the *previous* position [i] to avoid [k_{-1}], which is exactly*)
(* the induction-hypothesis form used in the proof.)                          *)
Lemma VecSum_run_bound k l : Thm1_hyp k l ->
  forall i, (i.+1 < size l)%N ->
  Rabs (vecSumAux (drop i.+1 l)).2 <= (2 - 2 * u) * pow (k i).
Proof.
case=> Hrepr Hgap Hlast.
(* Each input is bounded: |x_j| = |M_j| 2^(k_j-p+1) <= (2^p-1) 2^(k_j-p+1)    *)
(*                              = (2 - 2u) 2^(k_j).                           *)
have Hx : forall j, (j < size l)%N ->
  Rabs (nth 0 l j) <= (2 - 2 * u) * pow (k j).
  move=> j jLs; have [_ [M Mlt ->]] := Hrepr j jLs.
  rewrite Rabs_mult (Rabs_pos_eq _ (bpow_ge_0 _ _)) -abs_IZR.
  have I2p : IZR (2 ^ p) = pow p by [].
  have Hkj : pow (k j) = pow (p - 1) * pow (k j - p + 1)
    by rewrite -bpow_plus; congr bpow; lia.
  have Hpm1 : pow (-1)%Z = / 2 by rewrite /= /Z.pow_pos /=; lra.
  have H2u : u * pow (p - 1) = / 2
    by rewrite uE -bpow_plus (_ : (- p + (p - 1))%Z = (-1)%Z);
       [exact: Hpm1 | lia].
  have Hpp : pow p = 2 * pow (p - 1).
    have H := bpow_plus beta 1 (p - 1); rewrite bpow_1 in H.
    rewrite (_ : (1 + (p - 1))%Z = p) in H; last by lia.
    by rewrite H /= /Z.pow_pos /=; lra.
  rewrite Hkj -Rmult_assoc; apply: Rmult_le_compat_r; first exact: bpow_ge_0.
  have -> : (2 - 2 * u) * pow (p - 1) = IZR (2 ^ p - 1)
    by rewrite minus_IZR I2p Hpp; nra.
  by apply: IZR_le; lia.
(* Downward induction on the suffix.  [s_{i+1} = (vecSumAux (drop i.+1 l)).2]:*)
(*  - base [i.+2 = size l]: [s_{i+1} = x_{i+1}], and                          *)
(*      |x_{i+1}| <= (2-2u) 2^(k_{i+1}) <= (2-2u) 2^(k_i)                     *)
(*    by the weak gap [k_i >= k_{i+1}] (Hlast);                               *)
(*  - step [i.+2 < size l]: [s_{i+1} = RN(x_{i+1} + s_{i+2})]; with the IH    *)
(*      |s_{i+2}| <= (2-2u) 2^(k_{i+1}) and |x_{i+1}| <= (2-2u) 2^(k_{i+1}),  *)
(*      |x_{i+1}| + |s_{i+2}| <= (4-4u) 2^(k_{i+1}) <= (2-2u) 2^(k_i)         *)
(*    by the strict gap [k_i >= k_{i+1} + 1] (Hgap), and rounding to nearest  *)
(*    preserves the bound.                                                    *)
move=> i iLs; have [d le_d] := ubnP (size l - i.+2).
elim: d i iLs le_d => // d IHd i iLs; rewrite ltnS => le_d.
have [Hi2|Hi2] := eqVneq i.+2 (size l).
- (* base: the suffix is the singleton [x_{i+1}], so s_{i+1} = x_{i+1}.       *)
  have Hdrop : drop i.+1 l = [:: nth 0 l i.+1]
    by rewrite (drop_nth 0) // Hi2 drop_size.
  rewrite Hdrop /=.
  apply: Rle_trans (Hx i.+1 iLs) _.
  apply: Rmult_le_compat_l; last by apply: bpow_le; exact: (Hlast i Hi2).
  have u_le_1 : u <= 1 by rewrite uE -(pow0E beta); apply: bpow_le; lia.
  lra.
(* step: the suffix has >= 2 elements, so s_{i+1} = RN(x_{i+1} + s_{i+2}).    *)
have iLs' : (i < size l)%N := ltn_trans (ltnSn i) iLs.
have Hi2lt : (i.+2 < size l)%N by rewrite ltn_neqAle Hi2 iLs.
have [Hemin _] := Hrepr i iLs'.
have Hd1 : drop i.+1 l = nth 0 l i.+1 :: drop i.+2 l by rewrite (drop_nth 0).
have Hd2 : drop i.+2 l = nth 0 l i.+2 :: drop i.+3 l
  by rewrite (drop_nth 0) // Hi2lt.
have Hs : (vecSumAux (drop i.+1 l)).2
            = RND (nth 0 l i.+1 + (vecSumAux (drop i.+2 l)).2).
  rewrite Hd1 Hd2 vecSumAux_cons -Hd2.
  by case: (vecSumAux (drop i.+2 l)) => es s /=; rewrite /TwoSum.
rewrite Hs.
(* the tight bound B = (2 - 2u) 2^{k_i} is itself a float.                    *)
have Meq : (2 - 2 * u) * pow (k i) = IZR (2 ^ p - 1) * pow (k i - p + 1).
  have I2p : IZR (2 ^ p) = pow p by [].
  have Hki : pow (k i) = pow (p - 1) * pow (k i - p + 1)
    by rewrite -bpow_plus; congr bpow; lia.
  have Hpm1 : pow (-1)%Z = / 2 by rewrite /= /Z.pow_pos /=; lra.
  have Hu2 : u * pow (p - 1) = / 2
    by rewrite uE -bpow_plus (_ : (- p + (p - 1))%Z = (-1)%Z);
       [exact: Hpm1 | lia].
  have Hpp : pow p = 2 * pow (p - 1).
    have H := bpow_plus beta 1 (p - 1); rewrite bpow_1 in H.
    rewrite (_ : (1 + (p - 1))%Z = p) in H; last by lia.
    by rewrite H /= /Z.pow_pos /=; lra.
  rewrite Hki -Rmult_assoc; congr (_ * _).
  by rewrite minus_IZR I2p Hpp; nra.
have FB : format ((2 - 2 * u) * pow (k i)).
  rewrite Meq; apply: generic_format_FLT.
  exists (Float beta (2 ^ p - 1) (k i - p + 1));
    [by rewrite /F2R /= | | exact: Hemin].
  rewrite [Fnum _]/=; have h : (0 < 2 ^ p)%Z by apply: Z.pow_pos_nonneg; lia.
  rewrite Z.abs_eq; last by lia.
  by change (2 ^ p - 1 < 2 ^ p)%Z; lia.
(* the strict gap [k_i >= k_{i+1} + 1] gives [2 . 2^{k_{i+1}} <= 2^{k_i}].    *)
have Hgk : (k i.+1 + 1 <= k i)%Z by apply: Hgap.
have Hpowgap : 2 * pow (k i.+1) <= pow (k i).
  have E1 : pow (k i.+1 + 1) = 2 * pow (k i.+1)
    by rewrite bpow_plus bpow_1 /=; lra.
  by rewrite -E1; apply: bpow_le.
(* the tail running sum is bounded by the IH at [i.+1].                       *)
have s2_bnd : Rabs (vecSumAux (drop i.+2 l)).2 <= (2 - 2 * u) * pow (k i.+1).
  apply: IHd => //.
  by apply: (leq_trans _ le_d); rewrite subnS prednK ?subn_gt0 //.
have u_le_1 : u <= 1 by rewrite uE -(pow0E beta); apply: bpow_le; lia.
have HX := Hx i.+1 iLs.
(* rounding to nearest preserves the bound B, which is a float.               *)
apply: abs_round_le_generic; first exact: FB.
(* |x_{i+1}| + |s_{i+2}| <= (4 - 4u) 2^{k_{i+1}} <= (2 - 2u) 2^{k_i}.         *)
apply: Rle_trans (Rabs_triang _ _) _.
nra.
Qed.

(* The running high word [(vecSumAux m).2] of a VecSum is a float.            *)
Lemma format_vecSumAux2 m :
  {in m, forall z, format z} -> format (vecSumAux m).2.
Proof.
elim: m => [|a [|b m] IH] Hf.
- exact: generic_format_0.
- by have -> : (vecSumAux [:: a]).2 = a by []; apply: Hf; rewrite inE eqxx.
rewrite vecSumAux_cons.
case E : (vecSumAux (b :: m)) => [es s].
have -> :
  (let: DWR si ei1 := TwoSum a s in (ei1 :: es, si)).2 = dwh (TwoSum a s)
  by case: (TwoSum a s).
by rewrite TwoSum_hi; apply: generic_format_round.
Qed.

(* The [i]-th VecSum error [nth 0 (vecSumAux m).1 i] is the low word of the   *)
(* 2Sum combining [x_i] with the running sum [s_{i+1}] of the tail.           *)
Lemma vecSumAux_nth1 m i : (i.+1 < size m)%N ->
  nth 0 (vecSumAux m).1 i =
  dwl (TwoSum (nth 0 m i) (vecSumAux (drop i.+1 m)).2).
Proof.
elim: m i => [|a m' IH] i Hi.
  by move: Hi; rewrite /= ltn0.
case: m' IH Hi => [|b m] IH Hi.
  by move: Hi; rewrite /= ltnS ltn0.
rewrite vecSumAux_cons.
case E : (vecSumAux (b :: m)) => [es s].
case: i Hi => [|i] Hi.
  have -> : nth 0 [:: a, b & m] 0 = a by [].
  have -> : drop 1 [:: a, b & m] = b :: m by [].
  rewrite E [(es, s).2]/=.
  by case: (TwoSum a s).
rewrite ltnS in Hi.
have -> : nth 0 [:: a, b & m] i.+1 = nth 0 (b :: m) i by [].
have -> : drop i.+2 [:: a, b & m] = drop i.+1 (b :: m) by [].
by rewrite -(IH i) // E.
Qed.

(* The low word of a 2Sum [TwoSum x s] is small: its magnitude is at most     *)
(* [2 u 2^e0], provided [|x| < 2^(e0+1)] and [|s| <= (2-2u) 2^e0] (so the     *)
(* exact sum has magnitude below [2^(e0+2)]).  This is the tight per-step     *)
(* error bound behind [Herr] (the paper's [2 u^2 2^(k_{i-1})] would be a      *)
(* factor [2^p] too small: a single 2Sum error can reach [~u 2^(k_i)]).       *)
Lemma magnitude_vecSum_err x s e0 : format x -> format s ->
  Rabs x < pow (e0 + 1) -> Rabs s <= (2 - 2 * u) * pow e0 ->
  (emin <= e0 - p + 1)%Z ->
  Rabs (dwl (TwoSum x s)) <= 2 * u * pow e0.
Proof.
move=> Fx Fs Hx Hs Hemin.
have Hc : dwh (TwoSum x s) + dwl (TwoSum x s) = x + s
  by exact: TwoSum_correct_loc Fx Fs.
rewrite TwoSum_hi in Hc.
have -> : dwl (TwoSum x s) = - (RND (x + s) - (x + s)) by lra.
rewrite Rabs_Ropp.
have Hz : Rabs (x + s) < pow (e0 + 2).
  apply: Rle_lt_trans (Rabs_triang _ _) _.
  have Hs1 : Rabs s < pow (e0 + 1).
    apply: Rle_lt_trans Hs _.
    have -> : pow (e0 + 1) = 2 * pow e0 by rewrite bpow_plus bpow_1 /=; lra.
    have Hu : 0 < u by rewrite uE; apply: bpow_gt_0.
    have := bpow_gt_0 beta e0; nra.
  have -> : pow (e0 + 2) = pow (e0 + 1) + pow (e0 + 1)
    by rewrite !bpow_plus /= /Z.pow_pos /=; lra.
  lra.
have Hulp : ulp (x + s) <= pow (e0 + 2 - p).
  have [z0|z0] := Req_dec (x + s) 0.
    by rewrite z0 ulp_FLT_0; apply: bpow_le; lia.
  rewrite ulp_neq_0 //; apply: bpow_le; rewrite /cexp /FLT_exp.
  have Hm : (mag beta (x + s) <= e0 + 2)%Z by apply: mag_le_bpow.
  lia.
apply: (Rle_trans _ (/ 2 * ulp (x + s))).
  by apply: error_le_half_ulp.
apply: Rle_trans (_ : / 2 * pow (e0 + 2 - p) <= _).
  by apply: Rmult_le_compat_l; [lra | exact: Hulp].
have -> : 2 * u * pow e0 = / 2 * pow (e0 + 2 - p).
  rewrite uE.
  have -> : / 2 = pow (-1) by rewrite /= /Z.pow_pos /=; lra.
  have -> : (2 : R) = pow 1 by rewrite /= /Z.pow_pos /=; lra.
  by rewrite -!bpow_plus; congr bpow; lia.
by lra.
Qed.

(* Theorem 1.  [VecSum l] is F-nonoverlapping (wIZ) with the same sum.        *)
(* Proof (paper Section 2.1): [VecSum_run_bound] gives the running-sum bound, *)
(* whence each error [|e_{i+1}| <= 2 u 2^(k_i)] ([magnitude_vecSum_err]); the *)
(* errors are then F-nonoverlapping by the "multiples of 2u" ([uls]) argument,*)
(* which contradicts any overlap [|e_{i+1}| > 1/2 uls(e_i)].                  *)
Lemma VecSum_Thm1 k l : Thm1_hyp k l ->
  Fnonoverlap (vecSum l) /\ sumR (vecSum l) = sumR l.
Proof.
move=> Hk.
(* Each [x_i = M_i 2^(k_i-p+1)] with [|M_i| < 2^p] is FLT ([repr_format]).    *)
have Hfmt : {in l, forall z, format z}.
  case: Hk => Hrepr _ _ z /(nthP 0)[i iLs <-].
  exact: repr_format (Hrepr i iLs).
(* "with the same sum": VecSum is a chain of error-free 2Sums (Algorithm 4).  *)
split; last by apply: vecSum_sum.
(* Firstly: the running high word [s_{i+1} = (vecSumAux (drop i.+1 l)).2]     *)
(* is bounded, |s_{i+1}| <= (2 - 2u) 2^(k_i), by induction on the suffix using*)
(*   |s_{i+2}| + |x_{i+1}| <= (4 - 4u) 2^(k_{i+1}) <= (2 - 2u) 2^(k_i).       *)
have Hrun := VecSum_run_bound Hk.
(* This gives the tight error bound |e_{i+1}| <= 2 u 2^(k_i).  (The paper's   *)
(* 2 u^2 2^(k_i) is a factor 2^p too small and is FALSE: e.g. for l = [1;     *)
(* 2^-54] the 2Sum error is 2^-54, well above 2 u^2 = 2^-105.)                *)
have Herr : forall j, (j.+1 < size l)%N ->
    Rabs (nth 0 (vecSum l) j.+1) <= 2 * u * pow (k j).
  have [Hrepr _ _] := Hk.
  move=> j jLs.
  have jLl : (j < size l)%N := ltn_trans (ltnSn j) jLs.
  have [Hemin [M HM Hxeq]] := Hrepr j jLl.
  have -> : nth 0 (vecSum l) j.+1 = nth 0 (vecSumAux l).1 j
    by rewrite /vecSum; case: (vecSumAux l).
  rewrite vecSumAux_nth1 //.
  apply: magnitude_vecSum_err.
  - by apply: Hfmt; apply: mem_nth.
  - apply: format_vecSumAux2 => z zIn.
    by apply: Hfmt; rewrite -(cat_take_drop j.+1 l) mem_cat zIn orbT.
  - rewrite Hxeq Rabs_mult (Rabs_pos_eq _ (bpow_ge_0 _ _)) -abs_IZR.
    have -> : pow (k j + 1) = pow p * pow (k j - p + 1)
      by rewrite -bpow_plus; congr bpow; lia.
    apply: Rmult_lt_compat_r; first exact: bpow_gt_0.
    have -> : pow p = IZR (2 ^ p) by [].
    by apply: IZR_lt.
  - exact: Hrun j jLs.
  - exact: Hemin.
(* F-nonoverlapping (paper, by contradiction).                                *)
move=> i iLs Hn0.
suff : ~ (/ 2 * uls (nth 0 (vecSum l) i) < Rabs (nth 0 (vecSum l) i.+1)) by lra.
move=> Hover.
have Hi : (i.+1 < size l)%N by move: iLs; rewrite size_vecSum; case: (size l).
have He := Herr i Hi.
(* The paper's key estimate for [e_i = nth 0 (vecSum l) i], SCALE-INVARIANT:  *)
(*     uls(e_i) >= 4 u 2^(k_i).                                               *)
(* This is the multiples-of-2u argument of Theorem 1: after the paper's WLOG  *)
(* scaling [uls(e_i) = u], the [s_j] and [x_0, ..., x_i] are all multiples of *)
(* 2u, the offending [e_i] (not a multiple of 2u) forces [2^(k_i) <= 1/(4u)]. *)
(* NB: the earlier intermediate [2^(k_i) <= 1/4] is NOT scale-invariant, hence*)
(* unprovable alone -- [Hover] is invariant under scaling [l] by a power      *)
(* of two (every [k_j] shifts and [vecSum] commutes with the scaling) while   *)
(* [2^(k_i)] is not; only the ratio [uls(e_i) / 2^(k_i)] is pinned down.      *)
have Hilt : (i < size (vecSum l))%N := ltn_trans (ltnSn i) iLs.
have Hkey : 4 * u * pow (k i) <= uls (nth 0 (vecSum l) i).
  (* [4 u 2^(k_i)] is the clean power [2^(k_i+2-p)]; then [is_imul_uls_ge]    *)
  (* turns the [uls] lower bound into "[e_i] is a multiple of that grid".     *)
  have -> : 4 * u * pow (k i) = pow (k i + 2 - p).
    rewrite uE.
    have -> : (4 : R) = pow 2 by rewrite /= /Z.pow_pos /=; lra.
    by rewrite -!bpow_plus; congr bpow; lia.
  apply: is_imul_uls_ge.
  - by apply: (format_vecSum Hfmt); apply: mem_nth.
  - exact: Hn0.
  (* Core (paper's multiples-of-2u argument): the i-th VecSum output lies on  *)
  (* the coarse grid [2^(k_i+2-p) = 4 u 2^(k_i)].  Its rightmost nonzero bit  *)
  (* is no finer than [2 G_i]: the fine bits of the running sum are absorbed  *)
  (* into the high word, and the exponent gaps [k_{j-1} >= k_j + 1] make every*)
  (* [x_j], [s_j] (j <= i) a multiple of it.  This is the remaining hard step.*)
  by admit.
(* [Hover]: |e_{i+1}| > uls(e_i)/2 >= 2u 2^(k_i) >= |e_{i+1}| (Herr): absurd. *)
by lra.
Admitted.

(* The key separation step of Theorem 1.  When [2Sum a s] produces a NONZERO  *)
(* low word [ei1], the head of the already-normalised tail [es] stays below   *)
(* [1/2 uls ei1].  Given that [s] is on a finer grid than [a] ([uls s <=      *)
(* uls a]), the low word carries [s]'s rightmost bit, so [uls s <= uls ei1]   *)
(* ([TwoSum_err_uls_ge]); combine with [Fnonoverlap (s :: es)] at index 0     *)
(* ([Rabs (nth 0 es 0) <= 1/2 uls s]).  The operands are nonzero because a    *)
(* zero operand would round exactly and leave [ei1 = 0].  The exponent        *)
(* premise [uls s <= uls a] is the remaining content, discharged by the       *)
(* paper's [k_i] argument at the call site.                                   *)
Lemma Fnonoverlap_head a s es :
  format a -> format s -> uls s <= uls a ->
  Fnonoverlap (s :: es) -> (0 < size es)%N ->
  let: DWR _ ei1 := TwoSum a s in
  ei1 <> 0 -> Rabs (nth 0 es 0) <= / 2 * uls ei1.
Proof.
move=> Fa Fs Hulsle Fses Hsz.
case E : (TwoSum a s) => [si ei1] Hn0.
have Hc : dwh (TwoSum a s) + dwl (TwoSum a s) = a + s.
  by exact: TwoSum_correct_loc Fa Fs.
have Hei1 : RND (a + s) + ei1 = a + s by move: Hc; rewrite TwoSum_hi E dwlE.
have sn0 : s <> 0.
  move=> s0; apply: Hn0.
  have Ha : RND (a + s) = a by rewrite s0 Rplus_0_r; apply: round_generic.
  by lra.
have an0 : a <> 0.
  move=> a0; apply: Hn0.
  have Hb : RND (a + s) = s by rewrite a0 Rplus_0_l; apply: round_generic.
  by lra.
have Hle : Rabs (nth 0 es 0) <= / 2 * uls s.
  apply: (Fses 0%N); last exact: sn0.
  by rewrite /= ltnS.
have Hulsei : uls s <= uls ei1.
  have -> : ei1 = dwl (TwoSum a s) by rewrite E.
  by apply: (TwoSum_err_uls_ge Fa Fs an0 sn0 Hulsle); rewrite E.
apply: Rle_trans Hle _.
by have := Hulsei; lra.
Qed.

(* Theorem 1 (VecSum), stated as in the paper: given the input separation,    *)
(* [vecSum l] is F-nonoverlapping AND has the same exact sum.  The input      *)
(* hypotheses [sorted_mag l] + [pairwise_ulp l] are the concrete form of the  *)
(* paper's exponent conditions (writing [x_i = M_i * 2^(k_i)], [|M_i| < 2^p]: *)
(* [k_{i-1} >= k_i + 1] for all i except at most one "overlap" index, and     *)
(* [k_{n-2} >= k_{n-1}]); they are exactly what [Merge] produces on the six   *)
(* merged terms.                                                              *)
(* Informal proof.  Sum: this conjunct is precisely [vecSum_sum].  Separation:*)
(* run [2Sum] from the least-significant end (Algorithm 4); by induction each *)
(* error term is at most [1/2 uls] of the running high word, so the output is *)
(* F-nonoverlapping (with interleaving zeros).  The induction step is         *)
(* [magnitude_TwoSum] (each 2Sum error is <= 1/2 ulp of its sum) sharpened to *)
(* the [uls] bound using the exponent separation above.                       *)
Lemma vecSum_Fnonoverlap l :
  {in l, forall z, format z} -> sorted_mag l -> pairwise_ulp l ->
  Fnonoverlap (vecSum l) /\ sumR (vecSum l) = sumR l.
Proof.
move=> lF lM lP; split; last by apply: vecSum_sum.
rewrite /vecSum.
elim: l lF lM lP => // a [|b l] // IH ablF ablM ablP.
have -> : vecSumAux [:: a,  b  & l] =
          let: (es, s) := vecSumAux (b :: l) in
          let: DWR si ei1 := TwoSum a s in
          (ei1 :: es, si) by [].
case E : (vecSumAux (b :: l)) => [es s].
case E1 : (TwoSum a s) => [si ei1].
have sesF :  Fnonoverlap (s :: es).
  have := IH; rewrite E; apply.
  - by move=> z zIl; apply: ablF; rewrite inE zIl orbT.
  - by case: (sorted_mag_cons ablM).
  by case: (l) ablP => // c l1 /pairwise_ulp_cons[].
have sF : format s.
  have := @format_vecSumAux (b :: l).
  by rewrite E; case => // z zIl; apply: ablF; rewrite inE zIl orbT.
have aF : format a by apply: ablF; rewrite !inE eqxx.
move=> [|[|i]] /= iLs Hn0.
- have :  magnitudeDWR (TwoSum a s).
    by apply: magnitude_TwoSum.
  rewrite E1 => /=; rewrite Rmult_comm /Rdiv //.
  move=> Hm; have H : ulp si <= uls si by apply: ulp_le_ulps.
  by lra.
- have Hsz : (0 < size es)%N by move: iLs; case: (size es).
  (* [uls s <= uls a]: the running high word [s] of the tail sits on a grid   *)
  (* at least as fine as the coarse head [a].  This is the paper's [k_i]      *)
  (* exponent argument; not derivable from the simplified [sorted_mag] /      *)
  (* [pairwise_ulp] inputs alone, so it is the sole remaining gap here.       *)
  have Huls : uls s <= uls a by admit.
  have H := Fnonoverlap_head aF sF Huls sesF; rewrite E1 in H.
  exact: (H Hsz Hn0).
by apply: (sesF i.+1).
Admitted.

(* Theorem 2 (VSEB), stated as in the paper: if [e] is F-nonoverlapping (with *)
(* float terms) and the precision is large enough, [size e <= p + 1] (i.e. the*)
(* paper's [p >= n - 1] with [n = size e]; here [n = 6], [p = 53]), then      *)
(* [vseb e] is P-nonoverlapping (Priest, Def. 1) AND has the same exact sum.  *)
(* Informal proof (paper Thm 2): [vseb] walks the sequence with a running     *)
(* remainder, emitting a term only when the [2Sum] error is nonzero (thereby  *)
(* dropping interleaving zeros); it is error-free, whence the sum is          *)
(* preserved. The F-nonoverlap bound [|e_{i+1}| <= 1/2 uls(e_i)] makes every  *)
(* step a Fast2Sum with no rounding, so consecutive emitted terms satisfy the *)
(* STRICT [|y_{i+1}| < ulp(y_i)]; the [size e <= p + 1] hypothesis rules out  *)
(* the carry that could turn [<] into [=].                                    *)
(* Reusable step lemma: a nonzero 2Sum error [et = dwl(2Sum eps e)] is at     *)
(* least as coarse as [e] ([uls e <= uls et], by [TwoSum_err_uls_ge]), so     *)
(* prepending [et] to the tail [l] keeps F-nonoverlap.  This re-establishes   *)
(* the VSEB invariant when a term is emitted.                                 *)
Lemma Fnonoverlap_TwoSum_err eps e l :
  format eps -> format e -> Fnonoverlap [:: eps, e & l] ->
  dwl (TwoSum eps e) <> 0 -> Fnonoverlap (dwl (TwoSum eps e) :: l).
Proof.
Admitted.

(* Reusable step lemma (the [et = 0] branch): when [2Sum eps e] is exact      *)
(* ([dwl = 0], so [dwh = eps + e] merges them), prepending the merged high    *)
(* word to the tail keeps F-nonoverlap.                                       *)
Lemma Fnonoverlap_TwoSum_merge eps e l :
  format eps -> format e -> Fnonoverlap [:: eps, e & l] ->
  dwl (TwoSum eps e) = 0 -> Fnonoverlap (dwh (TwoSum eps e) :: l).
Proof.
Admitted.

(* Reusable block bound (paper Thm 2, geometric argument): the first term     *)
(* emitted by VSEB from a nonzero remainder [eps] over an F-nonoverlap tail   *)
(* has magnitude [< 2 |eps|].  [|r_i| <= |eps|(1 + u + u^2 + ...) < 2|eps|];  *)
(* the [size l < p] hypothesis keeps the geometric sum below [2].             *)
Lemma vsebAux_head_lt eps l :
  (Z.of_nat (size l).+1 <= p + 1)%Z ->
  format eps -> {in l, forall z, format z} -> Fnonoverlap (eps :: l) ->
  eps <> 0 -> Rabs (nth 0 (vsebAux eps l) 0) < 2 * Rabs eps.
Proof.
Admitted.

(* Core of Thm 2, by induction on the tail [l] of [eps :: l] (paper's running *)
(* remainder [eps] and high words [r_i]).  A step [2Sum(eps, e) = (r, et)]:   *)
(* when [et = 0] the remainder [r] is carried on (no term emitted); when      *)
(* [et <> 0] the high word [r] is emitted and [et] becomes the new remainder. *)
(* Two paper facts drive P-nonoverlap of the emitted [r]'s:                   *)
(*  - divisibility: [r_{i-1}], [eps_i] are multiples of [2^(k_i) = uls e_i];  *)
(*  - a per-block bound giving [ulp(y_j) >= 2 |eps_{i0}|], so the next emitted*)
(*    term [y_{j+1}] has [|y_{j+1}| < 2 |eps_{i0}| <= ulp(y_j)].              *)
(* The [size l < p] hypothesis (paper's [p >= n - 1]) bounds the block length *)
(* so the geometric sum [2 - 2^(i0-i-1)] stays [< 2] and no carry occurs.     *)
Lemma vsebAux_Pnonoverlap eps l :
  (Z.of_nat (size l).+1 <= p + 1)%Z ->
  format eps -> {in l, forall z, format z} -> Fnonoverlap (eps :: l) ->
  Pnonoverlap (vsebAux eps l).
Proof.
elim: l eps => [|e l' IH] eps Hsz epsF lF Fno.
  (* [vsebAux eps [::] = [:: eps]]: a single term is P-nonoverlapping.        *)
  by move=> i; rewrite /= ltnS ltn0.
have Fe : format e by apply: lF; rewrite inE eqxx.
case: l' IH lF Fno Hsz => [|e2 l''] IH lF Fno Hsz.
  (* Last step (paper's final 2Sum): [vsebAux eps [:: e] = [:: y0; y1]] with  *)
  (* [(y0, y1) = 2Sum(eps, e)]; P-nonoverlap is [|y1| < ulp y0], the Fast2Sum *)
  (* bound (no carry, using [p >= n - 1]).                                    *)
  rewrite vsebAux_1; case E1 : (TwoSum eps e) => [y0 y1].
  move=> [|i] /= Hi; last by move: Hi; rewrite ltnS ltnS ltn0.
  (* |y1| < ulp y0: the 2Sum error is <= half an ulp of the high word.        *)
  have Hm := magnitude_TwoSum epsF Fe; rewrite E1 /= in Hm.
  have Hy : 0 < ulp y0 by apply: ulp_gt_0.
  by lra.
(* General step: [2Sum(eps, e) = (r, et)].                                    *)
rewrite vsebAux_consS; case E1 : (TwoSum eps e) => [r et].
have Hr : r = RND (eps + e) by have := TwoSum_hi eps e; rewrite E1.
case: Req_EM_T => [et0|etn0].
  (* [et = 0]: nothing emitted, remainder [r] carried on; recurse on          *)
  (* [r :: e2 :: l''] once the invariant is re-established.                   *)
  apply: IH.
  - by move: Hsz; rewrite /=; lia.
  - by rewrite Hr; apply: generic_format_round.
  - by move=> z zI; apply: lF; rewrite inE zI orbT.
  (* Fnonoverlap (r :: e2 :: l''): [r] merges [eps, e] exactly (et = 0).      *)
  have H := Fnonoverlap_TwoSum_merge epsF Fe Fno; rewrite E1 /= in H.
  by apply: H.
(* [et <> 0]: emit [r], recurse on the new remainder [et].                    *)
have Fet : format et
  by have H := format_TwoSum epsF Fe; rewrite E1 /= in H; case: H.
have Fl' : {in e2 :: l'', forall z, format z}
  by move=> z zI; apply: lF; rewrite inE zI orbT.
have FnoEt : Fnonoverlap (et :: e2 :: l'').
  have H := Fnonoverlap_TwoSum_err epsF Fe Fno; rewrite E1 /= in H.
  by apply: H.
have Hrec : Pnonoverlap (vsebAux et (e2 :: l'')).
  by apply: IH => //; move: Hsz; rewrite /=; lia.
move=> [|i] /= Hi.
  (* Head: emitted [r = y_j] vs next [y_{j+1}].  [ulp r >= 2 |et|]            *)
  (* ([magnitude_TwoSum]) and [|y_{j+1}| < 2 |et|] ([vsebAux_head_lt]).       *)
  have Hulp : 2 * Rabs et <= ulp r.
    by have Hm := magnitude_TwoSum epsF Fe; rewrite E1 /= in Hm; lra.
  have Hnext : Rabs (nth 0 (vsebAux et (e2 :: l'')) 0) < 2 * Rabs et.
    by apply: vsebAux_head_lt => //; move: Hsz; rewrite /=; lia.
  by apply: (Rlt_le_trans _ _ _ Hnext Hulp).
(* Tail: P-nonoverlap of the recursive output (index shift).                  *)
by apply: (Hrec i); move: Hi; rewrite ltnS.
Qed.

(* Theorem 2 (paper): [vseb e] is P-nonoverlapping with the same sum, given   *)
(* [e] F-nonoverlapping and [size e <= p + 1].  Sum: [vseb_sum] (VSEB is a    *)
(* chain of exact 2Sums).  Separation: [vsebAux_Pnonoverlap].                 *)
Lemma vseb_Pnonoverlap e :
  (Z.of_nat (size e) <= p + 1)%Z ->
  {in e, forall z, format z} -> Fnonoverlap e ->
  Pnonoverlap (vseb e) /\ sumR (vseb e) = sumR e.
Proof.
move=> Hsz eF eFno.
split; last by apply: vseb_sum.
case: e Hsz eF eFno => [|e0 l'] Hsz eF eFno; first by move=> i; rewrite /= ltn0.
rewrite /vseb.
apply: vsebAux_Pnonoverlap => //.
- by apply: eF; rewrite inE eqxx.
by move=> z zI; apply: eF; rewrite inE zI orbT.
Qed.

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
(*   - VecSum turns that into an F-nonoverlapping (wIZ) sequence with         *)
(*     the same exact sum (Theorem 1 / Corollary 1).                          *)
(*   - VSEB returns a P-nonoverlapping sequence (Theorem 2), so its           *)
(*     first three terms form a TW number.                                    *)
(* ===========================================================================*)
Lemma TWSum_isTW x y : isTW x -> isTW y -> isTW (TWSum x y).
Proof.
case: x => x0 x1 x2; case: y => y0 y1 y2 => Hx Hy.
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
  case: (@vseb_Pnonoverlap e) => //.
  - by rewrite size_vecSum size_Merge.
  - apply/format_vecSum/format_Merge => //; first by apply: (isTW_format Hx).
    by apply: (isTW_format Hy).
  by case: (@vecSum_Fnonoverlap z).
(* and its terms are floating-point numbers.                                  *)
have Hr_format : {in vsebK 3 e, forall t, format t}.
  by apply/format_vsebK/format_vecSum.
(* Reading the first three terms off the P-nonoverlapping sequence            *)
(* yields a triple-word number.  Case on the (<=3, zero-padded) list [vsebK   *)
(* 3 e]; formats come from [Hr_format], the strict ulp bounds from either     *)
(* [Hr_nonover] (real terms) or [0 < ulp _] (the padding zeros).              *)
rewrite /TWSum -/z -/e.
move: Hr_nonover Hr_format; case: (vsebK 3 e) => [|r0 [|r1 [|r2 tl]]] Hno Hfmt.
- by split; [exact: generic_format_0 | exact: generic_format_0
           | exact: generic_format_0 | rewrite Rabs_R0; exact: ulp_gt_0
           | rewrite Rabs_R0; exact: ulp_gt_0].
- by split; [apply: Hfmt; rewrite !inE eqxx | exact: generic_format_0
           | exact: generic_format_0 | rewrite Rabs_R0; exact: ulp_gt_0
           | rewrite Rabs_R0; exact: ulp_gt_0].
- by split; [apply: Hfmt; rewrite !inE eqxx | 
             apply: Hfmt; rewrite !inE eqxx orbT | 
             exact: generic_format_0 | 
             apply: (Hno 0%N) | rewrite Rabs_R0; exact: ulp_gt_0].
by split; [apply: Hfmt; rewrite !inE eqxx | apply: Hfmt; rewrite !inE eqxx orbT
         | apply: Hfmt; rewrite !inE eqxx !orbT | 
           apply: (Hno 0%N) | apply: (Hno 1%N)].
Qed.

(* A float is at most [(2 - 2u) ufp] of itself (max-mantissa bound).  Holds   *)
(* also at 0 and in the subnormal range, so no no-underflow hypothesis.       *)
Lemma abs_le_ufp_norm x : format x -> Rabs x <= (2 - 2 * u) * ufp x.
Proof.
move=> Fx.
have Hu0 : 0 < u by rewrite uE; apply: bpow_gt_0.
have Hu1 : u <= 1 by rewrite uE -(pow0E beta); apply: bpow_le; lia.
case: (Req_dec x 0) => [xz|xn0].
  by rewrite xz Rabs_R0; have := ufp_gt_0 0; nra.
have Hmx : (emin < mag beta x)%Z.
  by apply: lt_bpow; apply: Rle_lt_trans (alpha_lB Fx xn0) _;
     exact: bpow_mag_gt.
have Hsucc : succ beta fexp (Rabs x) <= bpow beta (mag beta x).
  apply: succ_le_lt => //; first exact: generic_format_abs.
    by apply: generic_format_bpow; rewrite /fexp /FLT_exp; lia.
  by apply: bpow_mag_gt.
move: Hsucc; rewrite succ_eq_pos; last exact: Rabs_pos.
rewrite ulp_neq_0; last by move: (Rabs_pos_lt _ xn0); lra.
move=> Hs.
have Hcexp : bpow beta (mag beta x - p) <= bpow beta (cexp (Rabs x)).
  by apply: bpow_le; rewrite /cexp /FLT_exp mag_abs; lia.
have -> : (2 - 2 * u) * ufp x =
  bpow beta (mag beta x) - bpow beta (mag beta x - p).
  rewrite /ufp uE.
  have -> : (2 - 2 * bpow beta (-p)) = bpow beta 1 - bpow beta (1 - p).
    by rewrite (bpow_plus beta 1 (-p)) bpow_1 /=; lra.
  by rewrite Rmult_minus_distr_r -!bpow_plus; congr (bpow _ _ - bpow _ _); lia.
lra.
Qed.

(* A nonzero P-nonoverlap successor forces the predecessor from underflow:    *)
(* [|y| < ulp x] with [y] a nonzero float gives [emin <= mag x - p] (otherwise*)
(* [ulp x = 2^emin], and [|y| < 2^emin] would force [y = 0]).                 *)
Lemma nu_of_lt_ulp x y : format y -> y <> 0 -> Rabs y < ulp x ->
  (emin <= mag beta x - p)%Z.
Proof.
move=> Fy yn0 Hlt.
have Hemin : bpow beta emin <= Rabs y := alpha_lB Fy yn0.
have xn0 : x <> 0 by move=> xz; move: Hlt; rewrite xz ulp_FLT_0; lra.
move: Hlt; rewrite ulp_neq_0 // /cexp /FLT_exp => Hlt.
have Hb : bpow beta emin < bpow beta (Z.max (mag beta x - p) emin) by lra.
by move: (lt_bpow _ _ _ Hb); lia.
Qed.

(* A P-nonoverlap list whose head is 0 sums to 0: a zero limb forces its      *)
(* nonzero-float successors below [2^emin], hence to 0.                       *)
Lemma small_head_zero l : Pnonoverlap l -> {in l, forall z, format z} ->
  nth 0 l 0 = 0 -> sumR l = 0.
Proof.
elim: l => [//|a l IH] Pl Fl /= a0.
have Hl0 : sumR l = 0.
  case: l IH Pl Fl => [//|b l'] IH Pl Fl.
  apply: IH; first exact: Pnonoverlap_cons Pl.
    by move=> t tin; apply: Fl; rewrite inE tin orbT.
  have Hb : Rabs b < ulp a by apply: (Pl 0%N).
  case: (Req_dec b 0) => [b0|bn0]; first by rewrite /= b0.
  have Fb : format b by apply: Fl; rewrite !inE eqxx orbT.
  have Hb2 : bpow beta emin <= Rabs b := alpha_lB Fb bn0.
  by exfalso; move: Hb; rewrite a0 ulp_FLT_0; lra.
by rewrite a0 Hl0 Rplus_0_r.
Qed.

(* Key bound: for a P-nonoverlap list of floats, the whole sum is at most     *)
(* twice the [ufp] of the leading term -- the geometric series                *)
(* [(2-2u)(1 + u + u^2 + ...) = 2] collapses in the induction. No nonzero     *)
(* / no-underflow hyp: zero limbs are absorbed by [small_head_zero], and      *)
(* every non-last limb is non-underflowing by [nu_of_lt_ulp].                 *)
Lemma sumR_ufp_bound l : Pnonoverlap l -> {in l, forall z, format z} ->
  Rabs (sumR l) <= 2 * ufp (nth 0 l 0).
Proof.
have Hu0 : 0 < u by rewrite uE; apply: bpow_gt_0.
elim: l => [_ _|a l IH Pl Fl].
  rewrite Rabs_R0.
  by have := ufp_gt_0 (nth 0 (@nil R) 0); lra.
have Fa : format a by apply: Fl; rewrite inE eqxx.
have Hla : Rabs a <= (2 - 2 * u) * ufp a by apply: abs_le_ufp_norm.
have Hua : 0 < ufp a := ufp_gt_0 a.
case: l IH Pl Fl => [|b l] IH Pl Fl.
  have -> : nth 0 [:: a] 0 = a by [].
  have -> : sumR [:: a] = a by rewrite /= Rplus_0_r.
  nra.
have Hb : Rabs b < ulp a by apply: (Pl 0%N).
have Fb : format b by apply: Fl; rewrite !inE eqxx orbT.
have Hub : 0 < ufp b := ufp_gt_0 b.
have -> : nth 0 (a :: b :: l) 0 = a by [].
have -> : sumR (a :: b :: l) = a + sumR (b :: l) by [].
have IHbl : Rabs (sumR (b :: l)) <= 2 * ufp b.
  apply: IH; first exact: Pnonoverlap_cons Pl.
  by move=> t tin; apply: Fl; rewrite inE tin orbT.
case: (Req_dec b 0) => [b0|bn0].
  have Hs0 : sumR (b :: l) = 0.
    apply: small_head_zero; first exact: Pnonoverlap_cons Pl.
      by move=> t tin; apply: Fl; rewrite inE tin orbT.
    by rewrite /= b0.
  by rewrite Hs0 Rplus_0_r; nra.
have Ua : (emin <= mag beta a - p)%Z := nu_of_lt_ulp Fb bn0 Hb.
have Na : a <> 0.
  by move=> az; move: Hb; rewrite az ulp_FLT_0 => Hb';
     have := alpha_lB Fb bn0; lra.
have Hstep : ufp b <= u * ufp a by apply: ufp_ulp_step.
apply: Rle_trans (Rabs_triang _ _) _.
nra.
Qed.

(* [sumR] is additive over concatenation, and P-nonoverlap is stable by drop. *)
Lemma sumR_cat l1 l2 : sumR (l1 ++ l2) = sumR l1 + sumR l2.
Proof. by elim: l1 => [|a l1 IH] /=; rewrite ?IH; ring. Qed.

Lemma Pnonoverlap_drop k l : Pnonoverlap l -> Pnonoverlap (drop k l).
Proof.
move=> H i; rewrite size_drop ltn_subRL => Hi.
by rewrite !nth_drop addnS; apply: H; rewrite -addnS.
Qed.

(* A zero limb propagates: its successor is below [2^emin], hence 0.          *)
Lemma nth_step_zero l i : Pnonoverlap l -> {in l, forall z, format z} ->
  nth 0 l i = 0 -> nth 0 l i.+1 = 0.
Proof.
move=> Pl Fl Hi.
case: (ltnP i.+1 (size l)) => [Hlt|Hle]; last by rewrite nth_default.
have Hb : Rabs (nth 0 l i.+1) < ulp (nth 0 l i) by apply: Pl.
move: Hb; rewrite Hi ulp_FLT_0 => Hb.
case: (Req_dec (nth 0 l i.+1) 0) => [->//|Hn0].
have Hf : format (nth 0 l i.+1) by apply: Fl; apply: mem_nth.
by have := alpha_lB Hf Hn0; lra.
Qed.

Lemma sumR_head_drop1 l : sumR l = nth 0 l 0 + sumR (drop 1 l).
Proof. by case: l => [|a l] /=; rewrite ?drop0; lra. Qed.

(* ===========================================================================*)
(*  Error bound: the "Ensure" clause of Algorithm 8 (p >= 6):                 *)
(*    | r - (x + y) | <= (2 u^3 + 4.2 u^4) | x + y |.                         *)
(*                                                                            *)
(*  Sketch (paper, Theorem 3 specialised to k = 3):                           *)
(*   - Merge, VecSum and VSEB are all exact, so the only error comes          *)
(*     from keeping the first three terms of the expansion.                   *)
(*   - The dropped tail of a P-nonoverlapping expansion is bounded by         *)
(*     (2 u^3 + 4.2 u^4) of the total (Theorem 3, k = 3).                     *)
(* ===========================================================================*)
Lemma TWSum_error x y : isTW x -> isTW y ->
  Rabs (TWval (TWSum x y) - (TWval x + TWval y)) <=
     errc * Rabs (TWval x + TWval y).
Proof.
case: x => x0 x1 x2; case: y => y0 y1 y2 => Hx Hy.
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
  have HFe : Fnonoverlap e by case: (vecSum_Fnonoverlap Hzf Hzs Hzu).
  have Fe : {in e, forall t, format t} by apply: format_vecSum.
  have Py : Pnonoverlap (vseb e).
    by case: (vseb_Pnonoverlap _ Fe HFe) => //;
       rewrite /e size_vecSum size_Merge.
  have Fy : {in vseb e, forall t, format t} by apply: format_vseb.
  set y := vseb e.
  have Hsplit : sumR (vseb e) - sumR (vsebK 3 e) = sumR (drop 3 y).
    by rewrite /vsebK -/y -{1}(cat_take_drop 3 y) sumR_cat; ring.
  rewrite Hsplit -Hvseb_sum -/y.
  have Hu0 : 0 < u by rewrite uE; apply: bpow_gt_0.
  have Hu64 : u <= / 64.
    rewrite uE; have -> : (/ 64 = bpow beta (-6))%R
      by rewrite /= /Z.pow_pos /=; lra.
    by apply: bpow_le; lia.
  have Herrc : 0 <= errc by nra.
  have Hsub : {in drop 1 y, forall t, format t} /\
              {in drop 3 y, forall t, format t}.
    by split=> t /mem_drop tin; apply: Fy.
  case: Hsub => Fd1 Fd3.
  have Hty : Rabs (sumR (drop 3 y)) <= 2 * ufp (nth 0 (drop 3 y) 0).
    apply: sumR_ufp_bound; last exact: Fd3.
    by apply: Pnonoverlap_drop.
  case: (Req_dec (nth 0 y 3) 0) => [y3z|y3n].
    suff -> : sumR (drop 3 y) = 0.
      by rewrite Rabs_R0; apply: Rmult_le_pos => //; exact: Rabs_pos.
    apply: small_head_zero => //; first exact: Pnonoverlap_drop.
    by rewrite nth_drop addn0.
  have S3 : (3 < size y)%N.
    by rewrite ltnNge; apply/negP => Hle; apply: y3n; rewrite nth_default.
  have Fk : forall k, format (nth 0 y k).
    move=> k; case: (ltnP k (size y)) => [Hk|Hk].
      by apply: Fy; apply: mem_nth.
    by rewrite nth_default //; apply: generic_format_0.
  have y2n : nth 0 y 2 <> 0 by move=> H; apply/y3n/(nth_step_zero Py Fy H).
  have y1n : nth 0 y 1 <> 0 by move=> H; apply/y2n/(nth_step_zero Py Fy H).
  have y0n : nth 0 y 0 <> 0 by move=> H; apply/y1n/(nth_step_zero Py Fy H).
  have dstep : forall k, nth 0 y k.+1 <> 0 ->
                 ufp (nth 0 y k.+1) <= u * ufp (nth 0 y k).
    move=> k Hkn.
    have Hk : (k.+1 < size y)%N.
      by rewrite ltnNge; apply/negP => Hge; apply: Hkn; rewrite nth_default.
    have Hpk : Rabs (nth 0 y k.+1) < ulp (nth 0 y k) by apply: Py.
    apply: ufp_ulp_step.
    - by move=> H; apply: Hkn; apply: (nth_step_zero Py Fy H).
    - exact: Hkn.
    - exact: Hpk.
    exact: (nu_of_lt_ulp (Fk k.+1) Hkn Hpk).
  have d0 := dstep 0%N y1n.
  have d1 := dstep 1%N y2n.
  have d2 := dstep 2%N y3n.
  have U0 : 0 < ufp (nth 0 y 0) := ufp_gt_0 _.
  have U1 : 0 < ufp (nth 0 y 1) := ufp_gt_0 _.
  have U2 : 0 < ufp (nth 0 y 2) := ufp_gt_0 _.
  have e2 : ufp (nth 0 y 3) <= u * (u * (u * ufp (nth 0 y 0))).
    apply: Rle_trans d2 _; apply: Rmult_le_compat_l; first lra.
    apply: Rle_trans d1 _; apply: Rmult_le_compat_l; first lra.
    exact: d0.
  move: Hty; rewrite nth_drop addn0 => Hty.
  have Hd1y : Rabs (sumR (drop 1 y)) <= 2 * ufp (nth 0 y 1).
    have -> : nth 0 y 1 = nth 0 (drop 1 y) 0 by rewrite nth_drop addn0.
    apply: sumR_ufp_bound; last exact: Fd1.
    by apply: Pnonoverlap_drop.
  have Hlow : (1 - 2 * u) * ufp (nth 0 y 0) <= Rabs (sumR y).
    have Hy0 : ufp (nth 0 y 0) <= Rabs (nth 0 y 0) by apply: ufp_le_abs.
    have := Rabs_triang_inv (nth 0 y 0) (- sumR (drop 1 y)).
    rewrite Rabs_Ropp.
    have -> : nth 0 y 0 - - sumR (drop 1 y) = sumR y
      by rewrite [in RHS]sumR_head_drop1; ring.
    move=> Htri; nra.
  apply: Rle_trans Hty _.
  have Hscal : 2 * (u * (u * u)) <=
               (2 * (u * u * u) + 42 / 10 * (u * u * u * u)) * (1 - 2 * u)
    by nra.
  nra.
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

End TWAdd.
