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

Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section TWAdd.

Let p := 53%Z.
Let emax := 1024%Z.
Let emin := (3 - emax - p)%Z.

Let beta := radix2.

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

(* Following paper3, the whole development is under round-to-nearest        *)
(* (ties broken by [choice]): the paper sets RN(.) as its standing rounding *)
(* mode in the preliminaries and writes every operation as RN(...).  This   *)
(* is needed for the error-free transforms (e.g. 2Sum is exact and its low  *)
(* word is bounded by half an ulp) -- a generic [Valid_rnd] is too weak.    *)
Variable choice : Z -> bool.
(* Ties broken to even (the symmetry [RN(-t) = -RN(t)]); required by         *)
(* Flocq's [TwoSum_correct].                                                 *)
Hypothesis choice_sym : forall x, choice x = ~~ choice (- (x + 1))%Z.
Let rnd : R -> Z := Znearest choice.
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
Local Notation fastTwoSum := (fastTwoSum beta emin p rnd).
(* Round-to-nearest half-ulp error bound with this section's format and tie- *)
(* breaking pre-applied: [error_le_half_ulp_RN x : Prec_gt_0 p -> ...].      *)
Local Notation error_le_half_ulp_RN :=
  (@error_le_half_ulp_round beta (FLT_exp emin p)
     (FLT_exp_valid emin p) (FLT_exp_monotone emin p) choice).
(* Flocq's [TwoSum_correct] with this section's parameters and hypotheses    *)
(* pre-applied: [TwoSum_correct_RN x y : format x -> format y -> ...].        *)
Local Notation TwoSum_correct_RN :=
  (@TwoSum_correct emin p choice Hp2 emin_le_0 choice_sym).

(* ===========================================================================*)
(*  Basic error-free transforms                                               *)
(* ===========================================================================*)

(* Algorithm 2 of the paper: the 6-operation 2Sum.  Always exact:             *)
(*   s + e = a + b, with no assumption on the magnitudes of a and b.          *)
Definition TwoSum (a b : R) : dwR :=
  let s  := RND (a + b) in
  let a' := RND (s - b) in
  let b' := RND (s - a') in
  let da := RND (a - a') in
  let db := RND (b - b') in
  DWR s (RND (da + db)).

Definition formatDWR (a : dwR) := let: DWR b c := a in format b /\ format c.

Lemma format_TwoSum a b : format a -> format b -> formatDWR (TwoSum a b).
Proof. by move=> Fa Fb; split; try apply: generic_format_round. Qed.

(* The magnitude counterpart of [formatDWR]: in a 2Sum result [DWR s e]   *)
(* the error word [e] is at most half an ulp of the high word [s].        *)
Definition magnitudeDWR (a : dwR) := let: DWR s e := a in Rabs e <= ulp s / 2.

(* 2Sum is error-free: s + e = a + b.  We reuse Flocq's [TwoSum_correct]  *)
(* (the Pff bridge), instantiated with the operands SWAPPED: paper3's      *)
(* Algorithm 2 subtracts [b] first, whereas Flocq's variant subtracts its  *)
(* first argument first, so [TwoSum_correct b a] has exactly our           *)
(* intermediate values (up to commutativity of [+]).                       *)
Lemma TwoSum_correct_loc a b : format a -> format b ->
  let: DWR s e := TwoSum a b in s + e = a + b.
Proof.
move=> Fa Fb.
have := TwoSum_correct_RN b a Fb Fa.
rewrite -[radix2]/beta -[Znearest _]/rnd (Rplus_comm b a) /=.
set DA := RND (a - _); set DB := RND (b - _).
by rewrite (Rplus_comm DA DB).
Qed.

(* Magnitude analogue of [format_TwoSum] (Algorithm 2): the low word of a  *)
(* 2Sum is bounded by half an ulp of its high word.  Combine exactness     *)
(* [e = (a+b) - s] with the round-to-nearest bound |RN(x)-x| <= ulp(RN x)/2.*)
Lemma magnitude_TwoSum a b :
  format a -> format b -> magnitudeDWR (TwoSum a b).
Proof.
move=> Fa Fb.
have Hc := TwoSum_correct_loc Fa Fb.
move: Hc; rewrite /magnitudeDWR /TwoSum /=.
set s := RND (a + b).
set e := RND (RND (a - _) + RND (b - _)).
move=> Hc.
have He : e = a + b - s by lra.
rewrite He Rabs_minus_sym.
have /(_ p_gt_0) Hh := error_le_half_ulp_RN (a + b).
rewrite -[Znearest _]/rnd -/s in Hh.
lra.
Qed.

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

Definition TWval (x : twR) : R := let: TWR x0 x1 x2 := x in x0 + x1 + x2.

(* Sum of a sequence, used to state exactness of the building blocks.         *)
Fixpoint sumR (l : seq R) : R := if l is a :: l' then a + sumR l' else 0.

(* P-nonoverlapping (Priest, Definition 1): |x_{i+1}| < ulp (x_i).            *)
Definition Pnonoverlap (l : seq R) : Prop :=
  forall i, (i.+1 < size l)%N -> Rabs (nth 0 l i.+1) < ulp (nth 0 l i).

(* Dropping the head of a P-nonoverlapping sequence keeps it P-nonoverlapping. *)
Lemma Pnonoverlap_cons a l : Pnonoverlap (a :: l) -> Pnonoverlap l.
Proof. by move=> alP i iLs; apply: (alP i.+1). Qed.

(* The two preconditions of Theorem 6 on the merged sequence.                 *)

(* --- magnitude order ----------------------------------------------------- *)
(* [sorted_mag l]: the sequence is non-increasing in magnitude.               *)
Definition sorted_mag (l : seq R) : Prop :=
  forall i, (i.+1 < size l)%N -> Rabs (nth 0 l i.+1) <= Rabs (nth 0 l i).

(* Peel the head of a [sorted_mag] sequence: the first step plus the tail.     *)
Lemma sorted_mag_cons a1 a2 l :
  sorted_mag [:: a1,  a2 & l] -> Rabs a2 <= Rabs a1 /\ sorted_mag (a2 :: l).
Proof.
move=> a1a2lM; split; first by apply: (a1a2lM 0%N).
by move=> n Hn; apply: (a1a2lM n.+1).
Qed.

(* Cons a larger-magnitude head onto a [sorted_mag] sequence.                  *)
Lemma sorted_mag_cons_inv a1 a2 l :
  Rabs a2 <= Rabs a1 -> sorted_mag (a2 :: l) -> sorted_mag [:: a1,  a2 & l].
Proof. by move=> a2La1 a2lN [//|i Hi]; apply: (a2lN i). Qed.

(* Replace the head by an even larger one (still [sorted_mag]).                *)
Lemma sorted_mag_le a1 a2 l :
  sorted_mag (a1 :: l) -> Rabs a1 <= Rabs a2 -> sorted_mag (a2 :: l).
Proof.
case: l => // a3 l /sorted_mag_cons[a1La3 a3lS] a1La2.
by apply: sorted_mag_cons_inv => //; lra.
Qed.

(* --- pairwise ulp separation --------------------------------------------- *)
(* [pairwise_ulp l]: each term is below ulp of the term two positions before; *)
(* this tolerates a single overlap but never two in a row.                    *)
Definition pairwise_ulp (l : seq R) : Prop :=
  forall i, (i.+2 < size l)%N -> Rabs (nth 0 l i.+2) < ulp (nth 0 l i).

(* Peel the head: the third-term bound [Rabs a3 < ulp a1] plus the tail.       *)
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

(* [ulp] is strictly positive everywhere: at 0 it is [bpow emin] (FLT), and    *)
(* elsewhere [bpow (cexp _)].                                                   *)
Lemma ulp_gt_0 x : 0 < ulp x.
Proof.
have [->|xn0] := Req_dec x 0; first by rewrite ulp_FLT_0; apply: bpow_gt_0.
by rewrite ulp_neq_0 //; apply: bpow_gt_0.
Qed.

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

(* The three limbs of a triple-word are floating-point numbers (part of Def. 5). *)
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

(* Merge is a permutation of its two inputs, so it preserves the exact sum.    *)
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
  case E1 : TwoSum => [si ei1] => sF esF.
  have := @format_TwoSum a s => //.
  rewrite E1; case => //.
  by apply: ablF; rewrite inE eqxx.
have /IH[] :  {in b :: l,  forall z : R, format z}.
  by move=> z zIl; apply: ablF; rewrite inE zIl orbT.
  rewrite vecSumAux_cons.
case E : vecSumAux => [es s].
case E1 : TwoSum => [si ei1] => sF esF.
move=> z; rewrite inE => /orP[/eqP->|zIes].
  have := @format_TwoSum a s => //.
  rewrite E1; case => //.
  by apply: ablF; rewrite inE eqxx.
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
case E1 : TwoSum => [si ei1] /=.
have := @TwoSum_correct_loc a s.
rewrite E1 -Rplus_assoc => -> //.
- by rewrite Rplus_assoc ssE.
- by apply: ablF; rewrite inE eqxx.
case: (@format_vecSumAux (b :: l)) => [z zIl|].
  by apply: ablF; rewrite inE zIl !orbT.
by rewrite E.
Qed.

(* Two definitional unfoldings of [vsebAux] (by reflexivity), mirroring        *)
(* [vecSumAux_cons]: they expose [TwoSum eps e] so the following [case] can     *)
(* capture it in the goal, keeping the low words as the very variables that     *)
(* [TwoSum_correct_loc] talks about (otherwise [simpl] re-expands them to       *)
(* [RND ...] and the correctness fact no longer applies).                       *)
Lemma vsebAux_1 eps e :
  vsebAux eps [:: e] = let: DWR y0 y1 := TwoSum eps e in [:: y0; y1].
Proof. by []. Qed.

Lemma vsebAux_consS eps e e2 l :
  vsebAux eps [:: e, e2 & l] =
  let: DWR r et := TwoSum eps e in
  if Req_EM_T et 0 then vsebAux r (e2 :: l) else r :: vsebAux et (e2 :: l).
Proof. by []. Qed.

(* VSEB is error-free: [vsebAux] preserves the exact sum, prefix [eps]         *)
(* included.  Each step is a [TwoSum] (exact by [TwoSum_correct_loc]); whether *)
(* the error [et] is dropped ([et = 0], so [r = eps + e]) or emitted, the sum  *)
(* [eps + sumR l] is preserved.                                                *)
Lemma vsebAux_sum eps l :
  format eps -> {in l, forall z, format z} ->
  sumR (vsebAux eps l) = eps + sumR l.
Proof.
elim: l eps => [|e l IH] eps epsF lF.
  by rewrite /=; lra.
have eF : format e by apply: lF; rewrite inE eqxx.
case: l IH lF => [|e2 l'] IH lF.
  rewrite vsebAux_1; case E1 : (TwoSum eps e) => [y0 y1].
  move: (@TwoSum_correct_loc eps e epsF eF); rewrite E1 /= => Cc.
  by lra.
rewrite vsebAux_consS; case E1 : (TwoSum eps e) => [r et].
move: (@TwoSum_correct_loc eps e epsF eF); rewrite E1 /= => Cc.
move: (@format_TwoSum eps e epsF eF); rewrite E1 /= => -[rF etF].
have l'F : {in e2 :: l', forall z, format z}.
  by move=> z zIl; apply: lF; rewrite inE zIl orbT.
case: Req_EM_T => [et0|etn0].
  by rewrite (IH r rF l'F) /=; lra.
by rewrite /= (IH et etF l'F) /=; lra.
Qed.

(* VSEB preserves the exact sum (Theorem 2, sum part): [sumR (vseb l) = sumR l].*)
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

(* [uls x] -- "unit in the last significant place": the weight of the         *)
(* RIGHTMOST NONZERO bit of [x].  ([ulp x = 2^(cexp x)] is the weight of the   *)
(* last *representable* place -- the grid spacing; the weight of the leftmost  *)
(* bit is [ufp x], the other extreme.)  If [x = m * 2^(cexp x)] with           *)
(* [m = Ztrunc (mant x)] the integer mantissa, then [uls x = 2^(cexp x + v2 m)]*)
(* where [v2 m] is the 2-adic valuation of [m] -- here [trZ m], the count of   *)
(* trailing binary zeros of [m], built from [trP] on the positive part below.  *)
(* Hence [uls x = ulp x * 2^(v2 m) >= ulp x] (lemma [ulp_le_ulps]), equality   *)
(* iff the mantissa is odd -- e.g. for [x = -1.01101_2 * 2^364] the paper has  *)
(* [ulp x = 2^312] but [uls x = 2^359].  At [x = 0] we set [uls 0 = ulp 0].    *)

(* [trP p] : number of trailing binary zeros of the positive [p] (its 2-adic  *)
(* valuation).                                                                 *)
Fixpoint trP (p : positive) := if p is xO p1 then (trP p1).+1 else 0%N.

(* [two_power_pos n] : [2^n] as a positive.                                    *)
Definition two_power_pos n := iter n xO 1%positive.

(* [2^(trP p)] divides [p] (i.e. [trP p] trailing zeros can be factored out).  *)
Lemma trPE p1 : (two_power_pos (trP p1) | p1)%positive.
Proof.
have div1 q : (1 | q)%positive by exists q; rewrite Pos.mul_comm.
elim: p1 => //= p1 [q {2}->] /=; exists q; lia.
Qed.

(* [trZ z] : 2-adic valuation of [z] (its trailing binary zeros), [0] at [0];  *)
(* it ignores the sign, using [trP] on the positive part.                      *)
Definition trZ (z : Z) := if z is Zpos p1 then (trP p1) else
                          if z is Zneg p1 then (trP p1) else 0%N.

Lemma trZ0 : trZ 0 = 0%N.
Proof. by []. Qed.

Lemma two_power_nat_pos n : (Zpos (two_power_pos n) = two_power_nat n)%Z.
Proof. by elim: n. Qed.

(* [2^(trZ z)] divides [z]: the valuation really is extractable.               *)
Lemma trZE p1 : (2 ^ Z.of_nat (trZ p1) | p1)%Z.
Proof.
rewrite -two_power_nat_equiv.
case: p1 => [|p1|p1]; first by apply: Z.divide_0_r.
  by rewrite -two_power_nat_pos /=; apply/Z.divide_Zpos/trPE.
rewrite -two_power_nat_pos /=.
by apply/Z.divide_Zpos_Zneg_r/Z.divide_Zpos/trPE.
Qed.

(* uls, as documented above: [ulp 0] at zero, else [2^(cexp x + v2(mantissa))].*)
Definition uls (x : R) : R :=
  if Req_bool x 0 then ulp 0 else
  let m := Ztrunc (mant x) in pow (cexp x + Z.of_nat (trZ m))%Z.

Lemma uls0 : uls 0 = ulp 0.
Proof. by rewrite /uls; case: Req_bool_spec. Qed.

(* [x] factors as (its odd mantissa part) * [uls x] -- the defining property   *)
(* of [uls] as the weight of the rightmost nonzero bit.                        *)
Lemma ulsE x :
 format x -> 
 x = IZR (Ztrunc (mant x) / (2 ^ Z.of_nat (trZ (Ztrunc (mant x)))))%Z * uls x.
Proof.
move=> xF; rewrite /uls.
case: (Req_bool_spec x 0) => [->|x_neq0].
  by rewrite scaled_mantissa_0 Ztrunc_IZR Rmult_0_l.
rewrite -[X in X = _](scaled_mantissa_mult_bpow beta fexp) bpow_plus.
rewrite -[X in _ = _ * (_ * X)]IZR_Zpower; last by lia.
rewrite [X in _ = _ * X]Rmult_comm -[RHS]Rmult_assoc -mult_IZR.
rewrite Zmult_comm -Znumtheory.Zdivide_Zdiv_eq.
- by rewrite -scaled_mantissa_generic //.
- by apply: Zpower_gt_0; lia.
by apply: trZE.
Qed.

(* [ulp x <= uls x]: the rightmost nonzero bit is at or above the last place.  *)
Lemma ulp_le_ulps x : ulp x <= uls x.
Proof.
rewrite /uls.
case: Req_bool_spec => [->//|x_neq0]; first by lra.
rewrite ulp_neq_0 //;apply: bpow_le; lia.
Qed.

(* [ufp x] -- "unit in the first place": the weight [2^(mag x - 1)] of the     *)
(* leftmost bit, i.e. the largest power of two <= |x| (for x <> 0).  Paper     *)
(* Theorem 1 / Corollary 1 (p.3) state the VecSum input conditions with it.    *)
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
have -> : (2 = IZR beta)%R by rewrite /beta /=; lra.
by rewrite -bpow_plus_1; congr bpow; lia.
Qed.

(* Definition 2 (Fabiano): [l] is F-nonoverlapping when each term is at most  *)
(* half the [uls] of its predecessor.  This is Fabiano's separation (more     *)
(* restrictive than Shewchuk's ulp-nonoverlapping); it is the invariant that  *)
(* VecSum establishes (Thm 1) and that VSEB consumes (Thm 2) to yield a       *)
(* P-nonoverlapping output.                                                   *)
(* This is the "with interleaving zeros" form (paper Def. 3): the bound is    *)
(* required only across a NONZERO predecessor [nth 0 l i <> 0], so a zero      *)
(* error term (e.g. an exact [2Sum]) imposes no constraint on its successor.  *)
(* Without this guard the statement is false: at a zero predecessor the RHS    *)
(* would be [/2 * uls 0 = 2^(emin-1)], unreachable by a normal-sized term.     *)
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
(*  [sorted_mag]+[pairwise_ulp]; this block states Theorem 1 with the paper's  *)
(*  actual [k_i] exponent hypotheses, and the proof steps it goes through.     *)
(* ===========================================================================*)

(* Paper representation: [x = M * 2^(k-p+1)] with [|M| < 2^p], [M] an integer  *)
(* and the exponent [k] chosen (not necessarily canonical).  We also require    *)
(* [emin <= k - p + 1] so that [x] genuinely lands on the FLT grid -- without   *)
(* it [x = 2^(emin-1)] (M = 1, k = emin+p-2) satisfies the equation but is not  *)
(* a float.  The paper's x_i are floats, so this is the intended reading.       *)
Definition repr (k : Z) (x : R) : Prop :=
  (emin <= k - p + 1)%Z /\
  exists2 M : Z, (Z.abs M < 2 ^ p)%Z & x = IZR M * pow (k - p + 1)%Z.

(* Being [repr]-esentable at [k] makes [x] an FLT float: it is [F2R] of the     *)
(* integer float [Float M (k-p+1)], whose mantissa is < 2^p and whose exponent  *)
(* is >= emin.                                                                  *)
Lemma repr_format k x : repr k x -> format x.
Proof.
move=> [Hemin [M Mlt ->]].
apply: generic_format_FLT; exists (Float beta M (k - p + 1)%Z).
- by rewrite /F2R.
- exact: Mlt.
exact: Hemin.
Qed.

(* Hypotheses of Theorem 1 on inputs [l] with a chosen exponent map [k]:        *)
(*  - every [x_i] is representable at exponent [k_i];                           *)
(*  - [k_{i-1} >= k_i + 1] for every pair but the last (strict exponent gap);   *)
(*  - [k_{n-2} >= k_{n-1}] for the last pair (weak gap -- the allowed overlap). *)
Definition Thm1_hyp (k : nat -> Z) (l : seq R) : Prop :=
  [/\ forall i, (i < size l)%N -> repr (k i) (nth 0 l i),
      forall i, (i.+2 < size l)%N -> (k i.+1 + 1 <= k i)%Z &
      forall i, i.+2 = size l -> (k i.+1 <= k i)%Z ].

(* Paper "Firstly": the running high word [s_{i+1} = (vecSumAux (drop i.+1 l)).2]*)
(* is bounded by [(2-2u) 2^(k_i)].  (The paper writes |s_i| <= (2-2u)2^(k_{i-1});*)
(* we index by the *previous* position [i] to avoid [k_{-1}], which is exactly   *)
(* the induction-hypothesis form used in the proof.)                            *)
Lemma VecSum_run_bound k l : Thm1_hyp k l ->
  forall i, (i.+1 < size l)%N ->
  Rabs (vecSumAux (drop i.+1 l)).2 <= (2 - 2 * u) * pow (k i).
Proof.
case=> Hrepr Hgap Hlast.
(* Each input is bounded: |x_j| = |M_j| 2^(k_j-p+1) <= (2^p-1) 2^(k_j-p+1)       *)
(*                              = (2 - 2u) 2^(k_j).                              *)
have Hx : forall j, (j < size l)%N -> Rabs (nth 0 l j) <= (2 - 2 * u) * pow (k j)
  by admit.
(* Downward induction on the suffix.  [s_{i+1} = (vecSumAux (drop i.+1 l)).2]:   *)
(*  - base [i.+2 = size l]: [s_{i+1} = x_{i+1}], and                            *)
(*      |x_{i+1}| <= (2-2u) 2^(k_{i+1}) <= (2-2u) 2^(k_i)                        *)
(*    by the weak gap [k_i >= k_{i+1}] (Hlast);                                 *)
(*  - step [i.+2 < size l]: [s_{i+1} = RN(x_{i+1} + s_{i+2})]; with the IH        *)
(*      |s_{i+2}| <= (2-2u) 2^(k_{i+1}) and |x_{i+1}| <= (2-2u) 2^(k_{i+1}),     *)
(*      |x_{i+1}| + |s_{i+2}| <= (4-4u) 2^(k_{i+1}) <= (2-2u) 2^(k_i)           *)
(*    by the strict gap [k_i >= k_{i+1} + 1] (Hgap), and rounding to nearest     *)
(*    preserves the bound.                                                       *)
admit.
Admitted.

(* Theorem 1.  [VecSum l] is F-nonoverlapping (wIZ) with the same sum.          *)
(* Proof (paper Section 2.1): [VecSum_run_bound] gives the running-sum bound,   *)
(* whence each error [|e_i| <= 2 u^2 2^(k_i-1)]; the errors are then            *)
(* F-nonoverlapping by the "multiples of 2u" ([uls]) argument, which           *)
(* contradicts any overlap [|e_i| >= 1/2 uls(e_{i'})].                          *)
Lemma VecSum_Thm1 k l : Thm1_hyp k l ->
  Fnonoverlap (vecSum l) /\ sumR (vecSum l) = sumR l.
Proof.
move=> Hk.
(* Each [x_i = M_i 2^(k_i-p+1)] with [|M_i| < 2^p] is an FLT float ([repr_format]). *)
have Hfmt : {in l, forall z, format z}.
  case: Hk => Hrepr _ _ z /(nthP 0)[i iLs <-].
  exact: repr_format (Hrepr i iLs).
(* "with the same sum": VecSum is a chain of error-free 2Sums (Algorithm 4).   *)
split; last by apply: vecSum_sum.
(* Firstly (paper): the running high word [s_{i+1} = (vecSumAux (drop i.+1 l)).2]*)
(* is bounded, |s_{i+1}| <= (2 - 2u) 2^(k_i), by induction on the suffix using  *)
(*   |s_{i+2}| + |x_{i+1}| <= (4 - 4u) 2^(k_{i+1}) <= (2 - 2u) 2^(k_i).         *)
have Hrun := VecSum_run_bound Hk.
(* This gives the error bound |e_{i+1}| <= 2 u^2 2^(k_i) (justifies Fast2Sum).  *)
have Herr : forall i, (i.+1 < size l)%N ->
    Rabs (nth 0 (vecSum l) i.+1) <= 2 * (u * u) * pow (k i) by admit.
(* F-nonoverlapping (paper, by contradiction).                                 *)
move=> i iLs Hn0.
suff : ~ (/ 2 * uls (nth 0 (vecSum l) i) < Rabs (nth 0 (vecSum l) i.+1)) by lra.
move=> Hover.
(* Scale so that uls(e_i) = u.  Then [s_j] and [x_0, ..., x_i] are all          *)
(* multiples of 2u, so the offending [e_i] (a non-multiple of 2u) forces the    *)
(* exponent small: 2^(k_{i-1}) <= 1/2, hence 2^(k_i) <= 1/4,                    *)
have Hpow : pow (k i) <= / 4 by admit.
(* which contradicts the error bound [Herr i] together with [Hover].           *)
admit.
Admitted.

(* The genuinely hard step of Theorem 1 (the paper's [k_i] exponent argument). *)
(* When [2Sum a s] produces a NONZERO low word [ei1], the head of the already- *)
(* normalised tail [es] stays below [1/2 uls ei1].  Intuition: the low word    *)
(* carries [s]'s rightmost bit ([a] and the high word are coarser), so         *)
(* [uls s <= uls ei1]; combine with [Fnonoverlap (s :: es)] at index 0         *)
(* ([Rabs (nth 0 es 0) <= 1/2 uls s]).  Left admitted for now -- this is the   *)
(* remaining mathematical content of Theorem 1.                                *)
Lemma Fnonoverlap_head a s es :
  format a -> format s -> Fnonoverlap (s :: es) -> (0 < size es)%N ->
  let: DWR _ ei1 := TwoSum a s in
  ei1 <> 0 -> Rabs (nth 0 es 0) <= / 2 * uls ei1.
Proof.
Admitted.

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
  by have := ulp_le_ulps si; lra.
- have Hsz : (0 < size es)%N by move: iLs; case: (size es).
  have H := Fnonoverlap_head aF sF sesF; rewrite E1 in H.
  exact: (H Hsz Hn0).
by apply: (sesF i.+1).
Qed.

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
Lemma vseb_Pnonoverlap e :
  (Z.of_nat (size e) <= p + 1)%Z ->
  {in e, forall z, format z} -> Fnonoverlap e ->
  Pnonoverlap (vseb e) /\ sumR (vseb e) = sumR e.
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
(* yields a triple-word number.  Case on the (<=3, zero-padded) list [vsebK    *)
(* 3 e]; formats come from [Hr_format], the strict ulp bounds from either      *)
(* [Hr_nonover] (real terms) or [0 < ulp _] (the padding zeros).               *)
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
  Rabs (sumR (vseb e) - sumR (vsebK 3 e)) <= errc * Rabs (sumR e) by admit.
(* The result of TWSum is exactly the value of those three terms.  [vsebK 3 e] *)
(* has length <= 3 (it is a [take 3]); TWSum reads its (zero-padded) first      *)
(* three entries, whose sum is exactly [sumR (vsebK 3 e)].                      *)
have Hres : TWval (TWSum (TWR x0 x1 x2) (TWR y0 y1 y2)) = sumR (vsebK 3 e).
  have Hsz : (size (vsebK 3 e) <= 3)%N.
    rewrite /vsebK size_take; case: ifP => [_|Hf]; first by [].
    by rewrite leqNgt Hf.
  rewrite /TWSum -/z -/e.
  move: Hsz; case: (vsebK 3 e) => [|r0 [|r1 [|r2 [|r3 l]]]] /= H; try by lra.
  by exfalso; move/leP: H; lia.
(* Chaining the equalities and the truncation bound concludes.  Both operands  *)
(* sum to [sumR (vseb e)] (Merge/VecSum/VSEB preserve the sum), the result is   *)
(* [sumR (vsebK 3 e)] (Hres), so the error is the dropped tail bounded by       *)
(* [Htrunc].                                                                    *)
have E1 : TWval (TWR x0 x1 x2) + TWval (TWR y0 y1 y2) = sumR (vseb e).
  by rewrite /= Hvseb_sum Hvec_sum Hmerge_sum.
rewrite Hres E1 Rabs_minus_sym {2}Hvseb_sum.
exact: Htrunc.
Admitted.

End TWAdd.
