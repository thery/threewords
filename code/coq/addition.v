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

Local Notation float := (float
 radix2).
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

(* The two preconditions of Theorem 6 on the merged sequence.                 *)
Definition sorted_mag (l : seq R) : Prop :=
  forall i, (i.+1 < size l)%N -> Rabs (nth 0 l i.+1) <= Rabs (nth 0 l i).
Definition pairwise_ulp (l : seq R) : Prop :=
  forall i, (i.+2 < size l)%N -> Rabs (nth 0 l i.+2) < ulp (nth 0 l i).

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
(* Depends on (all from Flocq.Core, already imported via [Core]):              *)
(*   - [ulp_FLT_0]    : ulp 0 = bpow emin   (Flocq.Core.FLT)                   *)
(*   - [ulp_ge_ulp_0] : Exp_not_FTZ fexp -> ulp 0 <= ulp y   (Flocq.Core.Ulp) *)
(*   - [ulp_le_abs]   : y <> 0 -> format y -> ulp y <= Rabs y (Flocq.Core.Ulp)*)
(*   the [Exp_not_FTZ (FLT_exp emin p)] instance comes from                    *)
(*   [FLT_exp_monotone] + [monotone_exp_not_FTZ].                              *)
Lemma format_lt_ulp_0 y : format y -> Rabs y < ulp 0 -> y = 0.
Proof.
move=> yF yLu.
suff : ~ (0 < Rabs y) by split_Rabs; lra.
move=> ay_gt0.
have ayF : format (Rabs y) by apply: generic_format_abs.
have pLw : pow emin <= Rabs y by apply: alpha_LB ayF _.
rewrite ulp_FLT_0 in yLu; lra.
Qed.

(* P-nonoverlap separation implies magnitude order, zeros included.            *)
(* Depends on:                                                                 *)
(*   - [ulp_le_abs] : x <> 0 -> format x -> ulp x <= Rabs x  (Flocq.Core.Ulp)  *)
(*     for the x <> 0 case (then Rabs y < ulp x <= Rabs x);                    *)
(*   - [ulp_FLT_0] + [format_lt_ulp_0] above for the x = 0 case (then y = 0).  *)
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

(* The merge precondition for a single TW: its three limbs are magnitude-      *)
(* sorted.  Two applications of [format_lt_ulp_le] to the [isTW] conjuncts.    *)
Lemma isTW_sorted_mag x : isTW x ->
  let: TWR x0 x1 x2 := x in Rabs x1 <= Rabs x0 /\ Rabs x2 <= Rabs x1.
Proof.
by case : x => x0 x1 x2 [x0F x1F x2F x1Lux0 x2Lux1]; 
   split; apply: format_lt_ulp_le.
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
have Hz_sorted : sorted_mag z by admit.
(* ... and pairwise ulp-separated: the hypotheses of Theorem 6.               *)
have Hz_ulp : pairwise_ulp z by admit.
(* VecSum preserves the exact sum (Algorithm 4 is error-free).                *)
have He_sum : sumR e = sumR z by admit.
(* VSEB(3) of VecSum is P-nonoverlapping (Theorems 1, 2 and 6).               *)
have Hr_nonover : Pnonoverlap (vsebK 3 e) by admit.
(* and its terms are floating-point numbers.                                  *)
have Hr_format : {in vsebK 3 e, forall t, format t}.
  by apply/format_vsebK/format_vecSum.
(* Reading the first three terms off the P-nonoverlapping sequence            *)
(* yields a triple-word number.                                               *)
admit.
Admitted.

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
have Hmerge_sum : sumR z = (x0 + x1 + x2) + (y0 + y1 + y2) by admit.
(* VecSum is error-free.                                                      *)
have Hvec_sum : sumR e = sumR z by admit.
(* VSEB is error-free on the full output.                                     *)
have Hvseb_sum : sumR (vseb e) = sumR e by admit.
(* Truncating to the first three terms loses at most errc of the sum          *)
(* (Theorem 3 with k = 3).                                                    *)
have Htrunc :
  Rabs (sumR (vseb e) - sumR (vsebK 3 e)) <= errc * Rabs (sumR e) by admit.
(* The result of TWSum is exactly the value of those three terms.             *)
have Hres : TWval (TWSum (TWR x0 x1 x2) (TWR y0 y1 y2)) = sumR (vsebK 3 e)
  by admit.
(* Chaining the four equalities and the truncation bound concludes.           *)
admit.
Admitted.

End TWAdd.
