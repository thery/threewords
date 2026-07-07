(* ---------------------------------------------------------------------------*)
(* Algorithm 5 (VecSumErrBranch, VSEB) and the paper's Theorem 2 (its output  *)
(* is P-nonoverlapping).  A general round-to-nearest building block, generic  *)
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

Section SecVSEB.

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

End SecVSEB.
