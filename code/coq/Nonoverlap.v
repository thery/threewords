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
Require Import Uls.

Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Nonoverlap.

Variable p : Z.
Variable emin : Z.
Hypothesis Hp2 : (1 < p)%Z.

Let beta := radix2.

Open Scope R_scope.

Local Instance p_gt_0 : Prec_gt_0 p.
Proof. now apply Z.lt_trans with (2 := Hp2). Qed.

Local Notation pow e := (bpow beta e).
Local Notation u := (u p beta).
Local Notation fexp := (FLT_exp emin p).
Local Notation format := (generic_format beta fexp).
Local Notation cexp := (cexp beta fexp).
Local Notation mant := (scaled_mantissa beta fexp).
Local Notation ulp := (ulp beta fexp).
Local Notation uls := (uls p emin).

(* [u = 2^-p] (generic form of the roundoff unit [/2 * 2^(1-p)]).             *)
Lemma uE : u = pow (- p).
Proof.
rewrite /u.
have -> : (1 - p = 1 + - p)%Z by lia.
by rewrite bpow_plus bpow_1 /=; lra.
Qed.

(* Sum of a sequence, used to state exactness of the building blocks.         *)
Fixpoint sumR (l : seq R) : R := if l is a :: l' then a + sumR l' else 0.

(* Sum of absolute values, for the VSEB block bound (Theorem 2).              *)
Fixpoint sumRabs (l : seq R) : R :=
  if l is a :: l' then Rabs a + sumRabs l' else 0.

Lemma sumRabs_ge0 l : 0 <= sumRabs l.
Proof. elim: l => /= [|a l IH]; first lra. by have := Rabs_pos a; lra. Qed.

Lemma abs_sumR_le l : Rabs (sumR l) <= sumRabs l.
Proof.
elim: l => /= [|a l IH]; first by rewrite Rabs_R0; lra.
by apply: Rle_trans (Rabs_triang _ _) _; lra.
Qed.

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
(* Zero-free reading (paper Def. 3, "WLOG no zeros"): each NONZERO term is at *)
(* most half the [uls] of the PREVIOUS nonzero term.  Formalised by carrying  *)
(* the last nonzero as [prev] and skipping zeros -- a zero imposes no         *)
(* constraint yet cannot shield a large successor, since the bound is against *)
(* the last nonzero, not the immediate predecessor.  (The old immediate-      *)
(* predecessor guard was too weak: it accepted [1; 0; 1.5].)                  *)
Fixpoint Fnonoverlap_aux (prev : R) (l : seq R) : Prop :=
  if l is x :: l' then
    (x <> 0 -> Rabs x <= / 2 * uls prev) /\
    Fnonoverlap_aux (if Req_EM_T x 0 then prev else x) l'
  else True.

Definition Fnonoverlap (l : seq R) : Prop :=
  if l is x :: l' then Fnonoverlap_aux x l' else True.

(* A zero next element is skipped (the vacuous conjunct drops, [prev] stays). *)
Lemma Fnonoverlap_aux_cons0 prev l :
  Fnonoverlap_aux prev (0 :: l) <-> Fnonoverlap_aux prev l.
Proof.
have E0 : (if Req_EM_T (0 : R) 0 then prev else 0) = prev.
  by case: (Req_EM_T 0 0) => [_|H] //; case: (H erefl).
rewrite /= E0; split; first by move=> [_ H].
move=> H; split; last exact: H.
by move=> H0; case: (H0 erefl).
Qed.

(* Prepend a nonzero [x] bounded by [1/2 uls prev].                           *)
Lemma Fnonoverlap_aux_consN prev x l :
  x <> 0 -> Rabs x <= / 2 * uls prev -> Fnonoverlap_aux x l ->
  Fnonoverlap_aux prev (x :: l).
Proof.
move=> xn0 xB Hl.
have Ex : (if Req_EM_T x 0 then prev else x) = x.
  by case: (Req_EM_T x 0) => [xe0|_] //; case: (xn0 xe0).
rewrite /= Ex; split; last exact: Hl.
by move=> _; exact: xB.
Qed.

(* [prev] enters only through [uls prev], monotonically: coarsening [prev]    *)
(* ([uls prev <= uls prev']) preserves [Fnonoverlap_aux].  Used by the VSEB   *)
(* step lemmas, where the running term is replaced by a coarser one.          *)
Lemma Fnonoverlap_aux_prev prev prev' l :
  uls prev <= uls prev' -> Fnonoverlap_aux prev l -> Fnonoverlap_aux prev' l.
Proof.
elim: l prev prev' => [|x l IH] prev prev' Hle //= [Hx Hrec]; split.
  by move=> xn0; apply: Rle_trans (Hx xn0) _; lra.
have [xe0|xne0] := Req_dec x 0.
  have E : forall v : R, (if Req_EM_T x 0 then v else x) = v.
    by move=> v; case: (Req_EM_T x 0) => [_|H] //; case: (H xe0).
  by rewrite !E in Hrec *; apply: IH Hrec.
have E : forall v : R, (if Req_EM_T x 0 then v else x) = x.
  by move=> v; case: (Req_EM_T x 0) => [xe0|_] //; case: (xne0 xe0).
by rewrite !E in Hrec *; apply: (IH x x) Hrec; apply: Rle_refl.
Qed.

(* Recover the immediate-successor bound (old guard form) from the recursive  *)
(* definition: for a nonzero [nth i], the next term is [<= 1/2 uls (nth i)].  *)
Lemma Fnonoverlap_aux_imm prev l i :
  Fnonoverlap_aux prev l -> (i.+1 < size l)%N -> nth 0 l i <> 0 ->
  Rabs (nth 0 l i.+1) <= / 2 * uls (nth 0 l i).
Proof.
elim: l prev i => [|x l IH] prev i //= [Hx Htl].
case: i => [|i]; last by move=> Hi Hn0; apply: (IH _ i Htl).
case: l IH Htl => [|y l'] IH //= Htl _ xn0.
have E : (if Req_EM_T x 0 then prev else x) = x.
  by case: (Req_EM_T x 0) => [xe0|_] //; case: (xn0 xe0).
rewrite E /= in Htl; case: Htl => Hy _.
have [ye0|yne0] := Req_dec y 0; last by apply: Hy.
rewrite ye0 Rabs_R0; have : 0 < uls x by apply: uls_gt_0.
lra.
Qed.

(* Head bound: the second element is at most [1/2 uls] of the first.          *)
Lemma Fnonoverlap_head2 a b l :
  Fnonoverlap (a :: b :: l) -> b <> 0 -> Rabs b <= / 2 * uls a.
Proof. by move=> [H _]. Qed.

(* Drop the [eps, e] prefix: the tail keeps [Fnonoverlap_aux] with [prev = e] *)
(* (when [e <> 0]).                                                           *)
Lemma Fnonoverlap_tail a b l :
  Fnonoverlap (a :: b :: l) -> b <> 0 -> Fnonoverlap_aux b l.
Proof.
move=> Fab bn0; have E : (if Req_EM_T b 0 then a else b) = b.
  by case: (Req_EM_T b 0) => [be0|_] //; case: (bn0 be0).
by move: Fab; rewrite /= E => -[_].
Qed.

Lemma Fnonoverlap_imm l : Fnonoverlap l ->
  forall i, (i.+1 < size l)%N -> nth 0 l i <> 0 ->
    Rabs (nth 0 l i.+1) <= / 2 * uls (nth 0 l i).
Proof.
case: l => // x l Hl [|i] /=; last first.
  by move=> Hi Hn0; apply: (Fnonoverlap_aux_imm Hl Hi Hn0).
case: l Hl => [|y l'] //= Hl _ _.
case: Hl => Hy _.
have [ye0|yne0] := Req_dec y 0; last by apply: Hy.
rewrite ye0 Rabs_R0; have Hu : 0 < uls x by apply: uls_gt_0.
lra.
Qed.

(* VSEB block sum bound (Theorem 2): the terms after the remainder [prev]     *)
(* contribute at most [uls prev] in total, decaying geometrically.  Each      *)
(* nonzero head [x] has [|x| <= 1/2 uls prev] and [uls x <= |x|], so          *)
(* [|x| + (tail bound relative to uls x)] telescopes to [uls prev(1 - 2^-s)]. *)
(* Every FLT float is an integer multiple of the smallest quantum [pow emin]  *)
(* ([cexp z >= emin]).                                                        *)
Lemma is_imul_pow_emin z : format z -> is_imul z (pow emin).
Proof.
move=> zF; apply: (is_imul_pow_le (format_imul_cexp zF)).
by rewrite /cexp /FLT_exp; lia.
Qed.

(* Hence a sum of absolute values is a multiple of [pow emin].                *)
Lemma sumRabs_imul l :
  {in l, forall z, format z} -> is_imul (sumRabs l) (pow emin).
Proof.
elim: l => /= [_|a l IH lF]; first by exists 0%Z; rewrite Rmult_0_l.
apply: is_imul_add; last by apply: IH => z zl; apply: lF; rewrite inE zl orbT.
have Fa : format a by apply: lF; rewrite inE eqxx.
have [az|az] := Rle_dec 0 a.
  by rewrite Rabs_pos_eq //; apply: is_imul_pow_emin.
by rewrite Rabs_left; [apply/is_imul_opp/is_imul_pow_emin|lra].
Qed.

(* A nonnegative multiple of [pow emin] that is [< pow N] is [<= pow N - pow  *)
(* emin] (the largest such multiple): the near-underflow block bound.         *)
Lemma sumRabs_lt_le N l :
  {in l, forall z, format z} -> (emin <= N)%Z -> sumRabs l < pow N ->
  sumRabs l <= pow N - pow emin.
Proof.
move=> lF HN Hlt; have [k Hk] := sumRabs_imul lF; rewrite Hk in Hlt *.
have He : 0 < pow emin by apply: bpow_gt_0.
have HNe : pow N = IZR (2 ^ (N - emin)) * pow emin.
  have -> : (2 = radix2 :> Z)%Z by [].
  by rewrite IZR_Zpower; [rewrite -bpow_plus; congr bpow; lia | lia].
have Hklt : IZR k < IZR (2 ^ (N - emin)).
  by apply: (Rmult_lt_reg_r (pow emin)); [exact: He | rewrite -HNe].
have Hkle : (k <= 2 ^ (N - emin) - 1)%Z by have := lt_IZR _ _ Hklt; lia.
rewrite HNe; apply: Rle_trans (_ : IZR (2 ^ (N - emin) - 1) * pow emin <= _).
  by apply: Rmult_le_compat_r; [lra | apply: IZR_le].
by rewrite minus_IZR; lra.
Qed.

Lemma Fnonoverlap_aux_sumRabs prev l :
  Fnonoverlap_aux prev l -> {in l, forall z, format z} ->
  sumRabs l <= uls prev * (1 - (/ 2) ^ (size l)).
Proof.
elim: l prev => [|x l IH] prev; first by move=> _ _ /=; lra.
move=> Hf xlF.
have xF : format x by apply: xlF; rewrite inE eqxx.
have lF : {in l, forall z, format z}.
  by move=> z zl; apply: xlF; rewrite inE zl orbT.
have Hup : 0 < uls prev by apply: uls_gt_0.
have Hd0 : 0 < (/ 2) ^ (size l) by apply: pow_lt; lra.
have Hd1 : (/ 2) ^ (size l) <= 1.
  by rewrite -(pow1 (size l)); apply: pow_incr; lra.
have [xe0|xne0] := Req_dec x 0.
  rewrite /= xe0 Rabs_R0 Rplus_0_l.
  have Hrec : Fnonoverlap_aux prev l.
    by move: Hf; rewrite xe0 => /Fnonoverlap_aux_cons0.
  by apply: Rle_trans (IH prev Hrec lF) _; nra.
rewrite /=.
have Hx : Rabs x <= / 2 * uls prev by move: Hf => [/(_ xne0)].
have Ex : (if Req_EM_T x 0 then prev else x) = x.
  by case: (Req_EM_T x 0) => [xe0|_] //; case: (xne0 xe0).
have Hrec : Fnonoverlap_aux x l by move: Hf => [_]; rewrite Ex.
have Hux : uls x <= Rabs x by apply: uls_le_abs.
apply: Rle_trans (_ : Rabs x + uls x * (1 - (/ 2) ^ (size l)) <= _).
  by have := IH x Hrec lF; lra.
by nra.
Qed.

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

End Nonoverlap.
