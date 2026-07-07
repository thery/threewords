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

(* [p] is symbolic here (concrete only in [addition.v]), so the base-2 power  *)
(* identity that used to hold by computation needs [IZR_Zpower] ([0 <= p]).   *)
Lemma IZR_2powp : IZR (2 ^ p) = pow p.
Proof.
have -> : (2 = radix2 :> Z)%Z by [].
by rewrite IZR_Zpower //; lia.
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

(* Divisibility propagation -- the induction step of paper Thm 1 ("if"        *)
(* "2^k | s_i, x_{i-1}, ..., x_0 then 2^k | e_i, ..., e_0"). If every input   *)
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

(* [ufp x] -- "unit in the first place": the weight [2^(mag x - 1)] of the    *)
(* leftmost bit, i.e. the largest power of two <= |x| (for x <> 0).  Paper    *)
(* Theorem 1 / Corollary 1 (p.3) state the VecSum input conditions with it.   *)
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
  have I2p := IZR_2powp.
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
  have I2p := IZR_2powp.
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

(* The tight per-step error bound (paper: [|e_i| <= 2u 2^(k_{i-1})]), here    *)
(* indexed by the previous position: [|e_{i+1}| <= 2u 2^(k_i)].  Each error is*)
(* the low word of the 2Sum combining [x_i] with the running tail sum         *)
(* ([vecSumAux_nth1]); [magnitude_vecSum_err] bounds it from the input bound  *)
(* [|x_i| < 2^(k_i+1)] and the running-sum bound [VecSum_run_bound].          *)
Lemma vecSum_err_bound k l : Thm1_hyp k l ->
  forall i, (i.+1 < size l)%N ->
    Rabs (nth 0 (vecSum l) i.+1) <= 2 * u * pow (k i).
Proof.
move=> Hk.
have Hfmt : {in l, forall z, format z}.
  case: Hk => Hrepr _ _ z /(nthP 0)[i iLs <-].
  exact: repr_format (Hrepr i iLs).
have Hrun := VecSum_run_bound Hk.
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
  have -> : pow p = IZR (2 ^ p) by rewrite IZR_2powp.
  by apply: IZR_lt.
- exact: Hrun j jLs.
- exact: Hemin.
Qed.

(* Core of paper Theorem 1 (its "multiples of 2u" divisibility argument),     *)
(* isolated as a reusable lemma: given the running-sum bound and the per-step *)
(* error bound, the output errors are F-nonoverlapping.  Proof (paper Section *)
(* 2.1, by contradiction): an overlap [|e_i| > 1/2 uls(e_{i'})], [i' < i],    *)
(* WLOG [uls(e_{i'}) = u] (scale invariance).  By backward divisibility       *)
(* ([vecSumAux_imul]: [2^k | s_i, x_{i-1}, .., x_0 => 2^k | e_i, .., e_0]),   *)
(* since [s_{i-1}] is a multiple of [2u] (from [|s_{i-1}| >= 1]) some input   *)
(* [x_j], [j <= i-2], is off the [2u]-grid, so [2^(k_j) <= 1/2], whence       *)
(* [2^(k_{i-1}) <= 1/4], contradicting the error bound [|e_i| <= 2u 2^(k_i)]. *)
Lemma vecSum_Fnonoverlap_core k l : Thm1_hyp k l ->
  (forall i, (i.+1 < size l)%N ->
     Rabs (nth 0 (vecSum l) i.+1) <= 2 * u * pow (k i)) ->
  (forall i, (i.+1 < size l)%N ->
     Rabs (vecSumAux (drop i.+1 l)).2 <= (2 - 2 * u) * pow (k i)) ->
  Fnonoverlap (vecSum l).
Proof.
Admitted.

(* Theorem 1.  [VecSum l] is F-nonoverlapping (wIZ) with the same sum,        *)
(* assembling the running-sum bound [VecSum_run_bound], the per-step error    *)
(* bound [vecSum_err_bound] and the divisibility core [vecSum_Fnonoverlap_    *)
(* core].  The sum conjunct is [vecSum_sum] (a chain of error-free 2Sums).    *)
Lemma VecSum_Thm1 k l : Thm1_hyp k l ->
  Fnonoverlap (vecSum l) /\ sumR (vecSum l) = sumR l.
Proof.
move=> Hk.
have Hfmt : {in l, forall z, format z}.
  case: Hk => Hrepr _ _ z /(nthP 0)[i iLs <-].
  exact: repr_format (Hrepr i iLs).
split; last by apply: vecSum_sum.
apply: (vecSum_Fnonoverlap_core Hk).
  exact: vecSum_err_bound Hk.
exact: VecSum_run_bound Hk.
Qed.

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
  have H : (1 < size (s :: es))%N by rewrite /= ltnS.
  exact: (Fnonoverlap_imm Hp2 Fses H sn0).
have Hulsei : uls s <= uls ei1.
  have -> : ei1 = dwl (TwoSum a s) by rewrite E.
  by apply: (TwoSum_err_uls_ge Fa Fs an0 sn0 Hulsle); rewrite E.
apply: Rle_trans Hle _.
by have := Hulsei; lra.
Qed.

(* The separation conjunct of Theorem 1 on the concrete input hypotheses      *)
(* [sorted_mag l] + [pairwise_ulp l] (paper Corollary 1: at most one overlap, *)
(* never two consecutive; exactly what [Merge] produces on the six merged     *)
(* terms), isolated as a reusable lemma.  Same "multiples of 2u" divisibility *)
(* core as [vecSum_Fnonoverlap_core] but with the relaxed exponent gap; the   *)
(* single tolerated overlap does not break the contradiction (Corollary 1).   *)
Lemma vecSum_Fnonoverlap_sep l :
  {in l, forall z, format z} -> sorted_mag l -> pairwise_ulp l ->
  Fnonoverlap (vecSum l).
Proof.
Admitted.

(* Theorem 1 (VecSum), on the concrete input separation: [vecSum l] is        *)
(* F-nonoverlapping AND has the same exact sum.  Assembles the divisibility   *)
(* core [vecSum_Fnonoverlap_sep] with [vecSum_sum] (a chain of exact 2Sums).  *)
Lemma vecSum_Fnonoverlap l :
  {in l, forall z, format z} -> sorted_mag l -> pairwise_ulp l ->
  Fnonoverlap (vecSum l) /\ sumR (vecSum l) = sumR l.
Proof.
move=> lF lM lP; split; last by apply: vecSum_sum.
exact: vecSum_Fnonoverlap_sep lF lM lP.
Qed.

End SecVecSum.
