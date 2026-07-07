(* ---------------------------------------------------------------------------*)
(* Algorithm 8 (TWSum): the sum of two triple-word numbers, and its two main  *)
(* correctness results -- the result is a triple word ([TWSum_isTW]) and the  *)
(* relative error bound ([TWSum_error]).  Generic over the precision [p] and  *)
(* minimal exponent [emin] (binary64 is fixed only in [addition.v]); built on *)
(* [TwoSum], [Nonoverlap], [TWR], [Merge], [VecSum] and [VSEB].               *)
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
Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SecTWSum.

Variable p : Z.
Variable emin : Z.
Hypothesis Hp2 : (1 < p)%Z.
Hypothesis emin_le_0 : (emin <= 0)%Z.
(* The correctness of triple-word addition needs enough precision (paper      *)
(* Section 5: [p >= 4] for Theorem 6, [p >= 6] for the Theorem-3 truncation   *)
(* and [size < p + 1] for six merged terms).  [p >= 6] covers all of them;    *)
(* binary64 ([p = 53]) satisfies it in [addition.v].                          *)
Hypothesis Hp6 : (6 <= p)%Z.

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

(* Triple-word type and merge from [TWR.v]/[Merge.v]; fix [p]/[emin].         *)
Local Notation isTW := (isTW p emin).
Local Notation isTW_sorted_mag := (isTW_sorted_mag Hp2).
Local Notation Merge_pairwise_ulp := (Merge_pairwise_ulp Hp2).

(* [VecSum.v] / [VSEB.v] entry points; re-hide this format's [p]/[emin]/      *)
(* [choice] (and the [Hp2]/[emin_le_0]/[choice_sym] proofs).                  *)
Local Notation vecSum := (vecSum p emin choice).
Local Notation vseb := (vseb p emin choice).
Local Notation vsebK := (vsebK p emin choice).
Local Notation size_vecSum := (size_vecSum p emin choice).
Local Notation format_vecSum := (format_vecSum Hp2).
Local Notation format_vseb := (format_vseb Hp2).
Local Notation format_vsebK := (format_vsebK Hp2).
Local Notation vecSum_sum := (vecSum_sum Hp2 emin_le_0 choice_sym).
Local Notation vseb_sum := (vseb_sum Hp2 emin_le_0 choice_sym).
Local Notation vecSum_Fnonoverlap :=
  (vecSum_Fnonoverlap Hp2 emin_le_0 choice_sym).
Local Notation vseb_Pnonoverlap :=
  (vseb_Pnonoverlap Hp2 emin_le_0 choice_sym).

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
(* Merging two triples and running VecSum yields exactly six terms, so the    *)
(* [size <= p + 1] side condition of [vseb_Pnonoverlap] holds once [6 <= p].  *)
Lemma size_vecSum_Merge x0 x1 x2 y0 y1 y2 :
  (Z.of_nat
     (size (vecSum (Merge [:: x0; x1; x2] [:: y0; y1; y2]))) <= p + 1)%Z.
Proof. by rewrite size_vecSum size_Merge /=; lia. Qed.

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
  - exact: size_vecSum_Merge.
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
       rewrite /e; exact: size_vecSum_Merge.
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


End SecTWSum.
