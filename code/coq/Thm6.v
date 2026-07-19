(* ---------------------------------------------------------------------------*)
(* Paper Theorem 6 = the draft's Theorem 7 (doc/old-triplewors.pdf, 5.1):     *)
(* [VSEB (VecSum x_0 .. x_5)] is P-nonoverlapping, for [p >= 4].              *)
(*                                                                            *)
(* This is the ONE open result of the development.  It needs both [VecSum]    *)
(* and [VSEB] and nothing else, so it lives in its own file rather than in    *)
(* [TWSum.v] -- [Merge]/[TWR] are not on its path.                            *)
(*                                                                            *)
(* THE PROOF TO FOLLOW IS [doc/thm6.md] SECTION 5, not the published sketch.  *)
(* The published paper states Theorem 6 with only a five-line sketch and      *)
(* "for space constraints, the proof is not detailed"; the earlier draft      *)
(* proves the same statement in full as Theorem 7.  Beware: the sketch is not *)
(* a faithful compression of the draft (doc/thm6.md 5.6) -- it uses the wrong *)
(* index ([i] for the draft's [i_1]) and the wrong constant ([1/2 uls(e_j)]   *)
(* for the draft's [5/8 u]).                                                  *)
(* ---------------------------------------------------------------------------*)

From Stdlib Require Import ZArith Reals Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
Require Import Nmore Rmore Fmore Rstruct MULTmore prelim.
From Flocq Require Import Pff.Pff2Flocq.
Require Import Uls.
Require Import TwoSum.
Require Import Nonoverlap.
Require Import VecSum.
Require Import VSEB.

Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SecThm6.

Variable p : Z.
Hypothesis Hp2 : (1 < p)%Z.
(* The draft uses [p >= 4] explicitly, in the [|e_{i_1}| > 1/2 u] case of the *)
(* VSEB analysis ("this part uses p >= 4, and ties-to-even for p = 4").       *)
Hypothesis Hp4 : (4 <= p)%Z.

Local Notation beta := radix2.
Local Notation pow e := (bpow beta e).

Local Instance p_gt_0 : Prec_gt_0 p.
Proof. now apply Z.lt_trans with (2 := Hp2). Qed.

Open Scope R_scope.

Local Notation u := (u p beta).
Local Notation uE := (@uE p).

Variable choice : Z -> bool.
Hypothesis choice_sym : forall x, choice x = ~~ choice (- (x + 1))%Z.
Local Notation rnd := (Znearest choice).
Local Instance valid_rnd : Valid_rnd rnd := valid_rnd_N choice.

Local Notation fexp := (FLX_exp p).
Local Notation format := (generic_format beta fexp).
Local Notation ulp := (ulp beta fexp).
Local Notation cexp := (cexp beta fexp).
Local Notation mant := (scaled_mantissa beta fexp).
Local Notation uls := (uls p).

Local Notation Pnonoverlap := (Pnonoverlap p).
Local Notation pairwise_ulp := (pairwise_ulp p).

Local Notation vecSum := (vecSum p choice).
Local Notation vecSumAux := (vecSumAux p choice).
Local Notation vseb := (vseb p choice).
Local Notation vsebAux := (vsebAux p choice).
Local Notation vecSum_run_ufp := (vecSum_run_ufp Hp2 choice_sym).
Local Notation vecSum_err_ufp := (vecSum_err_ufp Hp2 choice_sym).

Local Notation RND := (round beta fexp rnd).
Local Notation magnitudeDWR := (magnitudeDWR p).
Local Notation TwoSum := (TwoSum.TwoSum p choice).
Local Notation vecSumAux_cons := (@vecSumAux_cons p choice).
Local Notation vecSumAux_nth1 := (@vecSumAux_nth1 p choice).
Local Notation format_vecSumAux := (@format_vecSumAux p Hp2 choice).
Local Notation dwh_TwoSum_r0 := (@dwh_TwoSum_r0 p choice).
Local Notation dwl_TwoSum_r0 := (@dwl_TwoSum_r0 p Hp2 choice choice_sym).
Local Notation TwoSum_err_uls_ge := (@TwoSum_err_uls_ge p Hp2 choice choice_sym).
Local Notation TwoSum_hi := (@TwoSum_hi p choice).
Local Notation TwoSum_correct_loc := (TwoSum_correct_loc Hp2 choice_sym).
Local Notation format_TwoSum := (@format_TwoSum p Hp2 choice).
Local Notation magnitude_TwoSum := (magnitude_TwoSum Hp2 choice_sym).
Local Notation vsebAux_head_lt_mass := (vsebAux_head_lt_mass Hp2 choice_sym).
Local Notation vsebAux_head_leB := (vsebAux_head_leB Hp2 choice_sym).
Local Notation uls_gt_0 := (@uls_gt_0 p).
Local Notation uls_le_abs := (@uls_le_abs p).
Local Notation format_vecSum := (format_vecSum Hp2).
Local Notation size_vecSum := (@size_vecSum p choice).
Local Notation vecSumAux_imul := (@vecSumAux_imul p Hp2 choice choice_sym).
Local Notation vecSumAux_split := (@vecSumAux_split p choice).

(* ===========================================================================*)
(*  Theorem 6 / draft Theorem 7.                                              *)
(*                                                                            *)
(*  NOTE what is NOT here, compared with the FLT statement on [main]: there is*)
(*  no no-underflow hypothesis [emin + p <= mag z].  FLX IS the paper's model *)
(*  (unlimited exponent range), so this is the paper's statement, unpatched.  *)
(*  That is not just cosmetic: the draft's proof WLOGs [uls(e_j) = u] and     *)
(*  [uls(e_{i_0}) = u] and states every constant relative to that             *)
(*  normalisation.  Rescaling is invalid under FLT with a real [emin] -- which*)
(*  is why [vecSum_sep] had to be done scaling-free with a symbolic carry.    *)
(*  Under FLX the WLOG is legitimate, so the draft's proof is transcribable.  *)
(*                                                                            *)
(*  ROADMAP (doc/thm6.md 5.1-5.3).  Available (Qed, ported from main):        *)
(*   *1 run bound   [vecSum_run_ufp] : |s_j| <= 4 ufp(x_j), <= 2 ufp(x_{j-1}) *)
(*      err bound   [vecSum_err_ufp] : |e_{i+1}| <= 2u ufp(x_i)               *)
(*      the tie     [RN_midpoint_even], [ties_to_even]                        *)
(*   To do:                                                                   *)
(*   *2 (5.2) Assume [uls(e_j) = u] (WLOG) and [e_i >= 5/8 u] for some j < i. *)
(*      Force: |s_{i-1}| >= 1; then [2u | s_{i-1}] but [2u  |  e_j] gives some*)
(*      i' <= i-2 with [~(2u | x_i')], so |x_{i-2}| < 1; hence |x_i| < u,     *)
(*      |s_i| <= 2u, |x_{i-1}| <= 1-u.  With |s_{i-1} + e_i| >= 1 + 5/8 u this*)
(*      pins [s_{i-1} = 1], [x_{i-1} = 1-u], [s_i = u+e_i], and [2u^2 | e_i]. *)
(*      Then the right-of-i and left-of-i case analyses.                      *)
(*   *3 (5.3) VSEB: take [i_0] with [y_j = r_{i_0-1}] (so [eps_{i_0} <> 0]),  *)
(*      and [i_1] the first nonzero [e_i] after [e_{i_0}]; WLOG               *)
(*      [uls(e_{i_0}) = u], so [|eps_{i_0}| >= u] and [ulp(y_j) >= 2u].  Then *)
(*      three cases: [i_1 <= 3 /\ e_{i_1} >= 5/8 u]; [i_1 >= 4 /\ e_{i_1} >=  *)
(*      5/8 u]; [0 < e_{i_1} < 5/8 u] (itself split on 1/2 u and 1/4 u).      *)
(*                                                                            *)
(*  The [<= 6] bound is paid for in *3, via the counting: "we are adding at   *)
(*  most 3 of them", and the final [|e_4| = |e_3|] / [|e_5| <= uls(e_4)] step.*)
(*  It is necessary: Theorem 6 is FALSE for 7 inputs (doc/thm6.md 3).         *)
(* ===========================================================================*)
(* Length-free variant of [vsebAux_head_lt_mass]: the block bound             *)
(* [|head| < 2|eps|] from a mass bound WITHOUT the block-length hypothesis.    *)
(* The length was only needed in the power-of-two ([uls eps = |eps|]) case of  *)
(* [vsebAux_head_lt_mass], to keep [pred(2|eps|)] above the tail mass; the      *)
(* stronger margin [(1 - 2u)] here supplies exactly that slack directly.  This *)
(* matters because a VecSum output can emit over a long (mostly-zero) tail     *)
(* whose length exceeds [p - 1] (e.g. at [p = 4], a size-6 output), so the     *)
(* length bound is genuinely unavailable -- but the tail mass is tiny.         *)
Lemma vsebAux_head_lt_massU eps l :
  format eps -> {in l, forall z, format z} -> eps <> 0 ->
  sumRabs l <= uls eps * (1 - 2 * u) ->
  Rabs (nth 0 (vsebAux eps l) 0) < 2 * Rabs eps.
Proof.
move=> epsF lF epsn0 Hsum.
have Hu0 : 0 < uls eps by apply: uls_gt_0.
have Hae : uls eps <= Rabs eps by apply: uls_le_abs.
have He0 : 0 < Rabs eps by apply: Rabs_pos_lt.
have Hupos : 0 < u by rewrite /Fmore.u; have := bpow_gt_0 beta (1 - p); lra.
have Hg : uls eps = pow (cexp eps + Z.of_nat (trZ (Ztrunc (mant eps)))).
  by rewrite /uls; case: Req_bool_spec => // eps0; case: (epsn0 eps0).
set g := (cexp eps + Z.of_nat (trZ (Ztrunc (mant eps))))%Z.
have HmB : (Z.abs (Ztrunc (mant eps)) < beta ^ p)%Z.
  apply: lt_IZR; rewrite abs_IZR -scaled_mantissa_generic // IZR_Zpower;
    last lia.
  apply: Rlt_le_trans (_ : pow (mag beta eps - cexp eps) <= _)%R.
    exact: scaled_mantissa_lt_bpow.
  by apply: bpow_le; rewrite /cexp /FLX_exp; lia.
have Heps : Rabs eps = IZR (Z.abs (Ztrunc (mant eps))) * pow (cexp eps).
  by rewrite {1}epsF /F2R /= Rabs_mult -abs_IZR Rabs_pow.
have Hcu : pow (cexp eps) <= uls eps.
  by rewrite Hg; apply: bpow_le; rewrite /g;
     have := Zle_0_nat (trZ (Ztrunc (mant eps))); lia.
suff [B [FB HVB HBlt]] :
    exists B, [/\ format B, Rabs eps + sumRabs l <= B & B < 2 * Rabs eps].
  by apply: Rle_lt_trans (vsebAux_head_leB epsF lF FB HVB) HBlt.
have [HM|HM] := Rle_lt_or_eq_dec _ _ Hae.
- (* [uls eps < Rabs eps] (mantissa > 1): [B = |eps| + uls eps] is a float in *)
  (* range, and [< 2|eps|] since [uls eps < |eps|].                           *)
  exists (Rabs eps + uls eps).
  have Huim : is_imul (uls eps) (pow g) by rewrite Hg; exists 1%Z;
    rewrite Rmult_1_l.
  have Heim : is_imul (Rabs eps) (pow g).
    have Him : is_imul eps (pow g) by rewrite -Hg; exact: uls_imul epsF.
    case: (Rle_lt_dec 0 eps) => He.
      by rewrite Rabs_pos_eq.
    by rewrite Rabs_left //; apply: is_imul_opp.
  split.
  + apply: (imul_format Hp2 (e := g) (b := Rabs eps + uls eps)) => //.
    * by apply: is_imul_add.
    * by rewrite Rabs_pos_eq; lra.
    rewrite bpow_plus.
    have Hub : Rabs eps <= (pow p - 1) * uls eps.
      rewrite Heps.
      apply: Rle_trans (_ : (pow p - 1) * pow (cexp eps) <= _).
        apply: Rmult_le_compat_r; first by apply: bpow_ge_0.
        have -> : pow p - 1 = IZR (beta ^ p - 1).
          by rewrite minus_IZR IZR_Zpower //; lia.
        by apply: IZR_le; lia.
      apply: Rmult_le_compat_l; last exact: Hcu.
      have h0p : (0 <= p)%Z by lia.
      by rewrite -(pow0E beta); have := bpow_le beta 0 p h0p; lra.
    have -> : pow g = uls eps by rewrite Hg.
    nra.
  + by nra.
  + by lra.
(* [uls eps = Rabs eps] (a power of two): [B = pred(2|eps|)].  Here the       *)
(* [(1 - 2u)] margin -- not a block-length bound -- keeps [B] above the tail  *)
(* mass, which is the whole point of this length-free variant.                *)
have HgF : pow g = uls eps by rewrite Hg.
have H3 : pow (g + 1) = 2 * pow g by rewrite bpow_plus bpow_1 /=; lra.
have H2 : 2 * Rabs eps = pow (g + 1) by rewrite H3 -HM Hg.
exists (pred beta fexp (2 * Rabs eps)); split.
+ by apply: generic_format_pred; rewrite H2;
     apply: generic_format_bpow; rewrite /FLX_exp; lia.
+ rewrite H2 pred_bpow.
  have Hpm : pow (fexp (g + 1)) = uls eps * (2 * u).
    have Hueq : u = pow (- p).
      rewrite /Fmore.u (_ : (- p = 1 + - p - 1)%Z); last lia.
      by rewrite !bpow_plus bpow_1 /=; lra.
    rewrite /fexp /FLX_exp -HgF Hueq.
    rewrite (_ : (g + 1 - p = g + (1 - p))%Z); last lia.
    rewrite bpow_plus; congr (_ * _).
    rewrite (_ : (1 - p = 1 + - p)%Z); last lia.
    by rewrite bpow_plus bpow_1 /=; lra.
  rewrite -H2 Hpm; nra.
+ by apply: pred_lt_id; rewrite H2; have := bpow_gt_0 beta (g + 1); lra.
Qed.

(* Paper core tool (doc/thm6.md 5.4): each VecSum error is at most half an     *)
(* ulp of the running high word it is dropped from, [|e_{i+1}| <= 1/2 ulp(s_i)]*)
(* -- directly [magnitude_TwoSum] on the step [2Sum(x_i, s_{i+1}) = (s_i,      *)
(* e_{i+1})].  This is the draft's recurring [|e_i| <= 1/2 ulp(s_{i-1})].      *)
Lemma vecSum_err_le_half_ulp_run (l : seq R) i :
  (i.+1 < size l)%N -> {in l, forall z, format z} ->
  Rabs (nth 0 (vecSum l) i.+1) <= / 2 * ulp ((vecSumAux (drop i l)).2).
Proof.
move=> Hi Hf.
have iLl : (i < size l)%N by apply: ltn_trans (ltnSn i) Hi.
have Fx : format (nth 0 l i) by apply: Hf; apply: mem_nth.
have Hdf : {in drop i.+1 l, forall z, format z}
  by move=> z /mem_drop zI; apply: Hf.
have [Fs _] := format_vecSumAux Hdf.
have -> : nth 0 (vecSum l) i.+1 = nth 0 (vecSumAux l).1 i
  by rewrite /vecSum; case: (vecSumAux l).
rewrite (vecSumAux_nth1 Hi).
have Hs : (vecSumAux (drop i l)).2
        = dwh (TwoSum (nth 0 l i) (vecSumAux (drop i.+1 l)).2).
  have Hdne : (0 < size (drop i.+1 l))%N by rewrite size_drop subn_gt0.
  rewrite (drop_nth 0 iLl).
  case Hd : (drop i.+1 l) Hdne => [//|b l0] _.
  rewrite vecSumAux_cons; case E : (vecSumAux (b :: l0)) => [es s].
  by case: (TwoSum (nth 0 l i) s).
rewrite Hs; have Hm := magnitude_TwoSum Fx Fs.
by move: Hm;
   case: (TwoSum (nth 0 l i) (vecSumAux (drop i.+1 l)).2) => hi lo /=;
   lra.
Qed.

(* ===========================================================================*)
(*  Step *2 forcing (doc/thm6.md 5.2), scale-invariant: [uls(e_j)] is kept    *)
(*  symbolic (as [pow k]) instead of the paper's WLOG [uls(e_j) = u], which is *)
(*  the FLX-legal reading of the WLOG rescaling.                              *)
(* ===========================================================================*)

(* An ulp lower bound forces a magnitude lower bound.  From                    *)
(* [5/8 pow k <= 1/2 ulp s] we get [ulp s >= 2 pow k] (the next power of two   *)
(* above [5/4 pow k]) and hence [|s| >= ufp s = 2^(p-1) ulp s >= pow(k+p)].    *)
(* This is the draft's "[|e_i| <= 1/2 ulp(s_{i-1})] gives [|s_{i-1}| >= 1]"    *)
(* (with [1 = 2^p uls(e_j)] after the [uls(e_j) = u] normalisation).           *)
Lemma abs_ge_of_ulp_lb (s : R) (k : Z) :
  5 / 8 * pow k <= / 2 * ulp s -> pow (k + p) <= Rabs s.
Proof.
move=> H.
have Hk : 0 < pow k by apply: bpow_gt_0.
have Hs0 : s <> 0 by move=> s0; move: H; rewrite s0 ulp_FLX_0; lra.
have Hulp : ulp s = pow (cexp s) by rewrite ulp_neq_0.
have Hce : (k < cexp s)%Z by apply: (lt_bpow beta); rewrite -Hulp; lra.
have Hcexp : cexp s = (mag beta s - p)%Z by rewrite /cexp /FLX_exp.
apply: Rle_trans (bpow_mag_le beta s Hs0).
apply: bpow_le; lia.
Qed.

(* Dual of [abs_ge_of_ulp_lb]: a magnitude upper bound forces an ulp upper     *)
(* bound.  [|x| < pow m] gives [mag x <= m], so [ulp x = pow(cexp x) =          *)
(* pow(mag x - p) <= pow(m - p)].  Used for the draft's [|x_{i-2}| < 1] giving  *)
(* [ulp(x_{i-2}) <= u], hence [|x_i| < u].                                     *)
Lemma ulp_le_of_abs_lt (x : R) (m : Z) :
  Rabs x < pow m -> ulp x <= pow (m - p).
Proof.
move=> Hlt.
case: (Req_dec x 0) => [->|xn0]; first by rewrite ulp_FLX_0; apply: bpow_ge_0.
rewrite ulp_neq_0 //; apply: bpow_le.
have := mag_le_bpow beta x _ xn0 Hlt; rewrite /cexp /FLX_exp; lia.
Qed.

(* Same for [ufp]: [|x| < pow m] gives [ufp x = pow(mag x - 1) <= pow(m - 1)]. *)
Lemma ufp_le_of_abs_lt (x : R) (m : Z) :
  x <> 0 -> Rabs x < pow m -> ufp x <= pow (m - 1).
Proof.
move=> xn0 Hlt; rewrite /ufp; apply: bpow_le.
have := mag_le_bpow beta x _ xn0 Hlt; lia.
Qed.

(* A format number strictly below [pow m] is at most its predecessor           *)
(* [pred(pow m) = pow m - pow(m - p)].  The draft's "[|x_{i-1}| <= 1 - u]"      *)
(* ([1 = pow(k+p)], [u = pow k], so [1 - u = pow(k+p) - pow k]).                *)
Lemma abs_le_pred_of_lt (x : R) (m : Z) :
  format x -> Rabs x < pow m -> Rabs x <= pow m - pow (m - p).
Proof.
move=> Fx Hlt.
have Fabs : format (Rabs x) by apply: generic_format_abs.
have Fpow : format (pow m) by apply: generic_format_bpow; rewrite /FLX_exp; lia.
have Hpg : Rabs x <= pred beta fexp (pow m) by apply: pred_ge_gt.
by rewrite pred_bpow in Hpg; exact: Hpg.
Qed.

(* [uls] of a nonzero number is a power of two -- the form its                *)
(* definition takes off the zero branch.  Lets a [uls] be named as            *)
(* [pow k], which is how the whole *2 chain is parameterised.                 *)
Lemma uls_pow (x : R) : x <> 0 -> exists k : Z, uls x = pow k.
Proof.
move=> xn0; rewrite /uls; case: Req_bool_spec => [x0|_]; first by case: xn0.
by exists (cexp x + Z.of_nat (trZ (Ztrunc (mant x))))%Z.
Qed.

(* When [|x|] is exactly a power of two its [ulp] is pinned:                  *)
(* [mag x = e + 1] so [cexp x = e - p + 1].  Turns the pinning                *)
(* conclusion [|s_i| = pow(k+p)] into the exact [ulp(s_i) = pow(k+1)].        *)
Lemma ulp_of_abs_pow (x : R) (e : Z) :
  Rabs x = pow e -> ulp x = pow (e - p + 1).
Proof.
move=> Hx.
have xn0 : x <> 0.
  move=> x0; move: Hx; rewrite x0 Rabs_R0 => H.
  by have := bpow_gt_0 beta e; lra.
have Hmag : mag beta x = (e + 1)%Z :> Z.
  apply: mag_unique; rewrite Hx; split.
    have -> : (e + 1 - 1 = e)%Z by lia.
    lra.
  by apply: bpow_lt; lia.
rewrite ulp_neq_0 // /cexp /FLX_exp Hmag.
by congr bpow; lia.
Qed.

(* Draft 5.2, first step: a violation forces the preceding running sum large. *)
(* If a VecSum error [e_{i+1}] reaches [5/8 uls(e_j)] (with [uls(e_j) = pow k])*)
(* then [|s_i| >= 2^p uls(e_j) = pow(k+p)] -- the draft's [|s_{i-1}| >= 1].     *)
(* Combines [vecSum_err_le_half_ulp_run] ([|e_{i+1}| <= 1/2 ulp(s_i)]) with    *)
(* [abs_ge_of_ulp_lb].                                                         *)
Lemma vecSum_run_ge_of_violation (l : seq R) (i : nat) (k : Z) :
  (i.+1 < size l)%N -> {in l, forall z, format z} ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  pow (k + p) <= Rabs (vecSumAux (drop i l)).2.
Proof.
move=> Hi Hf Hviol.
apply: abs_ge_of_ulp_lb; apply: Rle_trans Hviol _.
exact: vecSum_err_le_half_ulp_run.
Qed.

(* Draft 5.2, divisibility: since [|s_i| >= 2^p uls(e_j)], the running sum is  *)
(* a multiple of [2 uls(e_j) = pow(k+1)] -- the draft's "[2u | s_{i-1}]" (with *)
(* [uls(e_j) = u]).  A float of magnitude [>= pow(k+p)] lies on a grid at      *)
(* least as coarse as [pow(k+1)] ([is_imul_bound_pow_format]).                 *)
Lemma vecSum_run_imul_of_violation (l : seq R) (i : nat) (k : Z) :
  (i.+1 < size l)%N -> {in l, forall z, format z} ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  is_imul (vecSumAux (drop i l)).2 (pow (k + 1)).
Proof.
move=> Hi Hf Hviol.
have Fs : format (vecSumAux (drop i l)).2.
  have Hdf : {in drop i l, forall z, format z} by move=> z /mem_drop; apply: Hf.
  by have [Fs _] := format_vecSumAux Hdf.
have Hge := vecSum_run_ge_of_violation Hi Hf Hviol.
have H := is_imul_bound_pow_format Hge Fs.
by rewrite (_ : (k + 1 = k + p - p + 1)%Z); last lia.
Qed.

(* Draft 5.2, "[~(2u | x_{i'})] so [|x_{i'}| < 1]": a float off the            *)
(* [2 uls(e_j) = pow(k+1)] grid has magnitude below [1 = 2^p uls(e_j) =        *)
(* pow(k+p)].  Contrapositive of [is_imul_bound_pow_format]: a format number   *)
(* of magnitude [>= pow(k+p)] has [cexp >= k+1], so it lies on the [pow(k+1)]  *)
(* grid.                                                                       *)
Lemma abs_lt_of_not_imul (x : R) (k : Z) :
  format x -> ~ is_imul x (pow (k + 1)) -> Rabs x < pow (k + p).
Proof.
move=> Fx Hni.
case: (Rlt_le_dec (Rabs x) (pow (k + p))) => [//|Hge]; exfalso.
apply: Hni; have := is_imul_bound_pow_format Hge Fx.
by rewrite (_ : (k + 1 = k + p - p + 1)%Z); last lia.
Qed.

(* Chained magnitude isotony (draft's "by isotony"): on a [sorted_mag] list a  *)
(* later entry has no larger magnitude than an earlier one.                    *)
Lemma sorted_mag_le_nth (l : seq R) (i j : nat) :
  sorted_mag l -> (i <= j)%N -> (j < size l)%N ->
  Rabs (nth 0 l j) <= Rabs (nth 0 l i).
Proof.
move=> Hs; elim: j => [|j IH] Hij Hj.
  by move: Hij; rewrite leqn0 => /eqP->; apply: Rle_refl.
move: Hij; rewrite leq_eqVlt ltnS => /orP[/eqP->|Hij]; first exact: Rle_refl.
apply: Rle_trans (Hs j Hj) _.
by apply: IH => //; apply: ltn_trans (ltnSn j) Hj.
Qed.

(* Divisibility propagates from inputs to the VecSum output: if every input   *)
(* lies on the grid [pow g], so does every output ([vecSumAux_imul] packaged   *)
(* for [vecSum]).                                                              *)
Lemma vecSum_imul_forward (l : seq R) (g : Z) :
  {in l, forall z, format z} -> {in l, forall z, is_imul z (pow g)} ->
  {in vecSum l, forall z, is_imul z (pow g)}.
Proof.
move=> Hf Hm z; rewrite /vecSum.
have [H2 H1] := vecSumAux_imul Hf Hm.
case E : (vecSumAux l) => [es s0]; rewrite E /= in H2 H1.
by rewrite inE => /orP[/eqP->//|]; apply: H1.
Qed.

(* Draft 5.2, the propagation step: [2u | s_{i-1}] but [~ 2u | e_j] (j < i)    *)
(* forces some INPUT [x_{i'}] off the grid, with [i' < t] when the offending   *)
(* output sits in the prefix [j <= t] and the running sum [s_t] is on grid.    *)
(* Via [vecSumAux_split]: [vecSum (take t l ++ [s_t])] is the [t+1]-prefix of  *)
(* [vecSum l], and its inputs are [x_0..x_{t-1}] plus the (on-grid) [s_t].     *)
Lemma vecSum_not_imul_prefix (l : seq R) (t j : nat) (g : Z) :
  (t < size l)%N -> {in l, forall z, format z} -> (j <= t)%N ->
  is_imul (vecSumAux (drop t l)).2 (pow g) ->
  ~ is_imul (nth 0 (vecSum l) j) (pow g) ->
  exists2 i', (i' < t)%N & ~ is_imul (nth 0 l i') (pow g).
Proof.
move=> Ht Hf Hjt Hs Hnj.
set st := (vecSumAux (drop t l)).2.
set L := take t l ++ [:: st].
have Fst : format st.
  have Hdf : {in drop t l, forall z, format z} by move=> z /mem_drop; apply: Hf.
  by have [F _] := format_vecSumAux Hdf.
have HvL : vecSum L = (vecSumAux l).2 :: take t (vecSumAux l).1
  by rewrite /vecSum /L vecSumAux_split.
have Hnthj : nth 0 (vecSum L) j = nth 0 (vecSum l) j.
  rewrite HvL /vecSum; case: (vecSumAux l) => es s0.
  rewrite [(es, s0).1]/= [(es, s0).2]/=.
  by rewrite -[s0 :: take t es]/(take t.+1 (s0 :: es)) nth_take.
have HszL : size L = t.+1.
  by rewrite /L size_cat size_take_min /= addn1 (minn_idPl (ltnW Ht)).
apply: Classical_Prop.NNPP => Hnex.
have Hall : {in L, forall z, is_imul z (pow g)}.
  move=> z; rewrite /L mem_cat inE => /orP[|/eqP->]; last exact: Hs.
  move=> /(nthP 0)[i' Hi' <-].
  move: Hi'; rewrite size_take_min ltn_min => /andP[Hi't _].
  rewrite nth_take //.
  apply: Classical_Prop.NNPP => Hni'.
  by apply: Hnex; exists i'.
have HfL : {in L, forall z, format z}.
  by move=> z; rewrite /L mem_cat inE => /orP[/mem_take/Hf //|/eqP->//].
have Him := vecSum_imul_forward HfL Hall.
apply: Hnj; rewrite -Hnthj; apply: Him; apply: mem_nth.
by rewrite size_vecSum HszL.
Qed.

(* Draft 5.2, "[exists i' <= i-2, ~(2u | x_{i'})]": at a violation, with a     *)
(* reference error [e_j] ([j <= i]) whose [uls(e_j) = pow k] (so [e_j] is an   *)
(* odd multiple of the grid, [~ 2u | e_j] by [not_imul_uls_succ]), some input  *)
(* [x_{i'}] with [i' < i] is off the [2 uls(e_j) = pow(k+1)] grid.             *)
Lemma vecSum_exists_offgrid_input (l : seq R) (i j : nat) (k : Z) :
  (i.+1 < size l)%N -> {in l, forall z, format z} -> (j <= i)%N ->
  nth 0 (vecSum l) j <> 0 -> uls (nth 0 (vecSum l) j) = pow k ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  exists2 i', (i' < i)%N & ~ is_imul (nth 0 l i') (pow (k + 1)).
Proof.
move=> Hi Hf Hji Hej0 Huls Hviol.
have Hilt : (i < size l)%N by apply: ltn_trans (ltnSn i) Hi.
have Hjs : (j < size (vecSum l))%N.
  rewrite size_vecSum prednK; last by apply: ltn_trans Hi.
  by apply: leq_ltn_trans Hji Hilt.
have Fej : format (nth 0 (vecSum l) j)
  by apply: (format_vecSum Hf); apply: mem_nth.
have Hnej : ~ is_imul (nth 0 (vecSum l) j) (pow (k + 1))
  by exact: not_imul_uls_succ Fej Hej0 Huls.
apply: (vecSum_not_imul_prefix Hilt Hf Hji _ Hnej).
exact: vecSum_run_imul_of_violation Hi Hf Hviol.
Qed.

(* Draft 5.2, combining the previous two: at a violation, some input [x_{i'}]  *)
(* ([i' < i]) is off the [pow(k+1)] grid, hence [|x_{i'}| < 1 = pow(k+p)], and *)
(* by [sorted_mag] isotony EVERY later input [x_m] ([m >= i']) satisfies       *)
(* [|x_m| < 1].  (The draft's "[|x_{i'}| < 1] so by isotony [|x_{i-2}| < 1]".) *)
Lemma vecSum_inputs_lt_of_violation (l : seq R) (i j : nat) (k : Z) :
  (i.+1 < size l)%N -> {in l, forall z, format z} -> sorted_mag l ->
  (j <= i)%N -> nth 0 (vecSum l) j <> 0 -> uls (nth 0 (vecSum l) j) = pow k ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  exists2 i', (i' < i)%N &
    forall m, (i' <= m)%N -> (m < size l)%N -> Rabs (nth 0 l m) < pow (k + p).
Proof.
move=> Hi Hf Hsort Hji Hej0 Huls Hviol.
have [i' Hi'i Hoff] := vecSum_exists_offgrid_input Hi Hf Hji Hej0 Huls Hviol.
have Hi's : (i' < size l)%N by apply: ltn_trans Hi'i (ltn_trans (ltnSn i) Hi).
exists i' => // m Hm Hmsz.
apply: Rle_lt_trans (sorted_mag_le_nth Hsort Hm Hmsz) _.
by apply: (abs_lt_of_not_imul _ Hoff); apply: Hf; apply: mem_nth.
Qed.

(* Draft 5.2, "[|x_{i-1}| <= 1 - u]": each earlier input, being format and     *)
(* [< 1 = pow(k+p)], is [<= 1 - u = pow(k+p) - pow k].                         *)
Lemma vecSum_inputs_le_1mu_of_violation (l : seq R) (i j : nat) (k : Z) :
  (i.+1 < size l)%N -> {in l, forall z, format z} -> sorted_mag l ->
  (j <= i)%N -> nth 0 (vecSum l) j <> 0 -> uls (nth 0 (vecSum l) j) = pow k ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  exists2 i', (i' < i)%N &
    forall m, (i' <= m)%N -> (m < size l)%N ->
      Rabs (nth 0 l m) <= pow (k + p) - pow k.
Proof.
move=> Hi Hf Hsort Hji Hej0 Huls Hviol.
have [i' Hi'i Hlt] :=
  vecSum_inputs_lt_of_violation Hi Hf Hsort Hji Hej0 Huls Hviol.
exists i' => // m Hm Hmsz.
have Fm : format (nth 0 l m) by apply: Hf; apply: mem_nth.
have := abs_le_pred_of_lt Fm (Hlt m Hm Hmsz).
by rewrite (_ : (k + p - p = k)%Z); last lia.
Qed.

(* Draft 5.2, "[|x_i| < u]": with [|x_m| < 1] for the earlier inputs           *)
(* ([m >= i']) we get [ulp(x_m) <= u = pow k] ([ulp_le_of_abs_lt]), so          *)
(* [pairwise_ulp] ([|x_{m+2}| < ulp(x_m)]) yields [|x_{m+2}| < u].              *)
Lemma vecSum_inputs_lt_u_of_violation (l : seq R) (i j : nat) (k : Z) :
  (i.+1 < size l)%N -> {in l, forall z, format z} ->
  sorted_mag l -> pairwise_ulp l -> (j <= i)%N ->
  nth 0 (vecSum l) j <> 0 -> uls (nth 0 (vecSum l) j) = pow k ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  exists2 i', (i' < i)%N &
    forall m, (i' <= m)%N -> (m.+2 < size l)%N -> Rabs (nth 0 l m.+2) < pow k.
Proof.
move=> Hi Hf Hsort Hpair Hji Hej0 Huls Hviol.
have [i' Hi'i Hlt] :=
  vecSum_inputs_lt_of_violation Hi Hf Hsort Hji Hej0 Huls Hviol.
exists i' => // m Hm Hmsz.
have Hmsz' : (m < size l)%N.
  by apply: ltn_trans Hmsz; apply: ltn_trans (ltnSn m) (ltnSn m.+1).
have Hulp : ulp (nth 0 l m) <= pow k.
  have := ulp_le_of_abs_lt (Hlt m Hm Hmsz').
  by rewrite (_ : (k + p - p = k)%Z); last lia.
have [Hz|Hlt2] := Hpair m Hmsz; first by rewrite Hz Rabs_R0; apply: bpow_gt_0.
exact: Rlt_le_trans Hlt2 Hulp.
Qed.

(* Draft 5.2, "[|s_i| <= 2u]": with [|x_i| < u] and the *1 running-sum bound   *)
(* [|s_i| <= 4 ufp(x_i)] we get [|s_i| <= 4 ufp(x_i) <= 4 pow(k-1) = pow(k+1)  *)
(* = 2u].                                                                      *)
Lemma vecSum_run_le_2u_of_violation (l : seq R) (i j : nat) (k : Z) :
  ties_to_even choice -> (i.+1 < size l)%N -> {in l, forall z, format z} ->
  (forall m, (m < size l)%N -> nth 0 l m <> 0) ->
  sorted_mag l -> pairwise_ulp l -> (j <= i)%N ->
  nth 0 (vecSum l) j <> 0 -> uls (nth 0 (vecSum l) j) = pow k ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  exists2 i', (i' < i)%N &
    forall m, (i' <= m)%N -> (m.+2 < size l)%N ->
      Rabs (vecSumAux (drop m.+2 l)).2 <= pow (k + 1).
Proof.
move=> Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls Hviol.
have [i' Hi'i Hxlt] :=
  vecSum_inputs_lt_u_of_violation Hi Hf Hsort Hpair Hji Hej0 Huls Hviol.
exists i' => // m Hm Hmsz.
have Hxn0 : nth 0 l m.+2 <> 0 by apply: Hnz.
have Hufp : ufp (nth 0 l m.+2) <= pow (k - 1)
  by apply: ufp_le_of_abs_lt Hxn0 (Hxlt _ Hm Hmsz).
have [Hrun _] := vecSum_run_ufp Heven Hf Hnz Hsort Hpair Hmsz.
apply: Rle_trans Hrun _.
have -> : pow (k + 1) = 4 * pow (k - 1).
  have E4 : (4 : R) = pow 2 by rewrite /= /Z.pow_pos /=; lra.
  by rewrite (_ : (k + 1 = 2 + (k - 1))%Z) ?bpow_plus -?E4; [|lia].
by apply: Rmult_le_compat_l; [lra | exact: Hufp].
Qed.

(* Draft 5.2, "at the right of i": "[|x_i| < u] so [forall i' >= i+1,          *)
(* |e_{i'}| <= u^2]".  Each later error [e = dwl(2Sum(x, s))] with a small      *)
(* input [|x| < u = pow k] has [|e| <= 2u ufp(x) <= 2u pow(k-1) = pow(k-p) =    *)
(* u^2] ([vecSum_err_ufp] + [ufp_le_of_abs_lt]).  This is the block-mass        *)
(* content feeding the block bound; it does NOT need the pinning.             *)
Lemma vecSum_tail_err_le_u2_of_violation (l : seq R) (i j : nat) (k : Z) :
  ties_to_even choice -> (i.+1 < size l)%N -> {in l, forall z, format z} ->
  (forall m, (m < size l)%N -> nth 0 l m <> 0) ->
  sorted_mag l -> pairwise_ulp l -> (j <= i)%N ->
  nth 0 (vecSum l) j <> 0 -> uls (nth 0 (vecSum l) j) = pow k ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  exists2 i', (i' < i)%N &
    forall m, (i' <= m)%N -> (m.+2.+1 < size l)%N ->
      Rabs (nth 0 (vecSum l) m.+2.+1) <= pow (k - p).
Proof.
move=> Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls Hviol.
have [i' Hi'i Hxlt] :=
  vecSum_inputs_lt_u_of_violation Hi Hf Hsort Hpair Hji Hej0 Huls Hviol.
exists i' => // m Hm Hmsz.
have Hmsz2 : (m.+2 < size l)%N by apply: ltn_trans (ltnSn _) Hmsz.
have Hxn0 : nth 0 l m.+2 <> 0 by apply: Hnz.
have Hufp : ufp (nth 0 l m.+2) <= pow (k - 1)
  by apply: ufp_le_of_abs_lt Hxn0 (Hxlt m Hm Hmsz2).
have Herr := vecSum_err_ufp Heven Hf Hnz Hsort Hpair Hmsz.
apply: Rle_trans Herr _.
have H2u : 2 * u = pow (1 - p) by rewrite /Fmore.u; lra.
have -> : pow (k - p) = 2 * u * pow (k - 1).
  by rewrite H2u -bpow_plus; congr bpow; lia.
by apply: Rmult_le_compat_l; [have := bpow_ge_0 beta (1 - p); lra | exact: Hufp].
Qed.

(* ===========================================================================*)
(*  Draft 5.2, the "close to equality" PINNING (the draft's only gap -- it     *)
(*  says "by an easy case study" without detail).  Written top-down: the pure  *)
(*  interval/divisibility core [interval_pin] is isolated (and, for now,        *)
(*  admitted), and [vecSum_pinning_of_violation] gathers the bounds -- all      *)
(*  proved by the *2 lemmas above -- and applies it.                           *)
(*                                                                            *)
(*  Notation ([K] plays [uls(e_j)]'s exponent, so [pow K = u], [pow(K+p) = 1], *)
(*  [pow(K+1) = 2u], [pow(K-p) = u^2]): with [a = s_i], [b = e_{i+1}],          *)
(*  [c = x_i], [d = s_{i+1}] and the exact 2Sum identity [a + b = c + d],       *)
(*   - [a] is a multiple of [2u] with [|a| >= 1] and [|a+b| <= 1+u], so [a] is  *)
(*     pinned to [|a| = 1];                                                     *)
(*   - [c] is a float trapped in [(1 - 11/8 u, 1 - u]], so [|c| = 1 - u];       *)
(*   - hence [|d| = u + |b|] and [2u^2 | b].                                    *)
(* ===========================================================================*)
(* Conclusion 1 -- [|a| = 1] -- the tie-exclusion, PROVED.  [a] is a multiple  *)
(* of [2u] with [1 <= |a|], and [|a| <= 1 + u + 1/2 ulp a] pins [mag a] (using  *)
(* [p >= 4]), so [ulp a = 2u] and [|a| <= 1 + 2u]: [|a| in {1, 1+2u}].  The     *)
(* boundary [1+2u] is excluded because there [c+d = +-(1 + u)] is exactly the   *)
(* midpoint [pow(K+p) + pow((K+p)-p)], which round-to-nearest-EVEN sends to     *)
(* [pow(K+p)] ([RN_midpoint_even]), not to [1+2u].                             *)
Lemma interval_pin_abs (a b c d : R) (K : Z) :
  ties_to_even choice ->
  format c -> a = RND (c + d) ->
  is_imul a (pow (K + 1)) -> pow (K + p) <= Rabs a ->
  Rabs c <= pow (K + p) - pow K -> Rabs d <= pow (K + 1) ->
  a + b = c + d -> 5 / 8 * pow K <= Rabs b -> Rabs b <= / 2 * ulp a ->
  Rabs a = pow (K + p).
Proof.
move=> Heven Fc Ha_rnd [za Hza] Ha_ge Hc_le Hd_le Hid Hb_lo Hb_hi.
have HG : 0 < pow K by apply: bpow_gt_0.
have HA : 0 < pow (K + p) by apply: bpow_gt_0.
have H2G : pow (K + 1) = 2 * pow K by rewrite bpow_plus bpow_1 /=; lra.
have HAG : pow (K + p) = pow p * pow K by rewrite -bpow_plus; congr bpow; lia.
have Hb_eq : b = c + d - a by lra.
have an0 : a <> 0 by move=> a0; move: Ha_ge; rewrite a0 Rabs_R0; lra.
have Hulp_le : / 2 * ulp a <= Rabs a * pow (- p).
  rewrite ulp_neq_0 //.
  have Hmg : pow (mag beta a - 1) <= Rabs a by apply: bpow_mag_le.
  have -> : cexp a = (mag beta a - 1 + (1 - p))%Z by rewrite /cexp /FLX_exp; lia.
  rewrite bpow_plus.
  have -> : pow (1 - p) = 2 * pow (- p) by rewrite bpow_plus bpow_1 /=; lra.
  have := bpow_gt_0 beta (- p); nra.
have Hpp : pow 4 <= pow p by apply: bpow_le.
have Hp16 : (16 : R) <= pow p by move: Hpp; rewrite /= /Z.pow_pos /=; lra.
have Hpn : 0 < pow (- p) by apply: bpow_gt_0.
have Hpu : pow (- p) <= / 16.
  have hp4 : (- p <= -4)%Z by lia.
  by have := bpow_le beta (- p) (-4) hp4; rewrite /= /Z.pow_pos /=; lra.
have Ha_lt2A : Rabs a < 2 * pow (K + p).
  have Hchain : Rabs a <= pow (K + p) - pow K + pow (K + 1) + / 2 * ulp a.
    have := Rabs_triang (c + d) (- a); rewrite Rabs_Ropp.
    have -> : c + d + - a = b by lra.
    have := Rabs_triang c d; split_Rabs; lra.
  rewrite H2G HAG in Hchain *; nra.
have HKp1 : pow (K + p + 1) = 2 * pow (K + p) by rewrite bpow_plus bpow_1 /=; lra.
have Hmag : mag beta a = (K + p + 1)%Z :> Z.
  apply: mag_unique.
  rewrite (_ : (K + p + 1 - 1 = K + p)%Z); last lia.
  by rewrite HKp1; split; lra.
have Hulpa : ulp a = 2 * pow K.
  rewrite ulp_neq_0 // /cexp /FLX_exp Hmag.
  by rewrite (_ : (K + p + 1 - p = K + 1)%Z) ?H2G //; lia.
have Hb_le_G : Rabs b <= pow K by move: Hb_hi; rewrite Hulpa; lra.
have Ha_le : Rabs a <= pow (K + p) + 2 * pow K.
  have := Rabs_triang (c + d) (- a); rewrite Rabs_Ropp.
  have -> : c + d + - a = b by lra.
  have := Rabs_triang c d; rewrite Hulpa in Hb_hi; split_Rabs; lra.
have Hpow1 : pow (p - 1) = IZR (2 ^ (p - 1))
  by rewrite -IZR_Zpower; [congr IZR|lia].
have HAeq : pow (K + p) = IZR (2 ^ (p - 1)) * pow (K + 1)
  by rewrite -Hpow1 -bpow_plus; congr bpow; lia.
have Hza' : Rabs a = IZR (Z.abs za) * pow (K + 1).
  by rewrite Hza Rabs_mult abs_IZR (Rabs_pos_eq (pow _)) //; apply: bpow_ge_0.
have Hzge : (2 ^ (p - 1) <= Z.abs za)%Z.
  apply: le_IZR; apply: (Rmult_le_reg_r (pow (K + 1))); first by apply: bpow_gt_0.
  by rewrite -HAeq -Hza'.
have Hzle : (Z.abs za <= 2 ^ (p - 1) + 1)%Z.
  apply: le_IZR; apply: (Rmult_le_reg_r (pow (K + 1))); first by apply: bpow_gt_0.
  rewrite -Hza' plus_IZR Rmult_plus_distr_r Rmult_1_l -HAeq.
  by move: Ha_le; rewrite H2G.
have HKpe : pow (K + p) + pow K = pow (K + p) + pow (K + p - p)
  by congr (_ + _); congr bpow; lia.
have HRmid := @RN_midpoint_even p Hp2 choice (K + p) Heven.
rewrite -HKpe in HRmid.
have Hcase : (Z.abs za = 2 ^ (p - 1) \/ Z.abs za = 2 ^ (p - 1) + 1)%Z by lia.
case: Hcase => Hcase; first by rewrite Hza' Hcase HAeq.
exfalso.
have HRaeq : Rabs a = pow (K + p) + 2 * pow K.
  by rewrite Hza' Hcase plus_IZR Rmult_plus_distr_r Rmult_1_l -HAeq H2G.
have Hcd_le : Rabs (c + d) <= pow (K + p) + pow K
  by have := Rabs_triang c d; lra.
case: (Rle_lt_dec 0 a) => Ha0.
  have Hapos : a = pow (K + p) + 2 * pow K by rewrite -HRaeq Rabs_pos_eq.
  have Hcd : c + d = pow (K + p) + pow K.
    move: Hid Hb_le_G Hcd_le; rewrite Hapos; split_Rabs; lra.
  by move: HRmid; rewrite -Hcd -Ha_rnd Hapos; lra.
have Haneg : a = - (pow (K + p) + 2 * pow K).
  by have := Rabs_left _ Ha0; rewrite HRaeq; lra.
have Hcd : c + d = - (pow (K + p) + pow K).
  move: Hid Hb_le_G Hcd_le; rewrite Haneg; split_Rabs; lra.
have Hopp := @RN_opp_sym p choice choice_sym (pow (K + p) + pow (K + p - p)).
have Haval : a = - pow (K + p)
  by rewrite Ha_rnd Hcd HKpe Hopp -HKpe HRmid.
move: Haneg Haval; lra.
Qed.

(* Conclusion 2 -- [|c| = 1 - u] -- and the extra [|d| >= u], given [|a| = 1]. *)
(* The rounding fact [a = RN(c+d)] makes [a] a NEAREST float to [c+d], so with *)
(* [g = 1 - u] we get [-b <= u/2], hence (with the violation) [b in [5/8u, u]]; *)
(* then [c] is a multiple of [u] trapped in [(1 - 11/8 u, 1 - u]], so [c = 1-u],*)
(* and [d = b + u >= 13/8 u >= u].  ([2u^2 | e_i] is NOT provable here -- it     *)
(* needs the 2Sum structure -- so it moves to [vecSum_pinning_of_violation].)   *)
Lemma interval_pin_rest (a b c d : R) (K : Z) :
  ties_to_even choice ->
  format c -> a = RND (c + d) ->
  is_imul a (pow (K + 1)) -> Rabs a = pow (K + p) ->
  Rabs c <= pow (K + p) - pow K -> Rabs d <= pow (K + 1) ->
  a + b = c + d -> 5 / 8 * pow K <= Rabs b -> Rabs b <= / 2 * ulp a ->
  [/\ Rabs c = pow (K + p) - pow K,
      pow K <= Rabs d &
      Rabs (d - b) = pow K ].
Proof.
move=> Heven Fc Hr Hai Hae Hcl Hdl Hi Hbl Hbh.
have HG : 0 < pow K by apply: bpow_gt_0.
have HA : 0 < pow (K + p) by apply: bpow_gt_0.
have HAG : pow (K + p) = pow p * pow K by rewrite -bpow_plus; congr bpow; lia.
have Hp16 : (16 : R) <= pow p.
  have h4p : (4 <= p)%Z by lia.
  by have := bpow_le beta 4 p h4p; rewrite /= /Z.pow_pos /=; lra.
have an0 : a <> 0 by move=> a0; move: Hae; rewrite a0 Rabs_R0; lra.
have Hmaga : mag beta a = (K + p + 1)%Z :> Z.
  apply: mag_unique; rewrite Hae (_ : (K + p + 1 - 1 = K + p)%Z); last lia.
  by split; [lra | apply: bpow_lt; lia].
have HulpA : ulp a = 2 * pow K.
  rewrite ulp_neq_0 // /cexp /FLX_exp Hmaga.
  by rewrite (_ : (K + p + 1 - p = K + 1)%Z) ?bpow_plus ?bpow_1 /=; [lra|lia].
have Hb_G : Rabs b <= pow K by move: Hbh; rewrite HulpA; lra.
have [Fa Hnear] := round_N_pt beta fexp choice (c + d).
rewrite -Hr in Fa Hnear.
have HpredAG : pred beta fexp (pow (K + p)) = pow (K + p) - pow K
  by rewrite pred_bpow /fexp /FLX_exp (_ : (K + p - p = K)%Z) //; lia.
have FAG : format (pow (K + p) - pow K)
  by rewrite -HpredAG; apply: generic_format_pred; apply: generic_format_bpow;
     rewrite /FLX_exp; lia.
have Hce : c = a + b - d by lra.
have Hd2G : Rabs d <= 2 * pow K by move: Hdl; rewrite bpow_plus bpow_1 /=; lra.
have Hc_lo : pow (K + p) - 3 * pow K <= Rabs c
  by move: Hi Hae Hb_G Hd2G; split_Rabs; lra.
have HKm1 : pow (K + p) = 2 * pow (K + p - 1)
  by rewrite (_ : (K + p = K + p - 1 + 1)%Z) ?bpow_plus ?bpow_1 /=; [lra|lia].
have HKpm1 : pow (K + p - 1) = pow K * pow (p - 1)
  by rewrite -bpow_plus; congr bpow; lia.
have Hpm1 : (8 : R) <= pow (p - 1).
  have h3p : (3 <= p - 1)%Z by lia.
  by have := bpow_le beta 3 (p - 1) h3p; rewrite /= /Z.pow_pos /=; lra.
have cn0 : c <> 0 by move=> c0; move: Hc_lo; rewrite c0 Rabs_R0; nra.
have Hmagc : mag beta c = (K + p)%Z :> Z.
  apply: mag_unique; split; last by apply: Rle_lt_trans Hcl _; lra.
  by apply: Rle_trans Hc_lo; nra.
have Hcimul : is_imul c (pow K).
  have := format_imul_cexp Fc; rewrite /cexp /FLX_exp Hmagc.
  by rewrite (_ : (K + p - p = K)%Z) //; lia.
have [mc Hmc] := Hcimul.
have Hpp2 : pow p = IZR (2 ^ p) by rewrite -IZR_Zpower; [congr IZR|lia].
case: (Rle_lt_dec 0 a) => Ha0.
  have HaA : a = pow (K + p) by move: Hae; rewrite Rabs_pos_eq.
  have Hnb := Hnear _ FAG.
  have Hbge : - pow K / 2 <= b by move: Hnb; rewrite -Hi HaA; split_Rabs; lra.
  have Hbpos : 5 / 8 * pow K <= b by move: Hbl Hbge Hb_G; split_Rabs; lra.
  have Hcpos : 0 < c by rewrite Hce HaA; move: Hbpos Hd2G; split_Rabs; nra.
  have Hc_up : c <= pow (K + p) - pow K by move: Hcl; rewrite Rabs_pos_eq //; lra.
  have Hc_lo2 : pow (K + p) - 11 / 8 * pow K <= c
    by rewrite Hce HaA; move: Hbpos Hd2G; split_Rabs; lra.
  have Hmc_ge : (2 ^ p - 2 < mc)%Z.
    apply: lt_IZR; rewrite minus_IZR -Hpp2.
    by move: Hc_lo2; rewrite Hmc HAG; nra.
  have Hmc_le : (mc <= 2 ^ p - 1)%Z.
    apply: le_IZR; rewrite minus_IZR -Hpp2.
    by move: Hc_up; rewrite Hmc HAG; nra.
  have Hmceq : mc = (2 ^ p - 1)%Z by lia.
  have Hcval : c = pow (K + p) - pow K
    by rewrite Hmc Hmceq minus_IZR -Hpp2 HAG; ring.
  have Hdval : d = b + pow K by lra.
  have Hdb : d - b = pow K by rewrite Hdval; ring.
  split.
  - by rewrite Rabs_pos_eq //; lra.
  - by rewrite Rabs_pos_eq; rewrite Hdval; move: Hbpos; lra.
  by rewrite Hdb Rabs_pos_eq //; lra.
have HaA : a = - pow (K + p) by move: Hae; rewrite (Rabs_left _ Ha0); lra.
have FnAG : format (- (pow (K + p) - pow K)) by apply: generic_format_opp.
have Hnb := Hnear _ FnAG.
have Hble : b <= pow K / 2 by move: Hnb; rewrite -Hi HaA; split_Rabs; lra.
have Hbneg : b <= - (5 / 8 * pow K) by move: Hbl Hble Hb_G; split_Rabs; lra.
have Hcneg : c < 0 by rewrite Hce HaA; move: Hbneg Hd2G; split_Rabs; nra.
have Hc_up : - (pow (K + p) - pow K) <= c
  by move: Hcl; rewrite (Rabs_left _ Hcneg); lra.
have Hc_lo2 : c <= - (pow (K + p) - 11 / 8 * pow K)
  by rewrite Hce HaA; move: Hbneg Hd2G; split_Rabs; lra.
have Hmc_le : (mc < - (2 ^ p - 2))%Z.
  apply: lt_IZR; rewrite opp_IZR minus_IZR -Hpp2.
  by move: Hc_lo2; rewrite Hmc HAG; nra.
have Hmc_ge : (- (2 ^ p - 1) <= mc)%Z.
  apply: le_IZR; rewrite opp_IZR minus_IZR -Hpp2.
  by move: Hc_up; rewrite Hmc HAG; nra.
have Hmceq : mc = (- (2 ^ p - 1))%Z by lia.
have Hcval : c = - (pow (K + p) - pow K)
  by rewrite Hmc Hmceq opp_IZR minus_IZR -Hpp2 HAG; ring.
have Hdval : d = b - pow K by lra.
have Hdb : d - b = - pow K by rewrite Hdval; ring.
have Hdneg : d < 0 by rewrite Hdval; move: Hbneg; lra.
split.
- by rewrite (Rabs_left _ Hcneg) Hcval; lra.
- by rewrite (Rabs_left _ Hdneg) Hdval; move: Hbneg; lra.
by rewrite Hdb Rabs_Ropp Rabs_pos_eq //; lra.
Qed.

Lemma interval_pin (a b c d : R) (K : Z) :
  ties_to_even choice ->
  format c -> a = RND (c + d) ->
  is_imul a (pow (K + 1)) -> pow (K + p) <= Rabs a ->
  Rabs c <= pow (K + p) - pow K -> Rabs d <= pow (K + 1) ->
  a + b = c + d -> 5 / 8 * pow K <= Rabs b -> Rabs b <= / 2 * ulp a ->
  [/\ Rabs a = pow (K + p),
      Rabs c = pow (K + p) - pow K,
      pow K <= Rabs d &
      Rabs (d - b) = pow K ].
Proof.
move=> Heven Fc Hr Hai Hge Hcl Hdl Hi Hbl Hbh.
have HRa := interval_pin_abs Heven Fc Hr Hai Hge Hcl Hdl Hi Hbl Hbh.
have [HC HD HDB] := interval_pin_rest Heven Fc Hr Hai HRa Hcl Hdl Hi Hbl Hbh.
by split.
Qed.

Lemma vecSum_pinning_of_violation (l : seq R) (i j : nat) (k : Z) :
  ties_to_even choice -> (i.+1 < size l)%N -> {in l, forall z, format z} ->
  (forall m, (m < size l)%N -> nth 0 l m <> 0) ->
  sorted_mag l -> pairwise_ulp l -> (j <= i)%N ->
  nth 0 (vecSum l) j <> 0 -> uls (nth 0 (vecSum l) j) = pow k ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  [/\ Rabs (vecSumAux (drop i l)).2 = pow (k + p),
      Rabs (nth 0 l i) = pow (k + p) - pow k,
      is_imul (nth 0 (vecSum l) i.+1) (pow (k - p + 1)),
      pow k <= Rabs (vecSumAux (drop i.+1 l)).2 &
      (* the draft's "[s_i = u + e_i]", in signed form                        *)
      Rabs ((vecSumAux (drop i.+1 l)).2 - nth 0 (vecSum l) i.+1) = pow k ].
Proof.
move=> Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls Hviol.
have iLl : (i < size l)%N by apply: ltn_trans (ltnSn i) Hi.
have Ha_imul := vecSum_run_imul_of_violation Hi Hf Hviol.
have Ha_ge := vecSum_run_ge_of_violation Hi Hf Hviol.
have Hb_hi := vecSum_err_le_half_ulp_run Hi Hf.
have Fc : format (nth 0 l i) by apply: Hf; apply: mem_nth.
have [i'c Hi'c Hc] :=
  vecSum_inputs_le_1mu_of_violation Hi Hf Hsort Hji Hej0 Huls Hviol.
have Hc_le : Rabs (nth 0 l i) <= pow (k + p) - pow k
  by apply: Hc (ltnW Hi'c) iLl.
have Hi1 : (0 < i)%N by apply: leq_ltn_trans (leq0n i'c) Hi'c.
have [i'd Hi'd Hd] :=
  vecSum_run_le_2u_of_violation Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls Hviol.
have Hi1eq : (i.-1.+2 = i.+1)%N by rewrite prednK.
have Hle : (i'd <= i.-1)%N by rewrite -ltnS (prednK Hi1).
have Hd_sz : (i.-1.+2 < size l)%N by rewrite Hi1eq.
have Hd_le := Hd i.-1 Hle Hd_sz; rewrite Hi1eq in Hd_le.
have He : nth 0 (vecSum l) i.+1 =
          dwl (TwoSum (nth 0 l i) (vecSumAux (drop i.+1 l)).2).
  by rewrite -(vecSumAux_nth1 Hi) /vecSum; case: (vecSumAux l).
have Hsdwh : (vecSumAux (drop i l)).2 =
             dwh (TwoSum (nth 0 l i) (vecSumAux (drop i.+1 l)).2).
  have Hdne : (0 < size (drop i.+1 l))%N by rewrite size_drop subn_gt0.
  rewrite (drop_nth 0 iLl).
  case Hd0 : (drop i.+1 l) Hdne => [//|b0 l0] _.
  rewrite vecSumAux_cons; case E : (vecSumAux (b0 :: l0)) => [es s].
  by case: (TwoSum (nth 0 l i) s).
have Fs1 : format (vecSumAux (drop i.+1 l)).2.
  have Hdf : {in drop i.+1 l, forall z, format z}
    by move=> z /mem_drop; apply: Hf.
  by have [F _] := format_vecSumAux Hdf.
have Hcorr : dwh (TwoSum (nth 0 l i) (vecSumAux (drop i.+1 l)).2) +
             dwl (TwoSum (nth 0 l i) (vecSumAux (drop i.+1 l)).2) =
             nth 0 l i + (vecSumAux (drop i.+1 l)).2
  by exact: TwoSum_correct_loc Fc Fs1.
have Hid : (vecSumAux (drop i l)).2 + nth 0 (vecSum l) i.+1 =
           nth 0 l i + (vecSumAux (drop i.+1 l)).2
  by rewrite He Hsdwh.
have Ha_rnd : (vecSumAux (drop i l)).2 =
              RND (nth 0 l i + (vecSumAux (drop i.+1 l)).2)
  by rewrite Hsdwh TwoSum_hi.
have [HRs HRc HDd HDB] :=
  interval_pin Heven Fc Ha_rnd Ha_imul Ha_ge Hc_le Hd_le Hid Hviol Hb_hi.
split=> //.
(* [2u^2 | e_{i+1}]: the 2Sum error is a multiple of                           *)
(* [pow(min(cexp x_i, cexp s_{i+1}))], and both cexps are [>= k - p + 1]        *)
(* -- [cexp x_i = k] (from [|x_i| = 1 - u]) and [cexp s_{i+1} >= k-p+1] (from   *)
(* [|s_{i+1}| >= u]).                                                          *)
have Hmx : mag beta (nth 0 l i) = (k + p)%Z :> Z.
  apply: mag_unique; rewrite HRc; split; last by have := bpow_gt_0 beta k; lra.
  have -> : pow (k + p) = 2 * pow (k + p - 1)
    by rewrite (_ : (k + p = k + p - 1 + 1)%Z) ?bpow_plus ?bpow_1 /=; [lra|lia].
  have : pow k <= pow (k + p - 1) by apply: bpow_le; lia.
  lra.
have Hms1 : (k + 1 <= mag beta (vecSumAux (drop i.+1 l)).2)%Z.
  apply: mag_ge_bpow; have -> : (k + 1 - 1 = k)%Z by lia.
  exact: HDd.
rewrite He.
apply: is_imul_pow_le
  (@TwoSum_err_imul p Hp2 choice choice_sym _ _ Fc Fs1) _.
apply: Z.min_glb; rewrite /cexp /FLX_exp; [rewrite Hmx | ]; lia.
Qed.


(* Draft 5.2/5.3 workhorse: EVERY later error is bounded by the [uls]         *)
(* of any earlier nonzero one.  This is the paper's repeated step             *)
(* "[uls(e_i1)] <= 1/8 u, so [|e_{i1+1}|, ..., |e_5|] <= 1/8 u".              *)
(* Proof: with [uls(e_j) = pow K], either [|e_m| < 5/8 pow K] and there       *)
(* is nothing to do, or [|e_m|] reaches the violation threshold, the *2       *)
(* pinning applies and fixes [|s_{m-1}| = pow(K+p)], so                       *)
(* [ulp(s_{m-1}) = pow(K+1)] and the core tool                                *)
(* [|e_m| <= 1/2 ulp(s_{m-1})] gives exactly [|e_m| <= pow K].  Note          *)
(* [e_m] is NOT required to be nonzero, and no [size l <= 6] is needed.       *)
Lemma vecSum_tail_le_uls (l : seq R) (j m : nat) :
  ties_to_even choice ->
  {in l, forall z, format z} ->
  (forall i, (i < size l)%N -> nth (0:R) l i <> 0) ->
  sorted_mag l -> pairwise_ulp l ->
  (j < m)%N -> (m < size (vecSum l))%N ->
  nth 0 (vecSum l) j <> 0 ->
  Rabs (nth 0 (vecSum l) m) <= uls (nth 0 (vecSum l) j).
Proof.
move=> Heven Hfmt Hnz Hsort Hpair Hjm Hm Hnj.
have [K HK] := uls_pow Hnj.
have HpK := bpow_gt_0 beta K.
rewrite HK.
case: m Hjm Hm => [//|m'] Hjm Hm.
case: (Rle_lt_dec (5 / 8 * pow K) (Rabs (nth 0 (vecSum l) m'.+1))) =>
      [Hviol|Hsmall]; last by lra.
(* the violation case: the pinning fixes [ulp(s_{m-1})] exactly               *)
have Hszl : (m'.+1 < size l)%N.
  move: Hm; rewrite size_vecSum ltnS => Hm'.
  have H0 : (0 < size l)%N by case: (size l) Hm'.
  by rewrite -(prednK H0) ltnS.
have Hji : (j <= m')%N by rewrite -ltnS.
have [HRs _ _] :=
  vecSum_pinning_of_violation Heven Hszl Hfmt Hnz Hsort Hpair Hji Hnj HK
                              Hviol.
have Hulp := vecSum_err_le_half_ulp_run Hszl Hfmt.
rewrite (ulp_of_abs_pow HRs) in Hulp.
have Hee : (K + p - p + 1 = K + 1)%Z by lia.
rewrite Hee bpow_plus bpow_1 /= in Hulp.
lra.
Qed.


(* Draft 5.2, "at the right of i", the CASE LIST.  There the violating        *)
(* error satisfies [2u^2 | e_i] (the pinning) and [e_i <= u]                  *)
(* ([vecSum_tail_le_uls]), and the proof splits on [e_i = u],                 *)
(* [e_i = u - 2u^2], or [e_i <= u - 4u^2].  Scale-invariantly, with           *)
(* [t = pow K] for [u] and [g = pow(K-p+1)] for [2u^2]: a multiple of         *)
(* [g] bounded by [t] is [t], [t - g], or at most [t - 2g], because           *)
(* [t / g = pow(p-1)] is an integer, so the multiples of [g] below [t]        *)
(* step down by [g] from [t] itself.                                          *)
Lemma imul_case_split (x : R) (K : Z) :
  is_imul x (pow (K - p + 1)) -> Rabs x <= pow K ->
  [\/ Rabs x = pow K,
      Rabs x = pow K - pow (K - p + 1) |
      Rabs x <= pow K - 2 * pow (K - p + 1) ].
Proof.
move=> [n Hn] Hle.
have Hg := bpow_gt_0 beta (K - p + 1).
(* [t = pow(p-1) * g]: the number of [g]-steps up to [t] is an integer        *)
have Hpm : pow (p - 1) = IZR (2 ^ (p - 1))
  by rewrite -IZR_Zpower; [congr IZR|lia].
have Ht : pow K = IZR (2 ^ (p - 1)) * pow (K - p + 1).
  by rewrite -Hpm -bpow_plus; congr bpow; lia.
have HN : (0 < 2 ^ (p - 1))%Z by apply: Z.pow_pos_nonneg; lia.
have Hgp : 0 <= pow (K - p + 1) by apply: bpow_ge_0.
have Hxa : Rabs x = IZR (Z.abs n) * pow (K - p + 1).
  by rewrite Hn Rabs_mult abs_IZR (Rabs_pos_eq _ Hgp).
(* [|n| <= 2^(p-1)] from [|x| <= t]                                           *)
have Hn_le : (Z.abs n <= 2 ^ (p - 1))%Z.
  apply: le_IZR; apply: (Rmult_le_reg_r (pow (K - p + 1))) => //.
  by rewrite -Hxa -Ht.
(* three cases on how far [|n|] sits below [2^(p-1)]                          *)
case: (Z.eq_dec (Z.abs n) (2 ^ (p - 1))) => [Heq|Hne].
  by apply: Or31; rewrite Hxa Heq Ht.
case: (Z.eq_dec (Z.abs n) (2 ^ (p - 1) - 1)) => [Heq1|Hne1].
  apply: Or32; rewrite Hxa Heq1 Ht minus_IZR.
  by rewrite Rmult_minus_distr_r Rmult_1_l.
apply: Or33; rewrite Hxa Ht.
have Hn2 : (Z.abs n <= 2 ^ (p - 1) - 2)%Z by lia.
have := IZR_le _ _ Hn2; rewrite minus_IZR => Hle2.
have -> : IZR (2 ^ (p - 1)) * pow (K - p + 1) -
          2 * pow (K - p + 1) =
          (IZR (2 ^ (p - 1)) - 2) * pow (K - p + 1) by lra.
by apply: Rmult_le_compat_r; lra.
Qed.


(* Draft 5.2 "at the right of i", instantiated at a violation: the            *)
(* violating error is [e_i = u], [e_i = u - 2u^2], or [e_i <= u - 4u^2].      *)
(* The divisibility [2u^2 | e_i] comes from the pinning and the ceiling       *)
(* [e_i <= u] from [vecSum_tail_le_uls]; [imul_case_split] then splits.       *)
Lemma vecSum_err_case_of_violation (l : seq R) (i j : nat) (k : Z) :
  ties_to_even choice -> (i.+1 < size l)%N -> {in l, forall z, format z} ->
  (forall m, (m < size l)%N -> nth 0 l m <> 0) ->
  sorted_mag l -> pairwise_ulp l -> (j <= i)%N ->
  nth 0 (vecSum l) j <> 0 -> uls (nth 0 (vecSum l) j) = pow k ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  [\/ Rabs (nth 0 (vecSum l) i.+1) = pow k,
      Rabs (nth 0 (vecSum l) i.+1) = pow k - pow (k - p + 1) |
      Rabs (nth 0 (vecSum l) i.+1) <= pow k - 2 * pow (k - p + 1) ].
Proof.
move=> Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls Hviol.
have [_ _ Him _ _] :=
  vecSum_pinning_of_violation Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls
                              Hviol.
have H0 : (0 < size l)%N by case: (size l) Hi.
have Hsz : (i.+1 < size (vecSum l))%N by rewrite size_vecSum prednK.
have Hle := vecSum_tail_le_uls Heven Hf Hnz Hsort Hpair (leq_ltn_trans Hji
                               (ltnSn i)) Hsz Hej0.
rewrite Huls in Hle.
exact: imul_case_split Him Hle.
Qed.


(* If [s] sits at signed distance exactly [G] from [e], is itself at          *)
(* least [G] away from 0, and [e] is smaller than [2G], then [s] lies on      *)
(* the FAR side of [e]: [|s| = |e| + G].  (The near side would put [s]        *)
(* strictly inside [(-G, G)], contradicting [G <= |s|].)  This is what        *)
(* turns the draft's [s_i = u + e_i] into its per-case values.                *)
Lemma abs_pin_add (s e G : R) :
  Rabs (s - e) = G -> G <= Rabs s -> 0 < Rabs e -> Rabs e < 2 * G ->
  Rabs s = Rabs e + G.
Proof. by move=> Hse Hsg He0 He2; move: Hse Hsg He0 He2; split_Rabs; lra. Qed.

(* Draft 5.2, "[s_i = u + e_i]": at a violation, as soon as the error         *)
(* stays below [2u] the running sum is pushed to [|e_i| + u].  Both of        *)
(* the draft's named cases ([e_i = u] and [e_i = u - 2u^2]) satisfy that      *)
(* bound, so this one lemma yields both of their [s_i] values.                *)
Lemma vecSum_run_val_of_violation (l : seq R) (i j : nat) (k : Z) :
  ties_to_even choice -> (i.+1 < size l)%N -> {in l, forall z, format z} ->
  (forall m, (m < size l)%N -> nth 0 l m <> 0) ->
  sorted_mag l -> pairwise_ulp l -> (j <= i)%N ->
  nth 0 (vecSum l) j <> 0 -> uls (nth 0 (vecSum l) j) = pow k ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  Rabs (nth 0 (vecSum l) i.+1) < 2 * pow k ->
  Rabs (vecSumAux (drop i.+1 l)).2 =
    Rabs (nth 0 (vecSum l) i.+1) + pow k.
Proof.
move=> Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls Hviol Hlt.
have Hpk := bpow_gt_0 beta k.
have [_ _ _ HDd HDB] :=
  vecSum_pinning_of_violation Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls
                              Hviol.
by apply: abs_pin_add HDB HDd _ Hlt; lra.
Qed.

(* Draft 5.2 "at the right of i", COMPLETE: the three cases together          *)
(* with the running-sum value each forces.  Cases 1 and 2 are the             *)
(* draft's [e_i = u, s_i = 2u] and [e_i = u - 2u^2, s_i = 2u - 2u^2];         *)
(* case 3 is its [e_i <= u - 4u^2] remainder.                                 *)
Lemma vecSum_right_of_i_cases (l : seq R) (i j : nat) (k : Z) :
  ties_to_even choice -> (i.+1 < size l)%N -> {in l, forall z, format z} ->
  (forall m, (m < size l)%N -> nth 0 l m <> 0) ->
  sorted_mag l -> pairwise_ulp l -> (j <= i)%N ->
  nth 0 (vecSum l) j <> 0 -> uls (nth 0 (vecSum l) j) = pow k ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  [\/ Rabs (nth 0 (vecSum l) i.+1) = pow k /\
      Rabs (vecSumAux (drop i.+1 l)).2 = 2 * pow k,
      Rabs (nth 0 (vecSum l) i.+1) = pow k - pow (k - p + 1) /\
      Rabs (vecSumAux (drop i.+1 l)).2 = 2 * pow k - pow (k - p + 1) |
      Rabs (nth 0 (vecSum l) i.+1) <= pow k - 2 * pow (k - p + 1) ].
Proof.
move=> Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls Hviol.
have Hpk := bpow_gt_0 beta k.
have Hg : pow (k - p + 1) < pow k by apply: bpow_lt; lia.
have Hgp := bpow_gt_0 beta (k - p + 1).
have Hval := vecSum_run_val_of_violation Heven Hi Hf Hnz Hsort Hpair Hji
                                         Hej0 Huls Hviol.
case: (vecSum_err_case_of_violation Heven Hi Hf Hnz Hsort Hpair Hji Hej0
                                    Huls Hviol) => [He|He|He].
- by apply: Or31; split=> //; rewrite Hval ?He; lra.
- by apply: Or32; split=> //; rewrite Hval ?He; lra.
by apply: Or33.
Qed.


(* The VecSum step at index [i], as reusable facts: the exact 2Sum            *)
(* identity [s_i + e_{i+1} = x_i + s_{i+1}] and [s_i = RND(x_i +              *)
(* s_{i+1})].  Both were derived inline inside                                *)
(* [vecSum_pinning_of_violation]; the counting argument needs them at         *)
(* other indices, so they are factored out here.                              *)
Lemma vecSum_run_dwh (l : seq R) (i : nat) :
  (i.+1 < size l)%N ->
  (vecSumAux (drop i l)).2 =
    dwh (TwoSum (nth 0 l i) (vecSumAux (drop i.+1 l)).2).
Proof.
move=> Hi.
have iLl : (i < size l)%N by apply: ltn_trans (ltnSn i) Hi.
have Hdne : (0 < size (drop i.+1 l))%N by rewrite size_drop subn_gt0.
rewrite (drop_nth 0 iLl).
case Hd0 : (drop i.+1 l) Hdne => [//|b0 l0] _.
rewrite vecSumAux_cons; case E : (vecSumAux (b0 :: l0)) => [es s].
by case: (TwoSum (nth 0 l i) s).
Qed.

Lemma vecSum_run_dwl (l : seq R) (i : nat) :
  (i.+1 < size l)%N ->
  nth 0 (vecSum l) i.+1 =
    dwl (TwoSum (nth 0 l i) (vecSumAux (drop i.+1 l)).2).
Proof.
by move=> Hi; rewrite -(vecSumAux_nth1 Hi) /vecSum; case: (vecSumAux l).
Qed.

Lemma vecSum_run_step (l : seq R) (i : nat) :
  (i.+1 < size l)%N -> {in l, forall z, format z} ->
  (vecSumAux (drop i l)).2 + nth 0 (vecSum l) i.+1 =
    nth 0 l i + (vecSumAux (drop i.+1 l)).2.
Proof.
move=> Hi Hf.
have iLl : (i < size l)%N by apply: ltn_trans (ltnSn i) Hi.
have Fc : format (nth 0 l i) by apply: Hf; apply: mem_nth.
have Fs1 : format (vecSumAux (drop i.+1 l)).2.
  have Hdf : {in drop i.+1 l, forall z, format z}
    by move=> z /mem_drop; apply: Hf.
  by have [F _] := format_vecSumAux Hdf.
have Hcorr := TwoSum_correct_loc Fc Fs1.
by rewrite (vecSum_run_dwl Hi) (vecSum_run_dwh Hi).
Qed.

Lemma vecSum_run_rnd (l : seq R) (i : nat) :
  (i.+1 < size l)%N ->
  (vecSumAux (drop i l)).2 =
    RND (nth 0 l i + (vecSumAux (drop i.+1 l)).2).
Proof. by move=> Hi; rewrite (vecSum_run_dwh Hi) TwoSum_hi. Qed.

(* A running sum past the end of the list is [0]; contrapositive: a           *)
(* nonzero running sum pins its index inside the list.  This is how the       *)
(* draft's "[s_{i+2} <> 0]" turns into "in particular [i <= 3]".              *)
Lemma vecSum_run_nz_lt_size (l : seq R) (i : nat) :
  (vecSumAux (drop i l)).2 <> 0 -> (i < size l)%N.
Proof.
move=> Hnz; case: (leqP (size l) i) => [Hle|//].
by case: Hnz; rewrite (drop_oversize Hle).
Qed.

(* At the last index the running sum IS the input.                            *)
Lemma vecSum_run_last (l : seq R) (i : nat) :
  size l = i.+1 -> (vecSumAux (drop i l)).2 = nth 0 l i.
Proof.
move=> Hsz.
have iLl : (i < size l)%N by rewrite Hsz ltnSn.
rewrite (drop_nth 0 iLl).
have -> : drop i.+1 l = [::] by apply: drop_oversize; rewrite Hsz.
by [].
Qed.

(* Draft 5.2, "so we must have s_{i+1} >= u": from [|s_i| >= 2u], the         *)
(* input bound [|x_i| <= u - u^2] and the tail error [|e_{i+1}| <= u^2],      *)
(* the exact step identity [s_{i+1} = s_i + e_{i+1} - x_i] leaves at          *)
(* least [2u - u^2 - (u - u^2) = u].                                          *)
Lemma vecSum_run_ge_next (l : seq R) (i : nat) (k : Z) :
  (i.+2 < size l)%N -> {in l, forall z, format z} ->
  2 * pow k <= Rabs (vecSumAux (drop i.+1 l)).2 ->
  Rabs (nth 0 l i.+1) <= pow k - pow (k - p) ->
  Rabs (nth 0 (vecSum l) i.+2) <= pow (k - p) ->
  pow k <= Rabs (vecSumAux (drop i.+2 l)).2.
Proof.
move=> Hsz Hf Hs Hx He.
have Hst := vecSum_run_step Hsz Hf.
by move: Hst Hs Hx He; split_Rabs; lra.
Qed.


Lemma leq6_of_gt2 (n : nat) : (2 < n)%N -> (6 <= n.+3)%N.
Proof. by case: n => [|[|[|n]]]. Qed.

(* Draft 5.2, case [e_i = u], THE COUNTING: "so we must have                  *)
(* s_{i+1} >= u with x_{i+1} < u, so s_{i+2} <> 0.  In particular,            *)
(* i <= 3."  (Our [i] is the draft's [i-1], so the conclusion reads           *)
(* [i <= 2].)  The running sum two steps on is still at least [u],            *)
(* while every input from there on is below [u]; a running sum that has       *)
(* run off the end of the list is [0], and one sitting at the very last       *)
(* index IS that input -- either way it cannot reach [u].  So the list        *)
(* must extend at least to [i+3], and [size l <= 6] caps [i].                 *)
Lemma vecSum_right_of_i_count (l : seq R) (i j : nat) (k : Z) :
  ties_to_even choice -> (size l <= 6)%N -> (i.+1 < size l)%N ->
  {in l, forall z, format z} ->
  (forall m, (m < size l)%N -> nth 0 l m <> 0) ->
  sorted_mag l -> pairwise_ulp l -> (j <= i)%N ->
  nth 0 (vecSum l) j <> 0 -> uls (nth 0 (vecSum l) j) = pow k ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  Rabs (nth 0 (vecSum l) i.+1) = pow k ->
  (i <= 2)%N.
Proof.
move=> Heven Hsz6 Hi Hf Hnz Hsort Hpair Hji Hej0 Huls Hviol Heq.
have Hpk := bpow_gt_0 beta k.
have Hpkp := bpow_gt_0 beta (k - p).
have Hlt2 : Rabs (nth 0 (vecSum l) i.+1) < 2 * pow k by rewrite Heq; lra.
(* the draft's [s_i = 2u]                                                     *)
have Hs1 : Rabs (vecSumAux (drop i.+1 l)).2 = 2 * pow k.
  rewrite (vecSum_run_val_of_violation Heven Hi Hf Hnz Hsort Hpair Hji
                                       Hej0 Huls Hviol Hlt2) Heq.
  by lra.
have [ix Hix Hxlt] :=
  vecSum_inputs_lt_u_of_violation Hi Hf Hsort Hpair Hji Hej0 Huls Hviol.
have Hi0 : (0 < i)%N by apply: leq_ltn_trans (leq0n ix) Hix.
have Hpred : (i.-1.+2 = i.+1)%N by rewrite prednK.
have Hixle : (ix <= i.-1)%N by rewrite -ltnS prednK.
(* the list must reach i+2: otherwise s_{i+1} would BE x_{i+1} < u            *)
have HA : (i.+2 < size l)%N.
  case: (ltnP i.+2 (size l)) => [//|Hge].
  have Hszeq : size l = i.+2 by apply/eqP; rewrite eqn_leq Hge Hi.
  have Hx1 : Rabs (nth 0 l i.+1) < pow k.
    have H := Hxlt i.-1 Hixle; rewrite Hpred in H.
    by apply: H; rewrite Hszeq.
  by move: Hs1; rewrite (vecSum_run_last Hszeq) => H2; move: Hx1; lra.
(* the draft's [x_{i+1} <= u - u^2] and [|e_{i+2}| <= u^2]                    *)
have Hx1 : Rabs (nth 0 l i.+1) < pow k.
  have H := Hxlt i.-1 Hixle; rewrite Hpred in H; exact: H Hi.
have Hx1p : Rabs (nth 0 l i.+1) <= pow k - pow (k - p).
  have Fx : format (nth 0 l i.+1) by apply: Hf; apply: mem_nth.
  by have := abs_le_pred_of_lt Fx Hx1.
have [ie Hie Hetail] :=
  vecSum_tail_err_le_u2_of_violation Heven Hi Hf Hnz Hsort Hpair Hji Hej0
                                     Huls Hviol.
have Hiele : (ie <= i.-1)%N by rewrite -ltnS prednK.
have He2 : Rabs (nth 0 (vecSum l) i.+2) <= pow (k - p).
  have H := Hetail i.-1 Hiele.
  rewrite (_ : (i.-1.+2.+1 = i.+2)%N) in H; last by rewrite prednK.
  exact: H HA.
(* the draft's [s_{i+1} >= u]                                                 *)
have Hs1' : 2 * pow k <= Rabs (vecSumAux (drop i.+1 l)).2
  by rewrite Hs1; lra.
have HB := vecSum_run_ge_next HA Hf Hs1' Hx1p He2.
(* [i >= 3] would strand that running sum at or past the last index           *)
rewrite leqNgt; apply/negP => Hi3.
have H36 := leq6_of_gt2 Hi3.
have Hszeq : size l = i.+3.
  by apply/eqP; rewrite eqn_leq HA andbT; apply: leq_trans Hsz6 H36.
have Hx2 : Rabs (nth 0 l i.+2) < pow k.
  by apply: (Hxlt i (ltnW Hix)); rewrite Hszeq.
by move: HB; rewrite (vecSum_run_last Hszeq); lra.
Qed.




(* The MIRROR of [VecSum.RN_midpoint_even]: the tie just BELOW a power of     *)
(* two.  [pow e - pow(e-p-1)] is halfway between [pow e - pow(e-p)]           *)
(* (mantissa [2^p - 1], odd) and [pow e] (mantissa [2^p], even), so           *)
(* ties-to-even sends it UP to [pow e].  This is what makes the draft's       *)
(* "case x_{i-2} = 1-u ... s_{i-2} = 2" come out exact.                       *)
Lemma RN_midpoint_even_lo (e : Z) : ties_to_even choice ->
  RND (pow e - pow (e - p - 1)) = pow e.
Proof.
move=> Heven.
have Hpe := bpow_gt_0 beta e.
have Hpep := bpow_gt_0 beta (e - p - 1).
have Hlt1 : pow (e - p - 1) < pow (e - 1) by apply: bpow_lt; lia.
have Haux1 : pow ((e - 1) + 1)%Z = 2 * pow (e - 1).
  by rewrite bpow_plus bpow_1 /=; lra.
have He1 : pow e = 2 * pow (e - 1).
  by rewrite -Haux1; congr bpow; lia.
have Hx0 : 0 < pow e - pow (e - p - 1) by lra.
have Hmagx : mag beta (pow e - pow (e - p - 1)) = e :> Z.
  by apply: mag_unique_pos; split; lra.
have Hcexp : cexp (pow e - pow (e - p - 1)) = (e - p)%Z.
  by rewrite /cexp Hmagx /FLX_exp.
have Hpm1 : pow (-1)%Z = / 2 by rewrite /= /Z.pow_pos /=; lra.
have Hpp : pow p = IZR (2 ^ p).
  have -> : (2 = radix2 :> Z)%Z by [].
  by rewrite IZR_Zpower //; lia.
have Hppg := bpow_gt_0 beta p.
have Hsm : mant (pow e - pow (e - p - 1)) = pow p - / 2.
  rewrite /scaled_mantissa Hcexp Rmult_minus_distr_r -!bpow_plus.
  have -> : (e + - (e - p) = p)%Z by lia.
  have -> : (e - p - 1 + - (e - p) = -1)%Z by lia.
  by rewrite Hpm1.
have Hfloor : Zfloor (mant (pow e - pow (e - p - 1))) = (2 ^ p - 1)%Z.
  rewrite Hsm; apply: Zfloor_imp.
  have -> : (2 ^ p - 1 + 1 = 2 ^ p)%Z by lia.
  by rewrite minus_IZR -Hpp; lra.
have Hceil : Zceil (mant (pow e - pow (e - p - 1))) = (2 ^ p)%Z.
  rewrite Hsm; apply: Zceil_imp.
  by rewrite minus_IZR -Hpp; lra.
have HRD : round beta fexp Zfloor (pow e - pow (e - p - 1)) =
           pow e - pow (e - p).
  rewrite /round Hfloor Hcexp /F2R /= minus_IZR -Hpp Rmult_minus_distr_r.
  by rewrite -bpow_plus Rmult_1_l; congr (_ - _); congr bpow; lia.
have HRU : round beta fexp Zceil (pow e - pow (e - p - 1)) = pow e.
  rewrite /round Hceil Hcexp /F2R /= -Hpp -bpow_plus.
  by congr bpow; lia.
have Haux2 : pow ((e - p - 1) + 1)%Z = 2 * pow (e - p - 1).
  by rewrite bpow_plus bpow_1 /=; lra.
have Hhalf : pow (e - p) = 2 * pow (e - p - 1).
  by rewrite -Haux2; congr bpow; lia.
have Hmid :
  (pow e - pow (e - p - 1)) -
    round beta fexp Zfloor (pow e - pow (e - p - 1)) =
  round beta fexp Zceil (pow e - pow (e - p - 1)) -
    (pow e - pow (e - p - 1)).
  by rewrite HRD HRU Hhalf; lra.
rewrite (@round_N_middle beta fexp choice _ Hmid) Hfloor.
have Heven2p : Z.even (2 ^ p) = true.
  have -> : (2 ^ p = 2 * 2 ^ (p - 1))%Z.
    by rewrite -Z.pow_succ_r; [congr (_ ^ _)%Z; lia | lia].
  by rewrite Z.even_mul.
have -> : choice (2 ^ p - 1) = true.
  by rewrite Heven Z.even_sub Heven2p.
exact: HRU.
Qed.

(* ---- 5.2, "at the left of i" -------------------------------------------*)

(* Draft 5.2: "we saw that x_{i-1} = 1-u and x_{i-2} < 1, so                  *)
(* |x_{i-2}| = 1-u".  The pinning gives [|x_i| = A - G] (our index [i] is     *)
(* the draft's [i-1]); [sorted_mag] pushes that up to the previous input,     *)
(* while being a float below [A] pushes it back down -- so the previous       *)
(* input has exactly the same magnitude.                                      *)
Lemma vecSum_left_x_eq (l : seq R) (i j : nat) (k : Z) :
  ties_to_even choice -> (i.+1 < size l)%N -> {in l, forall z, format z} ->
  (forall m, (m < size l)%N -> nth 0 l m <> 0) ->
  sorted_mag l -> pairwise_ulp l -> (j <= i)%N ->
  nth 0 (vecSum l) j <> 0 -> uls (nth 0 (vecSum l) j) = pow k ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  Rabs (nth 0 l i.-1) = pow (k + p) - pow k.
Proof.
move=> Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls Hviol.
have iLl : (i < size l)%N by apply: ltn_trans (ltnSn i) Hi.
have [_ HRc _ _ _] :=
  vecSum_pinning_of_violation Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls
                              Hviol.
have [i' Hi'i Hlt] :=
  vecSum_inputs_lt_of_violation Hi Hf Hsort Hji Hej0 Huls Hviol.
have Hi0 : (0 < i)%N by apply: leq_ltn_trans (leq0n i') Hi'i.
have Hi'le : (i' <= i.-1)%N by rewrite -ltnS prednK.
have Hi1Ll : (i.-1 < size l)%N by apply: leq_ltn_trans (leq_pred i) iLl.
(* a float strictly below [A] is at most its predecessor [A - G]              *)
have Hup : Rabs (nth 0 l i.-1) <= pow (k + p) - pow k.
  have Fx : format (nth 0 l i.-1) by apply: Hf; apply: mem_nth.
  have H := abs_le_pred_of_lt Fx (Hlt i.-1 Hi'le Hi1Ll).
  by rewrite (_ : (k + p - p = k)%Z) in H; [|lia].
(* and isotony keeps it at least [|x_i| = A - G]                              *)
have Hlo : Rabs (nth 0 l i) <= Rabs (nth 0 l i.-1).
  by apply: sorted_mag_le_nth Hsort (leq_pred i) iLl.
by move: Hlo; rewrite HRc; lra.
Qed.


(* Draft 5.2's split "case x_{i-2} = -1+u" / "case x_{i-2} = 1-u": with       *)
(* [|x_{i-1}| = A - G] and [|s_i| = A], the pair either cancels (sum [G],     *)
(* the draft's [-1+u] case) or reinforces (sum [2A - G], its [1-u]            *)
(* case).  Stated on the SUM, so no sign bookkeeping leaks out.               *)
Lemma vecSum_left_sum_cases (l : seq R) (i j : nat) (k : Z) :
  ties_to_even choice -> (i.+1 < size l)%N -> {in l, forall z, format z} ->
  (forall m, (m < size l)%N -> nth 0 l m <> 0) ->
  sorted_mag l -> pairwise_ulp l -> (j <= i)%N ->
  nth 0 (vecSum l) j <> 0 -> uls (nth 0 (vecSum l) j) = pow k ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  Rabs (nth 0 l i.-1 + (vecSumAux (drop i l)).2) = pow k \/
  Rabs (nth 0 l i.-1 + (vecSumAux (drop i l)).2) =
    2 * pow (k + p) - pow k.
Proof.
move=> Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls Hviol.
have HX :=
  vecSum_left_x_eq Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls Hviol.
have [HRs _ _ _ _] :=
  vecSum_pinning_of_violation Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls
                              Hviol.
have HG := bpow_gt_0 beta k.
have HA := bpow_gt_0 beta (k + p).
have HGA : pow k < pow (k + p) by apply: bpow_lt; lia.
have H1 : nth 0 l i.-1 = pow (k + p) - pow k \/
          nth 0 l i.-1 = - (pow (k + p) - pow k).
  by move: HX; split_Rabs; lra.
have H2 : (vecSumAux (drop i l)).2 = pow (k + p) \/
          (vecSumAux (drop i l)).2 = - pow (k + p).
  by move: HRs; split_Rabs; lra.
by case: H1 => ->; case: H2 => ->; [right|left|left|right];
   split_Rabs; lra.
Qed.

(* Draft 5.2, case [x_{i-2} = -1+u]: "then e_{i-1} = 0 and s_{i-2} = u".      *)
(* The cancelling sum is [+/- G], already a float, so the 2Sum at that        *)
(* step is EXACT: the running sum takes the value and the error is [0].       *)
Lemma vecSum_left_opp (l : seq R) (i j : nat) (k : Z) :
  ties_to_even choice -> (i.+1 < size l)%N -> {in l, forall z, format z} ->
  (forall m, (m < size l)%N -> nth 0 l m <> 0) ->
  sorted_mag l -> pairwise_ulp l -> (j <= i)%N ->
  nth 0 (vecSum l) j <> 0 -> uls (nth 0 (vecSum l) j) = pow k ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  Rabs (nth 0 l i.-1 + (vecSumAux (drop i l)).2) = pow k ->
  Rabs (vecSumAux (drop i.-1 l)).2 = pow k /\ nth 0 (vecSum l) i = 0.
Proof.
move=> Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls Hviol Hsum.
have iLl : (i < size l)%N by apply: ltn_trans (ltnSn i) Hi.
have [i' Hi'i _] :=
  vecSum_inputs_lt_of_violation Hi Hf Hsort Hji Hej0 Huls Hviol.
have Hi0 : (0 < i)%N by apply: leq_ltn_trans (leq0n i') Hi'i.
have Hpk : (i.-1.+1 = i)%N by rewrite prednK.
have Hsz : (i.-1.+1 < size l)%N by rewrite Hpk.
(* the cancelling sum is a float, so the step rounds exactly                  *)
have HG := bpow_gt_0 beta k.
have Fsum : format (nth 0 l i.-1 + (vecSumAux (drop i l)).2).
  have H : nth 0 l i.-1 + (vecSumAux (drop i l)).2 = pow k \/
           nth 0 l i.-1 + (vecSumAux (drop i l)).2 = - pow k.
    by move: Hsum; split_Rabs; lra.
  case: H => ->; first by apply: format_pow.
  by apply/generic_format_opp/format_pow.
have Hrnd := vecSum_run_rnd Hsz.
have Hstep := vecSum_run_step Hsz Hf.
rewrite Hpk in Hrnd Hstep.
have Hs : (vecSumAux (drop i.-1 l)).2 =
          nth 0 l i.-1 + (vecSumAux (drop i l)).2.
  by rewrite Hrnd round_generic.
split; first by rewrite Hs.
by move: Hstep; rewrite Hs; lra.
Qed.


(* Draft 5.2, case [x_{i-2} = 1-u]: "then e_{i-1} = -u and s_{i-2} = 2".      *)
(* Here the pair reinforces, giving the sum [2A - G] -- exactly the tie       *)
(* just below [2A], which ties-to-even sends UP to [2A]                       *)
(* ([RN_midpoint_even_lo]).  The 2Sum error is then the discarded [G].        *)
Lemma vecSum_left_same (l : seq R) (i j : nat) (k : Z) :
  ties_to_even choice -> (i.+1 < size l)%N -> {in l, forall z, format z} ->
  (forall m, (m < size l)%N -> nth 0 l m <> 0) ->
  sorted_mag l -> pairwise_ulp l -> (j <= i)%N ->
  nth 0 (vecSum l) j <> 0 -> uls (nth 0 (vecSum l) j) = pow k ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  Rabs (nth 0 l i.-1 + (vecSumAux (drop i l)).2) =
    2 * pow (k + p) - pow k ->
  Rabs (vecSumAux (drop i.-1 l)).2 = 2 * pow (k + p) /\
  Rabs (nth 0 (vecSum l) i) = pow k.
Proof.
move=> Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls Hviol Hsum.
have iLl : (i < size l)%N by apply: ltn_trans (ltnSn i) Hi.
have [i' Hi'i _] :=
  vecSum_inputs_lt_of_violation Hi Hf Hsort Hji Hej0 Huls Hviol.
have Hi0 : (0 < i)%N by apply: leq_ltn_trans (leq0n i') Hi'i.
have Hpk : (i.-1.+1 = i)%N by rewrite prednK.
have Hsz : (i.-1.+1 < size l)%N by rewrite Hpk.
(* [2A = pow(k+p+1)] and [G = pow((k+p+1) - p - 1)]                           *)
have H2A : 2 * pow (k + p) = pow (k + p + 1).
  have -> : pow (k + p + 1) = pow (k + p) * pow 1.
    by rewrite -bpow_plus; congr bpow; lia.
  by rewrite bpow_1 /=; lra.
have HG : pow k = pow (k + p + 1 - p - 1).
  by congr bpow; lia.
(* the tie rounds up, in either sign                                          *)
have Hmid : RND (2 * pow (k + p) - pow k) = 2 * pow (k + p).
  by rewrite H2A HG; apply: RN_midpoint_even_lo.
have Hmidn : RND (- (2 * pow (k + p) - pow k)) = - (2 * pow (k + p)).
  by rewrite (@RN_opp_sym p choice choice_sym) Hmid.
have Hrnd := vecSum_run_rnd Hsz.
have Hstep := vecSum_run_step Hsz Hf.
rewrite Hpk in Hrnd Hstep.
have HA := bpow_gt_0 beta (k + p).
have HGp := bpow_gt_0 beta k.
have H : nth 0 l i.-1 + (vecSumAux (drop i l)).2 =
         2 * pow (k + p) - pow k \/
         nth 0 l i.-1 + (vecSumAux (drop i l)).2 =
         - (2 * pow (k + p) - pow k).
  by move: Hsum; split_Rabs; lra.
case: H => HE; rewrite HE in Hrnd Hstep.
- rewrite Hmid in Hrnd; split; first by rewrite Hrnd Rabs_pos_eq; lra.
  by move: Hstep; rewrite Hrnd; split_Rabs; lra.
rewrite Hmidn in Hrnd; split.
  by rewrite Hrnd Rabs_Ropp Rabs_pos_eq; lra.
by move: Hstep; rewrite Hrnd; split_Rabs; lra.
Qed.

(* ===========================================================================*)
(*  Step *3 (doc/thm6.md 5.3): the VSEB part.                                 *)
(*                                                                            *)
(*  The draft fixes [i_0] with [y_j = r_{i_0-1}] (so [eps_{i_0} <> 0]), lets  *)
(*  [i_1] the index of the first nonzero [e_i] after [e_{i_0}], normalises    *)
(*  [uls(e_{i_0}) = u], and records the two opening facts                     *)
(*  [|eps_{i_0}| >= u] and [ulp(y_j) >= 2 |eps_{i_0}|].  Every subsequent     *)
(*  estimate then has the SAME shape: bound [|e_{i_1}|] by a multiple of      *)
(*  [|eps_{i_0}|], add, and round.                                            *)
(* ===========================================================================*)

(* Draft 5.3, the recurring estimate.  With [ulp(y_j) >= 2|eps|] (the         *)
(* opening fact) and [|e| <= c * |eps|], the next emitted word                *)
(* [r = RND(eps + e)] obeys [|r| <= (1+c)/2 * ulp(y_j)].  Instantiating       *)
(* [c] reproduces the draft's constants: [c = 5/8] gives the 13/16            *)
(* bound, [c = 1/2] gives 3/4, [c = 1/4] gives 5/8.                           *)
Lemma vseb_next_le (yj eps e : R) (c : R) :
  2 * Rabs eps <= ulp yj ->
  Rabs e <= c * Rabs eps ->
  0 <= c ->
  format ((1 + c) / 2 * ulp yj) ->
  Rabs (RND (eps + e)) <= (1 + c) / 2 * ulp yj.
Proof.
move=> Hulp He Hc FB.
apply: Rabs_round_le_r => //.
have Habs : Rabs (eps + e) <= Rabs eps + Rabs e by apply: Rabs_triang.
have Hpe : 0 <= Rabs eps by apply: Rabs_pos.
by nra.
Qed.


(* Draft 5.3 opening, first fact: "[|eps_{i_0}| >= u]".  Scale-free, with     *)
(* the draft's normalisation [uls(e_{i_0}) = u] kept symbolic: the emitted    *)
(* remainder has [uls] at least that of the error consumed                    *)
(* ([TwoSum_err_uls_ge]), and [uls] is below the absolute value.              *)
Lemma vseb_emit_abs_ge (eps e : R) :
  format eps -> format e -> eps <> 0 -> e <> 0 ->
  uls e <= uls eps -> dwl (TwoSum eps e) <> 0 ->
  uls e <= Rabs (dwl (TwoSum eps e)).
Proof.
move=> Feps Fe epsn0 en0 Hle Hn0.
apply: Rle_trans (TwoSum_err_uls_ge Feps Fe epsn0 en0 Hle Hn0) _.
apply: uls_le_abs; last exact: Hn0.
have := format_TwoSum Feps Fe.
by case: (TwoSum eps e) => r et /= [_ Fet].
Qed.

(* Draft 5.3 opening, second fact: "[ulp(y_j) >= 2 |eps_{i_0}|]".  This is    *)
(* just the 2Sum magnitude property [|err| <= ulp(hi)/2].                     *)
Lemma vseb_emit_ulp_ge (eps e : R) :
  format eps -> format e ->
  2 * Rabs (dwl (TwoSum eps e)) <= ulp (dwh (TwoSum eps e)).
Proof.
move=> Feps Fe.
have := magnitude_TwoSum Feps Fe.
by case: (TwoSum eps e) => r et /=; lra.
Qed.

(* Draft 5.3 opening, combined: "[ulp(y_j) >= 2|eps_{i_0}| >= 2u]".           *)
Lemma vseb_emit_ulp_ge_uls (eps e : R) :
  format eps -> format e -> eps <> 0 -> e <> 0 ->
  uls e <= uls eps -> dwl (TwoSum eps e) <> 0 ->
  2 * uls e <= ulp (dwh (TwoSum eps e)).
Proof.
move=> Feps Fe epsn0 en0 Hle Hn0.
have H1 := vseb_emit_abs_ge Feps Fe epsn0 en0 Hle Hn0.
have H2 := vseb_emit_ulp_ge Feps Fe.
by lra.
Qed.


(* [p >= 4] in the form the constant bounds need it: 13, 5 and 3 all fit      *)
(* in [p] bits because [2^p >= 16].                                           *)
Lemma pow2_ge_16 : (16 <= 2 ^ p)%Z.
Proof.
have -> : (16 = 2 ^ 4)%Z by [].
by apply: Z.pow_le_mono_r; lia.
Qed.

(* A scaled integer with fewer than [p] bits is a float.                      *)
Lemma format_mult_pow (m e : Z) :
  (Z.abs m < 2 ^ p)%Z -> format (IZR m * pow e).
Proof.
move=> Hm.
have Hp2p : pow p = IZR (2 ^ p) by rewrite -IZR_Zpower; [congr IZR|lia].
apply: (@imul_format beta p Hp2 (IZR m * pow e) e (pow (p + e))).
- by exists m.
- rewrite Rabs_mult (Rabs_pos_eq (pow e)); last by apply: bpow_ge_0.
  rewrite bpow_plus; apply: Rmult_le_compat_r; first by apply: bpow_ge_0.
  by rewrite -abs_IZR Hp2p; apply: IZR_le; lia.
by apply: Rle_refl.
Qed.

(* The draft's constants (13/16, 3/4, 5/8, 1-u, 1-2u) times an [ulp] are      *)
(* floats: each is a short integer scaled by a power of two.                  *)
Lemma format_frac_ulp (m e : Z) (y : R) :
  (Z.abs m < 2 ^ p)%Z -> format (IZR m * pow e * ulp y).
Proof.
move=> Hm.
case: (Req_dec y 0) => [->|yn0].
  by rewrite ulp_FLX_0 Rmult_0_r; apply: generic_format_0.
rewrite ulp_neq_0 // Rmult_assoc -bpow_plus.
exact: format_mult_pow.
Qed.

(* Draft 5.3, the estimate in the form the case study actually uses: the      *)
(* draft always bounds [|e_{i_1}|] by a multiple of [u] and then leans on     *)
(* the opening fact [|eps_{i_0}| >= u].  Here [t] plays [u] (kept             *)
(* symbolic), so [|e| <= c t <= c |eps|] and [vseb_next_le] applies.          *)
Lemma vseb_next_le_uls (yj eps e t c : R) :
  0 <= c -> t <= Rabs eps ->
  2 * Rabs eps <= ulp yj ->
  Rabs e <= c * t ->
  format ((1 + c) / 2 * ulp yj) ->
  Rabs (RND (eps + e)) <= (1 + c) / 2 * ulp yj.
Proof.
move=> Hc Ht Hulp He FB.
apply: vseb_next_le => //.
by apply: Rle_trans He _; apply: Rmult_le_compat_l.
Qed.

(* ---- the draft's five constants, instantiated ---------------------------*)

(* "|eps_{i_0}| + |e_{i_1}| <= (1 + 5/8)|eps_{i_0}|, so                       *)
(* |r_{i_1-1}| <= 13/16 ulp(y_j)"  (case 0 < e_{i_1} < 5/8 u).                *)
Lemma vseb_next_13_16 (yj eps e t : R) :
  t <= Rabs eps -> 2 * Rabs eps <= ulp yj -> Rabs e <= 5 / 8 * t ->
  Rabs (RND (eps + e)) <= 13 / 16 * ulp yj.
Proof.
move=> Ht Hulp He.
have -> : 13 / 16 * ulp yj = (1 + 5 / 8) / 2 * ulp yj by lra.
apply: vseb_next_le_uls Ht Hulp He _; first by lra.
have -> : (1 + 5 / 8) / 2 * ulp yj = IZR 13 * pow (- 4) * ulp yj.
  by rewrite /= /Z.pow_pos /=; lra.
by apply: format_frac_ulp; move: pow2_ge_16; rewrite /=; lia.
Qed.

(* "Case |e_{i_1}| = 1/2 u ... |r_{i_1-1}| <= 3/4 ulp(y_j)".                  *)
Lemma vseb_next_3_4 (yj eps e t : R) :
  t <= Rabs eps -> 2 * Rabs eps <= ulp yj -> Rabs e <= / 2 * t ->
  Rabs (RND (eps + e)) <= 3 / 4 * ulp yj.
Proof.
move=> Ht Hulp He.
have -> : 3 / 4 * ulp yj = (1 + / 2) / 2 * ulp yj by lra.
apply: vseb_next_le_uls Ht Hulp He _; first by lra.
have -> : (1 + / 2) / 2 * ulp yj = IZR 3 * pow (- 2) * ulp yj.
  by rewrite /= /Z.pow_pos /=; lra.
by apply: format_frac_ulp; move: pow2_ge_16; rewrite /=; lia.
Qed.

(* "Case |e_{i_1}| = 1/4 u.  Then |r_{i_1-1}| <= 5/8 ulp(y_j)".               *)
Lemma vseb_next_5_8 (yj eps e t : R) :
  t <= Rabs eps -> 2 * Rabs eps <= ulp yj -> Rabs e <= / 4 * t ->
  Rabs (RND (eps + e)) <= 5 / 8 * ulp yj.
Proof.
move=> Ht Hulp He.
have -> : 5 / 8 * ulp yj = (1 + / 4) / 2 * ulp yj by lra.
apply: vseb_next_le_uls Ht Hulp He _; first by lra.
have -> : (1 + / 4) / 2 * ulp yj = IZR 5 * pow (- 3) * ulp yj.
  by rewrite /= /Z.pow_pos /=; lra.
by apply: format_frac_ulp; move: pow2_ge_16; rewrite /=; lia.
Qed.


(* [1 - k u] times an [ulp] is a float ([= (2^p - k) * pow(-p) * ulp]);       *)
(* this covers the draft's [1 - u] and [1 - 2u] bounds.                       *)
Lemma format_1_sub_ku_ulp (k : Z) (y : R) :
  (1 <= k)%Z -> (k < 2 ^ p)%Z -> format ((1 - IZR k * u) * ulp y).
Proof.
move=> Hk1 Hk2.
have Hpp2 : pow p = IZR (2 ^ p) by rewrite -IZR_Zpower; [congr IZR|lia].
have Hu : u = pow (- p).
  have H2u : 2 * u = pow (1 - p) by rewrite /Fmore.u; lra.
  have H1p : pow (1 - p) = 2 * pow (- p).
    have -> : (1 - p = 1 + - p)%Z by lia.
    by rewrite bpow_plus bpow_1 /=; lra.
  by lra.
have Hpm : pow p * pow (- p) = 1.
  by rewrite -bpow_plus (_ : (p + - p = 0)%Z) ?(pow0E beta); [|lia].
have -> : (1 - IZR k * u) * ulp y = IZR (2 ^ p - k) * pow (- p) * ulp y.
  rewrite minus_IZR -Hpp2 Hu.
  by rewrite -{1}Hpm; ring.
by apply: format_frac_ulp; rewrite Z.abs_eq; lia.
Qed.

(* Draft 5.3, case [i_1 >= 4]: "[|eps_{i_0}| + |e_{i_1}| <=                   *)
(* |eps_{i_0}| + (u - 2u^2) <= (2 - 2u)|eps_{i_0}|], so                       *)
(* [|r_{i_1-1}| <= (1 - u) ulp(y_j)]".                                        *)
Lemma vseb_next_1mu (yj eps e t : R) :
  t <= Rabs eps -> 2 * Rabs eps <= ulp yj ->
  Rabs e <= (1 - 2 * u) * t ->
  Rabs (RND (eps + e)) <= (1 - u) * ulp yj.
Proof.
move=> Ht Hulp He.
have Hu0 : 0 < u by apply: u_gt_0.
have H12u : 0 <= 1 - 2 * u.
  have -> : 2 * u = pow (1 - p) by rewrite /Fmore.u; lra.
  have h1p : (1 - p <= 0)%Z by lia.
  by have := bpow_le beta (1 - p) 0 h1p; rewrite (pow0E beta); lra.
have -> : (1 - u) * ulp yj = (1 + (1 - 2 * u)) / 2 * ulp yj by lra.
apply: vseb_next_le_uls Ht Hulp He _; first by lra.
have -> : (1 + (1 - 2 * u)) / 2 * ulp yj = (1 - IZR 1 * u) * ulp yj.
  by rewrite /=; lra.
by apply: format_1_sub_ku_ulp; move: pow2_ge_16; lia.
Qed.

(* Draft 5.3, case [i_1 >= 4], sub-case [|e_{i_1}| <= u - 4u^2]: "then we     *)
(* have the stronger estimate [|r_{i_1-1}| <= (1 - 2u) ulp(y_j)]".            *)
Lemma vseb_next_1m2u (yj eps e t : R) :
  t <= Rabs eps -> 2 * Rabs eps <= ulp yj ->
  Rabs e <= (1 - 4 * u) * t ->
  Rabs (RND (eps + e)) <= (1 - 2 * u) * ulp yj.
Proof.
move=> Ht Hulp He.
have Hu0 : 0 < u by apply: u_gt_0.
have H14u : 0 <= 1 - 4 * u.
  have H4u : 4 * u = pow (2 - p).
    have H2u : 2 * u = pow (1 - p) by rewrite /Fmore.u; lra.
    have Hsp : pow (2 - p) = 2 * pow (1 - p).
      have -> : (2 - p = 1 + (1 - p))%Z by lia.
      by rewrite bpow_plus bpow_1 /=; lra.
    by rewrite Hsp; lra.
  rewrite H4u.
  have h2p : (2 - p <= 0)%Z by lia.
  by have := bpow_le beta (2 - p) 0 h2p; rewrite (pow0E beta); lra.
have -> : (1 - 2 * u) * ulp yj = (1 + (1 - 4 * u)) / 2 * ulp yj by lra.
apply: vseb_next_le_uls Ht Hulp He _; first by lra.
have -> : (1 + (1 - 4 * u)) / 2 * ulp yj = (1 - IZR 2 * u) * ulp yj.
  by rewrite /=; lra.
by apply: format_1_sub_ku_ulp; move: pow2_ge_16; lia.
Qed.


(* ---- 5.3, case [i_1 >= 4] ----------------------------------------------*)

(* Draft 5.3, case [i_1 >= 4], sub-case [|e_{i_1}| = u - 2u^2]: "then         *)
(* y_{j+1} = r_{i_1-1} < ulp(y_j)".  The [(1-u)] bound already sits           *)
(* strictly below [ulp(y_j)]; the [ulp] is positive because it dominates      *)
(* [2|eps_{i_0}| >= 2t > 0].                                                  *)
Lemma vseb_next_lt_of_1mu (yj eps e t : R) :
  0 < t -> t <= Rabs eps -> 2 * Rabs eps <= ulp yj ->
  Rabs e <= (1 - 2 * u) * t ->
  Rabs (RND (eps + e)) < ulp yj.
Proof.
move=> Ht0 Ht Hulp He.
have Hu0 : 0 < u by apply: u_gt_0.
have Hulp0 : 0 < ulp yj by lra.
have H := vseb_next_1mu Ht Hulp He.
by nra.
Qed.

(* Draft 5.3, case [i_1 >= 4], sub-case [|e_{i_1}| <= u - 4u^2]: after the    *)
(* [(1-2u)] estimate the draft absorbs one more error,                        *)
(* [|e_{i_1+1}| <= u^2 <= u/2 ulp(y_j)], and concludes                        *)
(* [|y_{j+1}| < ulp(y_j)].  The sum is at most [(1 - 3u/2) ulp(y_j)],         *)
(* hence at most the FLOAT [(1-u) ulp(y_j)], which rounding cannot            *)
(* escape -- and that is still strictly below [ulp(y_j)].                     *)
Lemma vseb_merge_lt (yj r e' : R) :
  0 < ulp yj ->
  Rabs r <= (1 - 2 * u) * ulp yj ->
  Rabs e' <= / 2 * u * ulp yj ->
  Rabs (RND (r + e')) < ulp yj.
Proof.
move=> Hulp0 Hr He.
have Hu0 : 0 < u by apply: u_gt_0.
have Hsum : Rabs (r + e') <= (1 - IZR 1 * u) * ulp yj.
  apply: Rle_trans (Rabs_triang _ _) _.
  by rewrite /=; nra.
have HF : format ((1 - IZR 1 * u) * ulp yj).
  by apply: format_1_sub_ku_ulp; move: pow2_ge_16; lia.
have H : Rabs (RND (r + e')) <= (1 - 1 * u) * ulp yj.
  by apply: Rabs_round_le_r.
by nra.
Qed.


(* ---- 5.3, "adding at most 3 of them" ------------------------------------*)

(* The counting: a block of at most [n] further errors, each below [d],       *)
(* adds at most [n * d] to the mass carried past the head.                    *)
Lemma sumRabs_le_count (l : seq R) (n : nat) (d : R) :
  (size l <= n)%N -> 0 <= d -> (forall z, z \in l -> Rabs z <= d) ->
  sumRabs l <= INR n * d.
Proof.
elim: l n => [|a l IH] n Hsz Hd Hall /=.
  by have := pos_INR n; nra.
case: n Hsz => [//|n] Hsz.
have Ha : Rabs a <= d by apply: Hall; rewrite inE eqxx.
have Hrec : sumRabs l <= INR n * d.
  by apply: IH => // z zl; apply: Hall; rewrite inE zl orbT.
by rewrite S_INR; nra.
Qed.

(* Draft 5.3's block estimate, packaged: the emitted word [y_{j+1}] is the    *)
(* head of the continued VSEB walk, and [VSEB.vsebAux_head_leB] bounds it     *)
(* by any FLOAT [B] dominating [|eps_{i_0}|] plus the mass of the errors      *)
(* still to come.  So a [B] strictly below [ulp(y_j)] closes the case --      *)
(* this is the engine behind every "we are adding at most 3 of them".         *)
Lemma vseb_head_lt_of_mass (yj eps B : R) (l : seq R) :
  format eps -> {in l, forall z, format z} -> format B ->
  Rabs eps + sumRabs l <= B -> B < ulp yj ->
  Rabs (nth 0 (vsebAux eps l) 0) < ulp yj.
Proof.
move=> Feps Hl FB Hmass HB.
by apply: Rle_lt_trans (vsebAux_head_leB Feps Hl FB Hmass) HB.
Qed.

(* The same with the draft's split of the mass: the first error               *)
(* [e_{i_1}] is handled by the [(1+c)/2] estimate and the at-most-[n]         *)
(* later ones by [d] each, so [B = ((1+c)/2 + n d) ulp(y_j)] serves.          *)
Lemma vseb_head_lt_split (yj eps e B : R) (l : seq R) (n : nat) (d : R) :
  format eps -> format e -> {in l, forall z, format z} -> format B ->
  (size l <= n)%N -> 0 <= d -> (forall z, z \in l -> Rabs z <= d) ->
  Rabs eps + Rabs e + INR n * d <= B -> B < ulp yj ->
  Rabs (nth 0 (vsebAux eps (e :: l)) 0) < ulp yj.
Proof.
move=> Feps Fe Hl FB Hsz Hd Hall Hmass HB.
apply: vseb_head_lt_of_mass Feps _ FB _ HB.
  by move=> z; rewrite inE => /orP[/eqP->|zl]; [|apply: Hl].
have Hrec := sumRabs_le_count Hsz Hd Hall.
by rewrite /=; lra.
Qed.


(* ---- 5.3, case [0 < e_{i_1} < 5/8 u] -----------------------------------*)

(* [u] as a power of two, and the [p >= 4] consequence [u <= 1/16] that       *)
(* every sub-case below needs.                                                *)
Lemma uE_pow : u = pow (- p).
Proof.
have H2u : 2 * u = pow (1 - p) by rewrite /Fmore.u; lra.
have H1p : pow (1 - p) = 2 * pow (- p).
  have -> : (1 - p = 1 + - p)%Z by lia.
  by rewrite bpow_plus bpow_1 /=; lra.
by lra.
Qed.

Lemma u_le_inv16 : u <= / 16.
Proof.
have H16 : pow 4 = 16 by rewrite /= /Z.pow_pos /=; lra.
have Hle : pow (- p) <= pow (-4) by apply: bpow_le; lia.
have Hmul : pow 4 * pow (-4) = 1.
  by rewrite -bpow_plus (_ : (4 + -4 = 0)%Z) ?(pow0E beta); [|lia].
have H4 : 0 < pow (-4) by apply: bpow_gt_0.
rewrite uE_pow; nra.
Qed.

(* The sub-case shape at the level the draft actually argues at: what         *)
(* matters is the total MASS [M ulp(y_j)] of the errors after                 *)
(* [e_{i_1}], however it was obtained.  Three of the four sub-cases get       *)
(* it by counting ([M = 3d]); the [1/4 u] one needs the draft's sharper       *)
(* [|e_5| <= uls(e_4)] step, which only changes [M].                          *)
Lemma vseb_subcase_mass_lt (yj eps e : R) (l : seq R) (t c M : R) :
  format eps -> format e -> {in l, forall z, format z} ->
  0 < t -> t <= Rabs eps -> 2 * Rabs eps <= ulp yj ->
  0 <= c -> Rabs e <= c * t ->
  sumRabs l <= M * ulp yj ->
  (1 + c) / 2 + M <= 1 - u ->
  Rabs (nth 0 (vsebAux eps (e :: l)) 0) < ulp yj.
Proof.
move=> Feps Fe Hl Ht0 Ht Hulp Hc He Hmass Hbound.
have Hu0 : 0 < u by apply: u_gt_0.
have HU : 0 < ulp yj by lra.
have HB : format ((1 - IZR 1 * u) * ulp yj).
  by apply: format_1_sub_ku_ulp; move: pow2_ge_16; lia.
apply: (vseb_head_lt_of_mass Feps _ HB).
- by move=> z; rewrite inE => /orP[/eqP->|zl]; [|apply: Hl].
- have Hec : Rabs e <= c * Rabs eps by apply: Rle_trans He _; nra.
  by rewrite /=; nra.
by nra.
Qed.
(* The shape shared by the sub-cases of [0 < e_{i_1} < 5/8 u]: the head       *)
(* pair contributes [(1+c)/2 ulp(y_j)] and the at most 3 later errors [d]     *)
(* each, so as soon as [(1+c)/2 + 3d <= 1 - u] the FLOAT [(1-u) ulp(y_j)]     *)
(* dominates the whole block and the emitted word lands below                 *)
(* [ulp(y_j)].  Instantiating [c] and [d] reproduces the draft's cases.       *)
Lemma vseb_subcase_lt (yj eps e : R) (l : seq R) (t c d : R) :
  format eps -> format e -> {in l, forall z, format z} ->
  0 < t -> t <= Rabs eps -> 2 * Rabs eps <= ulp yj ->
  0 <= c -> Rabs e <= c * t ->
  (size l <= 3)%N -> 0 <= d ->
  (forall z, z \in l -> Rabs z <= d * ulp yj) ->
  (1 + c) / 2 + 3 * d <= 1 - u ->
  Rabs (nth 0 (vsebAux eps (e :: l)) 0) < ulp yj.
Proof.
move=> Feps Fe Hl Ht0 Ht Hulp Hc He Hsz Hd Hall Hbound.
have HU : 0 < ulp yj by lra.
have Hd0 : 0 <= d * ulp yj by nra.
have Htail := sumRabs_le_count Hsz Hd0 Hall.
have H3 : INR 3 = 3 by rewrite /=; lra.
rewrite H3 in Htail.
have Hmass : sumRabs l <= (3 * d) * ulp yj by lra.
apply: (vseb_subcase_mass_lt Feps Fe Hl Ht0 Ht Hulp Hc He Hmass).
by lra.
Qed.

(* Draft 5.3, sub-case [|e_{i_1}| > 1/2 u]: the tail errors are               *)
(* [<= u^2 <= u/2 ulp(y_j)], and "we are adding at most 3 of them".           *)
Lemma vseb_subcase_gt_half (yj eps e : R) (l : seq R) (t : R) :
  format eps -> format e -> {in l, forall z, format z} ->
  0 < t -> t <= Rabs eps -> 2 * Rabs eps <= ulp yj ->
  Rabs e <= 5 / 8 * t ->
  (size l <= 3)%N ->
  (forall z, z \in l -> Rabs z <= / 2 * u * ulp yj) ->
  Rabs (nth 0 (vsebAux eps (e :: l)) 0) < ulp yj.
Proof.
move=> Feps Fe Hl Ht0 Ht Hulp He Hsz Hall.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu16 := u_le_inv16.
apply: vseb_subcase_lt Feps Fe Hl Ht0 Ht Hulp _ He Hsz _ Hall _; try lra.
Qed.

(* Draft 5.3, sub-case [|e_{i_1}| = 1/2 u]: same tail bound, one notch        *)
(* tighter on the head pair.                                                  *)
Lemma vseb_subcase_half (yj eps e : R) (l : seq R) (t : R) :
  format eps -> format e -> {in l, forall z, format z} ->
  0 < t -> t <= Rabs eps -> 2 * Rabs eps <= ulp yj ->
  Rabs e <= / 2 * t ->
  (size l <= 3)%N ->
  (forall z, z \in l -> Rabs z <= / 2 * u * ulp yj) ->
  Rabs (nth 0 (vsebAux eps (e :: l)) 0) < ulp yj.
Proof.
move=> Feps Fe Hl Ht0 Ht Hulp He Hsz Hall.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu16 := u_le_inv16.
apply: vseb_subcase_lt Feps Fe Hl Ht0 Ht Hulp _ He Hsz _ Hall _; try lra.
Qed.

(* Draft 5.3, sub-case [1/2 u > |e_{i_1}|] and [|e_{i_1}| <> 1/4 u]: there    *)
(* [uls(e_{i_1}) <= 1/8 u], so the tail errors are [<= 1/8 u <= 1/16          *)
(* ulp(y_j)].  The count is exactly [3/4 + 3/16 = 15/16 <= 1 - u], tight      *)
(* at [p = 4].                                                                *)
Lemma vseb_subcase_lt_half (yj eps e : R) (l : seq R) (t : R) :
  format eps -> format e -> {in l, forall z, format z} ->
  0 < t -> t <= Rabs eps -> 2 * Rabs eps <= ulp yj ->
  Rabs e <= / 2 * t ->
  (size l <= 3)%N ->
  (forall z, z \in l -> Rabs z <= / 16 * ulp yj) ->
  Rabs (nth 0 (vsebAux eps (e :: l)) 0) < ulp yj.
Proof.
move=> Feps Fe Hl Ht0 Ht Hulp He Hsz Hall.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu16 := u_le_inv16.
apply: vseb_subcase_lt Feps Fe Hl Ht0 Ht Hulp _ He Hsz _ Hall _; try lra.
Qed.


(* Draft 5.3, sub-case [|e_{i_1}| = 1/4 u].  Counting alone does NOT          *)
(* close here: [5/8 + 3*(1/8) = 1] exactly.  The draft repairs it with        *)
(* "we can not have |e_4| = |e_3| ... so |e_5| <= uls(e_4) <= 1/16            *)
(* ulp(y_j)", i.e. the last of the three is half the size, giving a tail      *)
(* mass of [1/8 + 1/8 + 1/16 = 5/16] and the total [5/8 + 5/16 = 15/16].      *)
(* The refined tail mass is taken as a hypothesis: establishing it is         *)
(* the draft's index-level argument about positions 3, 4 and 5.               *)
Lemma vseb_subcase_quarter (yj eps e : R) (l : seq R) (t : R) :
  format eps -> format e -> {in l, forall z, format z} ->
  0 < t -> t <= Rabs eps -> 2 * Rabs eps <= ulp yj ->
  Rabs e <= / 4 * t ->
  sumRabs l <= 5 / 16 * ulp yj ->
  Rabs (nth 0 (vsebAux eps (e :: l)) 0) < ulp yj.
Proof.
move=> Feps Fe Hl Ht0 Ht Hulp He Hmass.
have Hu16 := u_le_inv16.
by apply: vseb_subcase_mass_lt Feps Fe Hl Ht0 Ht Hulp _ He Hmass _; lra.
Qed.

(* ===========================================================================*)
(*  THE ASSEMBLY (doc/thm6.md 5.3): the draft's own route to the theorem.     *)
(*                                                                            *)
(*  The draft proves P-nonoverlap by showing, at every emit of the VSEB walk, *)
(*  that the NEXT emitted word falls below [ulp] of the one just emitted --   *)
(*  and it gets there by bounding [|eps| + (mass of the errors still to come)]*)
(*  by a float under that [ulp].  [vsebBlock] records exactly that per-emit   *)
(*  obligation along the walk, and [vsebAux_Pnonoverlap_block] turns it into  *)
(*  the conclusion.  Every 5.3 case lemma above produces such a bound, with   *)
(*  [B = (1 - u) ulp(y_j)].                                                   *)
(* ===========================================================================*)

Fixpoint vsebBlock (eps : R) (l : seq R) : Prop :=
  match l with
  | [::]    => True
  | [:: _]  => True
  | e :: l' =>
      let: DWR r et := TwoSum eps e in
      if Req_EM_T et 0 then vsebBlock r l'
      else (exists B, [/\ format B,
                          Rabs et + sumRabs l' <= B &
                          B < ulp r])
           /\ vsebBlock et l'
  end.

(* One-step unfolding (by reflexivity), as for [vsebAux_consS].               *)
Lemma vsebBlock_consS eps e e2 l :
  vsebBlock eps [:: e, e2 & l] =
  (let: DWR r et := TwoSum eps e in
   if Req_EM_T et 0 then vsebBlock r (e2 :: l)
   else (exists B, [/\ format B,
                       Rabs et + sumRabs (e2 :: l) <= B &
                       B < ulp r])
        /\ vsebBlock et (e2 :: l)).
Proof. by []. Qed.

(* The driver: the per-emit float bound gives P-nonoverlap.  Same walk        *)
(* induction as [vsebAux_Pnonoverlap_mass], with [vsebAux_head_leB]           *)
(* supplying the emitted head bound instead of the mass machinery.            *)
Lemma vsebAux_Pnonoverlap_block eps l :
  format eps -> {in l, forall z, format z} ->
  vsebBlock eps l -> Pnonoverlap (vsebAux eps l).
Proof.
elim: l eps => [|e l' IH] eps epsF lF Hb.
  by move=> i; rewrite /= ltnS ltn0.
have Fe : format e by apply: lF; rewrite inE eqxx.
case: l' IH lF Hb => [|e2 l''] IH lF Hb.
  rewrite vsebAux_1; case E1 : (TwoSum eps e) => [y0 y1].
  move=> [|i] /= Hi; last by move: Hi; rewrite ltnS ltnS ltn0.
  have Hmag := magnitude_TwoSum epsF Fe; rewrite E1 /= in Hmag.
  case: (Req_dec y1 0) => [y10|y1n0]; first by left.
  right.
  have y0n0 : y0 <> 0.
    by move=> y00; apply: y1n0; move: Hmag;
       rewrite y00 ulp_FLX_0; split_Rabs; lra.
  have Hy : 0 < ulp y0 by rewrite ulp_neq_0 //; apply: bpow_gt_0.
  by lra.
rewrite vsebAux_consS; case E1 : (TwoSum eps e) => [r et].
have Hr : r = RND (eps + e) by have := TwoSum_hi eps e; rewrite E1.
move: Hb; rewrite vsebBlock_consS E1.
case: (Req_EM_T et 0) => [et0|etn0] Hb.
  apply: IH => //.
  - by rewrite Hr; apply: generic_format_round.
  by move=> z zI; apply: lF; rewrite inE zI orbT.
have Fet : format et
  by have H := format_TwoSum epsF Fe; rewrite E1 /= in H; case: H.
have Fl' : {in e2 :: l'', forall z, format z}
  by move=> z zI; apply: lF; rewrite inE zI orbT.
case: Hb => [[B [FB Hmass HB]] Hbrec].
have Hrec : Pnonoverlap (vsebAux et (e2 :: l'')) by apply: IH.
move=> [|i] /= Hi.
  right.
  have Hnext : Rabs (nth 0 (vsebAux et (e2 :: l'')) 0) <= B
    by apply: vsebAux_head_leB.
  by apply: (Rle_lt_trans _ _ _ Hnext HB).
by apply: (Hrec i); move: Hi; rewrite ltnS.
Qed.


(* A MERGE step costs nothing.  If the whole remaining block fits under       *)
(* [(1-2u)|eps|] then, after absorbing the next term [a] exactly into the     *)
(* remainder, what is left still fits under [(1-2u)|eps + a|]: the            *)
(* remainder loses at most [|a|] while the block loses exactly [|a|].         *)
(* So all the content of the draft's block estimate sits at the EMITS.        *)
Lemma mass_merge_step (eps a : R) (tail : seq R) :
  Rabs a + sumRabs tail <= (1 - 2 * u) * Rabs eps ->
  sumRabs tail <= (1 - 2 * u) * Rabs (eps + a).
Proof.
move=> Hmass.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu16 := u_le_inv16.
have Htri : Rabs eps - Rabs a <= Rabs (eps + a).
  by have := Rabs_triang_inv eps (- a); rewrite Rabs_Ropp; split_Rabs; lra.
have Ha : 0 <= Rabs a by apply: Rabs_pos.
by nra.
Qed.

(* Discharging one [vsebBlock] obligation.  The draft's per-emit bound is     *)
(* always of the form "the errors still to come are small next to the         *)
(* remainder": with [sumRabs tail <= (1 - 2u) |et|] and the free              *)
(* [2|et| <= ulp r] ([magnitude_TwoSum]), the block sits under                *)
(* [(2 - 2u)|et| <= (1 - u) ulp r], which is a float strictly below           *)
(* [ulp r].  So [B = (1 - u) ulp r] serves, as in every 5.3 case above.       *)
Lemma vsebBlock_obligation (r et : R) (tail : seq R) :
  et <> 0 -> 2 * Rabs et <= ulp r ->
  sumRabs tail <= (1 - 2 * u) * Rabs et ->
  exists B, [/\ format B, Rabs et + sumRabs tail <= B & B < ulp r].
Proof.
move=> etn0 Hulp Hmass.
have Hu0 : 0 < u by apply: u_gt_0.
have Het : 0 < Rabs et by apply: Rabs_pos_lt.
have HU : 0 < ulp r by lra.
have Hu16 := u_le_inv16.
exists ((1 - IZR 1 * u) * ulp r); split.
- by apply: format_1_sub_ku_ulp; move: pow2_ge_16; lia.
- by rewrite /=; nra.
by rewrite /=; nra.
Qed.
(* THE remaining core: the VecSum error sequence satisfies the draft's        *)
(* per-emit block bound.  This is exactly doc/thm6.md 5.2 + 5.3 -- the        *)
(* *2 forcing (all of which is proved above) feeding the *3 case study        *)
(* (whose four sub-cases and the [i_1 >= 4] case are proved above too;        *)
(* what is missing is the [i_1 <= 3] case, the [|e_4| = |e_3|] index          *)
(* argument, and the identification of [i_0] / [i_1] along the walk).         *)
Lemma vecSum_vsebBlock (l : seq R) :
  ties_to_even choice ->
  (size l <= 6)%N ->
  {in l, forall z, format z} ->
  (forall i, (i < size l)%N -> nth (0:R) l i <> 0) ->
  sorted_mag l -> pairwise_ulp l ->
  vsebBlock (head 0 (vecSum l)) (behead (vecSum l)).
Proof.
Admitted.

(* ===========================================================================*)
(*  LAYER 2 (the draft's Theorem 7 proper): the ZERO-FREE case.               *)
(*                                                                            *)
(*  This is what doc/thm6.md 5.1-5.3 actually proves.  The draft's [x_i] are  *)
(*  nonzero throughout -- it takes [uls(e_j)] and divides by it -- and our    *)
(*  [vecSum_run_ufp] / [vecSum_err_ufp] likewise need [Hnz].  Zeros are OUR   *)
(*  obligation, discharged in layer 1 below.                                  *)
(* ===========================================================================*)
Lemma vecSum_vseb_Pnonoverlap_nz (l : seq R) :
  ties_to_even choice ->
  (size l <= 6)%N ->
  {in l, forall z, format z} ->
  (forall i, (i < size l)%N -> nth (0:R) l i <> 0) ->
  sorted_mag l -> pairwise_ulp l ->
  Pnonoverlap (vseb (vecSum l)).
Proof.
move=> Heven Hsz Hfmt Hnz Hsort Hpair.
have HfV : {in vecSum l, forall z, format z} by apply: format_vecSum.
have HM := vecSum_vsebBlock Heven Hsz Hfmt Hnz Hsort Hpair.
rewrite /vseb; case E : (vecSum l) HfV HM => [|e0 tl] HfV HM.
  by move=> i; rewrite /= ltn0.
apply: vsebAux_Pnonoverlap_block => //.
- by apply: HfV; rewrite inE eqxx.
by move=> z zI; apply: HfV; rewrite inE zI orbT.
Qed.

(* ===========================================================================*)
(*  LAYER 1: zeros.  Under [sorted_mag] the zeros of [l] form a SUFFIX, so a  *)
(*  list is either zero-free (layer 2) or ends in a zero, which we peel.      *)
(* ===========================================================================*)

(* [sorted_mag] makes the zeros a suffix: a nonzero LAST entry forces every   *)
(* entry nonzero, since [|nth i| >= |last| > 0] along the chain.              *)
Lemma sorted_mag_last_nz (m : seq R) (x : R) :
  sorted_mag (rcons m x) -> x <> 0 ->
  forall i, (i < size (rcons m x))%N -> nth (0:R) (rcons m x) i <> 0.
Proof.
move=> Hsort xn0 i Hi.
have Hlast : nth (0:R) (rcons m x) (size m) = x by rewrite nth_rcons ltnn eqxx.
have Hsz : size (rcons m x) = (size m).+1 by rewrite size_rcons.
(* Walk down from the last index, using one [sorted_mag] step at a time.      *)
have Hdown : forall d, (d <= size m)%N ->
    nth (0:R) (rcons m x) (size m - d) <> 0.
  elim=> [_|d IH Hd]; first by rewrite subn0 Hlast.
  have Hd' : (d <= size m)%N by apply: ltnW.
  have Hlt : (size m - d.+1).+1 = (size m - d)%N by rewrite subnSK.
  have Hin : ((size m - d.+1).+1 < size (rcons m x))%N.
    by rewrite Hlt Hsz ltnS leq_subr.
  move=> Hz; apply: (IH Hd').
  have := Hsort _ Hin; rewrite Hlt Hz Rabs_R0 => Habs.
  by apply/Rabs_eq_R0/Rle_antisym => //; apply: Rabs_pos.
have -> : i = (size m - (size m - i))%N by rewrite subKn // -ltnS -Hsz.
by apply: Hdown; apply: leq_subr.
Qed.

(* [vecSumAux] on a list with a trailing zero: the deepest step is            *)
(* [2Sum(x_{n-1}, 0) = (x_{n-1}, 0)] (exact, since [x_{n-1}] is a float), so   *)
(* the running sum is unchanged and the emitted error is a trailing zero.      *)
Lemma vecSumAux_rcons0 (m : seq R) :
  (0 < size m)%N -> {in m, forall z, format z} ->
  vecSumAux (rcons m 0) =
    (rcons (vecSumAux m).1 0, (vecSumAux m).2).
Proof.
case: m => [//|a m _]; elim: m a => [a aF|b m IH a abF].
  have Fa : format a by apply: aF; rewrite inE eqxx.
  have -> : rcons [:: a] 0 = [:: a, 0 & [::]] by [].
  rewrite vecSumAux_cons.
  have E0 : vecSumAux [:: 0] = ([::], 0) by [].
  have Ea : vecSumAux [:: a] = ([::], a) by [].
  rewrite E0 Ea; case E : (TwoSum a 0) => [si ei1].
  have := dwh_TwoSum_r0 Fa; rewrite E /= => ->.
  by have := dwl_TwoSum_r0 Fa; rewrite E /= => ->.
have Hbm : {in b :: m, forall z, format z}.
  by move=> z zI; apply: abF; rewrite inE zI orbT.
have IH' := IH b Hbm; rewrite rcons_cons in IH'.
rewrite rcons_cons vecSumAux_cons rcons_cons vecSumAux_cons IH'.
by case: (vecSumAux (b :: m)) => es s /=; case: (TwoSum a s).
Qed.

(* VecSum carries a trailing zero through untouched: the running sum entering *)
(* the last step is [s = 0], so [2Sum(x_{n-2}, 0) = (x_{n-2}, 0)] and the     *)
(* emitted error is [0].                                                      *)
Lemma vecSum_rcons0 (m : seq R) :
  (0 < size m)%N -> {in m, forall z, format z} ->
  vecSum (rcons m 0) = rcons (vecSum m) 0.
Proof.
move=> Hs Hf; rewrite /vecSum vecSumAux_rcons0 //.
by case: (vecSumAux m) => es s /=.
Qed.

(* VSEB absorbs a trailing zero at the [vsebAux] level: the terminal step is  *)
(* [2Sum(_, 0) = (_, 0)], whose zero error either is dropped (output           *)
(* unchanged) or, at the very last position, emitted as a trailing zero.       *)
Lemma vsebAux_rcons0 (l : seq R) (eps : R) :
  format eps -> {in l, forall z, format z} ->
  vsebAux eps (rcons l 0) = vsebAux eps l \/
  vsebAux eps (rcons l 0) = rcons (vsebAux eps l) 0.
Proof.
(* [vsebAux w [:: 0] = [:: w; 0]]: a trailing zero is an exact merge.         *)
have vseb0 : forall w : R, format w -> vsebAux w [:: 0] = [:: w; 0].
  move=> w wF; rewrite vsebAux_1; case Ew : (TwoSum w 0) => [z0 z1].
  have := dwh_TwoSum_r0 wF; rewrite Ew /= => ->.
  by have := dwl_TwoSum_r0 wF; rewrite Ew /= => ->.
elim: l eps => [|e l' IH] eps epsF lF.
  by right; rewrite (vseb0 _ epsF).
have eF : format e by apply: lF; rewrite inE eqxx.
have Fl' : {in l', forall z, format z}.
  by move=> z zI; apply: lF; rewrite inE zI orbT.
have [rF etF] : format (dwh (TwoSum eps e)) /\
                format (dwl (TwoSum eps e))
  by apply: format_TwoSum.
rewrite rcons_cons.
case: l' IH lF Fl' rF etF => [|e2 l2] IH lF Fl' rF etF.
  (* One remaining term: the trailing zero is either dropped or emitted last. *)
  have -> : e :: rcons [::] 0 = [:: e, 0 & [::]] by [].
  rewrite vsebAux_consS vsebAux_1.
  case E : (TwoSum eps e) => [r et].
  have rF' : format r by move: rF; rewrite E.
  have etF' : format et by move: etF; rewrite E.
  case: (Req_EM_T et 0) => [et0|etn0].
    by left; rewrite [is_left _]/= (vseb0 r rF') et0.
  by right; rewrite [is_left _]/= (vseb0 et etF').
(* Two or more terms: recurse, the zero travelling to the tail.               *)
have -> : e :: rcons (e2 :: l2) 0 = [:: e, e2 & rcons l2 0] by rewrite rcons_cons.
rewrite !vsebAux_consS.
case E : (TwoSum eps e) => [r et].
have rF' : format r by move: rF; rewrite E.
have etF' : format et by move: etF; rewrite E.
case: (Req_EM_T et 0) => [et0|etn0]; rewrite [is_left _]/= -rcons_cons.
  exact: (IH r rF' Fl').
have [->|->] := IH et etF' Fl'; first by left.
by right; rewrite rcons_cons.
Qed.

(* VSEB absorbs a trailing zero: [2Sum(eps, 0) = (eps, 0)] has zero error, so *)
(* nothing is emitted and the remainder is carried.  The output therefore     *)
(* either is unchanged or gains a single trailing zero.                       *)
Lemma vseb_rcons0 (X : seq R) :
  (0 < size X)%N -> {in X, forall z, format z} ->
  vseb (rcons X 0) = vseb X \/ vseb (rcons X 0) = rcons (vseb X) 0.
Proof.
case: X => [//|e0 l'] _ Hf.
have e0F : format e0 by apply: Hf; rewrite inE eqxx.
have l'F : {in l', forall z, format z}.
  by move=> z zI; apply: Hf; rewrite inE zI orbT.
rewrite rcons_cons /vseb.
exact: vsebAux_rcons0.
Qed.

(* ===========================================================================*)
(*  Theorem 6 / draft Theorem 7 -- the target.                                *)
(* ===========================================================================*)
Lemma vecSum_vseb_Pnonoverlap (l : seq R) :
  ties_to_even choice ->
  (size l <= 6)%N ->
  {in l, forall z, format z} -> sorted_mag l -> pairwise_ulp l ->
  Pnonoverlap (vseb (vecSum l)).
Proof.
elim/last_ind: l => [_ _ _ _ _ i|m x IH Heven Hsz Hfmt Hsort Hpair].
  by rewrite /vseb /vecSum /= ltnS ltn0.
(* A nonzero last entry means the whole list is zero-free: layer 2 applies.   *)
case: (Req_dec x 0) => [x0|xn0]; last first.
  apply: vecSum_vseb_Pnonoverlap_nz => //.
  exact: sorted_mag_last_nz Hsort xn0.
(* Otherwise peel the trailing zero: VecSum passes it through, VSEB absorbs   *)
(* it, and the guard makes whatever trailing zero survives harmless.          *)
case: (posnP (size m)) => [/eqP|Hm].
  by rewrite size_eq0 => /eqP-> i; rewrite x0 /vseb /vecSum /= ltnS ltn0.
have Hfm : {in m, forall z, format z}.
  by move=> z zIm; apply: Hfmt; rewrite mem_rcons inE zIm orbT.
have Hrec : Pnonoverlap (vseb (vecSum m)).
  apply: IH => //.
  - by apply: leq_trans Hsz; rewrite size_rcons leqW.
  - exact: sorted_mag_rcons Hsort.
  exact: pairwise_ulp_rcons Hpair.
rewrite x0 vecSum_rcons0 //.
have Hsz0 : (0 < size (vecSum m))%N by rewrite size_vecSum.
have HfV : {in vecSum m, forall z, format z} by apply: format_vecSum.
have [->|->] := vseb_rcons0 Hsz0 HfV; first exact: Hrec.
exact: Pnonoverlap_rcons0.
Qed.

End SecThm6.
