(* ---------------------------------------------------------------------------*)
(* Algorithm 9 (3Prod^acc_{3,3}): the product of two triple-word numbers,     *)
(* and its two correctness results -- the result is a triple word             *)
(* ([ThreeProd_isTW]) and the relative error bound [28u^3 + 107u^4]           *)
(* ([ThreeProd_error]) -- paper Theorem 7 (doc/paper3.pdf, Section 6; see     *)
(* doc/thm7.md).  This starts the multiplication half of the paper.  Generic  *)
(* over the precision [p] (FLX, no [emin]); needs [p >= 6].                   *)
(*                                                                            *)
(* STATUS: the definition transcribes Algorithm 9 verbatim on top of          *)
(* [TwoProd] (Alg 3), [vecSum] (Alg 4) and [vsebK] (Alg 5).  Both theorems are *)
(* PROVED, reduced by the FLX WLOG (scale-invariance [ThreeProd_scale] and     *)
(* sign-invariance [ThreeProd_opp]/[_opp_r], the paper's "1 <= x0, y0 < 2") to *)
(* their normalised forms [ThreeProd_isTW_norm]/[ThreeProd_error_norm], which  *)
(* still carry the Section-6.2 mathematics and are [Admitted].  The full        *)
(* Section-6.1 term bounds are proved (product/error/FMA limbs); see            *)
(* doc/thm7.md.                                                               *)
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
Require Import Thm6.
Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SecThreeProd.

Variable p : Z.
Hypothesis Hp2 : (1 < p)%Z.
(* Algorithm 9 / Theorem 7 need [p >= 6] (paper Section 6.2).                 *)
Hypothesis Hp6 : (6 <= p)%Z.

Fact Hp4 : (4 <= p)%Z. Proof. by lia. Qed.

Local Notation beta := radix2.
Local Notation pow e := (bpow beta e).

Local Instance p_gt_0 : Prec_gt_0 p.
Proof. now apply Z.lt_trans with (2 := Hp2). Qed.

Open Scope R_scope.

Local Notation u := (u p beta).

Variable choice : Z -> bool.
Hypothesis choice_sym : forall x, choice x = ~~ choice (- (x + 1))%Z.
Local Notation rnd := (Znearest choice).
Local Instance valid_rnd : Valid_rnd rnd := valid_rnd_N choice.

Local Notation float := (float radix2).
Local Notation fexp := (FLX_exp p).
Local Notation format := (generic_format beta fexp).
Local Notation cexp := (cexp beta fexp).
Local Notation RND := (round beta fexp rnd).
Local Notation ulp := (ulp beta fexp).
Local Notation uls := (uls p).

(* Building blocks, with this format's [p]/[choice] hidden.                   *)
Local Notation TwoProd := (TwoProd p radix2 rnd).
Local Notation TwoSum := (TwoSum p choice).
Local Notation vecSumAux := (vecSumAux p choice).
Local Notation vecSum := (vecSum p choice).
Local Notation vsebAux := (vsebAux p choice).
Local Notation vseb := (vseb p choice).
Local Notation vsebK := (vsebK p choice).
Local Notation Pnonoverlap := (Pnonoverlap p).
Local Notation isTW := (isTW p).

(* ===========================================================================*)
(*  Algorithm 9 -- 3Prod^acc_{3,3}(x, y)                                      *)
(*  (46 operations & 2 tests; paper Section 6).                              *)
(*                                                                           *)
(*  The four [RN(_ + _ * _)] terms ([c], [z31], [z32]) are FMAs (a single    *)
(*  rounding).  The [b_i]/[e_i] are read off the (fixed-length) [vecSum]      *)
(*  outputs by position; [r0 = e0] and [(r1, r2) = VSEB(2)(e1, e2, e3, e4)].  *)
(* ===========================================================================*)
Definition ThreeProd (x y : twR) : twR :=
  let: TWR x0 x1 x2 := x in
  let: TWR y0 y1 y2 := y in
  let: (z00p, z00m) := TwoProd x0 y0 in
  let: (z01p, z01m) := TwoProd x0 y1 in
  let: (z10p, z10m) := TwoProd x1 y0 in
  let b := vecSum [:: z00m; z01p; z10p] in
  let b0 := nth 0 b 0 in
  let b1 := nth 0 b 1 in
  let b2 := nth 0 b 2 in
  let c   := RND (b2 + x1 * y1) in
  let z31 := RND (z10m + x0 * y2) in
  let z32 := RND (z01m + x2 * y0) in
  let z3  := RND (z31 + z32) in
  let e := vecSum [:: z00p; b0; b1; c; z3] in
  let e0 := nth 0 e 0 in
  match vsebK 2 [:: nth 0 e 1; nth 0 e 2; nth 0 e 3; nth 0 e 4] with
  | [:: r1, r2 & _] => TWR e0 r1 r2
  | [:: r1]         => TWR e0 r1 0
  | [::]            => TWR e0 0 0
  end.

(* ===========================================================================*)
(*  Lemma 1 (paper): [1/2 ulp(x)] divides [RN(x + y)].  Used for the          *)
(*  [b0]/[b1] divisibility in the Theorem-7 correctness case study.           *)
(* ===========================================================================*)
Lemma half_ulp_div_RN_add (x y : R) :
  format x -> format y -> x <> 0 ->
  is_imul (RND (x + y)) (/ 2 * ulp x).
Proof.
move=> Fx Fy x_neq0.
have He : / 2 * ulp x = pow (cexp x - 1).
  rewrite ulp_neq_0 //.
  have -> : / 2 = pow (-1) by rewrite /= /Z.pow_pos /=; lra.
  by rewrite -bpow_plus; congr bpow; lia.
rewrite He; set e := (cexp x - 1)%Z.
(* [x] itself is a multiple of [pow (cexp x)], hence of [1/2 ulp x = pow e].  *)
have Imx : is_imul x (pow e).
  by apply: is_imul_pow_le (format_imul_cexp Fx) _; rewrite /e; lia.
have [Ley|yLe] := Zle_or_lt e (cexp y).
  (* [y] no smaller than [1/2 ulp x]: [x + y] is on the [pow e] grid, so      *)
  (* [RN(x+y)] stays on it too.                                               *)
  apply: is_imul_pow_round; apply: is_imul_add => //.
  by apply: is_imul_pow_le (format_imul_cexp Fy) _.
(* [y] strictly smaller (its ulp [<= 1/4 ulp x]): then [|y| < pow(mag x - 2)] *)
(* and [|x| >= pow(mag x - 1) = 2 pow(mag x - 2)], so [|x + y|] -- and hence  *)
(* [|RN(x+y)|] -- stays [>= pow(mag x - 2)].  Thus [mag(RN(x+y)) >= mag x-1]  *)
(* and [cexp(RN(x+y)) >= e], making [RN(x+y)] a multiple of [pow e].          *)
have [->|y0] := Req_dec y 0.
  by rewrite Rplus_0_r (round_generic _ _ _ _ Fx).
have Hy : Rabs y < pow (mag beta x - 2).
  apply: (Rlt_le_trans _ (pow (mag beta y))); first by apply: bpow_mag_gt.
  by apply: bpow_le; move: yLe; rewrite /e /cexp /fexp; lia.
have Hx := bpow_mag_le beta x x_neq0.
have E2 : pow (mag beta x - 1) = 2 * pow (mag beta x - 2).
  have -> : (mag beta x - 1 = mag beta x - 2 + 1)%Z by lia.
  by rewrite bpow_plus_1.
have Hxy : pow (mag beta x - 2) <= Rabs (x + y).
  have Ht := Rabs_triang_inv x (- y).
  rewrite Rabs_Ropp in Ht.
  have Hxy0 : x - - y = x + y by lra.
  by rewrite Hxy0 in Ht; lra.
have HR : pow (mag beta x - 2) <= Rabs (RND (x + y)).
  by apply: Rabs_round_ge_bpow.
have Fr : format (RND (x + y)) by apply: generic_format_round.
apply: is_imul_pow_le (format_imul_cexp Fr) _.
have cexpE z : cexp z = (mag beta z - p)%Z by rewrite /cexp /fexp; lia.
rewrite /e !cexpE.
suff : (mag beta x - 1 <= mag beta (RND (x + y)))%Z by lia.
apply: mag_ge_bpow.
by have -> : (mag beta x - 1 - 1 = mag beta x - 2)%Z by lia.
Qed.

(* ===========================================================================*)
(*  Section 6.1 -- bounds on the intermediate terms.                          *)
(*                                                                            *)
(*  The paper WLOGs [1 <= x0, y0 < 2] (so [ufp x0 = ufp y0 = 1]).  We package  *)
(*  that normalisation together with the triple-word separation of one factor  *)
(*  as [tw_norm].  Every bound of Section 6.1 is a lemma over [tw_norm].       *)
(* ===========================================================================*)
Definition tw_norm (x0 x1 x2 : R) : Prop :=
  [/\ [/\ format x0, format x1 & format x2], 1 <= x0, x0 < 2,
      (x1 = 0 \/ Rabs x1 < ulp x0) & (x2 = 0 \/ Rabs x2 < ulp x1)].

(* Two [pow] rewrites used throughout: [2u = pow(1-p)] and [2u^2 = pow(1-2p)]. *)
Lemma pow_1mp : pow (1 - p) = 2 * u.
Proof. by rewrite /u; lra. Qed.

Lemma pow_1m2p : pow (1 - 2 * p) = 2 * (u * u).
Proof.
rewrite /u.
have -> : (1 - 2 * p = (1 - p) + ((1 - p) + (-1)))%Z by lia.
rewrite !bpow_plus.
have -> : pow (-1) = /2 by rewrite /= /Z.pow_pos /=; lra.
lra.
Qed.

(* Under the normalisation the leading limb has [ulp x0 = 2u].                 *)
Lemma tw_norm_ulp0 x0 x1 x2 : tw_norm x0 x1 x2 -> ulp x0 = 2 * u.
Proof.
move=> [] _ Hx0l Hx0r _ _.
have x0n0 : x0 <> 0 by lra.
have Hmag : (mag beta x0 = 1%Z :> Z).
  apply: mag_unique_pos; rewrite /= /Z.pow_pos /=; lra.
by rewrite ulp_neq_0 // /cexp /fexp Hmag /u; lra.
Qed.

(* First off-limb: [|x1| < 2u].  (Covers the [x1 = 0] case since [u > 0].)     *)
Lemma tw_norm_x1 x0 x1 x2 : tw_norm x0 x1 x2 -> Rabs x1 < 2 * u.
Proof.
move=> Hn.
have Hu0 : 0 < u by apply: u_gt_0.
have Hulp := tw_norm_ulp0 Hn.
case: Hn => _ _ _ [Hx1|Hx1] _.
  by rewrite Hx1 Rabs_R0; lra.
by rewrite -Hulp.
Qed.

(* Second off-limb: [|x2| < 2u^2].                                            *)
Lemma tw_norm_x2 x0 x1 x2 : tw_norm x0 x1 x2 -> Rabs x2 < 2 * (u * u).
Proof.
move=> Hn.
have Hu0 : 0 < u by apply: u_gt_0.
have Hx1b := tw_norm_x1 Hn.
have Hulpx1 : ulp x1 <= 2 * (u * u).
  case: (Req_dec x1 0) => [->|x1n0].
    by rewrite ulp_FLX_0 -pow_1m2p; apply: bpow_ge_0.
  have Hmag : (mag beta x1 <= 1 - p)%Z.
    by apply: mag_le_bpow => //; rewrite pow_1mp.
  by rewrite ulp_neq_0 // /cexp /fexp -pow_1m2p; apply: bpow_le; lia.
case: Hn => _ _ _ _ [->|Hx2].
  rewrite Rabs_R0.
  have Huu : 0 < u * u by nra.
  lra.
exact: (Rlt_le_trans _ _ _ Hx2 Hulpx1).
Qed.

(* [u = pow(-p)]: the workhorse rewrite for the product-term bounds.          *)
Lemma u_pow : u = pow (- p).
Proof.
rewrite /u.
have -> : (1 - p = 1 + - p)%Z by lia.
by rewrite bpow_plus bpow_1 /=; lra.
Qed.

(* A normalised leading limb is at most [2 - 2u] (the largest float below 2). *)
Lemma tw_norm_hi x0 x1 x2 : tw_norm x0 x1 x2 -> x0 <= 2 - 2 * u.
Proof.
move=> Hn; have Hulp := tw_norm_ulp0 Hn.
case: Hn => -[Fx0 _ _] Hx0l Hx0r _ _.
have x0n0 : x0 <> 0 by lra.
have [k Hk] : is_imul x0 (2 * u).
  have Ix0 := format_imul_cexp Fx0.
  have Hc : pow (cexp x0) = 2 * u by rewrite -Hulp; symmetry; apply: ulp_neq_0.
  by rewrite Hc in Ix0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hpp : pow p * u = 1.
  by rewrite u_pow -bpow_plus (_ : (p + - p = 0)%Z) ?pow0E; [lra|lia].
have Hp2u : pow p * (2 * u) = 2.
  have -> : pow p * (2 * u) = 2 * (pow p * u) by ring.
  by rewrite Hpp; lra.
have Hkub : (k <= 2 ^ p - 1)%Z.
  suff : (IZR k < IZR (2 ^ p))%R by move/lt_IZR; lia.
  rewrite IZR_2powp //.
  apply: (Rmult_lt_reg_r (2 * u)); first by lra.
  by rewrite -Hk Hp2u.
have -> : (2 - 2 * u = IZR (2 ^ p - 1) * (2 * u)).
  rewrite minus_IZR IZR_2powp //.
  by rewrite Rmult_minus_distr_r Hp2u; lra.
rewrite Hk; apply: Rmult_le_compat_r; first by lra.
by apply: IZR_le.
Qed.

(* ===========================================================================*)
(*  FLX scale-invariance (the paper's "WLOG 1 <= x0, y0 < 2").                 *)
(*                                                                            *)
(*  In FLX every operation of Algorithm 9 commutes with scaling an input by a  *)
(*  power of two ([round_bpow_FLX]).  We propagate this through the building    *)
(*  blocks ([TwoSum], [vecSum], [vsebAux]/[vseb]/[vsebK], [TwoProd]) and hence  *)
(*  through [ThreeProd]; combined with the scale-invariance of [isTW] and the  *)
(*  scaling of [TWval], it lets the two theorems reduce to normalised inputs.  *)
(* ===========================================================================*)

(* [RND] commutes with scaling by a power of two (FLX; no underflow).          *)
Lemma round_scale x c : RND (x * pow c) = RND x * pow c.
Proof. exact: round_bpow_FLX. Qed.

(* [TwoSum] scales: both output words pick up the common factor [pow c].       *)
Lemma TwoSum_scale a b c :
  TwoSum (a * pow c) (b * pow c) =
  DWR (dwh (TwoSum a b) * pow c) (dwl (TwoSum a b) * pow c).
Proof.
rewrite /TwoSum /dwh /dwl.
have Add : forall x y : R, x * pow c + y * pow c = (x + y) * pow c by move=> *; ring.
have Sub : forall x y : R, x * pow c - y * pow c = (x - y) * pow c by move=> *; ring.
by do 6! (rewrite ?Add ?Sub ?round_scale).
Qed.

(* [vecSumAux] scales: the emitted list and the running sum both pick up        *)
(* [pow c].                                                                    *)
Lemma vecSumAux_scale l c :
  vecSumAux [seq z * pow c | z <- l] =
  ([seq z * pow c | z <- (vecSumAux l).1], (vecSumAux l).2 * pow c).
Proof.
elim: l => [|x l IH].
  by rewrite /= Rmult_0_l.
case: l IH => [|y l'] IH; first by [].
rewrite map_cons map_cons vecSumAux_cons.
rewrite -map_cons IH.
case E0 : (vecSumAux (y :: l')) => [es0 s0].
rewrite TwoSum_scale.
rewrite vecSumAux_cons E0.
by case E1 : (TwoSum x s0) => [si0 ei0].
Qed.

(* [vecSum] scales.                                                            *)
Lemma vecSum_scale l c :
  vecSum [seq z * pow c | z <- l] = [seq z * pow c | z <- vecSum l].
Proof.
rewrite /vecSum vecSumAux_scale.
by case: (vecSumAux l) => es s0.
Qed.

(* [vsebAux] scales (the [et = 0] branch test is preserved: [pow c <> 0]).     *)
Lemma vsebAux_scale eps l c :
  vsebAux (eps * pow c) [seq z * pow c | z <- l] =
  [seq z * pow c | z <- vsebAux eps l].
Proof.
have pcn0 : pow c <> 0 by apply: Rgt_not_eq; apply: bpow_gt_0.
elim: l eps => [|e l IH] eps; first by [].
case: l IH => [|e2 l'] IH.
  rewrite map_cons vsebAux_1 vsebAux_1 TwoSum_scale.
  by case E1 : (TwoSum eps e) => [y0 y1].
rewrite map_cons map_cons vsebAux_consS.
rewrite TwoSum_scale.
rewrite vsebAux_consS.
case E1 : (TwoSum eps e) => [r0 et0].
rewrite dwhE dwlE.
case: (Req_EM_T et0 0) => [Et0|Et0].
  have Ec : et0 * pow c = 0 by rewrite Et0; ring.
  have -> : is_left (Req_EM_T (et0 * pow c) 0) = true.
    by case: (Req_EM_T (et0 * pow c) 0) => // H; case: (H Ec).
  by rewrite -map_cons IH.
have -> : is_left (Req_EM_T (et0 * pow c) 0) = false.
  case: (Req_EM_T (et0 * pow c) 0) => // H.
  by case: (Rmult_integral _ _ H) => k; [case: (Et0 k) | case: (pcn0 k)].
by rewrite -map_cons IH.
Qed.

(* [vseb] and [vsebK] scale.                                                   *)
Lemma vseb_scale l c :
  vseb [seq z * pow c | z <- l] = [seq z * pow c | z <- vseb l].
Proof.
case: l => [|e0 l'] //.
by rewrite map_cons /vseb vsebAux_scale.
Qed.

Lemma vsebK_scale k l c :
  vsebK k [seq z * pow c | z <- l] = [seq z * pow c | z <- vsebK k l].
Proof.
rewrite /vsebK vseb_scale.
by rewrite map_take.
Qed.

(* [TwoProd] scales: with factors [pow c1] on [a] and [pow c2] on [b], both     *)
(* words pick up [pow (c1 + c2)].                                              *)
Lemma TwoProd_scale a b c1 c2 :
  TwoProd (a * pow c1) (b * pow c2) =
  ((TwoProd a b).1 * pow (c1 + c2), (TwoProd a b).2 * pow (c1 + c2)).
Proof.
rewrite /TwoProd /=.
have Hprod : a * pow c1 * (b * pow c2) = a * b * pow (c1 + c2).
  by rewrite bpow_plus; ring.
rewrite Hprod round_scale.
congr pair.
have -> : a * b * pow (c1 + c2) - RND (a * b) * pow (c1 + c2) =
          (a * b - RND (a * b)) * pow (c1 + c2) by ring.
by rewrite round_scale.
Qed.

(* [nth] through a scaling [map] (the default [0] is fixed by the factor).     *)
Lemma nth_map_scale (l : seq R) (c : Z) i :
  nth 0 [seq z * pow c | z <- l] i = nth 0 l i * pow c.
Proof. by elim: l i => [|x l IH] [|i] //=; rewrite ?Rmult_0_l //. Qed.

(* [format], [ulp] under scaling by a power of two.                            *)
Lemma format_scale x c : format (x * pow c) <-> format x.
Proof.
have pcn0 : pow c <> 0 by apply: Rgt_not_eq; apply: bpow_gt_0.
split=> Hf.
  have Hr : RND x * pow c = x * pow c.
    by rewrite -round_scale (round_generic _ _ _ _ Hf).
  have HRx : RND x = x by apply: (Rmult_eq_reg_r (pow c)).
  by rewrite -HRx; apply: generic_format_round.
have HRxc : RND (x * pow c) = x * pow c.
  by rewrite round_scale (round_generic _ _ _ _ Hf).
by rewrite -HRxc; apply: generic_format_round.
Qed.

Lemma ulp_scale x c : ulp (x * pow c) = ulp x * pow c.
Proof.
case: (Req_dec x 0) => [->|xn0].
  by rewrite Rmult_0_l !ulp_FLX_0 Rmult_0_l.
have xcn0 : x * pow c <> 0.
  apply: Rmult_integral_contrapositive_currified => //.
  by apply: Rgt_not_eq; apply: bpow_gt_0.
rewrite !ulp_neq_0 // cexp_bpow_FLX // bpow_plus; ring.
Qed.

(* Scaling a triple word by [pow c] (component-wise).                          *)
Definition scaleTW (c : Z) (t : twR) : twR :=
  let: TWR t0 t1 t2 := t in TWR (t0 * pow c) (t1 * pow c) (t2 * pow c).

Lemma TWval_scale c t : TWval (scaleTW c t) = TWval t * pow c.
Proof. by case: t => t0 t1 t2 /=; ring. Qed.

(* [isTW] is scale-invariant (formats, and the strict [ulp] gaps, both scale). *)
Lemma isTW_scale c t : isTW (scaleTW c t) <-> isTW t.
Proof.
have pc0 : 0 < pow c by apply: bpow_gt_0.
have Rc : Rabs (pow c) = pow c by apply: Rabs_pos_eq; lra.
case: t => t0 t1 t2 /=; split=> -[F0 F1 F2 H1 H2]; split.
- by rewrite -(format_scale t0 c).
- by rewrite -(format_scale t1 c).
- by rewrite -(format_scale t2 c).
- case: H1 => [H1|H1]; [left; nra | right].
  move: H1; rewrite ulp_scale Rabs_mult Rc => HH.
  by apply: (Rmult_lt_reg_r (pow c)).
- case: H2 => [H2|H2]; [left; nra | right].
  move: H2; rewrite ulp_scale Rabs_mult Rc => HH.
  by apply: (Rmult_lt_reg_r (pow c)).
- by rewrite (format_scale t0 c).
- by rewrite (format_scale t1 c).
- by rewrite (format_scale t2 c).
- case: H1 => [->|H1]; [left; ring | right].
  rewrite ulp_scale Rabs_mult Rc.
  by apply: Rmult_lt_compat_r.
- case: H2 => [->|H2]; [left; ring | right].
  rewrite ulp_scale Rabs_mult Rc.
  by apply: Rmult_lt_compat_r.
Qed.

(* ===========================================================================*)
(*  Algorithm 9 is scale-equivariant: [ThreeProd] of scaled inputs is the      *)
(*  scaled [ThreeProd].  This is the FLX "WLOG 1 <= x0, y0 < 2" made explicit. *)
(* ===========================================================================*)
Lemma ThreeProd_scale a b x y :
  ThreeProd (scaleTW a x) (scaleTW b y) = scaleTW (a + b) (ThreeProd x y).
Proof.
case: x => x0 x1 x2; case: y => y0 y1 y2.
rewrite /ThreeProd /scaleTW.
have P1 : x1 * pow a * (y1 * pow b) = x1 * y1 * pow (a + b) by rewrite bpow_plus; ring.
have P2 : x0 * pow a * (y2 * pow b) = x0 * y2 * pow (a + b) by rewrite bpow_plus; ring.
have P3 : x2 * pow a * (y0 * pow b) = x2 * y0 * pow (a + b) by rewrite bpow_plus; ring.
rewrite !P1 !P2 !P3 !TwoProd_scale.
case: (TwoProd x0 y0) => w00p w00m.
case: (TwoProd x0 y1) => w01p w01m.
case: (TwoProd x1 y0) => w10p w10m.
have F1 : forall u v : R, (u, v).1 = u by [].
have F2 : forall u v : R, (u, v).2 = v by [].
rewrite !F1 !F2.
have Eb : forall i, nth 0 (vecSum [:: w00m * pow (a+b); w01p * pow (a+b); w10p * pow (a+b)]) i = nth 0 (vecSum [:: w00m; w01p; w10p]) i * pow (a+b).
  move=> i.
  have -> : [:: w00m * pow (a+b); w01p * pow (a+b); w10p * pow (a+b)] = [seq z * pow (a+b) | z <- [:: w00m; w01p; w10p]] by [].
  by rewrite vecSum_scale nth_map_scale.
rewrite !Eb.
set bb := vecSum [:: w00m; w01p; w10p].
have E4 : forall t : R, RND (t * pow (a+b) + x1 * y1 * pow (a+b)) = RND (t + x1 * y1) * pow (a+b).
  move=> t.
  have -> : t * pow (a+b) + x1 * y1 * pow (a+b) = (t + x1 * y1) * pow (a+b) by ring.
  by rewrite round_scale.
have E5 : RND (RND (w10m * pow (a+b) + x0 * y2 * pow (a+b)) + RND (w01m * pow (a+b) + x2 * y0 * pow (a+b))) = RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)) * pow (a+b).
  have -> : w10m * pow (a+b) + x0 * y2 * pow (a+b) = (w10m + x0 * y2) * pow (a+b) by ring.
  have -> : w01m * pow (a+b) + x2 * y0 * pow (a+b) = (w01m + x2 * y0) * pow (a+b) by ring.
  rewrite !round_scale.
  have -> : RND (w10m + x0 * y2) * pow (a+b) + RND (w01m + x2 * y0) * pow (a+b) = (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)) * pow (a+b) by ring.
  by rewrite round_scale.
rewrite !E4 !E5.
have Ee : forall i, nth 0 (vecSum [:: w00p * pow (a+b); nth 0 bb 0 * pow (a+b); nth 0 bb 1 * pow (a+b); RND (nth 0 bb 2 + x1 * y1) * pow (a+b); RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)) * pow (a+b)]) i = nth 0 (vecSum [:: w00p; nth 0 bb 0; nth 0 bb 1; RND (nth 0 bb 2 + x1 * y1); RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))]) i * pow (a+b).
  move=> i.
  have -> : [:: w00p * pow (a+b); nth 0 bb 0 * pow (a+b); nth 0 bb 1 * pow (a+b); RND (nth 0 bb 2 + x1 * y1) * pow (a+b); RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)) * pow (a+b)] = [seq z * pow (a+b) | z <- [:: w00p; nth 0 bb 0; nth 0 bb 1; RND (nth 0 bb 2 + x1 * y1); RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))]] by [].
  by rewrite vecSum_scale nth_map_scale.
rewrite !Ee.
set ee := vecSum [:: w00p; nth 0 bb 0; nth 0 bb 1; RND (nth 0 bb 2 + x1 * y1); RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))].
have Ev : vsebK 2 [:: nth 0 ee 1 * pow (a+b); nth 0 ee 2 * pow (a+b); nth 0 ee 3 * pow (a+b); nth 0 ee 4 * pow (a+b)] = [seq z * pow (a+b) | z <- vsebK 2 [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3; nth 0 ee 4]].
  have -> : [:: nth 0 ee 1 * pow (a+b); nth 0 ee 2 * pow (a+b); nth 0 ee 3 * pow (a+b); nth 0 ee 4 * pow (a+b)] = [seq z * pow (a+b) | z <- [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3; nth 0 ee 4]] by [].
  by rewrite vsebK_scale.
rewrite Ev.
set V := vsebK 2 [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3; nth 0 ee 4].
by case: V => [|r1 [|r2 rr]] //=; congr TWR; ring.
Qed.

(* ===========================================================================*)
(*  Sign-equivariance: negating [x_bar] alone flips every intermediate (each   *)
(*  is odd of degree one in the [x] limbs), so [ThreeProd] is odd in its first  *)
(*  argument.  Together with [ThreeProd_scale] this yields the paper's full     *)
(*  "WLOG 1 <= x0, y0 < 2" (positive, normalised).                            *)
(* ===========================================================================*)

(* [RND] commutes with negation (symmetric ties-to-even, via [choice_sym]).    *)
Lemma round_opp x : RND (- x) = - RND x.
Proof. exact: (RN_opp_sym p choice_sym). Qed.

Lemma nth_map_opp (l : seq R) i :
  nth 0 [seq - z | z <- l] i = - nth 0 l i.
Proof. by elim: l i => [|x l IH] [|i] //=; rewrite ?Ropp_0 //. Qed.

Lemma TwoSum_opp a b :
  TwoSum (- a) (- b) = DWR (- dwh (TwoSum a b)) (- dwl (TwoSum a b)).
Proof.
rewrite /TwoSum /dwh /dwl.
have Add : forall u v : R, - u + - v = - (u + v) by move=> *; ring.
have Sub : forall u v : R, - u - - v = - (u - v) by move=> *; ring.
by do 6! (rewrite ?Add ?Sub ?round_opp).
Qed.

Lemma vecSumAux_opp l :
  vecSumAux [seq - z | z <- l] =
  ([seq - z | z <- (vecSumAux l).1], - (vecSumAux l).2).
Proof.
elim: l => [|x l IH].
  by rewrite /= Ropp_0.
case: l IH => [|y l'] IH; first by [].
rewrite map_cons map_cons vecSumAux_cons.
rewrite -map_cons IH.
case E0 : (vecSumAux (y :: l')) => [es0 s0].
rewrite TwoSum_opp.
rewrite vecSumAux_cons E0.
by case E1 : (TwoSum x s0) => [si0 ei0].
Qed.

Lemma vecSum_opp l :
  vecSum [seq - z | z <- l] = [seq - z | z <- vecSum l].
Proof.
rewrite /vecSum vecSumAux_opp.
by case: (vecSumAux l) => es s0.
Qed.

Lemma vsebAux_opp eps l :
  vsebAux (- eps) [seq - z | z <- l] = [seq - z | z <- vsebAux eps l].
Proof.
elim: l eps => [|e l IH] eps; first by [].
case: l IH => [|e2 l'] IH.
  rewrite map_cons vsebAux_1 vsebAux_1 TwoSum_opp.
  by case E1 : (TwoSum eps e) => [y0 y1].
rewrite map_cons map_cons vsebAux_consS.
rewrite TwoSum_opp.
rewrite vsebAux_consS.
case E1 : (TwoSum eps e) => [r0 et0].
rewrite dwhE dwlE.
case: (Req_EM_T et0 0) => [Et0|Et0].
  have Ec : - et0 = 0 by rewrite Et0; ring.
  have -> : is_left (Req_EM_T (- et0) 0) = true.
    by case: (Req_EM_T (- et0) 0) => // H; case: (H Ec).
  by rewrite -map_cons IH.
have -> : is_left (Req_EM_T (- et0) 0) = false.
  case: (Req_EM_T (- et0) 0) => // H.
  have E0 : et0 = 0 by lra.
  by case: (Et0 E0).
by rewrite -map_cons IH.
Qed.

Lemma vseb_opp l :
  vseb [seq - z | z <- l] = [seq - z | z <- vseb l].
Proof.
case: l => [|e0 l'] //.
by rewrite map_cons /vseb vsebAux_opp.
Qed.

Lemma vsebK_opp k l :
  vsebK k [seq - z | z <- l] = [seq - z | z <- vsebK k l].
Proof.
rewrite /vsebK vseb_opp.
by rewrite map_take.
Qed.

(* [TwoProd] with the LEFT factor negated: both words flip sign.               *)
Lemma TwoProd_opp_l a b :
  TwoProd (- a) b = (- (TwoProd a b).1, - (TwoProd a b).2).
Proof.
rewrite /TwoProd /=.
have -> : - a * b = - (a * b) by ring.
rewrite round_opp.
congr pair.
have -> : - (a * b) - - RND (a * b) = - (a * b - RND (a * b)) by ring.
by rewrite round_opp.
Qed.

(* Negating a triple word (component-wise).                                    *)
Definition negTW (t : twR) : twR :=
  let: TWR t0 t1 t2 := t in TWR (- t0) (- t1) (- t2).

Lemma TWval_opp t : TWval (negTW t) = - TWval t.
Proof. by case: t => t0 t1 t2 /=; ring. Qed.

Lemma isTW_opp t : isTW (negTW t) <-> isTW t.
Proof.
have Fo : forall z, format (- z) <-> format z.
  move=> z; split=> H; last by apply: generic_format_opp.
  by rewrite -[z]Ropp_involutive; apply: generic_format_opp.
case: t => t0 t1 t2 /=; split=> -[F0 F1 F2 H1 H2]; split; rewrite ?ulp_opp.
- by apply/Fo.
- by apply/Fo.
- by apply/Fo.
- case: H1 => [H1|H1]; [left; lra | right].
  by move: H1; rewrite Rabs_Ropp ulp_opp.
- case: H2 => [H2|H2]; [left; lra | right].
  by move: H2; rewrite Rabs_Ropp ulp_opp.
- by apply/Fo.
- by apply/Fo.
- by apply/Fo.
- case: H1 => [H1|H1]; [left; lra | right].
  by rewrite Rabs_Ropp.
- case: H2 => [H2|H2]; [left; lra | right].
  by rewrite Rabs_Ropp.
Qed.

(* Algorithm 9 is odd in its first argument.                                   *)
Lemma ThreeProd_opp x y : ThreeProd (negTW x) y = negTW (ThreeProd x y).
Proof.
case: x => x0 x1 x2; case: y => y0 y1 y2.
rewrite /ThreeProd /negTW.
have P1 : (- x1) * y1 = - (x1 * y1) by ring.
have P2 : (- x0) * y2 = - (x0 * y2) by ring.
have P3 : (- x2) * y0 = - (x2 * y0) by ring.
rewrite !P1 !P2 !P3 !TwoProd_opp_l.
case: (TwoProd x0 y0) => w00p w00m.
case: (TwoProd x0 y1) => w01p w01m.
case: (TwoProd x1 y0) => w10p w10m.
have F1 : forall u v : R, (u, v).1 = u by [].
have F2 : forall u v : R, (u, v).2 = v by [].
rewrite !F1 !F2.
have Eb : forall i, nth 0 (vecSum [:: - w00m; - w01p; - w10p]) i = - nth 0 (vecSum [:: w00m; w01p; w10p]) i.
  move=> i.
  have -> : [:: - w00m; - w01p; - w10p] = [seq - z | z <- [:: w00m; w01p; w10p]] by [].
  by rewrite vecSum_opp nth_map_opp.
rewrite !Eb.
set bb := vecSum [:: w00m; w01p; w10p].
have E4 : forall t : R, RND (- t + - (x1 * y1)) = - RND (t + x1 * y1).
  move=> t.
  have -> : - t + - (x1 * y1) = - (t + x1 * y1) by ring.
  by rewrite round_opp.
have E5 : RND (RND (- w10m + - (x0 * y2)) + RND (- w01m + - (x2 * y0))) = - RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)).
  have -> : - w10m + - (x0 * y2) = - (w10m + x0 * y2) by ring.
  have -> : - w01m + - (x2 * y0) = - (w01m + x2 * y0) by ring.
  rewrite !round_opp.
  have -> : - RND (w10m + x0 * y2) + - RND (w01m + x2 * y0) = - (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)) by ring.
  by rewrite round_opp.
rewrite !E4 !E5.
have Ee : forall i, nth 0 (vecSum [:: - w00p; - nth 0 bb 0; - nth 0 bb 1; - RND (nth 0 bb 2 + x1 * y1); - RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))]) i = - nth 0 (vecSum [:: w00p; nth 0 bb 0; nth 0 bb 1; RND (nth 0 bb 2 + x1 * y1); RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))]) i.
  move=> i.
  have -> : [:: - w00p; - nth 0 bb 0; - nth 0 bb 1; - RND (nth 0 bb 2 + x1 * y1); - RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))] = [seq - z | z <- [:: w00p; nth 0 bb 0; nth 0 bb 1; RND (nth 0 bb 2 + x1 * y1); RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))]] by [].
  by rewrite vecSum_opp nth_map_opp.
rewrite !Ee.
set ee := vecSum [:: w00p; nth 0 bb 0; nth 0 bb 1; RND (nth 0 bb 2 + x1 * y1); RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))].
have Ev : vsebK 2 [:: - nth 0 ee 1; - nth 0 ee 2; - nth 0 ee 3; - nth 0 ee 4] = [seq - z | z <- vsebK 2 [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3; nth 0 ee 4]].
  have -> : [:: - nth 0 ee 1; - nth 0 ee 2; - nth 0 ee 3; - nth 0 ee 4] = [seq - z | z <- [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3; nth 0 ee 4]] by [].
  by rewrite vsebK_opp.
rewrite Ev.
set V := vsebK 2 [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3; nth 0 ee 4].
by case: V => [|r1 [|r2 rr]] //=; congr TWR; ring.
Qed.

(* [TwoProd] with the RIGHT factor negated: both words flip sign.              *)
Lemma TwoProd_opp_r a b :
  TwoProd a (- b) = (- (TwoProd a b).1, - (TwoProd a b).2).
Proof.
rewrite /TwoProd /=.
have -> : a * - b = - (a * b) by ring.
rewrite round_opp.
congr pair.
have -> : - (a * b) - - RND (a * b) = - (a * b - RND (a * b)) by ring.
by rewrite round_opp.
Qed.

(* Algorithm 9 is odd in its second argument, too.                            *)
Lemma ThreeProd_opp_r x y : ThreeProd x (negTW y) = negTW (ThreeProd x y).
Proof.
case: x => x0 x1 x2; case: y => y0 y1 y2.
rewrite /ThreeProd /negTW.
have P1 : x1 * (- y1) = - (x1 * y1) by ring.
have P2 : x0 * (- y2) = - (x0 * y2) by ring.
have P3 : x2 * (- y0) = - (x2 * y0) by ring.
rewrite !P1 !P2 !P3 !TwoProd_opp_r.
case: (TwoProd x0 y0) => w00p w00m.
case: (TwoProd x0 y1) => w01p w01m.
case: (TwoProd x1 y0) => w10p w10m.
have F1 : forall u v : R, (u, v).1 = u by [].
have F2 : forall u v : R, (u, v).2 = v by [].
rewrite !F1 !F2.
have Eb : forall i, nth 0 (vecSum [:: - w00m; - w01p; - w10p]) i = - nth 0 (vecSum [:: w00m; w01p; w10p]) i.
  move=> i.
  have -> : [:: - w00m; - w01p; - w10p] = [seq - z | z <- [:: w00m; w01p; w10p]] by [].
  by rewrite vecSum_opp nth_map_opp.
rewrite !Eb.
set bb := vecSum [:: w00m; w01p; w10p].
have E4 : forall t : R, RND (- t + - (x1 * y1)) = - RND (t + x1 * y1).
  move=> t.
  have -> : - t + - (x1 * y1) = - (t + x1 * y1) by ring.
  by rewrite round_opp.
have E5 : RND (RND (- w10m + - (x0 * y2)) + RND (- w01m + - (x2 * y0))) = - RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)).
  have -> : - w10m + - (x0 * y2) = - (w10m + x0 * y2) by ring.
  have -> : - w01m + - (x2 * y0) = - (w01m + x2 * y0) by ring.
  rewrite !round_opp.
  have -> : - RND (w10m + x0 * y2) + - RND (w01m + x2 * y0) = - (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)) by ring.
  by rewrite round_opp.
rewrite !E4 !E5.
have Ee : forall i, nth 0 (vecSum [:: - w00p; - nth 0 bb 0; - nth 0 bb 1; - RND (nth 0 bb 2 + x1 * y1); - RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))]) i = - nth 0 (vecSum [:: w00p; nth 0 bb 0; nth 0 bb 1; RND (nth 0 bb 2 + x1 * y1); RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))]) i.
  move=> i.
  have -> : [:: - w00p; - nth 0 bb 0; - nth 0 bb 1; - RND (nth 0 bb 2 + x1 * y1); - RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))] = [seq - z | z <- [:: w00p; nth 0 bb 0; nth 0 bb 1; RND (nth 0 bb 2 + x1 * y1); RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))]] by [].
  by rewrite vecSum_opp nth_map_opp.
rewrite !Ee.
set ee := vecSum [:: w00p; nth 0 bb 0; nth 0 bb 1; RND (nth 0 bb 2 + x1 * y1); RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))].
have Ev : vsebK 2 [:: - nth 0 ee 1; - nth 0 ee 2; - nth 0 ee 3; - nth 0 ee 4] = [seq - z | z <- vsebK 2 [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3; nth 0 ee 4]].
  have -> : [:: - nth 0 ee 1; - nth 0 ee 2; - nth 0 ee 3; - nth 0 ee 4] = [seq - z | z <- [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3; nth 0 ee 4]] by [].
  by rewrite vsebK_opp.
rewrite Ev.
set V := vsebK 2 [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3; nth 0 ee 4].
by case: V => [|r1 [|r2 rr]] //=; congr TWR; ring.
Qed.

(* ===========================================================================*)
(*  WLOG reduction: [ThreeProd_isTW]/[ThreeProd_error] reduce to normalised     *)
(*  positive inputs ([tw_norm]).  [tw_normP] packages [tw_norm] on a [twR].     *)
(* ===========================================================================*)
Definition tw_normP (t : twR) : Prop :=
  let: TWR t0 t1 t2 := t in tw_norm t0 t1 t2.

(* An [isTW] whose leading limb sits in [1, 2) is exactly a normalised [twR].   *)
Lemma isTW_tw_normP t : isTW t -> 1 <= tw0 t < 2 -> tw_normP t.
Proof.
by case: t => t0 t1 t2 [F0 F1 F2 H1 H2] /= [Hl Hr]; split=> //; split.
Qed.

(* Any nonzero [isTW] can be scaled (and sign-flipped) to a normalised [twR].   *)
Lemma isTW_normalize t :
  isTW t -> tw0 t <> 0 ->
  exists2 c : Z, True &
    (0 < tw0 t -> tw_normP (scaleTW c t)) /\
    (tw0 t < 0 -> tw_normP (scaleTW c (negTW t))).
Proof.
move=> Ht t0n0.
set m := mag beta (tw0 t).
have Hmag : pow (m - 1) <= Rabs (tw0 t) by apply: bpow_mag_le.
have Hmag2 : Rabs (tw0 t) < pow m by apply: bpow_mag_gt.
have Hp1m : 0 < pow (1 - m) by apply: bpow_gt_0.
have tw0_scale : forall c s, tw0 (scaleTW c s) = tw0 s * pow c by move=> c [s0 s1 s2].
have tw0_opp : forall s, tw0 (negTW s) = - tw0 s by move=> [s0 s1 s2].
have Hlo : pow (m - 1) * pow (1 - m) = 1.
  by rewrite -bpow_plus (_ : (m - 1 + (1 - m) = 0)%Z) ?pow0E //; lia.
have Hhi : pow m * pow (1 - m) = 2.
  rewrite -bpow_plus (_ : (m + (1 - m) = 1)%Z); last by lia.
  by rewrite /= /Z.pow_pos /=; lra.
exists (1 - m)%Z => //; split=> Hsg.
- apply: isTW_tw_normP; first by apply/isTW_scale.
  rewrite tw0_scale; rewrite Rabs_pos_eq in Hmag Hmag2; try lra.
  split.
    by rewrite -Hlo; apply: Rmult_le_compat_r; lra.
  by rewrite -Hhi; apply: Rmult_lt_compat_r; lra.
apply: isTW_tw_normP; first by apply/isTW_scale; apply/isTW_opp.
rewrite tw0_scale tw0_opp; rewrite Rabs_left in Hmag Hmag2; try lra.
split.
  by rewrite -Hlo; apply: Rmult_le_compat_r; lra.
by rewrite -Hhi; apply: Rmult_lt_compat_r; lra.
Qed.

(* Normalised (paper WLOG) forms of the two theorems.  These carry the actual  *)
(* Section-6.2 mathematics and remain to be discharged.                        *)
Lemma ThreeProd_isTW_norm x y :
  ties_to_even choice -> tw_normP x -> tw_normP y -> isTW (ThreeProd x y).
Proof.
Admitted.

Lemma ThreeProd_error_norm x y :
  ties_to_even choice -> tw_normP x -> tw_normP y ->
  Rabs (TWval (ThreeProd x y) - TWval x * TWval y) <=
     (28 * (u * u * u) + 107 * (u * u * u * u)) * Rabs (TWval x * TWval y).
Proof.
Admitted.

(* ===========================================================================*)
(*  Section 6.1 -- product-term bounds.  Each is a lemma over the two          *)
(*  normalisation contexts [tw_norm x0 x1 x2] / [tw_norm y0 y1 y2].            *)
(* ===========================================================================*)

(* The leading product [z00p = RN(x0 y0)] lies in [1, 4).                     *)
Lemma z00p_lb x0 x1 x2 y0 y1 y2 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 -> 1 <= RND (x0 * y0).
Proof.
move=> Nx Ny.
have F1 : format 1 by rewrite -(pow0E beta); apply: format_pow.
case: Nx => _ Hx0l _ _ _.
case: Ny => _ Hy0l _ _ _.
have H1 : 1 <= x0 * y0 by nra.
rewrite -{1}(round_generic _ _ _ _ F1).
by apply: round_le.
Qed.

Lemma z00p_ub x0 x1 x2 y0 y1 y2 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 -> RND (x0 * y0) < 4.
Proof.
move=> Nx Ny.
have Hu0 : 0 < u by apply: u_gt_0.
have Hxhi := tw_norm_hi Nx.
have Hyhi := tw_norm_hi Ny.
case: Nx => _ Hx0l _ _ _.
case: Ny => _ Hy0l _ _ _.
have Hprod : x0 * y0 <= 4 - 4 * u by nra.
have F44 : format (4 - 4 * u).
  have Hpm : pow p * u = 1.
    by rewrite u_pow -bpow_plus (_ : (p + - p = 0)%Z) ?pow0E //; lia.
  have -> : 4 - 4 * u = IZR (2 ^ p - 1) * (4 * u).
    rewrite minus_IZR IZR_2powp //.
    have -> : (pow p - 1) * (4 * u) = 4 * (pow p * u) - 4 * u by ring.
    by rewrite Hpm; ring.
  have -> : 4 * u = pow (2 - p).
    rewrite u_pow (_ : (2 - p = 2 + - p)%Z); last by lia.
    by rewrite bpow_plus /= /Z.pow_pos /=; lra.
  by apply: (format_mult_pow Hp2); rewrite Z.abs_eq; move: pow2_ge_16; lia.
apply: (Rle_lt_trans _ (4 - 4 * u)); last by lra.
rewrite -(round_generic _ _ _ _ F44).
by apply: round_le.
Qed.

(* [4u = pow(2-p)], used for the [< 4u] product bounds.                        *)
Lemma pow_2mp : pow (2 - p) = 4 * u.
Proof.
rewrite (_ : (2 - p = 2 + - p)%Z); last by lia.
by rewrite bpow_plus u_pow /= /Z.pow_pos /=; lra.
Qed.

(* Cross products [z01p = RN(x0 y1)], [z10p = RN(x1 y0)] are [<= 4u].          *)
Lemma z01p_bound x0 x1 x2 y0 y1 y2 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 -> Rabs (RND (x0 * y1)) <= 4 * u.
Proof.
move=> Nx Ny.
have Hu0 : 0 < u by apply: u_gt_0.
have Fx4 : format (4 * u) by rewrite -pow_2mp; apply: format_pow.
apply: Rabs_round_le_r => //.
case: Nx => _ Hx0l Hx0r _ _.
have Hy1 := tw_norm_x1 Ny.
have := Rabs_pos y1.
rewrite Rabs_mult (Rabs_pos_eq x0); last by lra.
by nra.
Qed.

Lemma z10p_bound x0 x1 x2 y0 y1 y2 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 -> Rabs (RND (x1 * y0)) <= 4 * u.
Proof.
move=> Nx Ny.
have Hu0 : 0 < u by apply: u_gt_0.
have Fx4 : format (4 * u) by rewrite -pow_2mp; apply: format_pow.
apply: Rabs_round_le_r => //.
case: Ny => _ Hy0l Hy0r _ _.
have Hx1 := tw_norm_x1 Nx.
have := Rabs_pos x1.
rewrite Rabs_mult (Rabs_pos_eq y0); last by lra.
by nra.
Qed.

(* The ignored/second-order products [x1 y1], [x0 y2], [x2 y0] are [< 4u^2].   *)
Lemma x1y1_bound x0 x1 x2 y0 y1 y2 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 -> Rabs (x1 * y1) < 4 * (u * u).
Proof.
move=> Nx Ny.
have Hu0 : 0 < u by apply: u_gt_0.
have Hx1 := tw_norm_x1 Nx.
have Hy1 := tw_norm_x1 Ny.
have := Rabs_pos x1; have := Rabs_pos y1.
by rewrite Rabs_mult; nra.
Qed.

Lemma x0y2_bound x0 x1 x2 y0 y1 y2 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 -> Rabs (x0 * y2) < 4 * (u * u).
Proof.
move=> Nx Ny.
have Hu0 : 0 < u by apply: u_gt_0.
have Hx0hi := tw_norm_hi Nx.
have Hy2 := tw_norm_x2 Ny.
have := Rabs_pos y2.
case: Nx => _ Hx0l _ _ _.
by rewrite Rabs_mult (Rabs_pos_eq x0); [nra | lra].
Qed.

Lemma x2y0_bound x0 x1 x2 y0 y1 y2 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 -> Rabs (x2 * y0) < 4 * (u * u).
Proof.
move=> Nx Ny.
have Hu0 : 0 < u by apply: u_gt_0.
have Hy0hi := tw_norm_hi Ny.
have Hx2 := tw_norm_x2 Nx.
have := Rabs_pos x2.
case: Ny => _ Hy0l _ _ _.
by rewrite Rabs_mult (Rabs_pos_eq y0); [nra | lra].
Qed.

(* [u^2 = pow(-2p)], [4u^2 = pow(2-2p)], and a float multiple of [u^2].       *)
Lemma u2_pow : u * u = pow (- (2 * p)).
Proof. by rewrite u_pow -bpow_plus; congr bpow; lia. Qed.

Lemma pow_2m2p : pow (2 - 2 * p) = 4 * (u * u).
Proof.
rewrite (_ : (2 - 2 * p = 2 + - (2 * p))%Z); last by lia.
by rewrite bpow_plus u2_pow /= /Z.pow_pos /=; lra.
Qed.

Lemma format_imul_u2 k : (Z.abs k < 2 ^ p)%Z -> format (IZR k * (u * u)).
Proof. by move=> Hk; rewrite u2_pow; apply: format_mult_pow. Qed.

(* [2^p >= 64] (from [p >= 6]); clears the [Z.abs k < 2^p] side-conditions.    *)
Fact two_p_ge_64 : (64 <= 2 ^ p)%Z.
Proof.
apply: (Z.le_trans _ (2 ^ 6)); first by [].
by apply: Z.pow_le_mono_r; lia.
Qed.

(* Master rounding bound: a value [<= k u^2] rounds to [<= k u^2] ([k < 2^p]). *)
Lemma round_le_imul_u2 w k :
  (Z.abs k < 2 ^ p)%Z -> Rabs w <= IZR k * (u * u) ->
  Rabs (RND w) <= IZR k * (u * u).
Proof. by move=> Hk Hw; apply: Rabs_round_le_r => //; apply: format_imul_u2. Qed.

(* [8u = pow(3-p)] and [8u^2 = pow(3-2p)], used for the [b2] 2Sum-error bound. *)
Lemma pow_3mp : pow (3 - p) = 8 * u.
Proof.
rewrite (_ : (3 - p = 3 + - p)%Z); last by lia.
by rewrite bpow_plus u_pow /= /Z.pow_pos /=; lra.
Qed.

Lemma pow_3m2p : pow (3 - 2 * p) = 8 * (u * u).
Proof.
rewrite (_ : (3 - 2 * p = 3 + - (2 * p))%Z); last by lia.
by rewrite bpow_plus u2_pow /= /Z.pow_pos /=; lra.
Qed.

(* [vecSum] of a 3-list, unfolded: [b0], [b1] (the [z00m + a] 2Sum) and [b2]   *)
(* (the [z01p + z10p] 2Sum error).                                             *)
Lemma vecSum3 a b c :
  format a -> format b -> format c ->
  vecSum [:: a; b; c] =
  [:: RND (a + RND (b + c)); a + RND (b + c) - RND (a + RND (b + c));
      b + c - RND (b + c)].
Proof.
move=> Fa Fb Fc.
rewrite /vecSum !vecSumAux_cons.
have -> : vecSumAux [:: c] = ([::], c) by [].
case Ebc : (TwoSum b c) => [s1 e1].
case Eac : (TwoSum a s1) => [s0 e0].
have Hs1 : s1 = RND (b + c) by move: (TwoSum_hi p choice b c); rewrite Ebc.
move: (TwoSum_correct_loc Hp2 choice_sym Fb Fc); rewrite Ebc => Hbc.
have Fs1 : format s1 by rewrite Hs1; apply: generic_format_round.
have Hs0 : s0 = RND (a + s1) by move: (TwoSum_hi p choice a s1); rewrite Eac.
move: (TwoSum_correct_loc Hp2 choice_sym Fa Fs1); rewrite Eac => Hac.
have -> : s0 = RND (a + RND (b + c)) by rewrite Hs0 Hs1.
have -> : e0 = a + RND (b + c) - RND (a + RND (b + c)) by rewrite -Hs1 -Hs0; lra.
have -> : e1 = b + c - RND (b + c) by rewrite -Hs1; lra.
by [].
Qed.

(* Leading product error [z00m = x0 y0 - RN(x0 y0)]: [|z00m| <= 2u].          *)
Lemma z00m_bound x0 x1 x2 y0 y1 y2 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  Rabs (x0 * y0 - RND (x0 * y0)) <= 2 * u.
Proof.
move=> Nx Ny.
have Hu0 : 0 < u by apply: u_gt_0.
case: (Nx) => _ Hx0l Hx0r _ _.
case: (Ny) => _ Hy0l Hy0r _ _.
have Hn0 : x0 * y0 <> 0 by nra.
have Hulp : ulp (x0 * y0) <= 4 * u.
  rewrite ulp_neq_0 // /cexp /fexp -pow_2mp; apply: bpow_le.
  suff : (mag beta (x0 * y0) <= 2)%Z by lia.
  apply: mag_le_bpow => //.
  rewrite Rabs_pos_eq; last by nra.
  have -> : pow 2 = 4 by rewrite /= /Z.pow_pos /=; lra.
  nra.
have He : Rabs (RND (x0 * y0) - x0 * y0) <= / 2 * ulp (x0 * y0)
  by apply: error_le_half_ulp.
rewrite Rabs_minus_sym; lra.
Qed.

(* ... and [z00m] is a multiple of [4u^2] (whence [uls z00m >= 4u^2]).        *)
Lemma z00m_imul x0 x1 x2 y0 y1 y2 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  is_imul (x0 * y0 - RND (x0 * y0)) (4 * (u * u)).
Proof.
move=> Nx Ny.
have Hu0 : 0 < u by apply: u_gt_0.
have Hulpx := tw_norm_ulp0 Nx.
have Hulpy := tw_norm_ulp0 Ny.
case: (Nx) => -[Fx0 _ _] Hx0l Hx0r _ _.
case: (Ny) => -[Fy0 _ _] Hy0l Hy0r _ _.
have x0n0 : x0 <> 0 by lra.
have y0n0 : y0 <> 0 by lra.
have Ix0 : is_imul x0 (pow (1 - p)).
  have Hc : pow (cexp x0) = pow (1 - p) by rewrite -ulp_neq_0 // Hulpx pow_1mp.
  by rewrite -Hc; apply: format_imul_cexp.
have Iy0 : is_imul y0 (pow (1 - p)).
  have Hc : pow (cexp y0) = pow (1 - p) by rewrite -ulp_neq_0 // Hulpy pow_1mp.
  by rewrite -Hc; apply: format_imul_cexp.
rewrite -pow_2m2p.
have Ip : is_imul (x0 * y0) (pow (2 - 2 * p)).
  have := is_imul_mul Ix0 Iy0.
  by rewrite -bpow_plus (_ : (1 - p + (1 - p) = 2 - 2 * p)%Z); last by lia.
apply: is_imul_minus => //.
by apply: is_imul_pow_round.
Qed.

(* Cross product errors [z01m], [z10m]: [<= 2u^2].                            *)
Lemma z01m_bound x0 x1 x2 y0 y1 y2 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  Rabs (x0 * y1 - RND (x0 * y1)) <= 2 * (u * u).
Proof.
move=> Nx Ny.
have Hu0 : 0 < u by apply: u_gt_0.
case: (Nx) => _ Hx0l Hx0r _ _.
have Hy1 := tw_norm_x1 Ny.
have Hprod : Rabs (x0 * y1) < 4 * u.
  rewrite Rabs_mult (Rabs_pos_eq x0); last by lra.
  have := Rabs_pos y1; nra.
case: (Req_dec (x0 * y1) 0) => [Hz|Hn0].
  by rewrite Hz round_0 Rminus_0_r Rabs_R0; nra.
have Hulp : ulp (x0 * y1) <= 4 * (u * u).
  rewrite ulp_neq_0 // /cexp /fexp -pow_2m2p; apply: bpow_le.
  suff : (mag beta (x0 * y1) <= 2 - p)%Z by lia.
  by apply: mag_le_bpow => //; rewrite pow_2mp.
have He : Rabs (RND (x0 * y1) - x0 * y1) <= / 2 * ulp (x0 * y1)
  by apply: error_le_half_ulp.
rewrite Rabs_minus_sym; lra.
Qed.

Lemma z10m_bound x0 x1 x2 y0 y1 y2 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  Rabs (x1 * y0 - RND (x1 * y0)) <= 2 * (u * u).
Proof.
move=> Nx Ny.
have Hu0 : 0 < u by apply: u_gt_0.
case: (Ny) => _ Hy0l Hy0r _ _.
have Hx1 := tw_norm_x1 Nx.
have Hprod : Rabs (x1 * y0) < 4 * u.
  rewrite Rabs_mult (Rabs_pos_eq y0); last by lra.
  have := Rabs_pos x1; nra.
case: (Req_dec (x1 * y0) 0) => [Hz|Hn0].
  by rewrite Hz round_0 Rminus_0_r Rabs_R0; nra.
have Hulp : ulp (x1 * y0) <= 4 * (u * u).
  rewrite ulp_neq_0 // /cexp /fexp -pow_2m2p; apply: bpow_le.
  suff : (mag beta (x1 * y0) <= 2 - p)%Z by lia.
  by apply: mag_le_bpow => //; rewrite pow_2mp.
have He : Rabs (RND (x1 * y0) - x1 * y0) <= / 2 * ulp (x1 * y0)
  by apply: error_le_half_ulp.
rewrite Rabs_minus_sym; lra.
Qed.

(* The FMA terms [z31 = RN(z10m + x0 y2)], [z32 = RN(z01m + x2 y0)]: [<= 6u^2].*)
Lemma z31_bound z10m x0 y2 :
  Rabs z10m <= 2 * (u * u) -> Rabs (x0 * y2) < 4 * (u * u) ->
  Rabs (RND (z10m + x0 * y2)) <= 6 * (u * u).
Proof.
move=> H1 H2.
have F6 : format (6 * (u * u)).
  by apply: (format_imul_u2 (k := 6)); have := two_p_ge_64; lia.
apply: Rabs_round_le_r => //.
by have := Rabs_triang z10m (x0 * y2); lra.
Qed.

Lemma z32_bound z01m x2 y0 :
  Rabs z01m <= 2 * (u * u) -> Rabs (x2 * y0) < 4 * (u * u) ->
  Rabs (RND (z01m + x2 * y0)) <= 6 * (u * u).
Proof.
move=> H1 H2.
have F6 : format (6 * (u * u)).
  by apply: (format_imul_u2 (k := 6)); have := two_p_ge_64; lia.
apply: Rabs_round_le_r => //.
by have := Rabs_triang z01m (x2 * y0); lra.
Qed.

(* [z3 = RN(z31 + z32)]: [<= 12u^2].                                          *)
Lemma z3_bound z31 z32 :
  Rabs z31 <= 6 * (u * u) -> Rabs z32 <= 6 * (u * u) ->
  Rabs (RND (z31 + z32)) <= 12 * (u * u).
Proof.
move=> H1 H2.
have F12 : format (12 * (u * u)).
  by apply: (format_imul_u2 (k := 12)); have := two_p_ge_64; lia.
apply: Rabs_round_le_r => //.
by have := Rabs_triang z31 z32; lra.
Qed.

(* [b2 = z01p + z10p - RN(z01p + z10p)] (the third VecSum limb): [<= 4u^2].    *)
Lemma b2_bound x0 x1 x2 y0 y1 y2 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  Rabs (RND (x0 * y1) + RND (x1 * y0) - RND (RND (x0 * y1) + RND (x1 * y0)))
    <= 4 * (u * u).
Proof.
move=> Nx Ny.
have Hu0 : 0 < u by apply: u_gt_0.
set s := RND (x0 * y1) + RND (x1 * y0).
have Hz01 := z01p_bound Nx Ny.
have Hz10 := z10p_bound Nx Ny.
have Hs8 : Rabs s <= 8 * u.
  by rewrite /s; have := Rabs_triang (RND (x0 * y1)) (RND (x1 * y0)); lra.
case: (Rlt_le_dec (Rabs s) (8 * u)) => Hs; last first.
  have Heq : Rabs s = 8 * u by lra.
  have Fs : format s.
    have Hor : s = 8 * u \/ s = - (8 * u) by split_Rabs; lra.
    have F8 : format (8 * u) by rewrite -pow_3mp; apply: format_pow.
    by case: Hor => ->; [ | apply: generic_format_opp].
  by rewrite (round_generic _ _ _ _ Fs) Rminus_diag Rabs_R0; nra.
case: (Req_dec s 0) => [->|sn0].
  by rewrite round_0 Rminus_0_r Rabs_R0; nra.
have Hulp : ulp s <= 8 * (u * u).
  rewrite ulp_neq_0 // /cexp /fexp -pow_3m2p; apply: bpow_le.
  suff : (mag beta s <= 3 - p)%Z by lia.
  by apply: mag_le_bpow => //; rewrite pow_3mp.
have He : Rabs (RND s - s) <= / 2 * ulp s by apply: error_le_half_ulp.
rewrite Rabs_minus_sym; lra.
Qed.

(* [c = RN(b2 + x1 y1)]: [<= 8u^2].                                           *)
Lemma c_bound b2 x1 y1 :
  Rabs b2 <= 4 * (u * u) -> Rabs (x1 * y1) < 4 * (u * u) ->
  Rabs (RND (b2 + x1 * y1)) <= 8 * (u * u).
Proof.
move=> H1 H2.
have F8 : format (8 * (u * u)).
  by apply: (format_imul_u2 (k := 8)); have := two_p_ge_64; lia.
apply: Rabs_round_le_r => //.
by have := Rabs_triang b2 (x1 * y1); lra.
Qed.

(* [s3 = RN(c + z3)]: [<= 20u^2].                                             *)
Lemma s3_bound c z3 :
  Rabs c <= 8 * (u * u) -> Rabs z3 <= 12 * (u * u) ->
  Rabs (RND (c + z3)) <= 20 * (u * u).
Proof.
move=> H1 H2.
have F20 : format (20 * (u * u)).
  by apply: (format_imul_u2 (k := 20)); have := two_p_ge_64; lia.
apply: Rabs_round_le_r => //.
by have := Rabs_triang c z3; lra.
Qed.

(* ===========================================================================*)
(*  Section 6.2 (part 2) -- the error sources.  [ThreeProd_error_norm] sums    *)
(*  six terms [eps0..eps5]; [eps1..eps4] are single-rounding errors bounded    *)
(*  here by [k u^3].  ([eps0] is a pure product bound; [eps5] is the VSEB      *)
(*  truncation, Theorem 3.)                                                    *)
(* ===========================================================================*)

(* [16u^2 = pow(4-2p)], [u^3 = pow(-3p)], [8u^3 = pow(3-3p)], [16u^3=pow(4-3p)]*)
Lemma pow_4m2p : pow (4 - 2 * p) = 16 * (u * u).
Proof.
rewrite (_ : (4 - 2 * p = 4 + - (2 * p))%Z); last by lia.
by rewrite bpow_plus u2_pow /= /Z.pow_pos /=; lra.
Qed.

Lemma u3_pow : u * u * u = pow (- (3 * p)).
Proof. by rewrite u2_pow u_pow -bpow_plus; congr bpow; lia. Qed.

Lemma pow_3m3p : pow (3 - 3 * p) = 8 * (u * u * u).
Proof.
rewrite (_ : (3 - 3 * p = 3 + - (3 * p))%Z); last by lia.
by rewrite bpow_plus u3_pow /= /Z.pow_pos /=; lra.
Qed.

Lemma pow_4m3p : pow (4 - 3 * p) = 16 * (u * u * u).
Proof.
rewrite (_ : (4 - 3 * p = 4 + - (3 * p))%Z); last by lia.
by rewrite bpow_plus u3_pow /= /Z.pow_pos /=; lra.
Qed.

(* Master rounding-error bound: [|w| < pow e] gives [|w - RN w| <= half pow    *)
(* (e-p)].                                                                     *)
Lemma round_err_le w e :
  Rabs w < pow e -> Rabs (w - RND w) <= / 2 * pow (e - p).
Proof.
move=> Hw.
case: (Req_dec w 0) => [->|wn0].
  rewrite round_0 Rminus_0_r Rabs_R0.
  by apply: Rmult_le_pos; [lra | apply: bpow_ge_0].
have Hulp : ulp w <= pow (e - p).
  rewrite ulp_neq_0 // /cexp /fexp; apply: bpow_le.
  suff : (mag beta w <= e)%Z by lia.
  by apply: mag_le_bpow.
have He : Rabs (RND w - w) <= / 2 * ulp w by apply: error_le_half_ulp.
rewrite Rabs_minus_sym.
have Hu0 : 0 < / 2 by lra.
lra.
Qed.

(* [u <= 1/64] (from [p >= 6]); the slack the [eps0] and assembly bounds need. *)
Lemma u_le_64 : u <= / 64.
Proof.
have -> : / 64 = pow (-6) by rewrite /= /Z.pow_pos /=; lra.
rewrite u_pow; apply: bpow_le; lia.
Qed.

(* [2u^3 = pow(1-3p)]: the tight cap on the third-order limbs.                 *)
Lemma pow_1m3p : pow (1 - 3 * p) = 2 * (u * u * u).
Proof.
rewrite (_ : (1 - 3 * p = 1 + - (3 * p))%Z); last by lia.
by rewrite bpow_plus u3_pow /= /Z.pow_pos /=; lra.
Qed.

(* A float below [pow e] is at most its predecessor [pow e - pow(e-p)] (it is  *)
(* a multiple of [pow(e-p)] and strictly below [2^p pow(e-p)]).                 *)
Lemma float_lt_bpow_le x e :
  format x -> Rabs x < pow e -> Rabs x <= pow e - pow (e - p).
Proof.
move=> Fx Hx.
have FRx : format (Rabs x) by apply: generic_format_abs.
have Fpe : format (pow e) by apply: format_pow.
have V : Valid_exp fexp by apply: FLX_exp_valid.
have Hpred := (@pred_ge_gt beta fexp V _ _ FRx Fpe Hx).
move: Hpred; rewrite pred_bpow.
move=> H; exact: H.
Qed.

(* Tight limb caps: the largest float below [2u] is [2u - 2u^2], below [2u^2]   *)
(* is [2u^2 - 2u^3].  (Needed for the [eps0] product bound.)                   *)
Lemma x1_tight x0 x1 x2 :
  tw_norm x0 x1 x2 -> Rabs x1 <= 2 * u - 2 * (u * u).
Proof.
move=> N.
have Hu0 : 0 < u by apply: u_gt_0.
have Hx1 := tw_norm_x1 N.
have Fx1 : format x1 by case: N => -[_ Fx1 _].
have Hlt : Rabs x1 < pow (1 - p) by rewrite pow_1mp.
have Hb := float_lt_bpow_le Fx1 Hlt.
move: Hb; rewrite pow_1mp (_ : (1 - p - p = 1 - 2 * p)%Z); last by lia.
rewrite pow_1m2p; lra.
Qed.

Lemma x2_tight x0 x1 x2 :
  tw_norm x0 x1 x2 -> Rabs x2 <= 2 * (u * u) - 2 * (u * u * u).
Proof.
move=> N.
have Hu0 : 0 < u by apply: u_gt_0.
have Hx2 := tw_norm_x2 N.
have Fx2 : format x2 by case: N => -[_ _ Fx2].
have Hlt : Rabs x2 < pow (1 - 2 * p) by rewrite pow_1m2p.
have Hb := float_lt_bpow_le Fx2 Hlt.
move: Hb; rewrite pow_1m2p (_ : (1 - 2 * p - p = 1 - 3 * p)%Z); last by lia.
rewrite pow_1m3p; lra.
Qed.

(* [eps0 = x1 y2 + x2 y1 + x2 y2] (the ignored products): [<= 8u^3 - 11.9u^4].  *)
Lemma eps0_bound x0 x1 x2 y0 y1 y2 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  Rabs (x1 * y2 + x2 * y1 + x2 * y2) <= 8 * (u * u * u) - 119 / 10 * (u * u * u * u).
Proof.
move=> Nx Ny.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := u_le_64.
have Hx1 := x1_tight Nx.
have Hy1 := x1_tight Ny.
have Hx2 := x2_tight Nx.
have Hy2 := x2_tight Ny.
have P1 := Rabs_pos x1; have P2 := Rabs_pos x2.
have Q1 := Rabs_pos y1; have Q2 := Rabs_pos y2.
apply: (Rle_trans _ (Rabs (x1 * y2) + Rabs (x2 * y1) + Rabs (x2 * y2))).
  have H1 := Rabs_triang (x1 * y2 + x2 * y1) (x2 * y2).
  have H2 := Rabs_triang (x1 * y2) (x2 * y1).
  lra.
rewrite !Rabs_mult.
nra.
Qed.

(* [eps1 = (z10m + x0 y2) - z31], [eps2 = (z01m + x2 y0) - z32]: [<= 4u^3].     *)
Lemma eps1_bound z10m x0 y2 :
  Rabs z10m <= 2 * (u * u) -> Rabs (x0 * y2) < 4 * (u * u) ->
  Rabs (z10m + x0 * y2 - RND (z10m + x0 * y2)) <= 4 * (u * u * u).
Proof.
move=> H1 H2.
have Hu0 : 0 < u by apply: u_gt_0.
have Hw : Rabs (z10m + x0 * y2) < pow (3 - 2 * p).
  rewrite pow_3m2p.
  have H3 := Rabs_triang z10m (x0 * y2).
  nra.
have Herr := round_err_le Hw.
move: Herr; rewrite (_ : (3 - 2 * p - p = 3 - 3 * p)%Z); last by lia.
rewrite pow_3m3p; nra.
Qed.

Lemma eps2_bound z01m x2 y0 :
  Rabs z01m <= 2 * (u * u) -> Rabs (x2 * y0) < 4 * (u * u) ->
  Rabs (z01m + x2 * y0 - RND (z01m + x2 * y0)) <= 4 * (u * u * u).
Proof.
move=> H1 H2.
have Hu0 : 0 < u by apply: u_gt_0.
have Hw : Rabs (z01m + x2 * y0) < pow (3 - 2 * p).
  rewrite pow_3m2p.
  have H3 := Rabs_triang z01m (x2 * y0).
  nra.
have Herr := round_err_le Hw.
move: Herr; rewrite (_ : (3 - 2 * p - p = 3 - 3 * p)%Z); last by lia.
rewrite pow_3m3p; nra.
Qed.

(* [eps3 = (z31 + z32) - z3]: [<= 8u^3].                                       *)
Lemma eps3_bound z31 z32 :
  Rabs z31 <= 6 * (u * u) -> Rabs z32 <= 6 * (u * u) ->
  Rabs (z31 + z32 - RND (z31 + z32)) <= 8 * (u * u * u).
Proof.
move=> H1 H2.
have Hu0 : 0 < u by apply: u_gt_0.
have Hw : Rabs (z31 + z32) < pow (4 - 2 * p).
  rewrite pow_4m2p.
  have H3 := Rabs_triang z31 z32.
  nra.
have Herr := round_err_le Hw.
move: Herr; rewrite (_ : (4 - 2 * p - p = 4 - 3 * p)%Z); last by lia.
rewrite pow_4m3p; nra.
Qed.

(* [eps4 = (b2 + x1 y1) - c]: [<= 4u^3].                                       *)
Lemma eps4_bound b2 x1 y1 :
  Rabs b2 <= 4 * (u * u) -> Rabs (x1 * y1) < 4 * (u * u) ->
  Rabs (b2 + x1 * y1 - RND (b2 + x1 * y1)) <= 4 * (u * u * u).
Proof.
move=> H1 H2.
have Hu0 : 0 < u by apply: u_gt_0.
have Hw : Rabs (b2 + x1 * y1) < pow (3 - 2 * p).
  rewrite pow_3m2p.
  have H3 := Rabs_triang b2 (x1 * y1).
  nra.
have Herr := round_err_le Hw.
move: Herr; rewrite (_ : (3 - 2 * p - p = 3 - 3 * p)%Z); last by lia.
rewrite pow_3m3p; nra.
Qed.

(* Summing the five constant error sources [eps0..eps4]: the numerator          *)
(* [8u^3-11.9u^4 + 4u^3 + 4u^3 + 8u^3 + 4u^3 = 28u^3 - 11.9u^4].                *)
Lemma eps04_sum e0 e1 e2 e3 e4 :
  Rabs e0 <= 8 * (u * u * u) - 119 / 10 * (u * u * u * u) ->
  Rabs e1 <= 4 * (u * u * u) -> Rabs e2 <= 4 * (u * u * u) ->
  Rabs e3 <= 8 * (u * u * u) -> Rabs e4 <= 4 * (u * u * u) ->
  Rabs (e0 + e1 + e2 + e3 + e4) <= 28 * (u * u * u) - 119 / 10 * (u * u * u * u).
Proof.
move=> H0 H1 H2 H3 H4.
have T1 := Rabs_triang (e0 + e1 + e2 + e3) e4.
have T2 := Rabs_triang (e0 + e1 + e2) e3.
have T3 := Rabs_triang (e0 + e1) e2.
have T4 := Rabs_triang e0 e1.
lra.
Qed.

(* [eps5]: the VSEB truncation error.  Given the VSEB output [vseb e] is        *)
(* P-nonoverlapping (this is exactly the [ThreeProd_isTW_norm] ingredient), the *)
(* tail dropped by keeping 3 limbs is [<= (2u^3 + 4.2u^4)|sum|] by Theorem 3    *)
(* ([Pnonoverlap_truncate_error] at k = 3).  Stated conditionally so it can be  *)
(* discharged now; the P-nonoverlap hypothesis comes from part 1.               *)
Lemma eps5_bound e :
  Pnonoverlap (vseb e) -> {in vseb e, forall z, format z} -> u <= / 64 ->
  Rabs (sumR (vseb e) - sumR (vsebK 3 e)) <=
    (2 * (u * u * u) + 42 / 10 * (u * u * u * u)) * Rabs (sumR (vseb e)).
Proof.
move=> Py Fy Hu64.
set y := vseb e.
have Hsplit : sumR y - sumR (vsebK 3 e) = sumR (drop 3 y).
  by rewrite /vsebK -/y -{1}(cat_take_drop 3 y) sumR_cat; ring.
rewrite Hsplit.
have -> : 2 * (u * u * u) + 42 / 10 * (u * u * u * u) =
          2 * u ^ 3 + 42 / 10 * u ^ 3.+1 by rewrite /=; ring.
case: (Req_dec (nth 0 y 0) 0) => [Hy0z|Hy0n]; last first.
  by apply: Pnonoverlap_truncate_error.
have H1 := @nth_step_zero p Hp2 y 0 Py Fy Hy0z.
have H2 := @nth_step_zero p Hp2 y 1 Py Fy H1.
have H3 := @nth_step_zero p Hp2 y 2 Py Fy H2.
have -> : sumR (drop 3 y) = 0.
  apply: (@small_head_zero p Hp2);
    [by apply: Pnonoverlap_drop
    | by move=> t /mem_drop; apply: Fy
    | by rewrite nth_drop addn0].
rewrite Rabs_R0.
have Hu0 : 0 < u by apply: u_gt_0.
apply: Rmult_le_pos; last exact: Rabs_pos.
have H4 : 0 <= u ^ 3 by apply: pow_le; lra.
have H5 : 0 <= u ^ 4 by apply: pow_le; lra.
lra.
Qed.

(* Final assembly: an error numerator [<= 28u^3 - 11.9u^4] over a product of    *)
(* magnitude [>= 1 - 4u] yields the relative bound [28u^3 + 107u^4].  The       *)
(* [107u^4] slack is exactly what makes [(28u^3-11.9u^4)/(1-4u) <= 28u^3+       *)
(* 107u^4] hold at [u = 1/64] ([p >= 6]).                                      *)
Lemma error_assembly err xy :
  Rabs err <= 28 * (u * u * u) - 119 / 10 * (u * u * u * u) ->
  1 - 4 * u <= Rabs xy ->
  Rabs err <= (28 * (u * u * u) + 107 * (u * u * u * u)) * Rabs xy.
Proof.
move=> Hn Hxy.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := u_le_64.
set B := 28 * (u * u * u) + 107 * (u * u * u * u).
have HB0 : 0 <= B by rewrite /B; nra.
apply: (Rle_trans _ (B * (1 - 4 * u))); last first.
  by apply: Rmult_le_compat_l.
apply: (Rle_trans _ _ _ Hn).
rewrite /B; nra.
Qed.

(* ---- degenerate inputs (a zero factor) -----------------------------------*)

Lemma negTW_id t : negTW (negTW t) = t.
Proof. by case: t => t0 t1 t2 /=; rewrite !Ropp_involutive. Qed.

(* A [twR] with a zero leading limb is the zero triple word.                   *)
Lemma isTW_zero_lead t : isTW t -> tw0 t = 0 -> t = TWR 0 0 0.
Proof.
case: t => t0 t1 t2 [_ _ _ H1 H2] /= t0z.
move: H1 H2; rewrite {}t0z => H1 H2.
have Ht1 : t1 = 0.
  case: H1 => // H1; move: H1; rewrite ulp_FLX_0 => H1; split_Rabs; lra.
have Ht2 : t2 = 0.
  move: H2; rewrite Ht1 => H2.
  case: H2 => // H2; move: H2; rewrite ulp_FLX_0 => H2; split_Rabs; lra.
by rewrite Ht1 Ht2.
Qed.

Lemma isTW_TWR000 : isTW (TWR 0 0 0).
Proof. by split; try exact: generic_format_0; left. Qed.

Lemma TwoSum00 : TwoSum 0 0 = DWR 0 0.
Proof.
rewrite /TwoSum Rplus_0_r round_0.
by do 8! (rewrite ?Rminus_0_l ?Rminus_0_r ?round_0 ?Ropp_0 ?Rplus_0_r ?Rplus_0_l).
Qed.

Lemma TwoProd00l a : TwoProd 0 a = (0, 0).
Proof.
by rewrite /TwoProd Rmult_0_l round_0 Rminus_0_r round_0.
Qed.

Lemma TwoProd00r a : TwoProd a 0 = (0, 0).
Proof.
by rewrite /TwoProd Rmult_0_r round_0 Rminus_0_r round_0.
Qed.

(* [VecSum] and [VSEB] of an all-zero list are all-zero.                       *)
Lemma vecSumAux_zeros n : vecSumAux (nseq n 0) = (nseq n.-1 0, 0).
Proof.
elim: n => [|[|n] IH] //.
rewrite [nseq n.+2 0]/= vecSumAux_cons -[0 :: nseq n 0]/(nseq n.+1 0) IH.
by rewrite TwoSum00.
Qed.

Lemma vsebAux_zeros n : vsebAux 0 (nseq n.+1 0) = [:: 0; 0].
Proof.
elim: n => [|n IH]; first by rewrite vsebAux_1 TwoSum00.
rewrite [nseq n.+2 0]/= vsebAux_consS TwoSum00.
by case: (Req_EM_T 0 0) => // _; rewrite -[0 :: nseq n 0]/(nseq n.+1 0) IH.
Qed.

(* [ThreeProd] of the zero triple word is zero (either argument).              *)
Lemma ThreeProd_0l y : ThreeProd (TWR 0 0 0) y = TWR 0 0 0.
Proof.
case: y => y0 y1 y2.
rewrite /ThreeProd !TwoProd00l /=.
rewrite !Rmult_0_l !Rplus_0_r !round_0.
do 40! (rewrite ?round_0 ?Rplus_0_r ?Rplus_0_l ?Rminus_0_r ?Rminus_0_l ?Ropp_0).
rewrite /vsebK /vseb.
have -> : [:: 0; 0; 0] = nseq 2.+1 0 by [].
by rewrite vsebAux_zeros.
Qed.

Lemma ThreeProd_0r x : ThreeProd x (TWR 0 0 0) = TWR 0 0 0.
Proof.
case: x => x0 x1 x2.
rewrite /ThreeProd !TwoProd00r /=.
rewrite !Rmult_0_r !Rplus_0_l !round_0.
do 40! (rewrite ?round_0 ?Rplus_0_r ?Rplus_0_l ?Rminus_0_r ?Rminus_0_l ?Ropp_0).
rewrite /vsebK /vseb.
have -> : [:: 0; 0; 0] = nseq 2.+1 0 by [].
by rewrite vsebAux_zeros.
Qed.

(* ===========================================================================*)
(*  Theorem 7, part 1: [ThreeProd x y] is a triple-word number (p >= 6).      *)
(*                                                                            *)
(*  The general statement reduces to the normalised one [ThreeProd_isTW_norm]  *)
(*  (paper WLOG [1 <= x0, y0 < 2]) using scale-invariance [ThreeProd_scale] /  *)
(*  [isTW_scale] and sign-invariance [ThreeProd_opp]/[_opp_r] / [isTW_opp];    *)
(*  a zero factor is the degenerate [ThreeProd_0l]/[_0r] case.                 *)
(* ===========================================================================*)
Lemma ThreeProd_isTW x y :
  ties_to_even choice ->
  isTW x -> isTW y -> isTW (ThreeProd x y).
Proof.
move=> Hc Hx Hy.
case: (Req_dec (tw0 x) 0) => [x0z | x0n].
  by rewrite (isTW_zero_lead Hx x0z) ThreeProd_0l; exact: isTW_TWR000.
case: (Req_dec (tw0 y) 0) => [y0z | y0n].
  by rewrite (isTW_zero_lead Hy y0z) ThreeProd_0r; exact: isTW_TWR000.
have [cx _ [Hxp Hxn]] := isTW_normalize Hx x0n.
have [cy _ [Hyp Hyn]] := isTW_normalize Hy y0n.
have Hxsg : 0 < tw0 x \/ tw0 x < 0 by lra.
have Hysg : 0 < tw0 y \/ tw0 y < 0 by lra.
case: Hxsg => Hxs; case: Hysg => Hys.
- rewrite -(isTW_scale (cx + cy)) -ThreeProd_scale.
  by apply: ThreeProd_isTW_norm => //; [apply: Hxp | apply: Hyp].
- rewrite -(isTW_opp (ThreeProd x y)) -(isTW_scale (cx + cy)).
  rewrite -ThreeProd_opp_r -ThreeProd_scale.
  by apply: ThreeProd_isTW_norm => //; [apply: Hxp | apply: Hyn].
- rewrite -(isTW_opp (ThreeProd x y)) -(isTW_scale (cx + cy)).
  rewrite -ThreeProd_opp -ThreeProd_scale.
  by apply: ThreeProd_isTW_norm => //; [apply: Hxn | apply: Hyp].
- rewrite -(isTW_scale (cx + cy)).
  have <- : ThreeProd (negTW x) (negTW y) = ThreeProd x y.
    by rewrite ThreeProd_opp ThreeProd_opp_r negTW_id.
  rewrite -ThreeProd_scale.
  by apply: ThreeProd_isTW_norm => //; [apply: Hxn | apply: Hyn].
Qed.

(* A relative-error bound is invariant under a common [pow s] scaling.         *)
Lemma error_scale_transfer (s : Z) (r rxy C : R) :
  Rabs (r * pow s - rxy * pow s) <= C * Rabs (rxy * pow s) ->
  Rabs (r - rxy) <= C * Rabs rxy.
Proof.
have ps : 0 < pow s by apply: bpow_gt_0.
rewrite -Rmult_minus_distr_r !Rabs_mult (Rabs_pos_eq (pow s)); last by lra.
rewrite -Rmult_assoc => H.
by apply: (Rmult_le_reg_r (pow s) _ _ ps).
Qed.

(* ===========================================================================*)
(*  Theorem 7, part 2: relative error of [ThreeProd] is [<= 28u^3+107u^4].    *)
(*  Proof plan (paper Section 6.2, part 2; see doc/thm7.md): the six error    *)
(*  sources [eps0..eps5] (the last is the Theorem-3 truncation bound at       *)
(*  k = 3), divided by [x*y >= 1 - 4u].                                       *)
(* ===========================================================================*)
Lemma ThreeProd_error x y :
  ties_to_even choice ->
  isTW x -> isTW y ->
  Rabs (TWval (ThreeProd x y) - TWval x * TWval y) <=
     (28 * (u * u * u) + 107 * (u * u * u * u)) * Rabs (TWval x * TWval y).
Proof.
move=> Hc Hx Hy.
set C := (28 * _ + _).
case: (Req_dec (tw0 x) 0) => [x0z | x0n].
  rewrite (isTW_zero_lead Hx x0z) ThreeProd_0l.
  have -> : TWval (TWR 0 0 0) = 0 by rewrite /TWval; ring.
  by rewrite Rmult_0_l Rminus_0_r Rabs_R0 Rmult_0_r; apply: Rle_refl.
case: (Req_dec (tw0 y) 0) => [y0z | y0n].
  rewrite (isTW_zero_lead Hy y0z) ThreeProd_0r.
  have -> : TWval (TWR 0 0 0) = 0 by rewrite /TWval; ring.
  by rewrite Rmult_0_r Rminus_0_r Rabs_R0 Rmult_0_r; apply: Rle_refl.
have [cx _ [Hxp Hxn]] := isTW_normalize Hx x0n.
have [cy _ [Hyp Hyn]] := isTW_normalize Hy y0n.
have Hxsg : 0 < tw0 x \/ tw0 x < 0 by lra.
have Hysg : 0 < tw0 y \/ tw0 y < 0 by lra.
apply: (@error_scale_transfer (cx + cy)%Z (TWval (ThreeProd x y))
                              (TWval x * TWval y) C).
case: Hxsg => Hxs; case: Hysg => Hys.
- have Hn := ThreeProd_error_norm Hc (Hxp Hxs) (Hyp Hys).
  rewrite ThreeProd_scale !TWval_scale in Hn.
  rewrite (_ : TWval x * pow cx * (TWval y * pow cy) = TWval x * TWval y * pow (cx + cy)) in Hn; last by rewrite bpow_plus; ring.
  exact Hn.
- have Hn := ThreeProd_error_norm Hc (Hxp Hxs) (Hyn Hys).
  rewrite ThreeProd_scale ThreeProd_opp_r !TWval_scale !TWval_opp in Hn.
  move: Hn.
  have E : TWval x * pow cx * (- TWval y * pow cy) = - (TWval x * TWval y * pow (cx + cy)) by rewrite bpow_plus; ring.
  rewrite E.
  have E2 : - TWval (ThreeProd x y) * pow (cx + cy) - - (TWval x * TWval y * pow (cx + cy)) = - (TWval (ThreeProd x y) * pow (cx + cy) - TWval x * TWval y * pow (cx + cy)) by ring.
  by rewrite E2 !Rabs_Ropp.
- have Hn := ThreeProd_error_norm Hc (Hxn Hxs) (Hyp Hys).
  rewrite ThreeProd_scale ThreeProd_opp !TWval_scale !TWval_opp in Hn.
  move: Hn.
  have E : - TWval x * pow cx * (TWval y * pow cy) = - (TWval x * TWval y * pow (cx + cy)) by rewrite bpow_plus; ring.
  rewrite E.
  have E2 : - TWval (ThreeProd x y) * pow (cx + cy) - - (TWval x * TWval y * pow (cx + cy)) = - (TWval (ThreeProd x y) * pow (cx + cy) - TWval x * TWval y * pow (cx + cy)) by ring.
  by rewrite E2 !Rabs_Ropp.
- have Hn := ThreeProd_error_norm Hc (Hxn Hxs) (Hyn Hys).
  have Hxy : ThreeProd (negTW x) (negTW y) = ThreeProd x y.
    by rewrite ThreeProd_opp ThreeProd_opp_r negTW_id.
  rewrite ThreeProd_scale Hxy !TWval_scale !TWval_opp in Hn.
  rewrite (_ : - TWval x * pow cx * (- TWval y * pow cy) = TWval x * TWval y * pow (cx + cy)) in Hn; last by rewrite bpow_plus; ring.
  exact Hn.
Qed.

End SecThreeProd.
