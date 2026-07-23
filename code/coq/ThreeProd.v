(* ---------------------------------------------------------------------------*)
(* Algorithm 9 (3Prod^acc_{3,3}): the product of two triple-word numbers,     *)
(* and its two correctness results -- the result is a triple word             *)
(* ([ThreeProd_isTW]) and the relative error bound [28u^3 + 107u^4]           *)
(* ([ThreeProd_error]) -- paper Theorem 7 (doc/paper3.pdf, Section 6; see     *)
(* doc/thm7.md).  This starts the multiplication half of the paper.  Generic  *)
(* over the precision [p] (FLX, no [emin]); needs [p >= 6].                   *)
(*                                                                            *)
(* STATUS: skeleton.  The definition transcribes Algorithm 9 verbatim on top  *)
(* of [TwoProd] (Alg 3), [vecSum] (Alg 4) and [vsebK] (Alg 5); the two        *)
(* theorems are stated and [Admitted], to be discharged following            *)
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

(* ===========================================================================*)
(*  Section 6.1 -- product-term bounds.  Each is a lemma over the two          *)
(*  normalisation contexts [tw_norm x0 x1 x2] / [tw_norm y0 y1 y2].            *)
(* ===========================================================================*)

(* The leading product [z00p = RN(x0 y0)] lies in [1, 4).                     *)
Lemma z00p_lb x0 x1 x2 y0 y1 y2 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 -> 1 <= RND (x0 * y0).
Proof.
Admitted.

Lemma z00p_ub x0 x1 x2 y0 y1 y2 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 -> RND (x0 * y0) < 4.
Proof.
Admitted.

(* ===========================================================================*)
(*  Theorem 7, part 1: [ThreeProd x y] is a triple-word number (p >= 6).      *)
(*  Proof plan (paper Section 6.2, part 1; see doc/thm7.md): the equivalence  *)
(*  with [VSEB(3)(e0..e4)], then F-nonoverlapping of                          *)
(*  [vecSum(z00p, b0, b1, s3)] plus the [e4] divisibility, and finally        *)
(*  Theorem 2 / Theorem 6.                                                    *)
(* ===========================================================================*)
Lemma ThreeProd_isTW x y :
  ties_to_even choice ->
  isTW x -> isTW y -> isTW (ThreeProd x y).
Proof.
Admitted.

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
Admitted.

End SecThreeProd.
