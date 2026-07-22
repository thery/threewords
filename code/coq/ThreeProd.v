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
Local Notation vecSum := (vecSum p choice).
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
