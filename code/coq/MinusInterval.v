(* ---------------------------------------------------------------------------*)
(* Exact subtraction on an interval: if [b - a] is exact and [c] lies between *)
(* [a] and [b], then [c - a] is exact too ([exact_minus_interval]).  A general*)
(* FLT fact, generic over the precision [p] and minimal exponent [emin], and  *)
(* independent of the rounding [choice]; built on the [uls] ("weight of the   *)
(* rightmost nonzero bit") machinery of [Uls.v], whose maximality property    *)
(* ([is_imul_uls_ge]) is what drives the proof.                               *)
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

Section MinusInterval.

(* Generic over the precision [p] and minimal exponent [emin] (binary64 is    *)
(* fixed only in [addition.v]), so these lemmas hold at any FLT format.       *)
Variable p : Z.
Variable emin : Z.
Context { prec_gt_0 : Prec_gt_0 p }.

Local Notation beta := radix2.
Local Notation pow e := (bpow beta e).

Open Scope R_scope.

Local Notation fexp := (FLT_exp emin p).
Local Notation format := (generic_format beta fexp).
Local Notation cexp := (cexp beta fexp).
Local Notation mant := (scaled_mantissa beta fexp).
Local Notation ulp := (ulp beta fexp).
Local Notation uls := (uls p emin).

(* ===========================================================================*)
(*  Representability toolbox                                                  *)
(* ===========================================================================*)

(* Converse of [format_imul_cexp]: a real lying on a grid at least as coarse  *)
(* as its own canonical exponent is a float.  In the vocabulary of the proof  *)
(* below, "[x] is representable with exponent [e]" implies "[x] is in the     *)
(* format".  (Not to be confused with [prelim.imul_format], which concludes   *)
(* the same from a bound on [|x|] rather than from [cexp].)                   *)
Lemma imul_cexp_format x e : is_imul x (pow e) -> (cexp x <= e)%Z -> format x.
Proof.
move=> [k Hk] Hce.
rewrite Hk in Hce *.
apply: generic_format_F2R => _.
exact: Hce.
Qed.

(* [cexp] is monotone on the nonnegatives ([mag] is, and [FLT_exp] is).       *)
Lemma cexp_le_pos x y : 0 < x -> x <= y -> (cexp x <= cexp y)%Z.
Proof.
move=> x_gt0 xLy.
apply: FLT_exp_monotone.
apply: mag_le_abs; first by lra.
by rewrite !Rabs_pos_eq; lra.
Qed.

(* The exponent of the rightmost nonzero bit, as a plain power of two: the    *)
(* "maximal exponent" [e_a] of the informal proof.                            *)
Lemma uls_pow x : x <> 0 -> exists e, uls x = pow e.
Proof.
move=> xn0.
exists (cexp x + Z.of_nat (trZ (Ztrunc (mant x))))%Z.
by rewrite /uls; case: Req_bool_spec.
Qed.

(* Maximality of [uls]: a nonzero float is not on the grid one step COARSER   *)
(* than its rightmost nonzero bit.  (Converse of [uls_imul], via              *)
(* [is_imul_uls_ge].)                                                         *)
Lemma not_imul_uls_succ x e : format x -> x <> 0 -> uls x = pow e ->
  ~ is_imul x (pow (e + 1)).
Proof.
move=> Fx xn0 Hu Hc.
have := is_imul_uls_ge Fx xn0 Hc.
rewrite Hu => /le_bpow; lia.
Qed.

(* A float that is NOT on the [2^(e+1)] grid is representable with exponent   *)
(* [e], i.e. its canonical exponent is at most [e].  (Otherwise               *)
(* [format_imul_cexp] would put it back on the [2^(e+1)] grid.)  This is the  *)
(* step that makes the maximality of [e_a] usable below.                      *)
Lemma format_not_imul_cexp_le x e :
  format x -> ~ is_imul x (pow (e + 1)) -> (cexp x <= e)%Z.
Proof.
move=> Fx Hn.
case: (Z_le_gt_dec (cexp x) e) => // Hgt.
case: Hn.
apply: is_imul_pow_le (format_imul_cexp Fx) _.
lia.
Qed.

(* ===========================================================================*)
(*  Exact subtraction on an interval                                          *)
(* ===========================================================================*)

(* If [b - a] is exact and [a <= c <= b], then [c - a] is exact.              *)
(*                                                                            *)
(* Proof (two cases, on whether [a] is expressible with [c]'s canonical       *)
(* exponent [e_c]; note [e_c <= e_b] as [cexp] is monotone).                  *)
(*  - If [a] is: then so is [c], hence so is [c - a]; and [0 < c - a <= c]    *)
(*    gives [cexp (c - a) <= e_c], so [c - a] is representable with that      *)
(*    exponent, i.e. in the format.                                           *)
(*  - Otherwise let [e_a] be [a]'s maximal exponent ([uls a = 2^e_a]).  Then  *)
(*    [e_a < e_c <= e_b], so [b] and [c] are both multiples of [2^(e_a+1)],   *)
(*    whence [b - a] and [c - a] are expressible with exponent [e_a].  By     *)
(*    maximality of [e_a], [b - a] is NOT a multiple of [2^(e_a+1)], so being *)
(*    a float it is representable with exponent [e_a] ([cexp (b-a) <= e_a]).  *)
(*    As [0 < c - a <= b - a], also [cexp (c - a) <= e_a], and [c - a] is a   *)
(*    multiple of [2^e_a]: it is in the format.                               *)
Lemma exact_minus_interval a b c :
  format a -> format b -> format c -> format (b - a) ->
  0 <= a -> a <= b -> a <= c -> c <= b -> format (c - a).
Proof.
move=> Fa Fb Fc Fba a_ge0 aLb aLc cLb.
(* Degenerate cases: [c = a] gives [0], and [a = 0] gives [c] itself.         *)
have [ca0|ca_n0] := Req_dec (c - a) 0.
  by rewrite ca0; exact: generic_format_0.
have ca_gt0 : 0 < c - a by lra.
have [a0|a_n0] := Req_dec a 0.
  by rewrite a0 Rminus_0_r.
have a_gt0 : 0 < a by lra.
have c_gt0 : 0 < c by lra.
(* [ea]: the maximal exponent of [a], i.e. [uls a = 2^ea].                    *)
have [ea Hulsa] := uls_pow a_n0.
have Hia : is_imul a (pow ea) by rewrite -Hulsa; exact: uls_imul.
have [Hcase|Hcase] := Z_le_gt_dec (cexp c) ea.
  (* Case A: [a] is expressible with [c]'s canonical exponent, hence so is    *)
  (* [c - a]; and [0 < c - a <= c] makes that exponent large enough.          *)
  have Hia' : is_imul a (pow (cexp c)) by apply: is_imul_pow_le Hia _.
  have Hic : is_imul c (pow (cexp c)) by exact: format_imul_cexp.
  apply: imul_cexp_format (is_imul_minus Hic Hia') _.
  by apply: cexp_le_pos => //; lra.
(* Case B: [ea < cexp c <= cexp b], so [b] is a multiple of [2^(ea+1)] while  *)
(* [a] is not (maximality of [ea]); hence neither is [b - a], which being a   *)
(* float is then representable with exponent [ea].                            *)
have Hcb : (cexp c <= cexp b)%Z by apply: cexp_le_pos => //; lra.
have Hib : is_imul b (pow (ea + 1)).
  by apply: is_imul_pow_le (format_imul_cexp Fb) _; lia.
have Hna : ~ is_imul a (pow (ea + 1)) by apply: not_imul_uls_succ.
have Hnd : ~ is_imul (b - a) (pow (ea + 1)).
  move=> Hd; apply: Hna.
  have -> : a = b - (b - a) by lra.
  by apply: is_imul_minus.
have Hcd : (cexp (b - a) <= ea)%Z by apply: format_not_imul_cexp_le.
(* [c - a] is a multiple of [2^ea], and [0 < c - a <= b - a] transfers the    *)
(* exponent bound from [b - a].                                               *)
have Hic : is_imul c (pow ea).
  by apply: is_imul_pow_le (format_imul_cexp Fc) _; lia.
apply: imul_cexp_format (is_imul_minus Hic Hia) _.
apply: Z.le_trans Hcd.
by apply: cexp_le_pos => //; lra.
Qed.

End MinusInterval.
