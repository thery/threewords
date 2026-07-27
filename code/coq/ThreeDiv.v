(* ---------------------------------------------------------------------------*)
(* Algorithm 14 (3Div): the QUOTIENT of two triple words, and its two         *)
(* correctness results -- the result is a triple word ([ThreeDiv_isTW]) and   *)
(* the relative error bounds [24u^3 + 1509u^4] (accurate variant,             *)
(* [ThreeDiv_error]) and [39u^3 + 1582u^4] (fast variant,                     *)
(* [ThreeDivFast_error]) -- paper doc/paper3.pdf, Section 10 and Theorem 10   *)
(* (see doc/thm10.md).  Generic over the precision [p] (FLX, no [emin]);      *)
(* needs [p >= 10].                                                           *)
(*                                                                            *)
(* Algorithm 14 is Algorithm 13 with the dividend folded in.  It starts from  *)
(* the SAME Newton double word [b ~ 1/x0] (the five lines of Algorithm 13,    *)
(* here [reciBW]) and then, instead of [b (2 - b x)], computes                *)
(*                                                                            *)
(*     (z b) (2 - b x)     rather than     z (b (2 - b x))                    *)
(*                                                                            *)
(* -- the old paper's Section 9 explains why: the two products [z b] and      *)
(* [2 - b x] are then INDEPENDENT (parallelisable), and the optimisations     *)
(* that the constraint [i0 = 1] allows are worth more on a TW x TW product    *)
(* than on a DW x TW one.                                                     *)
(*                                                                            *)
(*     a    <- RN((1 + 2u)/x0)          )                                     *)
(*     h11  <- RN(a*x0 - (1 + 2u))      )  the five lines of Algorithm 13,    *)
(*     h1   <- RN(-h11 - a*x1)          )  i.e. [reciBW (tw0 x) (tw1 x)]      *)
(*     (b01, b11) <- 2Prod(a, 1 - 2u)   )                                     *)
(*     b12  <- RN(b11 + a*h1)           )                                     *)
(*     b    <- Fast2Sum(b01, b12)       )                                     *)
(*     i    <- 2 - 3Prod_{2,3}(b, x)       (head [1], as in Algorithm 13)     *)
(*     a'   <- 3Prod_{2,3}(b, z)                                              *)
(*     y    <- 3Prod_{3,3}(a', i)                                             *)
(*                                                                            *)
(* The three products are parameters ([ThreeDivAux]): [mul1] and [mul2] are   *)
(* DW x TW (Algorithm 11 accurate, or Algorithm 12 fast) and [mul3] is the    *)
(* TW x TW product with a head-[1] second argument -- Algorithm 20 of the old *)
(* paper, [ThreeProdOneTW] in ThreeProdOne.v.  Whence the paper's constants   *)
(* [24 = 10.5 + 10.5 + 3] and [39 = 18 + 18 + 3].                             *)
(*                                                                            *)
(* STATUS: skeleton.  Definitions are complete and the four results are       *)
(* stated; every proof is [Admitted].  The plan is in doc/thm10.md; almost    *)
(* everything it needs is already proved for Algorithm 13 -- see the STEPS    *)
(* comment before [ThreeDivAux_error].                                        *)
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
Require Import ThreeProd.
Require Import ThreeProdFast.
Require Import ThreeProdDW.
Require Import ThreeProdDWFast.
Require Import ThreeProdOne.
Require Import ThreeReci.
Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SecThreeDiv.

Variable p : Z.
Hypothesis Hp2 : (1 < p)%Z.
(* Algorithm 14 needs [p >= 10], for the same reason as Algorithm 13: it is   *)
(* what forces the leading limb of [3Prod_{2,3}(b, x)] to be exactly [1].     *)
Hypothesis Hp10 : (10 <= p)%Z.

Lemma Hp6 : (6 <= p)%Z. Proof. lia. Qed.

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

Local Notation fexp := (FLX_exp p).
Local Notation format := (generic_format beta fexp).
Local Notation ulp := (ulp beta fexp).
Local Notation isTW := (isTW p).
Local Notation isDW := (isDW p).
Local Notation reciBW := (reciBW p choice).
Local Notation head_one := (head_one p).

(* The three products: Algorithms 11/12 (DW x TW) and Algorithm 20 (TW x TW   *)
(* with a head-[1] second argument).                                          *)
Local Notation ThreeProdDW := (ThreeProdDW p choice).
Local Notation ThreeProdDWFast := (ThreeProdDWFast p choice).
Local Notation ThreeProdOneTW := (ThreeProdOneTW p choice).

(* ===========================================================================*)
(*  Algorithm 14 -- 3Div(z, x)                                                *)
(* ===========================================================================*)

(* [mul1] computes [i = 2 - b x], [mul2] computes [a = b z], [mul3] the final *)
(* [y = a i].  Only [mul1] sees the [head_one] property; only [mul3] needs to *)
(* be sharp on a head-[1] second argument.                                    *)
Definition ThreeDivAux (mul1 mul2 mul3 : twR -> twR -> twR) (z x : twR) : twR :=
  let bw := reciBW (tw0 x) (tw1 x) in
  mul3 (mul2 bw z) (sub2TW (mul1 bw x)).

(* The accurate variant: both DW x TW products are Algorithm 11.              *)
Definition ThreeDiv (z x : twR) : twR :=
  ThreeDivAux ThreeProdDW ThreeProdDW ThreeProdOneTW z x.

(* The fast variant: both DW x TW products are Algorithm 12.                  *)
Definition ThreeDivFast (z x : twR) : twR :=
  ThreeDivAux ThreeProdDWFast ThreeProdDWFast ThreeProdOneTW z x.

(* ===========================================================================*)
(*  Correctness, part 1: the result is a triple word.                         *)
(*                                                                            *)
(*  Exactly Algorithm 13's assembly ([ThreeReciAux_isTW]) with one product    *)
(*  more: [mul1] must return a triple word and satisfy [head_one] (so that    *)
(*  [2 - mul1 b x] is again a triple word, by [sub2TW_isTW]), [mul2] must     *)
(*  return a triple word, and [mul3] must do so on a head-[1] second          *)
(*  argument.  Nothing new is needed: [reciB_isDW] and [reciBW_x_err] are     *)
(*  already proved, and [head_one] holds for Algorithms 11 and 12.            *)
(* ===========================================================================*)
Lemma ThreeDivAux_isTW mul1 mul2 mul3 :
  (forall b y, isDW b -> isTW y -> isTW (mul1 b y)) ->
  (forall b y, isDW b -> isTW y -> isTW (mul2 b y)) ->
  (forall a y, isTW a -> isTW y -> tw0 y = 1 -> isTW (mul3 a y)) ->
  head_one mul1 ->
  forall z x, isTW z -> isTW x -> tw0 x <> 0 ->
    isTW (ThreeDivAux mul1 mul2 mul3 z x).
Proof.
move=> Hmul1 Hmul2 Hmul3 Hhead z x Hz Hx Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := @u_le_1024 p Hp10.
have Fx0 : format (tw0 x) by case: x Hx {Hx0} => x0 x1 x2 [].
have Hx1 : tw1 x = 0 \/ Rabs (tw1 x) < ulp (tw0 x)
  by case: x Hx {Hx0 Fx0} => x0 x1 x2 [].
have HDW : isDW (reciBW (tw0 x) (tw1 x))
  by apply: (@reciB_isDW p Hp2 Hp10 choice choice_sym).
have Herr := @reciBW_x_err p Hp2 Hp10 choice choice_sym x Hx Hx0.
have Herr35 : Rabs (TWval (reciBW (tw0 x) (tw1 x)) * TWval x - 1)
                <= 35 * (u * u).
  have Hu3 : u * u * u <= /1024 * (u * u) by nra.
  by clear -Hu0 Hu1024 Hu3 Herr; nra.
have Hhead1 := Hhead _ _ HDW Hx Herr35.
rewrite /ThreeDivAux.
apply: Hmul3.
- by apply: Hmul2.
- by apply: (@sub2TW_isTW p Hp2); [apply: Hmul1|].
by case: (mul1 _ _) Hhead1 => t0 t1 t2 /= ->; ring.
Qed.

Lemma ThreeDiv_isTW z x :
  ties_to_even choice ->
  isTW z -> isTW x -> tw0 x <> 0 -> isTW (ThreeDiv z x).
Proof.
move=> Hc Hz Hx Hx0.
apply: (@ThreeDivAux_isTW ThreeProdDW ThreeProdDW ThreeProdOneTW) => //.
- by move=> b y Hb Hy; apply: (@ThreeProdDW_isTW p Hp2 Hp6 choice choice_sym).
- by move=> b y Hb Hy; apply: (@ThreeProdDW_isTW p Hp2 Hp6 choice choice_sym).
- by move=> a y Ha Hy Hy0;
     apply: (@ThreeProdOneTW_isTW p Hp2 Hp6 choice choice_sym).
exact: (@ThreeProdDW_head_one p Hp2 Hp10 choice choice_sym).
Qed.

Lemma ThreeDivFast_isTW z x :
  ties_to_even choice ->
  isTW z -> isTW x -> tw0 x <> 0 -> isTW (ThreeDivFast z x).
Proof.
move=> Hc Hz Hx Hx0.
apply: (@ThreeDivAux_isTW ThreeProdDWFast ThreeProdDWFast ThreeProdOneTW) => //.
- by move=> b y Hb Hy;
     apply: (@ThreeProdDWFast_isTW p Hp2 Hp6 choice choice_sym).
- by move=> b y Hb Hy;
     apply: (@ThreeProdDWFast_isTW p Hp2 Hp6 choice choice_sym).
- by move=> a y Ha Hy Hy0;
     apply: (@ThreeProdOneTW_isTW p Hp2 Hp6 choice choice_sym).
exact: (@ThreeProdDWFast_head_one p Hp2 Hp10 choice choice_sym).
Qed.

(* ===========================================================================*)
(*  Correctness, part 2: the relative error (paper Theorem 10).               *)
(*                                                                            *)
(*  Old paper Section 9.  With [d1] the relative error of [i = 2 - 3Prod(b,x)]*)
(*  (relative to [x b]), [d2] that of [a = 3Prod(b, z)] and [d3] that of the  *)
(*  final [y = 3Prod(a, i)]:                                                  *)
(*                                                                            *)
(*    |y - z/x| <= (d1 (1 + 71u^2) + (d2 + d3)(1 + 107u^2) + 1165u^4) |z/x|   *)
(*                                                                            *)
(*  STEPS, and what each one already has:                                     *)
(*                                                                            *)
(*  (1) [b] is a double word and [|b x - 1| <= 34u^2 + 123u^3]:               *)
(*      [reciB_isDW], [reciBW_x_err] -- PROVED (Algorithm 13).                *)
(*  (2) [i] has head [1] and [|i - 1| <= 40u^2]: [head_one] + [sub2TW_isTW],  *)
(*      the [|i - 1|] bound is inside [ThreeReciAux_error] -- PROVED, but it  *)
(*      must be FACTORED OUT of that proof to be reused here (it is the only  *)
(*      piece of Algorithm 13's assembly that is not already a lemma).        *)
(*  (3) the algebraic identity, the analogue of Algorithm 13's Newton split:  *)
(*        y - z/x = (y - a i) + (a - b z) i + z (b (2 - x b) - 1/x)           *)
(*                                     + (b z)(i - (2 - x b))                 *)
(*      whose last term is [-z (b x - 1)^2 / x] by [newton_id]; [newton_sq_le]*)
(*      bounds the square by [1165u^4] -- both PROVED.                        *)
(*  (4) the final arithmetic: [reci_error_assembly] generalised to three      *)
(*      error terms (or a fourth [assembly] lemma of the same shape).         *)
(*  (5) [d3] = [ThreeProdOneTW_error] -- the ONLY genuinely new bound.        *)
(*                                                                            *)
(*  As in Theorem 9, the [u^3] terms are [24 = 10.5 + 10.5 + 3] and           *)
(*  [39 = 18 + 18 + 3]; the [u^4] terms are stated as the paper's here and    *)
(*  will be corrected to whatever the honest accounting gives (Theorem 9's    *)
(*  [1465u^4] became [1830u^4]).  Note the [u^3] term is itself at risk this  *)
(*  time -- see the caveat on [ThreeProdOneTW_error].                         *)
(* ===========================================================================*)
Lemma ThreeDivAux_error mul1 mul2 mul3 d1 d2 d3 :
  ties_to_even choice ->
  (forall b y, isDW b -> isTW y -> isTW (mul1 b y)) ->
  (forall b y, isDW b -> isTW y -> isTW (mul2 b y)) ->
  head_one mul1 ->
  (forall b y, isDW b -> isTW y ->
     Rabs (TWval (mul1 b y) - TWval b * TWval y)
       <= d1 * Rabs (TWval b * TWval y)) ->
  (forall b y, isDW b -> isTW y ->
     Rabs (TWval (mul2 b y) - TWval b * TWval y)
       <= d2 * Rabs (TWval b * TWval y)) ->
  (forall a y, isTW a -> isTW y -> tw0 y = 1 ->
     Rabs (TWval y - 1) <= 40 * (u * u) ->
     Rabs (TWval (mul3 a y) - TWval a * TWval y)
       <= d3 * Rabs (TWval a * TWval y)) ->
  0 <= d1 -> d1 <= u * u -> 0 <= d2 -> d2 <= u * u ->
  0 <= d3 -> d3 <= u * u ->
  forall z x, isTW z -> isTW x -> tw0 x <> 0 ->
    Rabs (TWval (ThreeDivAux mul1 mul2 mul3 z x) - TWval z / TWval x)
      <= (d1 * (1 + 71 * (u * u)) + (d2 + d3) * (1 + 107 * (u * u))
          + 1165 * (u * u * u * u)) * Rabs (TWval z / TWval x).
Proof.
Admitted.

(* Theorem 10, accurate variant: [24u^3 + 1509u^4].                           *)
Lemma ThreeDiv_error z x :
  ties_to_even choice ->
  isTW z -> isTW x -> tw0 x <> 0 ->
  Rabs (TWval (ThreeDiv z x) - TWval z / TWval x) <=
     (24 * (u * u * u) + 1509 * (u * u * u * u)) *
       Rabs (TWval z / TWval x).
Proof.
Admitted.

(* Theorem 10, fast variant: [39u^3 + 1582u^4].                               *)
Lemma ThreeDivFast_error z x :
  ties_to_even choice ->
  isTW z -> isTW x -> tw0 x <> 0 ->
  Rabs (TWval (ThreeDivFast z x) - TWval z / TWval x) <=
     (39 * (u * u * u) + 1582 * (u * u * u * u)) *
       Rabs (TWval z / TWval x).
Proof.
Admitted.

End SecThreeDiv.
