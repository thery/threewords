(* ---------------------------------------------------------------------------*)
(* Algorithm 15 (3SqRt): the SQUARE ROOT of a triple word, and its two        *)
(* correctness results -- the result is a triple word ([ThreeSqRt_isTW]) and  *)
(* the relative error bounds [24u^3 + 10260u^4] (accurate variant,            *)
(* [ThreeSqRt_error]) and [39u^3 + 10333u^4] (fast variant,                   *)
(* [ThreeSqRtFast_error]) -- paper doc/paper3.pdf, Section 10 and Theorem 11  *)
(* (see doc/thm11.md).  Generic over the precision [p] (FLX, no [emin]);      *)
(* needs [p >= 11].                                                           *)
(*                                                                            *)
(* The proof follows the SUPPLEMENTARY MATERIAL, Section 3 of                 *)
(* doc/Algorithms_for_Triple-Word_Arithmetic.pdf -- the appendix paper3.pdf   *)
(* defers to.  (The long version doc/old-triplewors.pdf is of no help here:   *)
(* it stops at Section 9, the quotient, and its own roadmap reads [Section 10 *)
(* [???]], a placeholder never filled in.)  The underlying iteration is       *)
(* [r <- r (3/2 - (1/2) r^2 x)], quadratically convergent to [1/sqrt x].      *)
(*                                                                            *)
(*     a    <- RN((1 + 4u)/RN(sqrt x0))  )                                    *)
(*     a'   =  a/2                (exact) )                                   *)
(*     (h0(1), h11(1)) <- 2Prod(a, x0)   )                                    *)
(*     h1(1)  <- RN(h11(1) + a*x1)       )  the nine head lines, i.e.         *)
(*     (h01(2), h11(2)) <- 2Prod(a', h0(1))  [sqrtBW (tw0 x) (tw1 x)],        *)
(*     h0(2)  <- 3/2 - h01(2)     (exact) )  a double word [b ~ 1/sqrt x0]    *)
(*     h1(2)  <- -RN(h11(2) + a'*h1(1))  )                                    *)
(*     (b01, b11) <- 2Prod(a, h0(2))     )                                    *)
(*     b12  <- RN(b11 + a*h1(2))         )                                    *)
(*     b    <- Fast2Sum(b01, b12)        )                                    *)
(*     b'   =  b/2                (exact)                                     *)
(*     i(1) <- 3Prod_{2,3}(b, x)            (~ sqrt x)                        *)
(*     i(2) <- 3/2 - 3Prod_{2,3}(b', i(1))  (head [1], as in Algorithm 13)    *)
(*     y    <- 3Prod_{3,3}(i(1), i(2))                                        *)
(*                                                                            *)
(* Three structural differences from Algorithms 13 and 14: the seed [a]       *)
(* involves a real square root (nothing else in this development computes     *)
(* with [sqrt]); [2 - .] becomes [3/2 - .] ([sub32TW]), and the two halvings  *)
(* [a' = a/2], [b' = b/2] are exact scalings by [pow (-1)]; the last product  *)
(* is again the TW x TW one with a head-[1] SECOND argument, Algorithm 20     *)
(* ([ThreeProdOneTW] in ThreeProdOne.v).                                      *)
(*                                                                            *)
(* WHY THE PUBLISHED [24u^3] IS STILL REACHABLE FOR US, unlike Theorem 10's.  *)
(* The supplementary's global bound, with [d1], [d2], [d3] the three          *)
(* products' relative errors, is                                              *)
(*                                                                            *)
(*     |y - sqrt x| <= (d1 (1.5 + 287u^2) + d2 (0.5 + 123u^2)                 *)
(*                     + d3 (1 + 162u^2) + 9916u^4) sqrt x                    *)
(*                                                                            *)
(* whence [24 = 1.5(10.5) + 0.5(10.5) + 3] and [39 = 1.5(18) + 0.5(18) + 3].  *)
(* With OUR [d3 = 6u^3] instead of the announced [3u^3] (Algorithm 20's       *)
(* [delta3] is still loose -- see doc/thm10.md) that route gives [27u^3] and  *)
(* [42u^3], exactly as it does for Theorem 10.                                *)
(*                                                                            *)
(* BUT the weight [1.5] on [d1] is itself loose, and provably so.  Expanding  *)
(* to first order -- [i(1)] occurs TWICE, once as a factor of [y] and once    *)
(* inside [i(2)], with OPPOSITE signs -- gives                                *)
(*                                                                            *)
(*     y/sqrt x - 1  ~  d1/2 - d2/2 + d3                                      *)
(*                                                                            *)
(* (the seed error [e] cancels too: Newton is self-correcting).  So the true  *)
(* weight on [d1] is [1/2], not [3/2]: the supplementary reaches [1.5] by     *)
(* bounding [|d1 - (d1 + d2)/2|] with the triangle inequality, discarding the *)
(* cancellation.  Exploiting it gives [18.5u^3] and [26u^3].                  *)
(*                                                                            *)
(* AND THAT SLACK IS WHAT SAVES THE [u^4] TERM.  Our [d3] is also worse at    *)
(* [u^4] -- [1250] against the announced [263] -- and that excess lands       *)
(* undiluted (weight [1]), so the honest totals are [16.5u^3 + 11205u^4] and  *)
(* [24u^3 + 11241u^4] against the published [24u^3 + 10260u^4] and            *)
(* [39u^3 + 10333u^4].  Neither pair is termwise smaller.  But                *)
(*                                                                            *)
(*     945u^4 <= 7.5u^3   <=>   u <= 1/126                                    *)
(*                                                                            *)
(* and [u <= 2^-11], so the [u^3] slack absorbs the [u^4] excess with a wide  *)
(* margin; likewise [908u^4 <= 15u^3] for the fast variant.  So THEOREM 11    *)
(* HOLDS FOR US EXACTLY AS PUBLISHED -- the                                   *)
(* first of Theorems 9-11 for which that is true, and the reason to state it  *)
(* below with the paper's own constants rather than corrected ones.  It costs *)
(* nothing extra: the [delta3] tightening of doc/thm10.md would improve       *)
(* Theorems 9 and 10, not this one.                                           *)
(*                                                                            *)
(* STATUS.  The [isTW] HALF IS COMPLETE: [ThreeSqRt_isTW] and                 *)
(* [ThreeSqRtFast_isTW] are [Qed] on top of [ThreeSqRtAux_isTW], via          *)
(* [head_half] (obligation 5), [sub32TW_isTW], [isTW_TWval_gt0] and the       *)
(* tolerance-parametric [head_one_gen_c] added to ThreeReci.v.                *)
(*                                                                            *)
(* Eight admits remain, ALL in the error half: the seed [sqrtA_bound], the    *)
(* exactness [sqrtH0_2_exact], [sqrtB_isDW], [sqrtBW_x_err],                  *)
(* [sqrt_newton_residual], the assembly [ThreeSqRtAux_error] and its two      *)
(* instantiations.  Order of attack in doc/thm11.md Section 5.  Note the      *)
(* [isTW] half already CONSUMES [sqrtB_isDW] and [sqrtBW_x_err], so those     *)
(* two are shared and worth doing next.                                       *)
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

Section SecThreeSqRt.

Variable p : Z.
Hypothesis Hp2 : (1 < p)%Z.
(* Algorithm 15 asks for [p >= 11], one more than Algorithms 13 and 14.  Per  *)
(* the supplementary the extra bit is needed by the MODIFIED product used for *)
(* [i(2)] -- the variant whose penultimate line is [e1 <- Fast2Sum(.5)(...)]  *)
(* -- not by the exactness of [h0(2)], which follows from [h01(2) >= 1/2]     *)
(* alone.  See doc/thm11.md Section 4.                                        *)
Hypothesis Hp11 : (11 <= p)%Z.

Lemma Hp10 : (10 <= p)%Z. Proof. lia. Qed.
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
Local Notation RND := (round beta fexp rnd).
Local Notation TwoProd := (TwoProd p radix2 rnd).
Local Notation Fast2Sum := (Fast2Sum p choice).
Local Notation isTW := (isTW p).
Local Notation isDW := (isDW p).
Local Notation head_one := (head_one p).

(* The three products: Algorithms 11/12 (DW x TW) and Algorithm 20 (TW x TW   *)
(* with a head-[1] second argument).                                          *)
Local Notation ThreeProdDW := (ThreeProdDW p choice).
Local Notation ThreeProdDWFast := (ThreeProdDWFast p choice).
Local Notation ThreeProdOneTW := (ThreeProdOneTW p choice).

(* ===========================================================================*)
(*  [3/2 - x] on triple words                                                 *)
(*                                                                            *)
(*  Algorithm 15 subtracts a triple word from [3/2] ([i(2) <- 3/2 - 3Prod]).  *)
(*  Limb by limb this is [(3/2 - x0, -x1, -x2)]: the two low limbs are just   *)
(*  negated, and the head subtraction [3/2 - x0] is EXACT as soon as          *)
(*  [x0 = 1/2], which is what [head_half] below asserts of the product -- the *)
(*  exact analogue of Algorithm 13's [sub2TW] and its [tw0 = 1].              *)
(* ===========================================================================*)
Definition sub32TW (x : twR) : twR :=
  let: TWR x0 x1 x2 := x in TWR (3 / 2 - x0) (- x1) (- x2).

Lemma TWval_sub32TW x : TWval (sub32TW x) = 3 / 2 - TWval x.
Proof. by case: x => x0 x1 x2; rewrite /TWval /=; ring. Qed.

Lemma sub32TW_isTW t : isTW t -> tw0 t = 1 / 2 -> isTW (sub32TW t).
Proof.
case: t => t0 t1 t2 [F0 F1 F2 H1 H2] /= Ht0.
have -> : 3 / 2 - t0 = 1 by rewrite Ht0; field.
split.
- exact: format_1.
- exact: generic_format_opp.
- exact: generic_format_opp.
- case: H1 => [->|H1]; first by left; rewrite Ropp_0.
  right; rewrite Rabs_Ropp.
  (* The head moves from [1/2] up to [1], so the gap WIDENS: [ulp (1/2) = u]  *)
  (* and [ulp 1 = 2u].  Unlike [sub2TW_isTW], where the head is unchanged,    *)
  (* this step really needs monotonicity of [ulp].                            *)
  apply: Rlt_le_trans H1 _.
  by apply: ulp_le; rewrite Ht0 !Rabs_pos_eq; lra.
case: H2 => [->|H2]; first by left; rewrite Ropp_0.
by right; rewrite !Rabs_Ropp ulp_opp.
Qed.

(* ===========================================================================*)
(*  Algorithm 15 -- 3SqRt(x0, x1, x2)                                         *)
(*  (127 operations & 4 tests with Algorithm 11, 111 operations & 2 tests     *)
(*  with Algorithm 12; paper Section 10).                                     *)
(* ===========================================================================*)
(* The nine head lines, named one by one so that the bounds of doc/thm11.md   *)
(* can be stated and reused without unfolding the algorithm.                  *)

(* The seed.  [RN(sqrt x0)] is the only place in the whole development where  *)
(* a real square root is rounded; [1 + 4u] plays the role Algorithm 13's      *)
(* [1 + 2u] plays -- it biases the seed upwards by just enough that the       *)
(* rounding of [h01(2)] cannot go the wrong way.                              *)
Definition sqrtS (x0 : R) : R := RND (sqrt x0).

Definition sqrtA (x0 : R) : R := RND ((1 + 4 * u) / sqrtS x0).

(* [a/2] and [b/2] are exact: multiplying by [pow (-1)] never leaves FLX.     *)
Definition sqrtA' (x0 : R) : R := sqrtA x0 / 2.

Definition sqrtH0_1 (x0 : R) : R := (TwoProd (sqrtA x0) x0).1.

Definition sqrtH11_1 (x0 : R) : R := (TwoProd (sqrtA x0) x0).2.

Definition sqrtH1_1 (x0 x1 : R) : R :=
  RND (sqrtH11_1 x0 + sqrtA x0 * x1).

Definition sqrtH01_2 (x0 : R) : R :=
  (TwoProd (sqrtA' x0) (sqrtH0_1 x0)).1.

Definition sqrtH11_2 (x0 : R) : R :=
  (TwoProd (sqrtA' x0) (sqrtH0_1 x0)).2.

Definition sqrtH0_2 (x0 : R) : R := 3 / 2 - sqrtH01_2 x0.

Definition sqrtH1_2 (x0 x1 : R) : R :=
  - RND (sqrtH11_2 x0 + sqrtA' x0 * sqrtH1_1 x0 x1).

Definition sqrtB01 (x0 : R) : R := (TwoProd (sqrtA x0) (sqrtH0_2 x0)).1.

Definition sqrtB11 (x0 : R) : R := (TwoProd (sqrtA x0) (sqrtH0_2 x0)).2.

Definition sqrtB12 (x0 x1 : R) : R :=
  RND (sqrtB11 x0 + sqrtA x0 * sqrtH1_2 x0 x1).

Definition sqrtB (x0 x1 : R) : dwR :=
  Fast2Sum (sqrtB01 x0) (sqrtB12 x0 x1).

(* The Newton double word [b ~ 1/sqrt x0], packaged as a [twR] with a zero    *)
(* third limb -- the shape Algorithms 11 and 12 take as their first argument. *)
Definition sqrtBW (x0 x1 : R) : twR :=
  TWR (dwh (sqrtB x0 x1)) (dwl (sqrtB x0 x1)) 0.

(* [mul1] computes [i(1) = 3Prod(b, x) ~ sqrt x], [mul2] the inner            *)
(* [3Prod(b', i(1)) ~ 1/2] of [i(2)], and [mul3] the final [y = i(1) i(2)].   *)
(* Only [mul2] sees the head property (its result must have head exactly      *)
(* [1/2], so that [3/2 - .] is exact and [i(2)] has head [1]); only [mul3]    *)
(* needs to be sharp on a head-[1] second argument.                           *)
Definition ThreeSqRtAux (mul1 mul2 mul3 : twR -> twR -> twR) (x : twR)
    : twR :=
  let bw := sqrtBW (tw0 x) (tw1 x) in
  let i1 := mul1 bw x in
  mul3 i1 (sub32TW (mul2 (scaleTW (-1)%Z bw) i1)).

(* The accurate variant: both DW x TW products are Algorithm 11.              *)
Definition ThreeSqRt (x : twR) : twR :=
  ThreeSqRtAux ThreeProdDW ThreeProdDW ThreeProdOneTW x.

(* The fast variant: both DW x TW products are Algorithm 12.                  *)
Definition ThreeSqRtFast (x : twR) : twR :=
  ThreeSqRtAux ThreeProdDWFast ThreeProdDWFast ThreeProdOneTW x.

(* ===========================================================================*)
(*  The Newton identity (PROVED)                                              *)
(*                                                                            *)
(*  Everything downstream rests on this one polynomial identity.  Writing     *)
(*  [x = s * s] and [t = b * s], the EXACT value of the algorithm's last two  *)
(*  lines, [(b x)(3/2 - (1/2) b^2 x)], differs from [s] by                    *)
(*                                                                            *)
(*      - s (t - 1)^2 ((t - 1) + 3) / 2   ~   -(3/2) s (t - 1)^2              *)
(*                                                                            *)
(*  so the seed's relative error [e = b sqrt x - 1] enters the result only    *)
(*  SQUARED.  Since [e = O(u^2)] that is [O(u^4)]: the whole [u^3] budget of  *)
(*  Theorem 11 is made of the three products' rounding errors, none of it of  *)
(*  the Newton residual.  This is the analogue of Algorithm 13's              *)
(*  [newton_id : (a(2 - Xa))X - 1 = -(aX - 1)^2].                             *)
(*                                                                            *)
(*  Stated on [s] and [b] rather than on [x] and [1/sqrt x] on purpose: it is *)
(*  then a polynomial identity, with no division and no [sqrt], and [ring]    *)
(*  closes it.  (House rule: state error chains dimensionlessly.)             *)
(* ===========================================================================*)
Lemma sqrt_newton_id s b :
  (b * (s * s)) * (3 / 2 - (1 / 2) * (b * b) * (s * s)) - s
    = - s * ((b * s - 1) * (b * s - 1)) * ((b * s - 1) + 3) / 2.
Proof. field. Qed.

(* ===========================================================================*)
(*  The six intermediate obligations (doc/thm11.md Section 4)                 *)
(*                                                                            *)
(*  Stated here so that their shape is pinned before anything is proved --    *)
(*  the house top-down method.  Steps 1 and 2 are the genuinely new ones;     *)
(*  steps 3 and 4 mirror [reciB_isDW] and [reciBW_x_err] of Algorithm 13, and *)
(*  step 5 should FALL OUT of the already-proved [head_one] by scaling rather *)
(*  than be re-proved.                                                        *)
(* ===========================================================================*)

(* Step 1.  The seed.  Stated TWO-SIDED and asymmetrically, not as a single   *)
(* [Rabs] bound -- the house lesson, and here it is not a matter of taste:    *)
(* the LOWER bound is the whole point of the [1 + 4u].  Both roundings are    *)
(* within a relative [u], so                                                  *)
(*                                                                            *)
(*   (1 + 4u)(1 - u)/(1 + u)  <=  a sqrt x0  <=  (1 + 4u)(1 + u)/(1 - u)      *)
(*                                                                            *)
(* i.e. [1 + 2u - O(u^2)] to [1 + 6u + O(u^2)].  Since [a sqrt x0 > 1], its   *)
(* SQUARE stays above [1], so [h01(2) ~ (1/2)(a sqrt x0)^2 >= 1/2] -- which   *)
(* is exactly the supplementary's reason for starting at [1 + 4u] rather      *)
(* than [1], and what [sqrtH0_2_exact] then runs on.                          *)
(*                                                                            *)
(* NB an earlier draft of this file stated [|a sqrt x0 - 1| <= 4u + 8u^2].    *)
(* That is FALSE -- random search over binary64 reaches [5.50u], and the      *)
(* algebra above allows [6u].                                                 *)
Lemma sqrtA_bound x0 :
  format x0 -> 0 < x0 ->
  1 + 2 * u - 8 * (u * u) <= sqrtA x0 * sqrt x0
    <= 1 + 6 * u + 12 * (u * u).
Proof.
move=> Fx0 Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := @u_le_1024 p Hp10.
have HR : 0 < sqrt x0 by apply: sqrt_lt_R0.
(* (1) the rounding of the square root, within a relative [u].                *)
have HS : Rabs (sqrtS x0 - sqrt x0) <= u * Rabs (sqrt x0)
  by apply: (@relative_error_le p beta Hp2 choice).
rewrite (Rabs_pos_eq (sqrt x0)) in HS; last lra.
have HSb := Rabs_le_inv _ _ HS.
have HS0 : 0 < sqrtS x0 by nra.
(* (2) the rounding of the quotient, multiplied through by [S] so that no     *)
(* division survives into the arithmetic.                                     *)
have HA : Rabs (sqrtA x0 - (1 + 4 * u) / sqrtS x0)
            <= u * Rabs ((1 + 4 * u) / sqrtS x0)
  by apply: (@relative_error_le p beta Hp2 choice).
have HAS : Rabs (sqrtA x0 * sqrtS x0 - (1 + 4 * u)) <= u * (1 + 4 * u).
  have -> : sqrtA x0 * sqrtS x0 - (1 + 4 * u)
      = (sqrtA x0 - (1 + 4 * u) / sqrtS x0) * sqrtS x0
    by field; lra.
  rewrite Rabs_mult (Rabs_pos_eq (sqrtS x0)); last lra.
  have Hq : Rabs ((1 + 4 * u) / sqrtS x0) = (1 + 4 * u) / sqrtS x0.
    apply: Rabs_pos_eq; rewrite /Rdiv.
    by apply: Rmult_le_pos; [lra | left; apply: Rinv_0_lt_compat; lra].
  rewrite Hq in HA.
  have Hstep : Rabs (sqrtA x0 - (1 + 4 * u) / sqrtS x0) * sqrtS x0
      <= (u * ((1 + 4 * u) / sqrtS x0)) * sqrtS x0
    by apply: Rmult_le_compat_r; lra.
  apply: Rle_trans Hstep _.
  by rewrite /Rdiv; field_simplify; lra.
have HASb := Rabs_le_inv _ _ HAS.
(* (3) [a > 0], so the two magnitudes can be combined.                        *)
have HA0 : 0 < sqrtA x0 by nra.
(* (4) [a S] is pinned, [S] is within [(1 +- u) R], so [a R] is pinned too.   *)
by nra.
Qed.

(* Step 2.  [h0(2) = 3/2 - h01(2)] is EXACT.  This is NOT Sterbenz -- its     *)
(* hypothesis fails outright for [3/2 - 1/2].  The supplementary gives the    *)
(* reason in one line: the computation is exact BECAUSE [h01(2) >= 0.5], and  *)
(* [this is why we started with 1 + 4u instead of 1].  So [h01(2)] sits in    *)
(* the binade [[1/2, 1)], where [ulp = u]; [3/2] is a multiple of [u] there,  *)
(* hence so is the difference, which lands in [(1/2, 1]] -- representable.    *)
(* Pin [h01(2) >= 1/2] first; everything else is grid arithmetic.             *)
(* [h01(2)] lands in [[1/2, 1]].  Unfolding, [a' h0(1) = (1/2) a^2 x0 (1+d)]  *)
(* with [|d| <= u], and [a^2 x0 = (a sqrt x0)^2] is pinned by [sqrtA_bound]   *)
(* to [[1+2u-8u^2, 1+6u+12u^2]] -- so the half-square sits just ABOVE [1/2],  *)
(* which is the whole purpose of the [1 + 4u] seed.                           *)
Lemma sqrtH01_2_range x0 :
  format x0 -> 0 < x0 -> 1 / 2 <= sqrtH01_2 x0 <= 1.
Proof.
move=> Fx0 Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := @u_le_1024 p Hp10.
have HR : 0 < sqrt x0 by apply: sqrt_lt_R0.
have HsX : sqrt x0 * sqrt x0 = x0 by apply: sqrt_sqrt; lra.
have [Hlo Hhi] := sqrtA_bound Fx0 Hx0.
(* [h0(1) = RN(a x0)] is within a relative [u].                               *)
have Hh01 : Rabs (sqrtH0_1 x0 - sqrtA x0 * x0)
              <= u * Rabs (sqrtA x0 * x0)
  by apply: (@relative_error_le p beta Hp2 choice).
have HA0 : 0 < sqrtA x0 by nra.
have HAx : 0 < sqrtA x0 * x0 by nra.
rewrite (Rabs_pos_eq (sqrtA x0 * x0)) in Hh01; last lra.
have Hh01b := Rabs_le_inv _ _ Hh01.
(* [a' h0(1)] is then within [(1/2)(a sqrt x0)^2 (1 +- u)].                   *)
have Hprod : 1 / 2 + u <= sqrtA' x0 * sqrtH0_1 x0 <= 1 / 2 + 7 * u.
  (* [a' (a x0) = (1/2)(a sqrt x0)^2], rewriting [sqrt x0 * sqrt x0] FORWARD  *)
  (* to [x0] -- the reverse direction would rewrite under [sqrt] itself.      *)
  have HPgen : forall r a, r * r = x0 ->
      a / 2 * (a * x0) = / 2 * ((a * r) * (a * r)).
    by move=> r a <-; field.
  have HP : sqrtA' x0 * (sqrtA x0 * x0)
      = / 2 * ((sqrtA x0 * sqrt x0) * (sqrtA x0 * sqrt x0)).
    by rewrite /sqrtA'; apply: HPgen; exact: HsX.
  have HD : sqrtA' x0 * sqrtH0_1 x0
      = sqrtA' x0 * (sqrtA x0 * x0)
        + sqrtA' x0 * (sqrtH0_1 x0 - sqrtA x0 * x0) by ring.
  (* the perturbation is at most [u] times the main term                      *)
  have HA'0 : 0 < sqrtA' x0 by rewrite /sqrtA'; lra.
  have Hpert : Rabs (sqrtA' x0 * (sqrtH0_1 x0 - sqrtA x0 * x0))
      <= u * (sqrtA' x0 * (sqrtA x0 * x0)).
    rewrite Rabs_mult (Rabs_pos_eq (sqrtA' x0)); last lra.
    have Hs : Rabs (sqrtH0_1 x0 - sqrtA x0 * x0) <= u * (sqrtA x0 * x0)
      by lra.
    have Hm : sqrtA' x0 * Rabs (sqrtH0_1 x0 - sqrtA x0 * x0)
        <= sqrtA' x0 * (u * (sqrtA x0 * x0))
      by apply: Rmult_le_compat_l; lra.
    by apply: Rle_trans Hm _; lra.
  have Hpb := Rabs_le_inv _ _ Hpert.
  set T := sqrtA x0 * sqrt x0 in HP Hlo Hhi.
  (* square the seed range BEFORE handing it to [nra] -- the squared form is  *)
  (* what the goal needs and [nra] will not find it under the perturbation.   *)
  have HT0 : 0 < T by nra.
  have HT2a : (1 + 2 * u - 8 * (u * u)) * (1 + 2 * u - 8 * (u * u)) <= T * T
    by apply: Rmult_le_compat; nra.
  have HT2b : T * T <= (1 + 6 * u + 12 * (u * u)) * (1 + 6 * u + 12 * (u * u))
    by apply: Rmult_le_compat; nra.
  rewrite HP in Hpb.
  rewrite HD HP.
  have Hu2 : u * u <= / 1024 * u by nra.
  by nra.
(* rounding cannot leave [[1/2, 1]].                                          *)
have Hround := @relative_error_le p beta Hp2 choice (sqrtA' x0 * sqrtH0_1 x0).
rewrite (Rabs_pos_eq (sqrtA' x0 * sqrtH0_1 x0)) in Hround; last lra.
have Hrb := Rabs_le_inv _ _ Hround.
by rewrite /sqrtH01_2 /=; nra.
Qed.

(* [3/2] is on the [u]-grid, being [3 * 2^(p-1)] units of [u].                *)
Lemma is_imul_3_2 : is_imul (3 / 2) (pow (- p)).
Proof.
exists (3 * 2 ^ (p - 1))%Z.
rewrite mult_IZR.
have -> : IZR (2 ^ (p - 1)) = pow (p - 1).
  by rewrite -(IZR_Zpower radix2); [congr IZR|lia].
rewrite Rmult_assoc -bpow_plus.
have -> : (p - 1 + - p = -1)%Z by lia.
by have -> : pow (-1) = / 2 by []; lra.
Qed.

(* [h0(2) = 3/2 - h01(2)] is EXACT.  NOT Sterbenz -- its hypothesis fails     *)
(* outright for [3/2 - 1/2].  Both operands are multiples of [u]              *)
(* ([is_imul_bound_pow_format] on [h01(2) >= 1/2], and [is_imul_3_2]), and    *)
(* the difference lies in [[1/2, 1]], so [imul_format] applies.               *)
Lemma sqrtH0_2_exact x0 :
  format x0 -> 0 < x0 -> format (sqrtH0_2 x0).
Proof.
move=> Fx0 Hx0.
have [Hlo Hhi] := sqrtH01_2_range Fx0 Hx0.
have Fh : format (sqrtH01_2 x0) by apply: generic_format_round.
have Him1 : is_imul (sqrtH01_2 x0) (pow (- p)).
  have -> : (- p = -1 - p + 1)%Z by lia.
  apply: is_imul_bound_pow_format => //.
  have -> : pow (-1) = / 2 by [].
  by rewrite Rabs_pos_eq; lra.
(* REMAINS: the [imul_format] invocation.  Everything it consumes is proved   *)
(* just above -- [Him1] (h01(2) is a multiple of [u], from                    *)
(* [is_imul_bound_pow_format] and [h01(2) >= 1/2]), [is_imul_3_2], and the    *)
(* range [[1/2, 1]] -- and [is_imul_minus] closes the difference.  What is    *)
(* left is purely finding [imul_format]'s argument prefix: it lives in        *)
(* prelim.v, whose section is generic in [fexp], so the [FLX_exp p]           *)
(* instantiation has to be supplied.  See the GOTCHA on cross-file prefixes.  *)
Admitted.

(* Step 3.  [b] is a double word.  Mirrors [reciB_isDW].  CHECK the Fast2Sum  *)
(* ordering [|b01| >= |b12|] rather than assuming it: an unguarded Fast2Sum   *)
(* whose ordering fails loses [u max(|.|)], not [O(u^2)] -- that is exactly   *)
(* the Algorithm 18 defect recorded in doc/thm9.md.  If the ordering cannot   *)
(* be proved, switch [sqrtB] to [Fast2SumS], which costs no extra flop.       *)
Lemma sqrtB_isDW x0 x1 :
  format x0 -> format x1 -> 0 < x0 -> isDW (sqrtBW x0 x1).
Proof.
Admitted.

(* Step 4.  The seed double word against the true inverse square root, in the *)
(* dimensionless form the assembly consumes.  The supplementary states it as  *)
(* [|b - 1/sqrt x| <= (81u^2 + 622u^3)|1/sqrt x|]; Algorithm 13's analogue is *)
(* [reciBW_x_err], with [34u^2 + 126u^3].  The seed is more than twice as     *)
(* sloppy, which is where Theorem 11's large [u^4] term comes from.           *)
Lemma sqrtBW_x_err x :
  isTW x -> 0 < tw0 x ->
  Rabs (TWval (sqrtBW (tw0 x) (tw1 x)) * sqrt (TWval x) - 1)
    <= 81 * (u * u) + 622 * (u * u * u).
Proof.
Admitted.

(* Step 4b.  The Newton residual: the EXACT value of the last two lines is    *)
(* already within [O(u^4)] of [sqrt x], by [sqrt_newton_id] applied to        *)
(* step 4.  The supplementary's constant.  This is the only [u^4] contributor *)
(* that is not a product's error.                                             *)
Lemma sqrt_newton_residual x :
  isTW x -> 0 < tw0 x ->
  let b := TWval (sqrtBW (tw0 x) (tw1 x)) in
  Rabs (b * TWval x * (3 / 2 - (1 / 2) * (b * b) * TWval x) - sqrt (TWval x))
    <= 9916 * (u * u * u * u) * Rabs (sqrt (TWval x)).
Proof.
Admitted.

(* Step 5.  The head property [mul2] must satisfy: on a first argument that   *)
(* is [b/2] the product has head exactly [1/2], so that [3/2 - .] is exact    *)
(* and [i(2)] has head [1] -- which is what [ThreeProdOneTW] requires of its  *)
(* second argument.  The analogue of [head_one] in ThreeReci.v.               *)
(* Stated on the UNSCALED [b], with the halving inside, because that is how   *)
(* the assembly uses it: [mul2] is applied to [scaleTW (-1) bw], and the      *)
(* hypothesis available there is Algorithm 13's [|b x - 1| <= 35u^2] -- the   *)
(* very hypothesis of [head_one].                                             *)
(* The tolerance is [200u^2], not Algorithm 13's [35u^2].  Algorithm 15       *)
(* needs the slack: at the call site the second factor is [i(1) =             *)
(* 3Prod(b, x)], so the product is [b^2 x = (b sqrt x)^2 = (1 + e)^2] with    *)
(* [|e| <= 81u^2 + 622u^3], giving [|b i(1) - 1| <= 162u^2 + O(u^3)].         *)
(* Algorithm 13 never meets this because there the second factor is [x]       *)
(* itself, so the product carries ONE power of the seed error, not two.       *)
Definition head_half (mul : twR -> twR -> twR) : Prop :=
  forall b y, isDW b -> isTW y ->
    Rabs (TWval b * TWval y - 1) <= 200 * (u * u) ->
    tw0 (mul (scaleTW (-1)%Z b) y) = 1 / 2.

(* And it is NOT re-proved from scratch: the products commute with scaling,   *)
(* so halving the first argument halves the head, and [head_one] -- already   *)
(* proved for Algorithms 11 and 12 -- does all the work.  Generic in the      *)
(* multiplier, so both variants are one line.                                 *)
(*                                                                            *)
(* The threshold is why ThreeReci.v now carries [head_eq_1_c] and             *)
(* [head_one_gen_c], the tolerance-parametric forms.  Algorithm 13's [35u^2]  *)
(* is TOO TIGHT here: at the call site the second factor is                   *)
(* [i(1) = 3Prod(b, x)], so the product is [b^2 x = (b sqrt x)^2 = (1 + e)^2] *)
(* with [|e| <= 81u^2 + 622u^3], hence [|b i(1) - 1| <= 162u^2 + O(u^3)].     *)
(* Algorithm 13 never meets this: there the second factor is [x] itself, so   *)
(* the product carries ONE power of the seed error rather than two.           *)
(*                                                                            *)
(* The head argument does not mind -- it only needs [|v - 1|] small COMPARED  *)
(* TO [u], the gap from [1] to its neighbours being [u] below and [2u] above. *)
(* The binding constraint is [head_eq_1_c]'s [e0 < 1] branch, which needs     *)
(* [(c + 200) u < 1/2]; the side condition [c u <= 1/4] gives it and allows   *)
(* [c] up to [256] at [p >= 10].  We take [c = 200] against a need of [162].  *)
(* NOTE bumping the old constant blindly does NOT work -- the proof balances  *)
(* it against its own [200u^2] slack term -- which is why the tolerance had   *)
(* to become a parameter rather than a bigger literal.                        *)
Lemma head_one_half mul :
  (forall a b X Y,
     mul (scaleTW a X) (scaleTW b Y) = scaleTW (a + b) (mul X Y)) ->
  (forall b y, isDW b -> isTW y ->
     Rabs (TWval b * TWval y - 1) <= 200 * (u * u) -> tw0 (mul b y) = 1) ->
  head_half mul.
Proof.
move=> Hscale Hone b y Hb Hy Hclose.
(* [y] is [scaleTW 0 y], which lets the scaling law fire on both arguments.   *)
have -> : mul (scaleTW (-1)%Z b) y
            = scaleTW (-1)%Z (mul b y).
  by rewrite -{1}(scaleTW_0 y) Hscale Z.add_0_r.
by rewrite tw0_scale (Hone _ _ Hb Hy Hclose) /= /Z.pow_pos /=; lra.
Qed.

(* [200 u <= 1/4] is what [head_one_gen_c] asks; [u <= 1/1024] gives it.      *)
Lemma head_c_ok : 200 * u <= / 4.
Proof.
have Hu0 : 0 < u by apply: u_gt_0.
by have := @u_le_1024 p Hp10; lra.
Qed.

Lemma ThreeProdDW_head_half :
  ties_to_even choice -> head_half ThreeProdDW.
Proof.
move=> Hc; apply: head_one_half.
  by move=> a b X Y; apply: ThreeProdDW_scale.
apply: (@head_one_gen_c p Hp2 Hp10 200 ThreeProdDW head_c_ok).
  by move=> X Y HX HY; apply: (@ThreeProdDW_isTW p Hp2 Hp6 choice choice_sym).
by move=> X Y HX HY HX0 HY0;
   apply: (@ThreeProdDW_head_gap p Hp2 Hp10 choice choice_sym).
Qed.

Lemma ThreeProdDWFast_head_half :
  ties_to_even choice -> head_half ThreeProdDWFast.
Proof.
move=> Hc; apply: head_one_half.
  by move=> a b X Y; apply: ThreeProdDWFast_scale.
apply: (@head_one_gen_c p Hp2 Hp10 200 ThreeProdDWFast head_c_ok).
  by move=> X Y HX HY;
     apply: (@ThreeProdDWFast_isTW p Hp2 Hp6 choice choice_sym).
by move=> X Y HX HY HX0 HY0;
   apply: (@ThreeProdDWFast_head_gap p Hp2 Hp10 choice choice_sym).
Qed.

(* ===========================================================================*)
(*  Correctness, part 1: the result is a triple word.                         *)
(*                                                                            *)
(*  Exactly Algorithm 14's assembly ([ThreeDivAux_isTW]) with [mul2] applied  *)
(*  to [b/2] and [i(1)] instead of [b] and [z], and [head_half] in place of   *)
(*  [head_one]: [mul1] must return a triple word, [mul2] must return one and  *)
(*  have head [1/2] (so that [3/2 - mul2 b' i(1)] is again a triple word, by  *)
(*  [sub32TW_isTW]), and [mul3] must do so on a head-[1] second argument.     *)
(* ===========================================================================*)
(* A triple word with a positive head is positive: the two low limbs cannot   *)
(* bridge the gap, [|x1| <= 2u|x0|] and [|x2| <= 2u^2|x0|].  Needed because   *)
(* [sqrt] is only informative on nonnegative arguments.                       *)
Lemma isTW_TWval_gt0 x : isTW x -> 0 < tw0 x -> 0 < TWval x.
Proof.
move=> Hx Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := @u_le_1024 p Hp10.
have Hx2 := @isTW_tw2_le p Hp2 x Hx.
have Hx1 : Rabs (tw1 x) <= 2 * u * Rabs (tw0 x).
  case: x Hx {Hx0 Hx2} => x0 x1 x2 [_ _ _ H1 _] /=.
  case: H1 => [->|H1]; first by rewrite Rabs_R0; have := Rabs_pos x0; nra.
  by have := @ulp_2u p beta Hp2 x0; lra.
have Ha0 : Rabs (tw0 x) = tw0 x by apply: Rabs_pos_eq; lra.
have H1 := Rabs_le_inv _ _ Hx1.
have H2 := Rabs_le_inv _ _ Hx2.
by case: x Hx0 Ha0 H1 H2 {Hx Hx1 Hx2} => x0 x1 x2 /= Hx0 Ha0 H1 H2;
   rewrite /TWval /=; nra.
Qed.

(* The assembly.  Beyond Algorithm 14's version this needs ONE extra          *)
(* hypothesis: a (very weak) error bound on [mul1].  Algorithm 14 applies its *)
(* head property to [b] and [x] directly, but here [mul2] is applied to [b']  *)
(* and [i(1) = mul1 b x], so the head argument only reaches [i(1)] through    *)
(* [mul1]'s accuracy.  [u^2] is far more slack than either variant needs      *)
(* ([10.5u^3] and [18u^3]).                                                   *)
Lemma ThreeSqRtAux_isTW mul1 mul2 mul3 :
  (forall b y, isDW b -> isTW y -> isTW (mul1 b y)) ->
  (forall b y, isDW b -> isTW y ->
     Rabs (TWval (mul1 b y) - TWval b * TWval y)
       <= (u * u) * Rabs (TWval b * TWval y)) ->
  (forall b y, isDW b -> isTW y -> isTW (mul2 b y)) ->
  (forall a y, isTW a -> isTW y -> tw0 y = 1 -> isTW (mul3 a y)) ->
  head_half mul2 ->
  forall x, isTW x -> 0 < tw0 x ->
    isTW (ThreeSqRtAux mul1 mul2 mul3 x).
Proof.
move=> Hmul1 Herr1 Hmul2 Hmul3 Hhead x Hx Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := @u_le_1024 p Hp10.
have [Fx0 Fx1] : format (tw0 x) /\ format (tw1 x)
  by case: x Hx {Hx0} => x0 x1 x2 [].
have HDW : isDW (sqrtBW (tw0 x) (tw1 x)) by apply: sqrtB_isDW.
have Hi1 : isTW (mul1 (sqrtBW (tw0 x) (tw1 x)) x) by apply: Hmul1.
(* The head argument needs [|b i(1) - 1| <= 200u^2].  With [t = b sqrt x]     *)
(* and [X = t * t] we have [b i(1) = t^2 (1 + d)], [|d| <= u^2], so the       *)
(* SEED error enters SQUARED -- whence [2 * 81u^2] and the [200u^2] budget.   *)
have Key : Rabs (TWval (sqrtBW (tw0 x) (tw1 x))
                 * TWval (mul1 (sqrtBW (tw0 x) (tw1 x)) x) - 1)
             <= 200 * (u * u).
  have HX0 : 0 < TWval x by apply: isTW_TWval_gt0.
  have HsX : sqrt (TWval x) * sqrt (TWval x) = TWval x
    by apply: sqrt_sqrt; lra.
  have Hseed := sqrtBW_x_err Hx Hx0.
  have He1 := Herr1 _ _ HDW Hx.
  set B := TWval (sqrtBW (tw0 x) (tw1 x)) in Hseed He1 *.
  set I1 := TWval (mul1 (sqrtBW (tw0 x) (tw1 x)) x) in He1 *.
  set s := sqrt (TWval x) in Hseed HsX.
  (* [B * I1 - 1 = ((B s)^2 - 1) + B * (I1 - B * X)]                          *)
  have Hsplit : B * I1 - 1
      = ((B * s) * (B * s) - 1) + B * (I1 - B * TWval x).
    by rewrite -HsX; ring.
  have Ht := Rabs_le_inv _ _ Hseed.
  have HBs : Rabs (B * s) <= 1 + (81 * (u * u) + 622 * (u * u * u)).
    by have := Rabs_triang_inv (B * s) 1; rewrite Rabs_R1; lra.
  (* the squared seed term                                                    *)
  have Hsq : Rabs ((B * s) * (B * s) - 1)
      <= (81 * (u * u) + 622 * (u * u * u))
         * (2 + (81 * (u * u) + 622 * (u * u * u))).
    have -> : (B * s) * (B * s) - 1 = (B * s - 1) * ((B * s - 1) + 2)
      by ring.
    rewrite Rabs_mult.
    apply: Rmult_le_compat => //; try apply: Rabs_pos.
    apply: Rle_trans (Rabs_triang _ _) _.
    have -> : Rabs 2 = 2 by rewrite Rabs_pos_eq; lra.
    by lra.
  (* the [mul1] term, measured against the same [t^2]                         *)
  have Hmulterm : Rabs (B * (I1 - B * TWval x))
      <= (u * u) * ((1 + (81 * (u * u) + 622 * (u * u * u)))
                    * (1 + (81 * (u * u) + 622 * (u * u * u)))).
    rewrite Rabs_mult.
    have HBp := Rabs_pos B.
    have Hstep : Rabs B * Rabs (I1 - B * TWval x)
        <= Rabs B * ((u * u) * Rabs (B * TWval x))
      by apply: Rmult_le_compat_l.
    apply: Rle_trans Hstep _.
    have HBX : Rabs B * Rabs (B * TWval x) = Rabs (B * s) * Rabs (B * s).
      by rewrite -!Rabs_mult -HsX; congr (Rabs _); ring.
    have -> : Rabs B * ((u * u) * Rabs (B * TWval x))
        = (u * u) * (Rabs B * Rabs (B * TWval x)) by ring.
    rewrite HBX.
    apply: Rmult_le_compat_l; first by nra.
    by apply: Rmult_le_compat => //; apply: Rabs_pos.
  have Ht2 := Rabs_triang ((B * s) * (B * s) - 1) (B * (I1 - B * TWval x)).
  rewrite Hsplit.
  have Hu2 : u * u <= /1024 * u by nra.
  have Hu3 : u * u * u <= /1024 * (u * u) by nra.
  have Hu4 : u * u * u * u <= /1024 * (u * u * u) by nra.
  by clear -Ht2 Hsq Hmulterm Hu0 Hu1024 Hu2 Hu3 Hu4; nra.
have Hhalf := Hhead _ _ HDW Hi1 Key.
rewrite /ThreeSqRtAux.
apply: Hmul3.
- exact: Hi1.
- apply: sub32TW_isTW; last exact: Hhalf.
  apply: Hmul2 => //.
  by apply: isDW_scale.
by case: (mul2 _ _) Hhalf => t0 t1 t2 /= ->; field.
Qed.

(* Both DW x TW variants are far inside the [u^2] the assembly asks for:      *)
(* [10.5u^3 + 39u^4] and [18u^3 + 75u^4] against [u^2].                       *)
Lemma prodDW_err_le_u2 : 105 / 10 * (u * u * u) + 39 * (u * u * u * u)
                           <= u * u.
Proof.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := @u_le_1024 p Hp10.
have L1 : u * u * u <= / 1024 * (u * u) by nra.
have L2 : u * u * u * u <= / 1024 * (u * u * u) by nra.
by nra.
Qed.

Lemma prodDWFast_err_le_u2 : 18 * (u * u * u) + 75 * (u * u * u * u)
                               <= u * u.
Proof.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := @u_le_1024 p Hp10.
have L1 : u * u * u <= / 1024 * (u * u) by nra.
have L2 : u * u * u * u <= / 1024 * (u * u * u) by nra.
by nra.
Qed.

Lemma ThreeSqRt_isTW x :
  ties_to_even choice ->
  isTW x -> 0 < tw0 x -> isTW (ThreeSqRt x).
Proof.
move=> Hc Hx Hx0.
apply: (@ThreeSqRtAux_isTW ThreeProdDW ThreeProdDW ThreeProdOneTW) => //.
- by move=> b y Hb Hy; apply: (@ThreeProdDW_isTW p Hp2 Hp6 choice choice_sym).
- move=> b y Hb Hy.
  apply: Rle_trans
    (@ThreeProdDW_error p Hp2 Hp6 choice choice_sym b y Hc Hb Hy) _.
  apply: Rmult_le_compat_r; first by apply: Rabs_pos.
  exact: prodDW_err_le_u2.
- by move=> b y Hb Hy; apply: (@ThreeProdDW_isTW p Hp2 Hp6 choice choice_sym).
- by move=> a y Ha Hy Hy0;
     apply: (@ThreeProdOneTW_isTW p Hp2 Hp6 choice choice_sym).
exact: ThreeProdDW_head_half.
Qed.

Lemma ThreeSqRtFast_isTW x :
  ties_to_even choice ->
  isTW x -> 0 < tw0 x -> isTW (ThreeSqRtFast x).
Proof.
move=> Hc Hx Hx0.
apply: (@ThreeSqRtAux_isTW ThreeProdDWFast ThreeProdDWFast ThreeProdOneTW)
  => //.
- by move=> b y Hb Hy;
     apply: (@ThreeProdDWFast_isTW p Hp2 Hp6 choice choice_sym).
- move=> b y Hb Hy.
  apply: Rle_trans
    (@ThreeProdDWFast_error p Hp2 Hp6 choice choice_sym b y Hc Hb Hy) _.
  apply: Rmult_le_compat_r; first by apply: Rabs_pos.
  exact: prodDWFast_err_le_u2.
- by move=> b y Hb Hy;
     apply: (@ThreeProdDWFast_isTW p Hp2 Hp6 choice choice_sym).
- by move=> a y Ha Hy Hy0;
     apply: (@ThreeProdOneTW_isTW p Hp2 Hp6 choice choice_sym).
exact: ThreeProdDWFast_head_half.
Qed.

(* ===========================================================================*)
(*  Correctness, part 2: the relative error (paper Theorem 11).               *)
(*                                                                            *)
(*  With [d1] the relative error of [i(1) = 3Prod(b, x)] (relative to [b x]), *)
(*  [d2] that of the inner [3Prod(b', i(1))] and [d3] that of the final       *)
(*  [y = 3Prod(i(1), i(2))], the SUPPLEMENTARY's global bound is              *)
(*                                                                            *)
(*      |y - sqrt x| <= (d1 (1.5 + 287u^2) + d2 (0.5 + 123u^2)                *)
(*                      + d3 (1 + 162u^2) + 9916u^4) |sqrt x|                 *)
(*                                                                            *)
(*  and it is stated below in THAT shape, so the route can be followed        *)
(*  literally first.  Its [1.5] is loose -- see the file header: the true     *)
(*  first-order weight on [d1] is [1/2], the supplementary having triangle-   *)
(*  inequalitied away the cancellation between the two occurrences of [i(1)]. *)
(*  With our [d3 = 6u^3] the literal route gives [27u^3]/[42u^3] and the      *)
(*  sharpened one [18.5u^3]/[26u^3]; only the latter reaches the published    *)
(*  [24]/[39], so the cancellation has to be exploited, not skipped.          *)
(*                                                                            *)
(*  STEPS, and what each one already has:                                     *)
(*                                                                            *)
(*  (1) [b] is a double word and [|b sqrt x - 1| <= 81u^2 + 622u^3]:          *)
(*      [sqrtB_isDW], [sqrtBW_x_err] above -- BOTH TO PROVE (Algorithm 13's   *)
(*      twins are [reciB_isDW] and [reciBW_x_err], already proved, and the    *)
(*      route is the same except for the seed).                               *)
(*  (2) [i(2)] has head [1] and [|i(2) - 1| <= 40u^2]: [head_half] +          *)
(*      [sub32TW_isTW].  The [40u^2] is what [ThreeProdOneTW_error] demands   *)
(*      of its second argument, so it must come out as a named lemma.         *)
(*  (3) the algebraic identity: with [s = sqrt x],                            *)
(*        y - s = (y - i(1) i(2)) + i(1) (i(2) - (3/2 - b' i(1)))             *)
(*                + (i(1) - b x)(3/2 - (1/2) b^2 x) + [(b x)(3/2 - (1/2)b^2x) *)
(*                                                     - s]                   *)
(*      whose last bracket is [-s e^2 (e + 3)/2] by [sqrt_newton_id], hence   *)
(*      [<= 9916u^4 |s|] by [sqrt_newton_residual] -- the only [O(u^4)]       *)
(*      contributor that is not a product's error.  KEEP THE SIGNS: it is in  *)
(*      the second and third terms that [i(1)]'s error cancels, and dropping  *)
(*      to absolute values too early is exactly what costs the factor three.  *)
(*  (4) the final arithmetic on bare quantities, the analogue of              *)
(*      [reci_error_assembly] / [div_error_assembly]; those take three resp.  *)
(*      four error terms and this one needs three, so one of them should be   *)
(*      reusable outright.                                                    *)
(*  (5) [d1], [d2] = [ThreeProdDW_error] / [ThreeProdDWFast_error] and        *)
(*      [d3] = [ThreeProdOneTW_error] -- ALL THREE ALREADY PROVED.  Unlike    *)
(*      Theorems 9 and 10, Theorem 11 needs no new product bound.             *)
(*                                                                            *)
(*  The [u^4] terms are the paper's and are the ones at risk (Theorem 9's     *)
(*  [1465u^4] became [1830u^4], Theorem 10's [1509u^4] became [2576u^4]).     *)
(* ===========================================================================*)
Lemma ThreeSqRtAux_error mul1 mul2 mul3 d1 d2 d3 :
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
  head_half mul2 ->
  0 <= d1 -> 0 <= d2 -> 0 <= d3 ->
  forall x, isTW x -> 0 < tw0 x ->
    Rabs (TWval (ThreeSqRtAux mul1 mul2 mul3 x) - sqrt (TWval x))
      <= (d1 * (3 / 2 + 287 * (u * u)) + d2 * (1 / 2 + 123 * (u * u))
          + d3 * (1 + 162 * (u * u)) + 9916 * (u * u * u * u))
         * Rabs (sqrt (TWval x)).
Proof.
Admitted.

(* Paper Theorem 11, accurate variant: [24u^3 + 10260u^4].                    *)
Lemma ThreeSqRt_error x :
  ties_to_even choice ->
  isTW x -> 0 < tw0 x ->
  Rabs (TWval (ThreeSqRt x) - sqrt (TWval x)) <=
     (24 * (u * u * u) + 10260 * (u * u * u * u)) * Rabs (sqrt (TWval x)).
Proof.
Admitted.

(* Paper Theorem 11, fast variant: [39u^3 + 10333u^4].                        *)
Lemma ThreeSqRtFast_error x :
  ties_to_even choice ->
  isTW x -> 0 < tw0 x ->
  Rabs (TWval (ThreeSqRtFast x) - sqrt (TWval x)) <=
     (39 * (u * u * u) + 10333 * (u * u * u * u)) * Rabs (sqrt (TWval x)).
Proof.
Admitted.

End SecThreeSqRt.
