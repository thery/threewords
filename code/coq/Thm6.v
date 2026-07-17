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
Local Notation uls := (uls p).

Local Notation Pnonoverlap := (Pnonoverlap p).
Local Notation pairwise_ulp := (pairwise_ulp p).

Local Notation vecSum := (vecSum p choice).
Local Notation vseb := (vseb p choice).
Local Notation vecSum_run_ufp := (vecSum_run_ufp Hp2 choice_sym).
Local Notation vecSum_err_ufp := (vecSum_err_ufp Hp2 choice_sym).

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
Admitted.

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

(* VecSum carries a trailing zero through untouched: the running sum entering *)
(* the last step is [s = 0], so [2Sum(x_{n-2}, 0) = (x_{n-2}, 0)] and the     *)
(* emitted error is [0].                                                      *)
Lemma vecSum_rcons0 (m : seq R) :
  (0 < size m)%N -> {in m, forall z, format z} ->
  vecSum (rcons m 0) = rcons (vecSum m) 0.
Proof.
Admitted.

(* VSEB absorbs a trailing zero: [2Sum(eps, 0) = (eps, 0)] has zero error, so *)
(* nothing is emitted and the remainder is carried.  The output therefore     *)
(* either is unchanged or gains a single trailing zero.                       *)
Lemma vseb_rcons0 (X : seq R) :
  (0 < size X)%N -> {in X, forall z, format z} ->
  vseb (rcons X 0) = vseb X \/ vseb (rcons X 0) = rcons (vseb X) 0.
Proof.
Admitted.

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
