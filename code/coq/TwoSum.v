(* ---------------------------------------------------------------------------*)
(* The error-free transform 2Sum (paper Algorithm 2) and its properties:      *)
(* exactness, the format and half-ulp magnitude of its two words, and that    *)
(* its low word (the error) lands on the coarse input grid ([is_imul]).  A    *)
(* general round-to-nearest building block, generic over the precision [p]    *)
(* and minimal exponent [emin] (binary64 is fixed only in [addition.v]);      *)
(* built on [Uls] and imported by the triple-word development.                *)
(* ---------------------------------------------------------------------------*)

From Stdlib Require Import ZArith Reals Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
Require Import Nmore Rmore Fmore Rstruct MULTmore prelim Nonoverlap.
From Flocq Require Import Pff.Pff2Flocq.
Require Import Uls.

Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Sec2Sum.

(* Generic over precision [p] and minimal exponent [emin]; [2Sum] needs       *)
(* [1 < p] and [emin <= 0] (for Flocq's [TwoSum_correct]).                    *)
Variable p : Z.
Variable emin : Z.
Hypothesis Hp2 : (1 < p)%Z.
Hypothesis emin_le_0 : (emin <= 0)%Z.

Let beta := radix2.
Local Notation pow e := (bpow beta e).

(* The [Prec_gt_0 p] instance is DERIVED from [Hp2], so lemmas depend on      *)
(* [Hp2] (which callers pass) rather than a separate unresolved instance.     *)
Local Instance p_gt_0 : Prec_gt_0 p.
Proof. now apply Z.lt_trans with (2 := Hp2). Qed.

Open Scope R_scope.

Local Notation u := (u p beta).

Variable choice : Z -> bool.
Hypothesis choice_sym : forall x, choice x = ~~ choice (- (x + 1))%Z.
Let rnd : R -> Z := Znearest choice.
Local Instance valid_rnd : Valid_rnd rnd := valid_rnd_N choice.

Local Notation float := (float radix2).
Local Notation fexp := (FLT_exp emin p).
Local Notation format := (generic_format beta fexp).
Local Notation cexp := (cexp beta fexp).
Local Notation mant := (scaled_mantissa beta fexp).
Local Notation RND := (round beta fexp rnd).
Local Notation ulp := (ulp beta fexp).
Local Notation uls := (uls p emin).
Local Notation fastTwoSum := (fastTwoSum beta emin p rnd).
Local Notation Fnonoverlap := (Fnonoverlap p emin).
Local Notation error_le_half_ulp_RN :=
  (@error_le_half_ulp_round beta (FLT_exp emin p)
     (FLT_exp_valid emin p) (FLT_exp_monotone emin p) choice).
Local Notation TwoSum_correct_RN :=
  (@TwoSum_correct emin p choice Hp2 emin_le_0 choice_sym).

(*  Basic error-free transforms                                               *)
(* ===========================================================================*)

(* Algorithm 2 of the paper: the 6-operation 2Sum.  Always exact:             *)
(*   s + e = a + b, with no assumption on the magnitudes of a and b.          *)
Definition TwoSum (a b : R) : dwR :=
  let s  := RND (a + b) in
  let a' := RND (s - b) in
  let b' := RND (s - a') in
  let da := RND (a - a') in
  let db := RND (b - b') in
  DWR s (RND (da + db)).

(* Named projectors for the double-word record [dwR] (prelim: [DWR xh xl]),   *)
(* so a [TwoSum]/[Fast2Sum] result's components can be named without a [let]. *)
Definition dwh (d : dwR) : R := let: DWR xh _ := d in xh.
Definition dwl (d : dwR) : R := let: DWR _ xl := d in xl.

Lemma dwhE xh xl : dwh (DWR xh xl) = xh. Proof. by []. Qed.
Lemma dwlE xh xl : dwl (DWR xh xl) = xl. Proof. by []. Qed.

(* The high word of a 2Sum is the rounded sum.                                *)
Lemma TwoSum_hi a b : dwh (TwoSum a b) = RND (a + b). Proof. by []. Qed.

Definition formatDWR (a : dwR) := let: DWR b c := a in format b /\ format c.

Lemma format_TwoSum a b : format a -> format b -> formatDWR (TwoSum a b).
Proof. by move=> Fa Fb; split; try apply: generic_format_round. Qed.

(* The magnitude counterpart of [formatDWR]: in a 2Sum result [DWR s e]       *)
(* the error word [e] is at most half an ulp of the high word [s].            *)
Definition magnitudeDWR (a : dwR) := let: DWR s e := a in Rabs e <= ulp s / 2.

(* 2Sum is error-free: s + e = a + b.  We reuse Flocq's [TwoSum_correct]      *)
(* (the Pff bridge), instantiated with the operands SWAPPED: paper3's         *)
(* Algorithm 2 subtracts [b] first, whereas Flocq's variant subtracts its     *)
(* first argument first, so [TwoSum_correct b a] has exactly our              *)
(* intermediate values (up to commutativity of [+]).                          *)
Lemma TwoSum_correct_loc a b : format a -> format b ->
  let: DWR s e := TwoSum a b in s + e = a + b.
Proof.
move=> Fa Fb.
have := TwoSum_correct_RN b a Fb Fa.
rewrite -[radix2]/beta -[Znearest _]/rnd (Rplus_comm b a) /=.
set DA := RND (a - _); set DB := RND (b - _).
by rewrite (Rplus_comm DA DB).
Qed.

Lemma dwh_TwoSum_r0 eps : format eps -> dwh (TwoSum eps 0) = eps.
Proof. by move=> Feps; rewrite TwoSum_hi Rplus_0_r round_generic. Qed.

Lemma dwl_TwoSum_r0 eps : format eps -> dwl (TwoSum eps 0) = 0.
Proof.
move=> Feps.
have F0 : format 0 by apply: generic_format_0.
have Hc : dwh (TwoSum eps 0) + dwl (TwoSum eps 0) = eps + 0.
  by exact: TwoSum_correct_loc Feps F0.
by move: Hc; rewrite dwh_TwoSum_r0 //; lra.
Qed.

(* Magnitude analogue of [format_TwoSum] (Algorithm 2): the low word of a     *)
(* 2Sum is bounded by half an ulp of its high word.  Combine exactness        *)
(* [e = (a+b) - s] with the round-to-nearest bound |RN(x)-x| <= ulp(RN x)/2.*)
Lemma magnitude_TwoSum a b :
  format a -> format b -> magnitudeDWR (TwoSum a b).
Proof.
move=> Fa Fb.
have Hc := TwoSum_correct_loc Fa Fb.
move: Hc; rewrite /magnitudeDWR /TwoSum /=.
set s := RND (a + b).
set e := RND (RND (a - _) + RND (b - _)).
move=> Hc.
have He : e = a + b - s by lra.
rewrite He Rabs_minus_sym.
have /(_ p_gt_0) Hh := error_le_half_ulp_RN (a + b).
rewrite -[Znearest _]/rnd -/s in Hh.
lra.
Qed.

(* The low word (error) of a 2Sum is a multiple of the coarser input grid     *)
(* [bpow (min (cexp a) (cexp b))]: [a], [b], and [RN(a+b)] all live on it, so *)
(* so does [a + b - RN(a+b)].                                                 *)
Lemma TwoSum_err_imul a b : format a -> format b ->
  is_imul (dwl (TwoSum a b)) (bpow beta (Z.min (cexp a) (cexp b))).
Proof.
move=> Fa Fb.
have Hc : dwh (TwoSum a b) + dwl (TwoSum a b) = a + b
  by exact: TwoSum_correct_loc Fa Fb.
have -> : dwl (TwoSum a b) = (a + b) - RND (a + b)
  by move: Hc; rewrite TwoSum_hi; lra.
have Hab : is_imul (a + b) (bpow beta (Z.min (cexp a) (cexp b))).
  apply: is_imul_add.
    by apply: (is_imul_pow_le _ (Z.le_min_l _ _)); apply: format_imul_cexp.
  by apply: (is_imul_pow_le _ (Z.le_min_r _ _)); apply: format_imul_cexp.
by apply: is_imul_minus => //; apply: is_imul_pow_round.
Qed.

(* The TwoSum error inherits at least the [uls] of the smaller-grid operand:  *)
(* if [uls s <= uls a] then [uls s <= uls (dwl (TwoSum a s))].  Both operands *)
(* lie on the grid [bpow (cexp s + trZ (mant s))] (= [uls s]), hence so does  *)
(* the exact error [a + s - RND(a + s)]; [is_imul_uls_ge] then lifts that grid*)
(* up to the error's own [uls].  This is the separation core of Fnonoverlap.  *)
Lemma TwoSum_err_uls_ge a s : format a -> format s -> a <> 0 -> s <> 0 ->
  uls s <= uls a -> dwl (TwoSum a s) <> 0 -> uls s <= uls (dwl (TwoSum a s)).
Proof.
move=> Fa Fs an0 sn0 Hle en0.
have Hulss : uls s = bpow beta (cexp s + Z.of_nat (trZ (Ztrunc (mant s)))).
  by rewrite /uls; case: Req_bool_spec.
have Hulsa : uls a = bpow beta (cexp a + Z.of_nat (trZ (Ztrunc (mant a)))).
  by rewrite /uls; case: Req_bool_spec.
have HleZ : (cexp s + Z.of_nat (trZ (Ztrunc (mant s))) <=
             cexp a + Z.of_nat (trZ (Ztrunc (mant a))))%Z.
  by apply: (le_bpow beta); rewrite -Hulss -Hulsa.
have Ha : is_imul a (bpow beta (cexp s + Z.of_nat (trZ (Ztrunc (mant s))))).
  by apply: (is_imul_pow_le _ HleZ); rewrite -Hulsa; exact: uls_imul.
have Hs : is_imul s (bpow beta (cexp s + Z.of_nat (trZ (Ztrunc (mant s))))).
  by rewrite -Hulss; exact: uls_imul.
have Herr : is_imul (dwl (TwoSum a s))
              (bpow beta (cexp s + Z.of_nat (trZ (Ztrunc (mant s))))).
  have Hc : dwh (TwoSum a s) + dwl (TwoSum a s) = a + s
    by exact: TwoSum_correct_loc Fa Fs.
  have -> : dwl (TwoSum a s) = (a + s) - RND (a + s)
    by move: Hc; rewrite TwoSum_hi; lra.
  apply: is_imul_minus; first by apply: is_imul_add.
  by apply: is_imul_pow_round; apply: is_imul_add.
have Ferr : format (dwl (TwoSum a s)).
  move: (format_TwoSum Fa Fs); rewrite /formatDWR.
  by case: (TwoSum a s) => b c [].
apply: Rle_trans (is_imul_uls_ge Ferr en0 Herr).
by apply: Req_le.
Qed.

Lemma Fnonoverlap_TwoSum_err eps e l :
  format eps -> format e -> Fnonoverlap [:: eps, e & l] ->
  dwl (TwoSum eps e) <> 0 -> Fnonoverlap (dwl (TwoSum eps e) :: l).
Proof.
move=> Feps Fe Fno etn0.
have Hc : dwh (TwoSum eps e) + dwl (TwoSum eps e) = eps + e.
  by exact: TwoSum_correct_loc Feps Fe.
have Het : RND (eps + e) + dwl (TwoSum eps e) = eps + e.
  by move: Hc; rewrite TwoSum_hi.
(* A zero operand rounds exactly, leaving [dwl = 0]; so both are nonzero.     *)
have epsn0 : eps <> 0.
  move=> eps0; apply: etn0.
  have HR : RND (eps + e) = e by rewrite eps0 Rplus_0_l; apply: round_generic.
  by lra.
have en0 : e <> 0.
  move=> e0; apply: etn0.
  have HR : RND (eps + e) = eps by rewrite e0 Rplus_0_r; apply: round_generic.
  by lra.
(* [|e| <= 1/2 uls eps] and [uls e <= |e|] give [uls e <= uls eps], so the    *)
(* error inherits at least [e]'s grid: [uls e <= uls (dwl (TwoSum eps e))].   *)
have He2 : Rabs e <= / 2 * uls eps by exact: Fnonoverlap_head2 Fno en0.
have Hueps : uls e <= uls eps.
  have Hule : uls e <= Rabs e by apply: uls_le_abs.
  have Hu0 : 0 < uls eps by apply: uls_gt_0.
  by lra.
have Huet : uls e <= uls (dwl (TwoSum eps e)).
  by apply: (TwoSum_err_uls_ge Feps Fe epsn0 en0 Hueps).
(* The tail [l] carries over from the input (drop [eps, e]), with the running *)
(* term [e] weakened to the coarser error ([uls e <= uls (dwl ..)]).          *)
by apply: (Fnonoverlap_aux_prev Huet (Fnonoverlap_tail Fno en0)).
Qed.

(* Reusable step lemma (the [et = 0] branch): when [2Sum eps e] is exact      *)
(* ([dwl = 0], so [dwh = eps + e] merges them), prepending the merged high    *)
(* word to the tail keeps F-nonoverlap.  Needs [e <> 0] (the paper's zero-free*)
(* convention -- a zero [e] is dropped by [vsebAux_cons0] before this fires). *)
(* The tail carries over from the input directly; the only new obligation is  *)
(* the head bound [|nth l 0| <= 1/2 uls (eps + e)], which follows from        *)
(* [|nth l 0| <= 1/2 uls e] and [uls e <= uls (eps + e)]: [eps + e] is a      *)
(* nonzero float lying on [e]'s grid ([uls e]), so [is_imul_uls_ge] lifts it. *)
Lemma Fnonoverlap_TwoSum_merge eps e l :
  format eps -> format e -> e <> 0 -> dwh (TwoSum eps e) <> 0 ->
  Fnonoverlap [:: eps, e & l] ->
  dwl (TwoSum eps e) = 0 -> Fnonoverlap (dwh (TwoSum eps e) :: l).
Proof.
move=> Feps Fe en0 rn0 Fno etz.
have Hc : dwh (TwoSum eps e) + dwl (TwoSum eps e) = eps + e.
  by exact: TwoSum_correct_loc Feps Fe.
have Hr : dwh (TwoSum eps e) = eps + e by move: Hc; rewrite etz; lra.
have Frr : format (dwh (TwoSum eps e)).
  by rewrite TwoSum_hi; apply: generic_format_round.
set r := dwh (TwoSum eps e) in Hr Frr rn0 *.
(* [uls e <= uls r]: [r = eps + e] is a nonzero float on [e]'s grid [uls e].  *)
have Hue : uls e <= uls r.
  case: (Req_dec eps 0) => [eps0|epsn0].
    by rewrite Hr eps0 Rplus_0_l; apply: Rle_refl.
  have He0 : Rabs e <= / 2 * uls eps by exact: Fnonoverlap_head2 Fno en0.
  have Hueps : uls e <= uls eps.
    have Hu0 : 0 < uls eps by apply: uls_gt_0.
    have Hle : uls e <= Rabs e by apply: uls_le_abs.
    lra.
  have gE : uls e = pow (cexp e + trN (Ztrunc (mant e))).
    by rewrite /uls; case: Req_bool_spec.
  have gepsE : uls eps = pow (cexp eps + trN (Ztrunc (mant eps))).
    by rewrite /uls; case: Req_bool_spec.
  have HleZ : (cexp e + trN (Ztrunc (mant e)) <=
               cexp eps + trN (Ztrunc (mant eps)))%Z.
    by apply: (le_bpow beta); rewrite -gE -gepsE.
  have Hime : is_imul e (pow (cexp e + trN (Ztrunc (mant e)))).
    by rewrite -gE; exact: uls_imul.
  have Himeps : is_imul eps (pow (cexp e + trN (Ztrunc (mant e)))).
    by apply: (is_imul_pow_le _ HleZ); rewrite -gepsE; exact: uls_imul.
  have Himr : is_imul r (pow (cexp e + trN (Ztrunc (mant e)))).
    by rewrite Hr; apply: is_imul_add.
  apply: Rle_trans (is_imul_uls_ge Frr rn0 Himr).
  by rewrite gE; apply: Rle_refl.
(* Tail carries over from the input, running term [e] weakened to [r].        *)
by apply: (Fnonoverlap_aux_prev Hue (Fnonoverlap_tail Fno en0)).
Qed.


End Sec2Sum.
