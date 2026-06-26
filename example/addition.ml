(* ------------------------------------------------------------------ *)
(* Triple-word addition (Algorithm 8, "TWSum") from                    *)
(*   N. Fabiano, J.-M. Muller, J. Picot,                               *)
(*   "Algorithms for triple-word arithmetic", IEEE TC, 2019.           *)
(*   (doc/paper3.pdf, Section 5)                                        *)
(*                                                                      *)
(* A triple-word (TW) number is an unevaluated sum of three binary64   *)
(* floating-point numbers (x0, x1, x2) that is P-nonoverlapping        *)
(* (|x_{i+1}| < ulp(x_i)).  The sum of two TW numbers is computed by   *)
(*                                                                      *)
(*     z = Merge((x0,x1,x2),(y0,y1,y2))     (* 6 terms, sorted *)      *)
(*     e = VecSum(z)                                                    *)
(*     r = VSEB(3)(e)                                                   *)
(*                                                                      *)
(* with the guaranteed relative error bound                            *)
(*                                                                      *)
(*     | r - (x + y) | / | x + y |  <=  2 u^3 + 4.2 u^4,                *)
(*                                                                      *)
(* where u = 2^-53 for binary64.                                       *)
(*                                                                      *)
(* Run the tests with:   ocaml addition.ml                             *)
(* ------------------------------------------------------------------ *)

let u = ldexp 1.0 (-53)      (* unit roundoff, 2^-53 *)

type tw = float * float * float

(* ---- basic error-free transforms ---------------------------------- *)

(* Algorithm 1: Fast2Sum.  Exact when |a| >= |b|.  s + e = a + b. *)
let fast2sum a b =
  let s = a +. b in
  let z = s -. a in
  let e = b -. z in
  (s, e)

(* Algorithm 2: 2Sum.  Always exact: s + e = a + b, no ordering needed. *)
let two_sum a b =
  let s  = a +. b in
  let a' = s -. b in
  let b' = s -. a' in
  let da = a -. a' in
  let db = b -. b' in
  let e  = da +. db in
  (s, e)

(* ---- Algorithm 4: VecSum ------------------------------------------ *)
(* Input  x.(0..n-1); output e.(0..n-1) with same exact sum,           *)
(* "more nonoverlapping".  Processes from the least significant term.  *)
let vec_sum (x : float array) : float array =
  let n = Array.length x in
  let e = Array.make n 0.0 in
  if n = 0 then e
  else begin
    let s = ref x.(n - 1) in
    for i = n - 2 downto 0 do
      let (si, ei1) = two_sum x.(i) !s in
      e.(i + 1) <- ei1;
      s := si
    done;
    e.(0) <- !s;
    e
  end

(* ---- Algorithm 5: VecSumErrBranch (VSEB) -------------------------- *)
(* Returns the full normalised output (length n, zero-padded).         *)
let vseb_full (e : float array) : float array =
  let n = Array.length e in
  let y = Array.make n 0.0 in
  if n = 0 then y
  else if n = 1 then (y.(0) <- e.(0); y)
  else begin
    let j   = ref 0 in
    let eps = ref e.(0) in
    for i = 0 to n - 3 do
      let (r, et) = two_sum !eps e.(i + 1) in
      if et <> 0.0 then begin
        y.(!j) <- r;
        eps := et;
        incr j
      end else
        eps := r
    done;
    let (a, b) = two_sum !eps e.(n - 1) in
    y.(!j) <- a;
    y.(!j + 1) <- b;
    y
  end

(* VSEB(k): keep only the first k terms (the dropped tail is the error). *)
let vseb k e =
  let y = vseb_full e in
  Array.sub y 0 (min k (Array.length y))

(* ---- Merge two magnitude-sorted sequences ------------------------- *)
let rec merge (xs : float list) (ys : float list) : float list =
  match xs, ys with
  | [], _ -> ys
  | _, [] -> xs
  | x :: xs', y :: ys' ->
      if abs_float y <= abs_float x
      then x :: merge xs' ys
      else y :: merge xs ys'

(* ---- Algorithm 6: ToTW -- normalise three FP numbers into a TW ----- *)
let to_tw a b c : tw =
  let (d0, d1) = two_sum a b in
  let e = vec_sum [| d0; d1; c |] in
  let r = vseb_full e in
  (r.(0), r.(1), r.(2))

(* ---- Algorithm 8: TWSum -- sum of two triple-word numbers ---------- *)
let tw_sum ((x0, x1, x2) : tw) ((y0, y1, y2) : tw) : tw =
  let z = Array.of_list (merge [ x0; x1; x2 ] [ y0; y1; y2 ]) in
  let e = vec_sum z in
  let r = vseb_full e in
  (r.(0), r.(1), r.(2))

(* ================================================================== *)
(* Testing infrastructure: exact arithmetic via floating-point        *)
(* expansions (Shewchuk).  two_sum is error-free, so we can keep an    *)
(* exact representation of sums of doubles as a list of doubles.       *)
(* ================================================================== *)

(* grow-expansion: exact expansion whose sum is (sum expn) + f. *)
let grow (expn : float list) (f : float) : float list =
  let q = ref f in
  let hs =
    List.map (fun ei -> let (s, h) = two_sum ei !q in q := s; h) expn
  in
  hs @ [ !q ]

(* exact sum of a list of doubles, as an expansion *)
let exact_sum (xs : float list) : float list =
  List.fold_left grow [] xs

(* approximate the real value of an expansion (sum from small to large) *)
let value_of (expn : float list) : float =
  let sorted =
    List.sort (fun a b -> compare (abs_float a) (abs_float b)) expn
  in
  List.fold_left ( +. ) 0.0 sorted

(* exact residual r - (x + y), returned as an expansion *)
let residual (x0, x1, x2) (y0, y1, y2) (r0, r1, r2) =
  exact_sum [ r0; r1; r2; -.x0; -.x1; -.x2; -.y0; -.y1; -.y2 ]

(* ---- random TW generator ------------------------------------------ *)
let random_tw () : tw =
  let a = 1.0 +. Random.float 2.0 in                  (* [1, 3)  *)
  let b = (Random.float 1.0 -. 0.5) *. a *. ldexp 1.0 (-51) in
  let c = (Random.float 1.0 -. 0.5) *. a *. ldexp 1.0 (-102) in
  to_tw a b c

(* check P-nonoverlapping-ness loosely: |x_{i+1}| <= |x_i| *)
let is_sorted (x0, x1, x2) =
  abs_float x1 <= abs_float x0 && abs_float x2 <= abs_float x1

(* ================================================================== *)
let () =
  Random.self_init ();
  Random.init 42;                       (* reproducible *)

  Printf.printf "u = 2^-53 = %.3e\n" u;
  Printf.printf "error bound coeff: 2 u^3 + 4.2 u^4 = %.3e (relative)\n\n"
    (2.0 *. u ** 3.0 +. 4.2 *. u ** 4.0);

  (* --- a couple of explicit sanity checks --------------------------- *)
  let show name (x0, x1, x2) =
    Printf.printf "  %s = (%.17g, %.17g, %.17g)\n" name x0 x1 x2
  in
  let x = to_tw 1.0 (ldexp 1.0 (-53)) (ldexp 1.0 (-106)) in
  let y = to_tw 1.0 (ldexp 1.0 (-54)) (ldexp 1.0 (-108)) in
  show "x" x;
  show "y" y;
  let r = tw_sum x y in
  show "x+y" r;
  let res = residual x y r in
  Printf.printf "  exact residual ~ %.3e\n\n" (value_of res);

  (* --- randomised error-bound test ---------------------------------- *)
  let n = 200_000 in
  let bound_coeff = 2.0 *. u ** 3.0 +. 4.2 *. u ** 4.0 in
  let slack = 1.0 +. 1e-6 in
  let failures = ref 0 in
  let worst = ref 0.0 in          (* worst relative error, in units of u^3 *)
  let not_tw = ref 0 in
  for _ = 1 to n do
    let x = random_tw () and y = random_tw () in
    let r = tw_sum x y in
    if not (is_sorted r) then incr not_tw;
    let sref = value_of (exact_sum
                 (let (x0,x1,x2)=x and (y0,y1,y2)=y in [x0;x1;x2;y0;y1;y2])) in
    let res  = abs_float (value_of (residual x y r)) in
    let rel  = res /. abs_float sref in
    if rel /. (u ** 3.0) > !worst then worst := rel /. (u ** 3.0);
    if rel > bound_coeff *. slack then incr failures
  done;

  Printf.printf "random trials: %d\n" n;
  Printf.printf "worst relative error: %.4f u^3  (bound = 2 u^3)\n" !worst;
  Printf.printf "results not magnitude-sorted: %d\n" !not_tw;
  Printf.printf "bound violations (rel > 2u^3 + 4.2u^4): %d\n" !failures;
  if !failures = 0 then print_string "OK: error bound holds on all trials\n"
  else print_string "FAIL: error bound violated\n"
