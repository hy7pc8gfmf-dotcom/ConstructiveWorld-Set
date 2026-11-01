(* UpReqSumB.v -- pointwise <=_B summation lifting piece.                   *)
(* Mission.: pointwise <=_B summation lifting: pointwise real_le_b implies  *)
(*   real_le_b of the list sum (n-ary Bishop summation face, Fubini-type    *)
(*   lifting). Four statements: the Fixpoint length machine sumb_lenR, its  *)
(*   nonnegativity sumb_lenR_nonneg, the constant-sum collapse              *)
(*   sumb_sum_const, and the main piece sumb_list_sum_le_b.                 *)
(* Dependencies.: S01-S15 (the exported faces of CW_ConstructiveWorld_219), *)
(*   plus UpRealLeB (real_le_b, the Set-level Bishop order face) and        *)
(*   UpRealLeB2 (real_le_closure_b_nonneg, the nonnegative-coefficient      *)
(*   completer). Engine triple from S08: real_list_sum / real_list_sum_le   *)
(*   / real_list_sum_add; ring faces from S02 (real_le_refl,                *)
(*   real_plus_zero, real_eq_trans, real_eq_sym, real_eq_refl,              *)
(*   real_mult_zero, real_mult_one, real_mult_comm), order faces from S07   *)
(*   (real_le_plus_compat, real_lt_zero_one, RealSetoid.real_lt_le_iff_req, *)
(*   RealSetoid.real_le_id_l, RealSetoid.real_le_id_r,                      *)
(*   RealSetoid.real_eq_plus_compat), right distributivity from S09         *)
(*   (real_distrib_r).                                                      *)
(* References.: Bishop-style constructive analysis. The universal face of   *)
(*   the Bishop order lets n pointwise certificates share one delta, so no  *)
(*   1/n splitting chain is needed -- the essential difference from the     *)
(*   plain-eps half-split family (compare UpReqStrictStepGen).              *)
(* Constructivity.: Set-layer statements (real_le_b is a Set-valued forall  *)
(*   type; conclusions leak zero Prop); zero assumption slots and zero open *)
(*   proofs (every proof ends in Qed; the three Print Assumptions at the    *)
(*   file tail must all report Closed under the global context); pure       *)
(*   term-mode explicit assembly (real_eq is not Id, rewrite is forbidden,  *)
(*   the whole chain walks real_eq_trans and the compat combinators).       *)
(* Build.: Rocq 9.1 direct invocation (toolchain env.sh of the same         *)
(*   source), every compile wrapped by the cpu_guard thermal protocol,      *)
(*   rocq c -native-compiler no -q.                                         *)

From Stdlib Require Import QArith.Qring.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpRealLeB.
Require Import UpRealLeB2.

(* ============================================================ *)
(* Part 1, S.1 self-standing length machine: lenR (Real layer, free of     *)
(*   the nat-bridge interface).                                            *)
(* ============================================================ *)

Fixpoint sumb_lenR (X : Type) (l : list X) : Real :=
  match l with
  | nil => real_zero
  | cons _ rest => real_plus real_one (sumb_lenR X rest)
  end.

(* ============================================================ *)
(* Part 1, S.2 length nonnegativity: 0 <= lenR l.                          *)
(*   Induction: the cons step 0 <= 1 + lenR rest goes through the (0+0 vs  *)
(*   0) setoid equality plus pointwise nonnegative add compatibility.      *)
(* ============================================================ *)

Lemma sumb_lenR_nonneg : forall (X : Type) (l : list X),
  real_le real_zero (sumb_lenR X l).
Proof.
  intros X l. induction l as [| w rest IH]; simpl.
  - apply real_le_refl.
  - apply (RealSetoid.real_le_id_l (real_plus real_zero real_zero) real_zero
                                   (real_plus real_one (sumb_lenR X rest))).
    + apply real_plus_zero.
    + apply (real_le_plus_compat real_zero real_one real_zero (sumb_lenR X rest)).
      * exact (RealSetoid.real_lt_le_iff_req real_zero real_one (inl real_lt_zero_one)).
      * exact IH.
Qed.

(* ============================================================ *)
(* Part 1, S.3 constant-sum collapse: the sum of the constant c equals     *)
(*   lenR l * c.                                                           *)
(*   Induction: the cons step c + sum_const rest == c + lenR rest * c (IH) *)
(*   == 1*c + lenR rest * c (unary reshaping) == (1 + lenR rest) * c       *)
(*   (distributivity).                                                     *)
(* ============================================================ *)

Lemma sumb_sum_const : forall (X : Type) (c : Real) (l : list X),
  real_eq (real_list_sum X (fun _ : X => c) l) (real_mult (sumb_lenR X l) c).
Proof.
  intros X c l. induction l as [| w rest IH]; simpl.
  - (* 0 == 0*c: via the c*0 middle term (mult_zero zeroes on the right; *)
    (* comm bridge) *)
    apply (real_eq_trans _ (real_mult c real_zero) _).
    + apply real_eq_sym. apply real_mult_zero.
    + apply real_mult_comm.
  - apply (real_eq_trans _
             (real_plus c (real_mult (sumb_lenR X rest) c)) _).
    + apply (RealSetoid.real_eq_plus_compat c
               (real_list_sum X (fun _ : X => c) rest)
               c
               (real_mult (sumb_lenR X rest) c)).
      * apply real_eq_refl.
      * exact IH.
    + apply (real_eq_trans _
               (real_plus (real_mult real_one c)
                          (real_mult (sumb_lenR X rest) c)) _).
      * apply (RealSetoid.real_eq_plus_compat c
                 (real_mult (sumb_lenR X rest) c)
                 (real_mult real_one c)
                 (real_mult (sumb_lenR X rest) c)).
        -- (* c == 1*c: c*1 == c (mult_one zeroes on the right) plus comm *)
           (* bridge *)
           apply (real_eq_trans _ (real_mult c real_one) _).
           ++ apply real_eq_sym. apply real_mult_one.
           ++ apply real_mult_comm.
        -- apply real_eq_refl.
      * (* (1*c)+(lenR*c) == (1+lenR)*c: distrib_r direct (same orientation, *)
        (* zero flipping) *)
        apply real_distrib_r.
Qed.

(* ============================================================ *)
(* Part 2, S.4 main piece: pointwise <=_B summation lifting (the n-ary     *)
(*   Bishop summation face).                                               *)
(*   sumb_list_sum_le_b: pointwise <=_B implies the sum <=_B.              *)
(*   Proof chain:                                                          *)
(*     given delta > 0: unfold the pointwise <=_B at one shared delta (no  *)
(*     1/n splitting: the universal face of real_le_b needs only n copies  *)
(*     of the same delta); lift each pointwise lt branch through the Or    *)
(*     encoding as a one-way bridge up to real_le (the Or encoding serves  *)
(*     as a one-way bridge only); real_list_sum_le lifts the order         *)
(*     order-preservingly: sum f <= sum (g+delta); sum (g+delta) == sum g  *)
(*     + sum (constant delta) == sum g + lenR*delta (the add + Part 1      *)
(*     sum_const, two reshaping steps); the nonnegative-coefficient        *)
(*     completer closes it in one step (C := lenR l, the nonnegativity     *)
(*     certificate = the Part 1 lenR_nonneg piece).                        *)
(* ============================================================ *)

Lemma sumb_list_sum_le_b : forall (X : Type) (f g : X -> Real) (l : list X),
  (forall w : X, real_le_b (f w) (g w)) ->
  real_le_b (real_list_sum X f l) (real_list_sum X g l).
Proof.
  intros X f g l H.
  (* Zero unfold: the completer conclusion matches the real_le_b shape *)
  (* directly (the outer delta universal face is consumed by the engine; *)
  (* the pointwise eps unification happens inside the universal position *)
  (* of the engine premise) *)
  apply (real_le_closure_b_nonneg
           (real_list_sum X f l)
           (real_list_sum X g l)
           (sumb_lenR X l)).
  - (* premise 1: 0 <= C := lenR l (the Part 1 piece) *)
    apply sumb_lenR_nonneg.
  - (* premise 2: forall eps > 0, sum f <= sum g + lenR * eps *)
    intros eps Heps.
    (* pointwise uniform eps: f w < g w + eps (the lt branch) lifted to *)
    (* real_le (the Or encoding inl one-way bridge) *)
    assert (Hpt : forall w : X, real_le (f w) (real_plus (g w) eps)).
    { intro w.
      exact (RealSetoid.real_lt_le_iff_req (f w) (real_plus (g w) eps)
               (inl (H w eps Heps))). }
    pose proof (real_list_sum_le X f (fun w : X => real_plus (g w) eps) l Hpt) as Hsum.
    (* reshape the right end: sum (g+eps) == sum g + sum (constant eps) *)
    (* == sum g + lenR * eps *)
    apply (RealSetoid.real_le_id_r
             (real_list_sum X f l)
             (real_list_sum X (fun w : X => real_plus (g w) eps) l)
             (real_plus (real_list_sum X g l)
                        (real_mult (sumb_lenR X l) eps))).
    + apply (real_eq_trans _
               (real_plus (real_list_sum X g l)
                          (real_list_sum X (fun _ : X => eps) l)) _).
      * apply (real_list_sum_add X g (fun _ : X => eps) l).
      * apply (RealSetoid.real_eq_plus_compat (real_list_sum X g l)
                 (real_list_sum X (fun _ : X => eps) l)
                 (real_list_sum X g l)
                 (real_mult (sumb_lenR X l) eps)).
        -- apply real_eq_refl.
        -- apply sumb_sum_const.
    + exact Hsum.
Qed.

(* ============================================================ *)
(*                                                                        *)
(* [Conclusion S1 | pointwise uniform eps] sumb_list_sum_le_b: provable,  *)
(*   and free of 1/n splitting. Root cause: real_le_b is a Set-valued     *)
(*   universal face (forall eps > 0); the n-ary summation completion      *)
(*   needs only one shared delta for every pointwise certificate -- the   *)
(*   n copies of delta merge into the right end and collapse to the sum   *)
(*   of the constant delta, accounted in one stroke by the sum_const      *)
(*   reshaping into lenR*delta. This differs in essence from the          *)
(*   plain-eps family eps/2 splitting chains (the leb2_half_add base      *)
(*   piece): the universal slack is naturally duplicable on the Bishop    *)
(*   face, with no constructive halving needed.                           *)
(* [Conclusion S2 | self-standing length machine] sumb_lenR: a three-line *)
(*   Real-layer Fixpoint, self-standing, with zero nat-bridge interface   *)
(*   use -- the nat embedding is self-carried; this design carries zero   *)
(*   nat numerals and walks Real induction throughout.                    *)
(* [Conclusion S3 | completer selection] the main piece takes the         *)
(*   nonnegative-coefficient completer (C := lenR l, the certificate      *)
(*   sumb_lenR_nonneg) -- strict positivity of lenR fails on the empty    *)
(*   list (lenR nil == 0), so the C>0 certificate route is unavailable;   *)
(*   exactly the spec scenario of real_le_closure_b_nonneg (UpRealLeB2);  *)
(*   the empty-list branch closes naturally through the completer C+1>0   *)
(*   certificate machining face, with zero case analysis.                 *)
(* [Conclusion S4 | Or-encoding usage boundary] the pointwise lifting     *)
(*   uses only the one-way bridge (the lt branch inl to real_le),         *)
(*   consistent with the boundary that the Or-form min counterexample is  *)
(*   unprovable -- this piece claims no Or-form pointwise premise         *)
(*   lifting.                                                             *)
(* [Catalog] the four-piece spec (lenR / lenR_nonneg / sum_const / main)  *)
(*   is all landed in this file; the sumb_ prefix is exclusive in the     *)
(*   library.                                                             *)
(* [Closure] all pieces Print Assumptions Closed (see the file tail).     *)
(*                                                                        *)
(* ============================================================ *)

Print Assumptions sumb_lenR_nonneg.
Print Assumptions sumb_sum_const.
Print Assumptions sumb_list_sum_le_b.
