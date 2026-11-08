(* ConstructiveWorld-Set -- constructive analysis over Q with every statement face carried by [Set]. *)

(** * u5c_dm_escape_discharge: premise-free escape instances of [dmec_escape_to_dist_any] at the Newton sequences of the square roots of 2 and 3.

    Mission.  Supply instances of the escape lemma [dmec_escape_to_dist_any]
      for the Newton sequences of the square roots of 2 and 3:
      [dmec_escape_to_dist_any_ir2] and [dmec_escape_to_dist_any_is3].  The
      tail-bound and vanish premises of the general lemma are resolved at
      each instance by [ir2_tail], [ir2_vanish], [is3_tail] and
      [is3_vanish]; each discharge adds no premises of its own.

    Dependencies.  Requires [S01_BaseRing], [S02_CauchyComplete],
      [S03_QExp], [SumInvFactEscape], [UpReqBanachNormOpp],
      [UpReqIrrationalCriterion], [UpReqSqrt3Irrational] and
      [u5c_dm_escape_to_dist_any] of this development.  Stdlib:
      [QArith.QArith], [QArith.Qabs], [ZArith.ZArith], [Arith.Arith],
      [Bool.Bool], [Setoid], [Morphisms] and [Qfield].

    References.  This development, u5c_dm_escape_discharge.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" u5c_dm_escape_discharge.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import SumInvFactEscape.
Require Import UpReqBanachNormOpp.
Require Import UpReqIrrationalCriterion.
Require Import UpReqSqrt3Irrational.
Require Import u5c_dm_escape_to_dist_any.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.
From Stdlib Require Import Setoid Morphisms Qfield.

(* ================== Section 1. Newton sequence of sqrt 2 ================== *)
(* The supply lemmas [ir2_tail] and [ir2_vanish] resolve the tail-bound and
   vanish premises [Ht] and [Hv] of the general lemma at this instance. *)
(* ========================================================================== *)

Lemma dmec_escape_to_dist_any_ir2 :
  forall (q : Q) (n0 : nat), (1 <= n0)%nat ->
    QltT (ir2_e n0) (Qabs ((q - ir2_x n0)%Q)) ->
    forall c : Q, QltT 0 c ->
    QleT' ((c + c)%Q) ((Qabs ((q - ir2_x n0)%Q) - ir2_e n0)%Q) ->
    sigT (fun c' : Q => And (QltT 0 c')
      (real_lt (real_const c')
         (real_metric (existT (fun u : Qseq => cauchy u) ir2_x
                          (lic_seq_cauchy ir2_x ir2_e ir2_tail ir2_vanish))
                      (real_const q)))).
Proof.
  intros q n0 Hn01 Hesc c Hc0 Hmarg.
  exact (dmec_escape_to_dist_any ir2_x ir2_e ir2_tail ir2_vanish
           q n0 Hn01 Hesc c Hc0 Hmarg).
(* The witness stays transparent under [Defined] so downstream consumers can
   compute with the [sigT] component in Qeq-determined assembly. *)
Defined.

(* ================== Section 2. Newton sequence of sqrt 3 ================== *)
(* The supply lemmas [is3_tail] and [is3_vanish] resolve the tail-bound and
   vanish premises [Ht] and [Hv], in the same way as in Section 1. *)
(* ========================================================================== *)

Lemma dmec_escape_to_dist_any_is3 :
  forall (q : Q) (n0 : nat), (1 <= n0)%nat ->
    QltT (is3_e n0) (Qabs ((q - is3_x n0)%Q)) ->
    forall c : Q, QltT 0 c ->
    QleT' ((c + c)%Q) ((Qabs ((q - is3_x n0)%Q) - is3_e n0)%Q) ->
    sigT (fun c' : Q => And (QltT 0 c')
      (real_lt (real_const c')
         (real_metric (existT (fun u : Qseq => cauchy u) is3_x
                          (lic_seq_cauchy is3_x is3_e is3_tail is3_vanish))
                      (real_const q)))).
Proof.
  intros q n0 Hn01 Hesc c Hc0 Hmarg.
  exact (dmec_escape_to_dist_any is3_x is3_e is3_tail is3_vanish
           q n0 Hn01 Hesc c Hc0 Hmarg).
(* As in Section 1, the witness stays transparent under [Defined]. *)
Defined.

Print Assumptions dmec_escape_to_dist_any_ir2.
Print Assumptions dmec_escape_to_dist_any_is3.
