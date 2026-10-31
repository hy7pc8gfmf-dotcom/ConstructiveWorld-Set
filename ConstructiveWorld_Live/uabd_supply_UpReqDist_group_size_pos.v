(* ========================================================================= *)
(*  uabd_supply_UpReqDist_group_size_pos.v - positivity of the nat counting  *)
(*  embedding behind the GRPO group size (UpReqDist ReqGRPO companion).      *)
(* ========================================================================= *)
(*  Mission. UpReqDist carries the GRPO group size by reqd_group_size :=     *)
(*  length group_enum with the constructive counting embedding reqd_of_nat   *)
(*  from nat into the ordered carrier (0 maps to zero, S n maps to one plus  *)
(*  the embedding of n). The positivity slot real_lt zero (reqd_of_nat       *)
(*  (length enum)) holds under an InT witness that the enumeration contains  *)
(*  element. Two theorems: uabd_reqd_nat_S_pos (the S k-shaped embedding is  *)
(*  strictly positive, by induction on k: the base reshapes one plus zero    *)
(*  back to one and closes with one_pos, the step composes two positives     *)
(*  with plus_positive) and uabd_reqd_len_pos_cover (the cover-witness form, *)
(*  by induction on the InT derivation: both constructors are cons-shaped,   *)
(*  the length is S-shaped, both cases reduce to the first theorem).         *)
(*  Dependencies. S01_BaseRing (InT), S07_RealSetoidExpLog (the              *)
(*  RealInterfaceEnhancedSetoid class), UpReqDist (reqd_of_nat), Stdlib List.*)
(*  References. EpsOptimalReach reqd_of_nat_pos (Not(Id l nil) negative      *)
(*  antecedent form) and NatLenPos nlp_len_pos_cover (real_of_nat cover      *)
(*  witness); an independent slot of the same shape over the counting        *)
(*  embedding, coexisting with the in-library pieces above.                  *)
(*  Constructivity. The statement face is carried entirely by Set: real_lt   *)
(*  is the Set-valued order of the interface carrier (the lt field of the    *)
(*  RealInterfaceEnhancedSetoid instance is this same predicate), InT a      *)
(*  relation; both proofs are genuine constructions ending in Qed, no opaque *)
(*  placeholders, no classical logic; the tail runs Print Assumptions per    *)
(*  statement with Closed as the criterion.                                  *)
(*  Build. rocq c -native-compiler no -q -Q . ""                             *)
(*  uabd_supply_UpReqDist_group_size_pos.v                                   *)
(* ========================================================================= *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import UpReqDist.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.
(* The interface class in this tree is unparameterized; its carrier is the global Real. *)
Notation R := Real.

Section uabdReqGrpSupply.

(* (1) the S k-shaped embedding is strictly positive (induction on k) *)
Lemma uabd_reqd_nat_S_pos :
  forall k : nat, real_lt zero (UpReqDist.reqd_of_nat (Datatypes.S k)).
Proof.
  intro k. induction k as [| k IH].
  - (* base: reqd_of_nat 1 reduces to one plus zero; reshape back to one, then one_pos *)
    apply (lt_id_r zero one (UpReqDist.reqd_of_nat 1)).
    + apply (req_trans one (plus one zero) (UpReqDist.reqd_of_nat 1)).
      * apply (req_sym (plus one zero) one). apply plus_zero.
      * apply req_refl.
    + exact one_pos.
  - (* step: reqd_of_nat (S (S k)) reduces to one plus reqd_of_nat (S k); compose the two positives *)
    apply (lt_id_r zero (plus one (UpReqDist.reqd_of_nat (Datatypes.S k)))
                      (UpReqDist.reqd_of_nat (Datatypes.S (Datatypes.S k)))).
    + apply req_refl.
    + apply plus_positive.
      * exact one_pos.
      * exact IH.
Qed.

(* (2) the cover-witness form: induction on the InT derivation (both constructors cons-shaped, no empty match) *)
Theorem uabd_reqd_len_pos_cover :
  forall (G : Set) (enum : list G),
    (forall i : G, InT i enum) ->
    forall g0 : G,
      real_lt zero (UpReqDist.reqd_of_nat (Datatypes.length enum)).
Proof.
  intros G enum cover g0.
  induction (cover g0) as [l0 | y l0 Hin IH].
  - exact (uabd_reqd_nat_S_pos (Datatypes.length l0)).
  - exact (uabd_reqd_nat_S_pos (Datatypes.length l0)).
Qed.

End uabdReqGrpSupply.

Print Assumptions uabd_reqd_nat_S_pos.
Print Assumptions uabd_reqd_len_pos_cover.
