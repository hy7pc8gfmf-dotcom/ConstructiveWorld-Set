(* ConstructiveWorld-Set — enumerated-instance discharge of the TempEntropy sumf interface face. *)

(** * UpAblT1_UpReqTempEntropy: interface-slot discharge theorems for the
      sumf face of the [ReqTempEntropy] section, resolved at the concrete
      finite-sum instance [sumd_sumf] of [UpReqSumD].

    Mission.  The six interface assumptions of the [ReqTempEntropy] sumf
      face ([fsum_ext] / [fsum_add] / [fsum_linear] / [fsum_pos] /
      [fsum_le] / [fsum_zero_nonneg]) hold unconditionally at the
      concrete enumerated finite-sum instance; the assumption slots
      reduce to pure data slots (the enumeration list); six stations
      [uabT1_rte_fsum_*] in source order.

    Dependencies.  Requires [S01_BaseRing] through [S15_TailFEPUp] and
      [UpReqSumD] (via which the discharge lemmas [sumd_sum_*] carry the
      content) of this development; interface = the argument-less Class
      [RealInterfaceEnhancedSetoid] (module [RealInterfaceEnhancedMod]).

    References.  This development, UpAblT1_UpReqTempEntropy.v, the
      baseline module in ConstructiveWorld-Main whose statement names
      are carried over here verbatim (statement-face Set-carrier
      completion).  Adaptation = binder-shell removal + notation
      rebinding + supply-face convergence on this development's own
      precedent (the source argumented Class applications raised
      "Illegal application (Non-functional construction)"): the binder
      pair [(R : Set)] [{RIS : RealInterfaceEnhancedSetoid R}] is
      removed from every station, [R := Real] by notation (UpReqSumD.v
      L58), and the predicate faces follow the discharge lemmas' own
      faces exactly ([real_eq]/[real_lt]/[real_le], UpReqSumD.v L113-114),
      so the extraction face converges; the nonemptiness slot of
      [fsum_pos] keeps its source shape ([Not (enum = nil)], the host
      [sumd_sum_pos] datum face).

    Constructivity.  All Set-layer statements; every station closed by
      [Qed], zero admitted items; the nontrivial content lives in the
      discharge lemmas, the list-induction chains [sumd_list_sum_*],
      consumed directly; tail [Print Assumptions] report the closure
      face; no new axioms.

    Build.  [coqc -native-compiler no -q -Q . ""
      UpAblT1_UpReqTempEntropy.v] compiles cleanly (exit 0); the first
      eight bytes of the artifact are [436f7121 00015ff4]. *)

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
Require Import UpReqSumD.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* R := Real by notation: the argument-less Class fields resolve through
   the global Real instance (UpReqSumD.v L58 precedent). *)
Notation R := Real.

(* F1 ←L47 fsum_ext (verbatim slot: pointwise equality transports to the sums) *)
Theorem uabT1_rte_fsum_ext :
  forall (S : Set) (enum : list S) (f g : S -> R),
    (forall s : S, real_eq (f s) (g s)) -> real_eq (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros S enum f g H.
  exact (sumd_sum_ext S enum f g H).
Qed.

(* F2 ←L49 fsum_add *)
Theorem uabT1_rte_fsum_add :
  forall (S : Set) (enum : list S) (f g : S -> R),
    real_eq (sumd_sumf S enum (fun s : S => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g)).
Proof.
  intros S enum f g.
  exact (sumd_sum_add S enum f g).
Qed.

(* F3 ←L52 fsum_linear *)
Theorem uabT1_rte_fsum_linear :
  forall (S : Set) (enum : list S) (a : R) (f : S -> R),
    real_eq (sumd_sumf S enum (fun s : S => mult a (f s))) (mult a (sumd_sumf S enum f)).
Proof.
  intros S enum a f.
  exact (sumd_sum_linear S enum a f).
Qed.

(* F4 ←L55 fsum_pos (nonempty-enum slot explicit, sumd_sum_pos same shape) *)
Theorem uabT1_rte_fsum_pos :
  forall (S : Set) (enum : list S),
    Not (enum = nil) ->
    forall f : S -> R,
      (forall s : S, real_lt zero (f s)) -> real_lt zero (sumd_sumf S enum f).
Proof.
  intros S enum Hne f H.
  exact (sumd_sum_pos S enum f Hne H).
Qed.

(* F5 ←L57 fsum_le *)
Theorem uabT1_rte_fsum_le :
  forall (S : Set) (enum : list S) (f g : S -> R),
    (forall s : S, real_le (f s) (g s)) -> real_le (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros S enum f g H.
  exact (sumd_sum_le S enum f g H).
Qed.

(* F6 ←L59 fsum_zero_nonneg (surjective-data slot explicit, member-indexed form) *)
Theorem uabT1_rte_fsum_zero_nonneg :
  forall (S : Set) (enum : list S),
    (forall s : S, sumd_in S s enum) ->
    forall f : S -> R,
      (forall s : S, real_le zero (f s)) -> real_eq (sumd_sumf S enum f) zero ->
      forall s : S, real_eq (f s) zero.
Proof.
  intros S enum Hsurj f Hnn H0 s.
  exact (sumd_sum_zero_nonneg_surj S enum f Hsurj Hnn H0 s).
Qed.

(* ============ PA tail (per-station Closed reading) ============ *)
Print Assumptions uabT1_rte_fsum_ext.
Print Assumptions uabT1_rte_fsum_add.
Print Assumptions uabT1_rte_fsum_linear.
Print Assumptions uabT1_rte_fsum_pos.
Print Assumptions uabT1_rte_fsum_le.
Print Assumptions uabT1_rte_fsum_zero_nonneg.
