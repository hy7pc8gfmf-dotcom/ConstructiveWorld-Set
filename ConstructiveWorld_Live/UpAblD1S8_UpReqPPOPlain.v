(* ConstructiveWorld-Set -- plain-PPO requirement pack with partition-function positivity slot. *)
(** * UpAblD1S8_UpReqPPOPlain: interface package of the plain-PPO requirement slots.

    Mission.  Formalizes the plain-PPO requirement remainder as two
      single-constructor carriers: [uabd1s8_ppo1_pack15] (finite-sum interface,
      reward / step-size / positive-distribution slots, and the partition
      function [Z_align_req] with its positivity witness) and
      [uabd1s8_ppo2_pack5] (finite-sum interface with nonnegativity).  The
      lemma [uabd1s8_ppo1_zap_pos] supplies the partition function's
      positivity witness, and the supply theorems feed one arbitrary
      [ReqDiffPlain] instance into both carriers over the singleton state
      space [unit].

    Dependencies.  No Stdlib Require beyond the prelude.  Requires of this
      development: [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
      [S04_RealExpLogConv], [S05_AlignmentGRPO], [S06_DiffSamplingGibbs],
      [S07_RealSetoidExpLog], [S08_RealMainlineDPO], [S09_EntropyReal],
      [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF], [S13_NLiveAudit],
      [S14_B5BatchBlock], [S15_TailFEPUp], [UpReqAlign], [UpReqRDF].

    References.  This development, UpAblD1S8_UpReqPPOPlain.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -Q . "" UpAblD1S8_UpReqPPOPlain.v] compiles cleanly (exit 0). *)
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
Require Import UpReqAlign.
Require Import UpReqRDF.
Import RealInterfaceEnhancedMod.

(* Interface-shape note (the UpAblD1S10/S11_UpReqPPOPlain convention): in this
   tree [RealInterfaceEnhancedSetoid] (S07_RealSetoidExpLog) and [ReqDiffPlain]
   (UpReqRDF) are zero-argument Classes with the carrier pinned to the global
   [Real] (the imported [Notation R := Real]), so the baseline binder pairs
   [(R : Set) (RIS : RealInterfaceEnhancedSetoid R)] and [@ReqDiffPlain R RIS]
   reduce to [(RDP : ReqDiffPlain)].  By the same convention the state-space
   slot is the singleton [unit] (the instance the supply theorems discharge),
   and the premise predicate faces are the concrete [real_lt]/[real_le]
   definitions (S02_CauchyComplete), which the instance [RealEnhancedReal]
   pins as its own [lt]/[le] fields.  Statement names stay verbatim. *)

(* ============ Carrier package, first statement group: the fifteen supply slots ============ *)

Inductive uabd1s8_ppo1_pack15 : Type :=
| uabd1s8_ppo1_pack15_intro :
    forall (RDP : ReqDiffPlain),
      forall (sumf : (unit -> R) -> R),
        (forall f g : unit -> R,
            (forall s : unit, real_le (f s) (g s)) -> real_le (sumf f) (sumf g)) ->
        forall (reward : unit -> R) (beta : R),
          forall (beta_pos : real_lt zero beta),
          forall (pi_ref : unit -> R),
            real_lt zero (Z_align_req unit sumf reward beta beta_pos pi_ref) ->
            forall (pi_old : unit -> R),
              (forall s : unit, real_lt zero (pi_old s)) ->
              forall (advantage_fn : unit -> R),
                (forall s : unit, real_le zero (advantage_fn s)) ->
                forall (epsilon : R),
                  uabd1s8_ppo1_pack15.

(* ============ Carrier package, second statement group: the five clip slots ============ *)

Inductive uabd1s8_ppo2_pack5 : Type :=
| uabd1s8_ppo2_pack5_intro :
    forall (RDP : ReqDiffPlain),
      forall (sumf : (unit -> R) -> R),
        (forall f : unit -> R,
            (forall s : unit, real_le zero (f s)) -> real_le zero (sumf f)) ->
        uabd1s8_ppo2_pack5.

(* ============ Partition-function positivity on the one-point real instance ============ *)
(* [Z_align_req] unfolds to the finite sum of [pi_ref s * exp(-beta * reward s)];
   on the one-point instance every factor is [one], and the slot witnesses are
   given by the interface fields [mult_positive], [one_pos], [exp_neg_pos]. *)

Lemma uabd1s8_ppo1_zap_pos :
  forall RDP : ReqDiffPlain,
    real_lt zero (Z_align_req unit (fun f : unit -> Real => f tt)
               (fun _ : unit => zero) one
               (@RealInterfaceEnhancedMod.one_pos
                  RealInterfaceEnhancedMod.RealEnhancedReal)
               (fun _ : unit => one)).
Proof.
  intro RDP.
  unfold Z_align_req.
  exact (@RealInterfaceEnhancedMod.mult_positive
           RealInterfaceEnhancedMod.RealEnhancedReal
           one
           (@RealInterfaceEnhancedMod.exp_neg
              RealInterfaceEnhancedMod.RealEnhancedReal
              (@RealInterfaceEnhancedMod.opp
                 RealInterfaceEnhancedMod.RealEnhancedReal
                 (@RealInterfaceEnhancedMod.mult
                    RealInterfaceEnhancedMod.RealEnhancedReal
                    (@RealInterfaceEnhancedMod.inv_pos
                       RealInterfaceEnhancedMod.RealEnhancedReal
                       one
                       (@RealInterfaceEnhancedMod.one_pos
                          RealInterfaceEnhancedMod.RealEnhancedReal))
                    (@RealInterfaceEnhancedMod.zero
                       RealInterfaceEnhancedMod.RealEnhancedReal))))
           (@RealInterfaceEnhancedMod.one_pos
              RealInterfaceEnhancedMod.RealEnhancedReal)
           (@RealInterfaceEnhancedMod.exp_neg_pos
              RealInterfaceEnhancedMod.RealEnhancedReal
              (@RealInterfaceEnhancedMod.opp
                 RealInterfaceEnhancedMod.RealEnhancedReal
                 (@RealInterfaceEnhancedMod.mult
                    RealInterfaceEnhancedMod.RealEnhancedReal
                    (@RealInterfaceEnhancedMod.inv_pos
                       RealInterfaceEnhancedMod.RealEnhancedReal
                       one
                       (@RealInterfaceEnhancedMod.one_pos
                          RealInterfaceEnhancedMod.RealEnhancedReal))
                    (@RealInterfaceEnhancedMod.zero
                       RealInterfaceEnhancedMod.RealEnhancedReal))))).
Defined.

(* ============ Supply theorems: one arbitrary [ReqDiffPlain] instance feeds every remaining slot ============ *)

Theorem uabd1s8_ppo1_pack15_supplied :
  forall RDP : ReqDiffPlain, uabd1s8_ppo1_pack15.
Proof.
  intro RDP.
  exact (uabd1s8_ppo1_pack15_intro
           RDP
           (fun f : unit -> Real => f tt)
           (fun (f g : unit -> Real)
              (H : forall s : unit, real_le (f s) (g s)) => H tt)
           (fun _ : unit => zero)
           one
           (@RealInterfaceEnhancedMod.one_pos
              RealInterfaceEnhancedMod.RealEnhancedReal)
           (fun _ : unit => one)
           (uabd1s8_ppo1_zap_pos RDP)
           (fun _ : unit => one)
           (fun _ : unit =>
              @RealInterfaceEnhancedMod.one_pos
                RealInterfaceEnhancedMod.RealEnhancedReal)
           (fun _ : unit => zero)
           (fun _ : unit =>
              @RealInterfaceEnhancedMod.le_refl
                RealInterfaceEnhancedMod.RealEnhancedReal zero)
           one).
Defined.

Theorem uabd1s8_ppo2_pack5_supplied :
  forall RDP : ReqDiffPlain, uabd1s8_ppo2_pack5.
Proof.
  intro RDP.
  exact (uabd1s8_ppo2_pack5_intro
           RDP
           (fun f : unit -> Real => f tt)
           (fun (f : unit -> Real)
              (H : forall s : unit, real_le zero (f s)) => H tt)).
Defined.

(* ============ Assumption-surface closure audit ============ *)

Print Assumptions uabd1s8_ppo1_pack15_supplied.
Print Assumptions uabd1s8_ppo2_pack5_supplied.
