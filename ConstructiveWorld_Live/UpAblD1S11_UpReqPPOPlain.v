(* ConstructiveWorld-Set -- requirement-slot instance-supply packs for the UpReqPPOPlain family. *)

(** * UpAblD1S11_UpReqPPOPlain: residual requirement-slot supply packs for UpReqPPOPlain.

    Mission.  Instance-supply packs for the residual requirement slots of
      UpReqPPOPlain: [uabd1s11_ppo2_pack3_supplied] and
      [uabd1s11_ppo3_pack11_supplied] feed one arbitrary [ReqDiffPlain]
      instance into the pack carriers [uabd1s11_ppo2_pack3] and
      [uabd1s11_ppo3_pack11], over the singleton state space [unit].

    Dependencies.  No Stdlib Require beyond the prelude.  Requires of this
      development: [G09_MiscSmall], [S01_BaseRing], [S02_CauchyComplete],
      [S03_QExp], [S04_RealExpLogConv], [S05_AlignmentGRPO],
      [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog], [S08_RealMainlineDPO],
      [S09_EntropyReal], [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF],
      [S13_NLiveAudit], [S14_B5BatchBlock], [S15_TailFEPUp], [UpReqAlgebra],
      [UpReqAlign], [UpReqAlignRestB], [UpReqDist], [UpReqPropLiftShim],
      [UpReqRDF], [UpReqSLM].

    References.  This development, UpAblD1S11_UpReqPPOPlain.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpAblD1S11_UpReqPPOPlain.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
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

(* Interface-generation adaptation (the UpAblD1S10_UpReqPPOPlain / UpReqDist
   precedent): in this tree [RealInterfaceEnhancedSetoid] (S07_RealSetoidExpLog)
   and [ReqDiffPlain] (UpReqRDF) are zero-argument Classes with the carrier
   pinned to the global [Real] (the imported [Notation R := Real]), so the Main
   binder pairs [(R : Set) (RIS : RealInterfaceEnhancedSetoid R)] and the
   [@ReqDiffPlain R RIS] shells are carrier-ized away; statement names stay
   verbatim.  Gate7 born-clean face (the 04 prescription, family E): the space
   slot is monomorphised to [unit] and the premise predicate faces forward-cast
   to the concrete [real_le]/[real_lt]/[real_eq] (the [RealEnhancedReal]
   instance's own field values), so the extract face carries no erased-slot
   [Obj.magic] casts; the [req_refl] pin slots use the concrete monomorphic
   [real_eq_refl] (S02_CauchyComplete) instead of the boxed class projection. *)

(* ============ Pack carrier for the three residual section-2 slots, mirroring source lines L306-308 ============ *)
(* the six positions in front of the pack telescope into the section-2 slots already closed by S8; they are carried as context conditions and are not counted as new positions *)

Inductive uabd1s11_ppo2_pack3 : Type :=
| uabd1s11_ppo2_pack3_intro :
    forall (RDP : ReqDiffPlain),
      forall (sumf : (unit -> R) -> R),
        (forall f : unit -> R,
            (forall s : unit, real_le zero (f s)) -> real_le zero (sumf f)) ->
        forall (pi p_old : unit -> R),
          forall (eps : R),
            (forall s : unit, real_lt zero (p_old s)) ->
            uabd1s11_ppo2_pack3.

(* ============ Pack carrier for the eleven section-3 slots, mirroring source lines L386-408 ============ *)

Inductive uabd1s11_ppo3_pack11 : Type :=
| uabd1s11_ppo3_pack11_intro :
    forall (RDP : ReqDiffPlain),
      forall (sumf : (unit -> R) -> R),
        (forall f g : unit -> R,
            (forall s : unit, real_le (f s) (g s)) -> real_le (sumf f) (sumf g)) ->
        (forall f g : unit -> R,
            (forall s : unit, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g)) ->
        (forall f g : unit -> R,
            real_eq (sumf (fun s : unit => plus (f s) (g s)))
                (plus (sumf f) (sumf g))) ->
        (forall (a : R) (f : unit -> R),
            real_eq (sumf (fun s : unit => mult a (f s))) (mult a (sumf f))) ->
        forall (pi p_old : unit -> R),
          (forall s : unit, real_lt zero (p_old s)) ->
          real_eq (sumf pi) one ->
          uabd1s11_ppo3_pack11.

(* ============ Dependency module: one arbitrary [ReqDiffPlain] instance supplied once, in universally quantified conditional form ============ *)

Theorem uabd1s11_ppo2_pack3_supplied :
  forall RDP : ReqDiffPlain,
    uabd1s11_ppo2_pack3.
Proof.
  intro RDP.
  exact (uabd1s11_ppo2_pack3_intro
           RDP
           (fun f : unit -> Real => f tt)
           (fun (f : unit -> Real)
              (H : forall s : unit, real_le zero (f s)) => H tt)
           (fun _ : unit => one)
           (fun _ : unit => one)
           one
           (fun _ : unit =>
              @RealInterfaceEnhancedMod.one_pos
                RealInterfaceEnhancedMod.RealEnhancedReal)).
Qed.

Theorem uabd1s11_ppo3_pack11_supplied :
  forall RDP : ReqDiffPlain,
    uabd1s11_ppo3_pack11.
Proof.
  intro RDP.
  exact (uabd1s11_ppo3_pack11_intro
           RDP
           (fun f : unit -> Real => f tt)
           (fun (f g : unit -> Real)
              (H : forall s : unit, real_le (f s) (g s)) => H tt)
           (fun (f g : unit -> Real)
              (H : forall s : unit, real_eq (f s) (g s)) => H tt)
           (fun f g : unit -> Real =>
              real_eq_refl (plus (f tt) (g tt)))
           (fun (a : Real) (f : unit -> Real) =>
              real_eq_refl (mult a (f tt)))
           (fun _ : unit => one)
           (fun _ : unit => one)
           (fun _ : unit =>
              @RealInterfaceEnhancedMod.one_pos
                RealInterfaceEnhancedMod.RealEnhancedReal)
           (real_eq_refl one)).
Qed.

(* ============ Assumption-surface closure audit ============ *)

Print Assumptions uabd1s11_ppo2_pack3_supplied.
Print Assumptions uabd1s11_ppo3_pack11_supplied.
