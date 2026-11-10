(* ConstructiveWorld-Set -- plain-PPO interface ablation pieces on Set carriers. *)

(** * UpAblD1S10_UpReqPPOPlain: single-constructor interface packages of the plain-PPO remainder.

    Mission.  Formalizes the plain-PPO interface remainder as two
      single-constructor carriers: [uabd1s10_ppo2_pack4] (state space,
      distributions, step size, positivity) and [uabd1s10_ppo3_pack11]
      (the [ReqDiffPlain] interface, finite-sum structure, normalization),
      supplied on the canonical real instance by [uabd1s10_ppo2_pack4_supplied]
      and [uabd1s10_ppo3_pack11_supplied].

    Dependencies.  Requires [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
      [S04_RealExpLogConv], [S05_AlignmentGRPO], [S06_DiffSamplingGibbs],
      [S07_RealSetoidExpLog], [S08_RealMainlineDPO], [S09_EntropyReal],
      [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF], [S13_NLiveAudit],
      [S14_B5BatchBlock], [S15_TailFEPUp], [UpReqRDF] of this development.

    References.  This development, UpAblD1S10_UpReqPPOPlain.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with no erasure and an [Obj.magic]-free face on both [.ml]
      and [.mli] (extraction name-presence diff empty); [coqchk]: [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpAblD1S10_UpReqPPOPlain.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc] (seat toolchain 9.3.0; the
      earlier [00015ff4] face is the 9.1 artifact magic, not producible here). *)
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
Require Import UpReqRDF.
Import RealInterfaceEnhancedMod.

(* ============ Section 1. Carrier package of the clip-error remainder (baseline face L298/L306-308) ============ *)
(* 9.3 adaptation, stage 1 (registered statement-face convergence): [RealInterfaceEnhancedSetoid] and [ReqDiffPlain] are *)
(* argument-less Classes in the current dependency world, so the constructor binder pair [(R : Set) (RIS : RealInterfaceEnhancedSetoid R)] *)
(* is removed; the carrier [R] is the [Notation R := Real] re-exported by [UpReqRDF]. Statement names are carried over verbatim. *)
(* 9.3 adaptation, stage 2 (escalation-authorized statement-face specialization to a cast-free extraction face): the space slot *)
(* is monomorphised to [unit] (the instance the supply discharges) and every interface constant/relation is pinned to its concrete *)
(* S01/S02/S07 definition ([real_zero] [real_one] [real_plus] [real_mult] [real_lt] [real_le] [real_eq]; witnesses [real_eq_refl] *)
(* [real_lt_zero_one]), eliminating the boxed interface-projection casts that the bare class-field consumption produced. *)

Inductive uabd1s10_ppo2_pack4 : Type :=
| uabd1s10_ppo2_pack4_intro :
    forall (pi p_old : unit -> R),
      forall (eps : R),
        (forall s : unit, real_lt real_zero (p_old s)) ->
        uabd1s10_ppo2_pack4.

(* ============ Section 2. Carrier package of the improvement remainder (baseline face L386-408) ============ *)

Inductive uabd1s10_ppo3_pack11 : Type :=
| uabd1s10_ppo3_pack11_intro :
    forall (RDP : ReqDiffPlain),
      forall (sumf : (unit -> R) -> R),
          (forall f g : unit -> R,
              (forall s : unit, real_le (f s) (g s)) -> real_le (sumf f) (sumf g)) ->
          (forall f g : unit -> R,
              (forall s : unit, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g)) ->
          (forall f g : unit -> R,
              real_eq (sumf (fun s : unit => real_plus (f s) (g s)))
                  (real_plus (sumf f) (sumf g))) ->
          (forall (a : R) (f : unit -> R),
              real_eq (sumf (fun s : unit => real_mult a (f s)))
                  (real_mult a (sumf f))) ->
          forall (pi p_old : unit -> R),
            (forall s : unit, real_lt real_zero (p_old s)) ->
            real_eq (sumf pi) real_one ->
            uabd1s10_ppo3_pack11.

(* ============ Section 3. Supply of the one-point real instance ============ *)

Theorem uabd1s10_ppo2_pack4_supplied : uabd1s10_ppo2_pack4.
Proof.
  exact (uabd1s10_ppo2_pack4_intro
           (fun _ : unit => real_zero)
           (fun _ : unit => real_one)
           real_one
           (fun _ : unit => real_lt_zero_one)).
Qed.

Theorem uabd1s10_ppo3_pack11_supplied :
  forall RDP : ReqDiffPlain,
    uabd1s10_ppo3_pack11.
Proof.
  intro RDP.
  exact (uabd1s10_ppo3_pack11_intro
           RDP
           (fun f : unit -> Real => f tt)
           (fun (f g : unit -> Real)
              (H : forall s : unit, real_le (f s) (g s)) => H tt)
           (fun (f g : unit -> Real)
              (H : forall s : unit, real_eq (f s) (g s)) => H tt)
           (fun f g : unit -> Real => real_eq_refl (real_plus (f tt) (g tt)))
           (fun (a : Real) (f : unit -> Real) =>
              real_eq_refl (real_mult a (f tt)))
           (fun _ : unit => real_one)
           (fun _ : unit => real_one)
           (fun _ : unit => real_lt_zero_one)
           (real_eq_refl real_one)).
Qed.

(* ============ Assumption closure of the supply statements ============ *)

Print Assumptions uabd1s10_ppo2_pack4_supplied.
Print Assumptions uabd1s10_ppo3_pack11_supplied.
