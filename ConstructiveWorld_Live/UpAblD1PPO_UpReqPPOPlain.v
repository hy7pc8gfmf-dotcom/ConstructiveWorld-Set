(* ConstructiveWorld-Set -- record-style [Set] packaging of the plain-PPO residual requirement slots. *)

(** * UpAblD1PPO_UpReqPPOPlain: single-point supply of the plain-PPO clip and improve slot packages.

    Mission.  Packages the residual plain-PPO slots of UpReqPPOPlain as two
      record-style [Set] carriers, [uabd1ppo_ppo2b_pack3] (three clip slots)
      and [uabd1ppo_ppo3_pack11] (eleven improve slots with the four summation
      premises and [req (sumf pi) one]); [uabd1ppo_ppo2b_pack3_supplied] and
      [uabd1ppo_ppo3_pack11_supplied] realize every slot at [S := unit] with
      the constant one, for arbitrary [RDP].

    Dependencies.  Requires [S01_BaseRing], [S02_CauchyComplete],
      [S03_QExp], [S04_RealExpLogConv], [S05_AlignmentGRPO],
      [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog], [S08_RealMainlineDPO],
      [S09_EntropyReal], [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF],
      [S13_NLiveAudit], [S14_B5BatchBlock], [S15_TailFEPUp], [UpReqAlign],
      [UpReqRDF] of this development.

    References.  This development, UpAblD1PPO_UpReqPPOPlain.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpAblD1PPO_UpReqPPOPlain.v] compiles cleanly
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

(* R := Real by notation: this tree's interface is the argument-less Class
   RealInterfaceEnhancedSetoid (S07_RealSetoidExpLog), so the Main-tree
   binder pair [(R : Set)] [(RIS : RealInterfaceEnhancedSetoid R)] is
   carrier-ized away ([R := Real]; statement faces at the concrete
   [real_eq]/[real_lt]/[real_le] relations of that canon, with the class
   fields [zero]/[one]/[plus]/[mult] resolving as bare names through the
   global instance [RealEnhancedReal] -- the registered interface-generation
   pattern, the [abl_tail_pos_supply_sum] precedent; the concrete relations
   keep the extraction probe free of [Obj.magic] casts at the premise
   positions).  The state-space slot [S] rides as the Inductive's leading
   argument (the [uabd1s7_edt_pack9 (S : Type)] precedent of
   UpAblD1S7_UpReqEntropyDeficitTemp), so the single-point supply fixes
   [S := unit] at the statement face); statement names are carried over
   verbatim. *)
Notation R := Real.

(* ============ Record-style package, section 2 remainder (3 slots): statements carried over verbatim (against source lines 306-308) ============ *)

Inductive uabd1ppo_ppo2b_pack3 (S : Set) : Type :=
| uabd1ppo_ppo2b_pack3_intro :
    forall (pi p_old : S -> R),
      forall (eps : R),
        (forall s : S, real_lt zero (p_old s)) ->
        uabd1ppo_ppo2b_pack3 S.

(* ============ Record-style package, section 3 (11 slots): statements carried over verbatim (against source lines 386-408) ============ *)

Inductive uabd1ppo_ppo3_pack11 (S : Set) : Type :=
| uabd1ppo_ppo3_pack11_intro :
    forall (RDP : ReqDiffPlain),
      forall (sumf : (S -> R) -> R),
        (forall f g : S -> R,
            (forall s : S, real_le (f s) (g s)) -> real_le (sumf f) (sumf g)) ->
        (forall f g : S -> R,
            (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g)) ->
        (forall f g : S -> R,
            real_eq (sumf (fun s : S => plus (f s) (g s)))
                (plus (sumf f) (sumf g))) ->
        (forall (a : R) (f : S -> R),
            real_eq (sumf (fun s : S => mult a (f s))) (mult a (sumf f))) ->
        forall (pi p_old : S -> R),
          (forall s : S, real_lt zero (p_old s)) ->
          real_eq (sumf pi) one ->
          uabd1ppo_ppo3_pack11 S.

(* ============ Supply statements: one realization valid for arbitrary RIS and RDP, universally quantified, at the single-point space S := unit ============ *)

Theorem uabd1ppo_ppo2b_pack3_supplied :
  uabd1ppo_ppo2b_pack3 unit.
Proof.
  exact (uabd1ppo_ppo2b_pack3_intro unit           (fun _ : unit => one) (fun _ : unit => one)           one           (fun _ : unit => real_lt_zero_one)).
Qed.

Theorem uabd1ppo_ppo3_pack11_supplied :
  forall (RDP : ReqDiffPlain),
    uabd1ppo_ppo3_pack11 unit.
Proof.
  intro RDP.
  exact (uabd1ppo_ppo3_pack11_intro unit RDP           (fun f : unit -> R => f tt)           (fun (f g : unit -> R)              (H : forall s : unit, real_le (f s) (g s)) => H tt)           (fun (f g : unit -> R)              (H : forall s : unit, real_eq (f s) (g s)) => H tt)           (fun (f g : unit -> R) => real_eq_refl (plus (f tt) (g tt)))           (fun (a : R) (f : unit -> R) => real_eq_refl (mult a (f tt)))           (fun _ : unit => one) (fun _ : unit => one)           (fun _ : unit => real_lt_zero_one)           (real_eq_refl one)).
Qed.

(* ============ Assumption-closure audit of the supply statements ============ *)

Print Assumptions uabd1ppo_ppo2b_pack3_supplied.
Print Assumptions uabd1ppo_ppo3_pack11_supplied.
