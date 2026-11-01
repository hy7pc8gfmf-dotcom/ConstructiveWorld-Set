(* UpAblD1S7_UpReqEntropyUniqueTemp.v -- data-supply pack, entropy and temperature. *)
(*                                                                                  *)
(* Mission. Carry verbatim the statement face of a data-supply bundle over an       *)
(*   abstract carrier S: a summation functor real_sum_over_S with positivity        *)
(*   (pointwise positive data give a positive sum), extensionality up to            *)
(*   pointwise real_eq, scalar linearity over real_mult, and additivity over        *)
(*   real_plus; a temperature T with real_lt real_zero T; and an energy             *)
(*   function. One supply theorem instantiates every component on the               *)
(*   single-point carrier S := unit.                                                *)
(* Dependencies. Stdlib List; the declared Require face S01_BaseRing through        *)
(*   S15_TailFEPUp, all in-tree; the proof term consumes S02 real_eq/               *)
(*   real_lt/real_zero/real_one/real_plus/real_mult/real_eq_refl and S07            *)
(*   real_lt_zero_one.                                                              *)
(* References. The interface of a finite-temperature data-supply package: a         *)
(*   positivity-preserving, extensional, scalar-linear and additive sum             *)
(*   functor over a finite carrier, with a positive temperature and an energy       *)
(*   function -- the standard shape of a partition-function package; the            *)
(*   single-point instance realizes the trivial carrier of that interface.          *)
(* Constructivity. All statements ride Set-level exit faces (real_eq/               *)
(*   real_lt); no classical reasoning. The instance is S := unit, sum               *)
(*   (fun f => f tt), T := real_one with real_lt_zero_one, zero energy:             *)
(*   positivity and extensionality reduce to evaluation at tt; linearity and        *)
(*   additivity close by real_eq_refl; the theorem is one explicit term             *)
(*   ending in Qed, and Print Assumptions reports Closed under the global           *)
(*   context.                                                                       *)
(* Build. rocq c -native-compiler no -q -Q . "" UpAblD1S7_UpReqEntropyUniqueTemp.v  *)
(*   (every compile wrapped by the thermal-guard protocol of the CI).               *)

From Stdlib Require Import List.
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

(* ============ Pack (record-style): section statement face, carried verbatim ============ *)

Inductive uabd1s7_eut_pack9 (S : Type) : Type :=
| uabd1s7_eut_pack9_intro :
    forall real_sum_over_S : (S -> Real) -> Real,
        (forall (f : S -> Real),
            (forall s : S, real_lt real_zero (f s)) ->
            real_lt real_zero (real_sum_over_S f)) ->
        (forall (f g : S -> Real),
            (forall s : S, real_eq (f s) (g s)) ->
            real_eq (real_sum_over_S f) (real_sum_over_S g)) ->
        (forall (a : Real) (f : S -> Real),
            real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
                    (real_mult a (real_sum_over_S f))) ->
        (forall (f g : S -> Real),
            real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
                    (real_plus (real_sum_over_S f) (real_sum_over_S g))) ->
        forall T : Real,
          forall T_pos : real_lt real_zero T,
          forall energy : S -> Real,
            uabd1s7_eut_pack9 S.

(* ============ Supply theorem: one single-point instance for the pack ============ *)

Theorem uabd1s7_eut_pack9_supplied : uabd1s7_eut_pack9 unit.
Proof.
  exact (uabd1s7_eut_pack9_intro unit           (fun (f : unit -> Real) => f tt)           (fun (f : unit -> Real)              (H : forall s : unit, real_lt real_zero (f s)) => H tt)           (fun (f g : unit -> Real)              (H : forall s : unit, real_eq (f s) (g s)) => H tt)           (fun (a : Real) (f : unit -> Real) => real_eq_refl (real_mult a (f tt)))           (fun (f g : unit -> Real) => real_eq_refl (real_plus (f tt) (g tt)))           real_one real_lt_zero_one           (fun _ : unit => real_zero)).
Qed.

(* ============ Assumption audit ============ *)

Print Assumptions uabd1s7_eut_pack9_supplied.
