(* UpAblD1S7_UpReqEntropyDeficitTemp.v -- single-point instance supply for the
   real entropy deficit temperature interface of UpReqEntropyDeficitTemp.v
   (Section RealEntropyDeficitTemp).
   Mission. Record, as one inductive datum, the nine statements of that section
   (S, real_sum_over_S, real_sum_pos_preserved, real_sum_over_S_ext,
   real_sum_over_S_linear, real_sum_over_S_add, T, T_pos, energy; source lines
   202-217, transcribed verbatim) and supply a witness: one constructor
   application fixes all nine slots at once.
   Dependencies. Stdlib List; the tree S-chain S01_BaseRing through
   S15_TailFEPUp, consumed read-only; no new Require, and the source module of
   the packed statements is deliberately not required (no mixed-generation
   object files).
   References. UpReqEntropyDeficitTemp.v, Section RealEntropyDeficitTemp; the
   sum_pos slot family precedent fa57_sum_carrier_realizes, which
   real_sum_pos_preserved follows by direct carrier instantiation.
   Constructivity. All slots are carried on Set: Real and its comparators
   real_lt, real_eq are Set-valued (S02_CauchyComplete), so the record is
   informative and extractable. The witness is the single-point instance
   S := unit, sum carrier fun f => f tt, T := real_one, energy := the zero
   function; T_pos is real_lt_zero_one (S07_RealSetoidExpLog); the linearity
   and extensionality slots are real_eq_refl (S02_CauchyComplete) at the single
   point. No classical reasoning; the closing Print Assumptions must report
   the theorem as closed under the global context. S is quantified by the
   inductive itself rather than by the constructor: a Type-valued constructor
   argument would be erased by the extractor, which would insert a cast at
   every application site of the witness; quantified by the inductive, the
   extracted type stays polymorphic and cast-free.
   Build. rocq c -native-compiler no -q -Q . "" (Rocq 9.1.0).
 *)
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

(* Pack record: the nine statements, transcribed verbatim. *)

Inductive uabd1s7_edt_pack9 (S : Type) : Type :=
| uabd1s7_edt_pack9_intro :
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
            uabd1s7_edt_pack9 S.

(* Single-point instance fixing all nine slots at once. *)

Theorem uabd1s7_edt_pack9_supplied : uabd1s7_edt_pack9 unit.
Proof.
  exact (uabd1s7_edt_pack9_intro unit           (fun (f : unit -> Real) => f tt)           (fun (f : unit -> Real)              (H : forall s : unit, real_lt real_zero (f s)) => H tt)           (fun (f g : unit -> Real)              (H : forall s : unit, real_eq (f s) (g s)) => H tt)           (fun (a : Real) (f : unit -> Real) => real_eq_refl (real_mult a (f tt)))           (fun (f g : unit -> Real) => real_eq_refl (real_plus (f tt) (g tt)))           real_one real_lt_zero_one           (fun _ : unit => real_zero)).
Qed.

(* Assumption audit. *)

Print Assumptions uabd1s7_edt_pack9_supplied.
