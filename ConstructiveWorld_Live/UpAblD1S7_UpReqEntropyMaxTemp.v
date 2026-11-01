(* UpAblD1S7_UpReqEntropyMaxTemp.v - data-supply package for the real
   entropy-maximum development (Section RealEntropyMaxTemp of the upstream
   file UpReqEntropyMaxTemp.v).

   Mission.  Package the ten-statement data-supply interface of that section
     as one informative record: a summation operator over an arbitrary sample
     space is positive on pointwise-positive profiles, respects pointwise
     equality and pointwise ordering, is linear under scalar multiplication,
     and is additive over pointwise sums; the record also carries a positive
     temperature, its positivity witness, and an energy profile.  One witness
     theorem supplies all ten slots at once.
   Dependencies.  Stdlib List; registered tree modules S01_BaseRing through
     S15_TailFEPUp (read-only; the import face is exactly the source face,
     no added imports, no source-version imports).
   References.  Upstream statement lines 170-189, ten slots verbatim:
     S:170, real_sum_over_S:171, real_sum_pos_preserved:172,
     real_sum_over_S_ext:175, real_sum_over_S_le:179,
     real_sum_over_S_linear:181, real_sum_over_S_add:184, T:187, T_pos:188,
     energy:189.  real_sum_pos_preserved rides the established sum-positive
     carrier family: supplied by direct carrier realization at the single
     carrier, not restated from a source version.
     Instance: sample space unit; summation fun f => f tt; T := real_one;
     energy := the zero profile.  The positivity, extensionality and
     monotonicity limbs apply the premise at the single point; linearity and
     additivity limbs close by reflexivity of the pointwise equality carrier.
   Constructivity.  All statements are informative; predicates ride the
     real-layer Set carriers of the tree; assumption-free closure, with the
     global-context audit printed at the tail.
   Build.  coqc -native-compiler no -q -Q . ""
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

(* Package record: the ten slot statements enter verbatim (upstream lines 170-189);
   the sample space rides the record as a type argument, mirroring the upstream
   section variable, so the witness names the instance it supplies. *)

Inductive uabd1s7_emt_pack10 (S : Type) : Type :=
| uabd1s7_emt_pack10_intro :
    forall real_sum_over_S : (S -> Real) -> Real,
      (forall (f : S -> Real),
          (forall s : S, real_lt real_zero (f s)) ->
          real_lt real_zero (real_sum_over_S f)) ->
      (forall (f g : S -> Real),
          (forall s : S, real_eq (f s) (g s)) ->
          real_eq (real_sum_over_S f) (real_sum_over_S g)) ->
      (forall (f g : S -> Real),
          (forall s : S, real_le (f s) (g s)) ->
          real_le (real_sum_over_S f) (real_sum_over_S g)) ->
      (forall (a : Real) (f : S -> Real),
          real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
                  (real_mult a (real_sum_over_S f))) ->
      (forall (f g : S -> Real),
          real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
                  (real_plus (real_sum_over_S f) (real_sum_over_S g))) ->
      forall T : Real,
        forall T_pos : real_lt real_zero T,
        forall energy : S -> Real,
          uabd1s7_emt_pack10 S.

(* Witness: one single-point instance feeds all ten slots at once. *)

Theorem uabd1s7_emt_pack10_supplied : uabd1s7_emt_pack10 unit.
Proof.
  exact (uabd1s7_emt_pack10_intro unit           (fun (f : unit -> Real) => f tt)           (fun (f : unit -> Real)              (H : forall s : unit, real_lt real_zero (f s)) => H tt)           (fun (f g : unit -> Real)              (H : forall s : unit, real_eq (f s) (g s)) => H tt)           (fun (f g : unit -> Real)              (H : forall s : unit, real_le (f s) (g s)) => H tt)           (fun (a : Real) (f : unit -> Real) => real_eq_refl (real_mult a (f tt)))           (fun (f g : unit -> Real) => real_eq_refl (real_plus (f tt) (g tt)))           real_one real_lt_zero_one           (fun _ : unit => real_zero)).
Qed.

(* Global-context closure audit. *)

Print Assumptions uabd1s7_emt_pack10_supplied.