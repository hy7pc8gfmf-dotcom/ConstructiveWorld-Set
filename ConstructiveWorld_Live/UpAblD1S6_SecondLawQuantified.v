(* ========================================================================== *)
(*  UpAblD1S6_SecondLawQuantified.v -- single-point supply instance for the   *)
(*  eight open statement slots of the SlqSecondLaw section (host source       *)
(*  SecondLawQuantified.v, live tree, read-only).                             *)
(*  Mission.: package the remaining section statement faces verbatim as one   *)
(*        inductive record (uabd1s6_slq_pack8) with the state carrier S       *)
(*        hoisted to the leading type argument, and close them with one       *)
(*        witness (uabd1s6_slq_pack8_supplied) at the unit instance. The      *)
(*        eight slots: summator sumf, extensionality, linearity, additivity,  *)
(*        temperature positivity T_pos, and the energy function. The source   *)
(*        positivity slot (L78, sumpos) is intentionally not packaged: that   *)
(*        slot is already discharged by an earlier instance of the same       *)
(*        section; a second instantiation of one slot is avoided by design.   *)
(*  Dependencies.: S01_BaseRing S02_CauchyComplete S03_QExp                  *)
(*        S04_RealExpLogConv S05_AlignmentGRPO S06_DiffSamplingGibbs         *)
(*        S07_RealSetoidExpLog S08_RealMainlineDPO S09_EntropyReal           *)
(*        S10_KVQuantTrig S11_TP3B5 S12_B5RecycleSF S13_NLiveAudit           *)
(*        S14_B5BatchBlock S15_TailFEPUp; Stdlib List.                       *)
(*  References.: SecondLawQuantified.v, Section SlqSecondLaw (source L76-92   *)
(*        statement faces re-stated verbatim inside the pack record).         *)
(*  Constructivity.: the witness closes constructively on the single-point    *)
(*        carrier S := unit with sumf := fun f => f tt. The extensionality    *)
(*        slot is the dependent direct take H tt; the linearity and           *)
(*        additivity slots close by beta-normalization coincidence on both    *)
(*        sides (real_eq_refl); T := real_one with real_lt_zero_one; energy   *)
(*        is the zero function. Fully constructive closure; tail Print        *)
(*        Assumptions Closed; extraction Obj.magic = 0.                       *)
(*  Build.: rocq c -native-compiler no -q -Q <seat>/world "" born in place    *)
(*        in that world of fresh live-tree burns (single file, guard wrapped).*)
(* ========================================================================== *)

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

(* ============================================================ *)
(*  Pack record: the eight section statement faces re-stated      *)
(*  verbatim from the host source (L76-92) as one inductive with  *)
(*  a single constructor; the point carrier S is hoisted to the   *)
(*  inductive's leading type argument so extraction keeps it as   *)
(*  an OCaml type argument instead of erasing it, which keeps     *)
(*  the witness terms cast-free (slot faces and witness term      *)
(*  carried unchanged). The source positivity slot (L78) is       *)
(*  intentionally absent (see header).                            *)
(* ============================================================ *)

Inductive uabd1s6_slq_pack8 (S : Type) : Type :=
| uabd1s6_slq_pack8_intro :
    forall sumf : (S -> Real) -> Real,
      (forall (f g : S -> Real),
          (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g)) ->
      (forall (a : Real) (f : S -> Real),
          real_eq (sumf (fun s : S => real_mult a (f s)))
                  (real_mult a (sumf f))) ->
      (forall (f g : S -> Real),
          real_eq (sumf (fun s : S => real_plus (f s) (g s)))
                  (real_plus (sumf f) (sumf g))) ->
      forall T : Real,
        forall T_pos : real_lt real_zero T,
          forall energy : S -> Real,
            uabd1s6_slq_pack8 S.

(* ============ Supply witness: one single-point instance closes all eight packaged slots ============ *)

Theorem uabd1s6_slq_pack8_supplied : uabd1s6_slq_pack8 unit.
Proof.
  exact (uabd1s6_slq_pack8_intro unit           (fun (f : unit -> Real) => f tt)           (fun (f g : unit -> Real)              (H : forall s : unit, real_eq (f s) (g s)) => H tt)           (fun (a : Real) (f : unit -> Real) => real_eq_refl (real_mult a (f tt)))           (fun (f g : unit -> Real) => real_eq_refl (real_plus (f tt) (g tt)))           real_one real_lt_zero_one           (fun _ : unit => real_zero)).
Qed.

(* ============ Assumption-face closure report ============ *)

Print Assumptions uabd1s6_slq_pack8_supplied.
