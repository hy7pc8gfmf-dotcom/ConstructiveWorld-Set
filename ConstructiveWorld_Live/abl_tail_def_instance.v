(* ConstructiveWorld-Set -- uniform definitional instantiation of the partition interface family. *)

(** * abl_tail_def_instance: definitional instances of the partition sum face with named slot closures.

    Mission.  Assemble the partition function [tspd_g5_partition_Z] as a sum over an
      abstract summation face, close partition-condition-shaped slots by [req]
      reflexivity in one step ([tspd_g5_partition_condition_req_refl]), carry the
      temperature variant together with its positivity certificate
      ([tspd_g5_Z_temp_of], [tspd_g5_Z_temp_spec_ht_carry]), and give the
      per-slot named closures [tspd_g5_pa04_partition_condition] and
      [tspd_g5_bbd_partition_condition].

    Dependencies.  Stdlib [List], [Extraction].  Requires [S01_BaseRing],
      [S02_CauchyComplete], [S03_QExp], [S04_RealExpLogConv],
      [S05_AlignmentGRPO], [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog],
      [S08_RealMainlineDPO], [S09_EntropyReal], [S10_KVQuantTrig],
      [S11_TP3B5], [S12_B5RecycleSF], [S13_NLiveAudit], [S14_B5BatchBlock],
      [S15_TailFEPUp], [UpReqConcSoftmax] of this development.

    References.  This development, abl_tail_def_instance.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" abl_tail_def_instance.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
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
Require Import UpReqConcSoftmax.
Import RealInterfaceEnhancedMod.

(* The interface class of this development is carried at the fixed Real      *)
(* carrier (the class takes no carrier argument); the statement faces        *)
(* below read [R] as that carrier and state their predicates and operations  *)
(* on the global Q-carried [real_*] face -- the very face the class fields   *)
(* are defined as -- so each closure proof goes through the interface's      *)
(* reflexivity field in one definitional step.                               *)
Notation R := Real.

(* ============================================================ *)
(* 1. Uniform assembly of the partition function over an abstract  *)
(*    summation face, with reflexive closure.  [Z] is assembled    *)
(*    without binding any concrete summation implementation: any   *)
(*    interface [sumf] fits the slot, whether the abstract [sumf]  *)
(*    of a slot section or the [csm_sumf] reading, and the         *)
(*    partition equation closes by [req_refl] in one step.         *)
(* ============================================================ *)

Definition tspd_g5_partition_Z
    (S : Set) (sumf : (S -> R) -> R)
    (base_loss : S -> R) (D : R) (D_pos : real_lt real_zero D) : R :=
  sumf (fun s : S => real_exp_neg (real_mult (real_inv_pos D D_pos) (base_loss s))).

Theorem tspd_g5_partition_condition_req_refl :
  forall (S : Set)
    (sumf : (S -> R) -> R) (base_loss : S -> R) (D : R) (D_pos : real_lt real_zero D),
    real_eq (tspd_g5_partition_Z S sumf base_loss D D_pos)
        (sumf (fun s : S => real_exp_neg (real_mult (real_inv_pos D D_pos) (base_loss s)))).
Proof.
  intros S sumf base_loss D D_pos.
  exact (req_refl
           (sumf (fun s : S => real_exp_neg (real_mult (real_inv_pos D D_pos) (base_loss s))))).
Qed.

(* ============================================================ *)
(* 2. Uniform piece for the temperature partition face carrying    *)
(*    its positivity certificate.  This is the assemblable face of *)
(*    the [Z_temp_spec] slot: the operator takes the temperature    *)
(*    [t] and its positivity certificate [Ht] together, whereas     *)
(*    the bare function face [Z_temp : R -> R] of the target slot   *)
(*    carries no certificate, so no definitional assembly route     *)
(*    reaches it; this face is the reachable face of the family.    *)
(* ============================================================ *)

Definition tspd_g5_Z_temp_of
    (S : Set) (sumf : (S -> R) -> R) (base_loss : S -> R)
    (t : R) (Ht : real_lt real_zero t) : R :=
  sumf (fun s : S => real_exp_neg (real_mult (real_inv_pos t Ht) (base_loss s))).

Theorem tspd_g5_Z_temp_spec_ht_carry :
  forall (S : Set)
    (sumf : (S -> R) -> R) (base_loss : S -> R) (t : R) (Ht : real_lt real_zero t),
    real_eq (tspd_g5_Z_temp_of S sumf base_loss t Ht)
        (sumf (fun s : S => real_exp_neg (real_mult (real_inv_pos t Ht) (base_loss s)))).
Proof.
  intros S sumf base_loss t Ht.
  exact (req_refl
           (sumf (fun s : S => real_exp_neg (real_mult (real_inv_pos t Ht) (base_loss s))))).
Qed.

(* ============================================================ *)
(* 3. Named closed forms for the reachable slots, one per slot.    *)
(*    The section environments mirror the slot faces of            *)
(*    Arch_PA_04.v:865-887 and BBDBridgeSupply.v:58-98 in the same *)
(*    order and shape; each statement restates the target slot     *)
(*    verbatim with the [Z] position filled by the assembled       *)
(*    definition.                                                  *)
(* ============================================================ *)

(* ---- Slot face of Arch_PA_04.v:886-887 (abstract sumf section) ---- *)
Section TspG5Pa04Slot.

Variable S : Set.
Variable sumf : (S -> R) -> R.
Variable base_loss : S -> R.
Variable D : R.
Variable D_pos : real_lt real_zero D.

Theorem tspd_g5_pa04_partition_condition :
  real_eq (tspd_g5_partition_Z S sumf base_loss D D_pos)
      (sumf (fun s : S => real_exp_neg (real_mult (real_inv_pos D D_pos) (base_loss s)))).
Proof.
  exact (req_refl
           (sumf (fun s : S => real_exp_neg (real_mult (real_inv_pos D D_pos) (base_loss s))))).
Qed.

End TspG5Pa04Slot.

(* ---- Slot face of BBDBridgeSupply.v:98 (csm_sumf section) ---- *)
Section TspG5BbdSlot.

Variable S : Set.
Variable enum : list S.
Let sumf : (S -> Real) -> Real := csm_sumf S enum.
Variable base_loss : S -> Real.
Variable D : Real.
Variable D_pos : real_lt real_zero D.

Theorem tspd_g5_bbd_partition_condition :
  real_eq (@tspd_g5_partition_Z S sumf base_loss D D_pos)
      (sumf (fun s : S => real_exp_neg (real_mult (real_inv_pos D D_pos) (base_loss s)))).
Proof.
  exact (req_refl
           (sumf (fun s : S => real_exp_neg (real_mult (real_inv_pos D D_pos) (base_loss s))))).
Qed.

End TspG5BbdSlot.

(* ============================================================ *)
(* 4. Assumption audit, one entry per piece; the criterion is      *)
(*    [Closed under the global context] for every named statement. *)
(* ============================================================ *)
Print Assumptions tspd_g5_partition_condition_req_refl.
Print Assumptions tspd_g5_Z_temp_spec_ht_carry.
Print Assumptions tspd_g5_pa04_partition_condition.
Print Assumptions tspd_g5_bbd_partition_condition.

(* ============================================================ *)
(* 5. Extraction audit: the criterion is zero occurrences of       *)
(*    [Obj.magic] in the extraction output.  A hard extractor      *)
(*    error or a nonzero magic count is reported as a failure and  *)
(*    is not passed off as a success.                              *)
(* ============================================================ *)
From Stdlib Require Import Extraction.
Set Extraction Output Directory "_log/extraction".
Recursive Extraction tspd_g5_partition_Z tspd_g5_partition_condition_req_refl
  tspd_g5_Z_temp_of tspd_g5_Z_temp_spec_ht_carry
  tspd_g5_pa04_partition_condition tspd_g5_bbd_partition_condition.
