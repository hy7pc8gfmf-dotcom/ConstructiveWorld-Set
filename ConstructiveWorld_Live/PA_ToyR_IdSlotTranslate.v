(* PA_ToyR_IdSlotTranslate.v - interface translation and per-slot
   instantiation of the four sum_eq_list slots in Id form.
   Mission.  An Id-form interface-translation bridge pair plus four host
     verification theorems.  idt_sum_eq_list: the local list folder
     idt_list_sum agrees with its definitional wrapper idt_sumf.
     idt_bs_list_sum_attn_agree / idt_bs_list_sum_s13_agree: the local
     folder agrees with the exported host folds AttnDoeblin.bs_list_sum
     and S13_NLiveAudit.bs_list_sum.  idt_slot_attdoeblin / idt_slot_g01
     / idt_slot_s13 / idt_slot_s15: the four host slots (each slot's
     sum_over_S := idt_sumf definitional instance) are realized against
     the matching host fold.
   Dependencies.  Tree modules S01_BaseRing through S15_TailFEPUp,
     UpReqSumD, AttnDoeblin; Stdlib [List] with [ListNotations]; the
     RealInterfaceEnhancedMod field view is imported so the bare [R] /
     [S] names resolve on the section carrier.
   References.  Declaration faces: idt_list_sum (L46), idt_sumf (L53),
     idt_sum_eq_list (L58), idt_bs_list_sum_attn_agree (L74),
     idt_bs_list_sum_s13_agree (L83), idt_slot_attdoeblin (L101),
     idt_slot_g01 (L110), idt_slot_s13 (L119), idt_slot_s15 (L128);
     host folds bs_list_sum at AttnDoeblin L496 and S13_NLiveAudit
     L2765.
   Constructivity.  All of the Set layer: Id is a Set-valued inductive
     family; purely constructive statements, zero-assumption closure;
     the nil step closes by id_refl, the cons step by the id_cong2
     congruence bridge (nothing rests on conversion of neutral
     arguments); the trailing Print Assumptions census covers all seven
     named pieces.
   Build.  rocq c -native-compiler no -q -Q . "" (Rocq 9.1 toolchain).
*)

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
Require UpReqSumD.
Require Import AttnDoeblin.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* Section: carrier context and the four same-shape slots.  The bare   *)
(* names bound by Context {RI}{SS} are the host files' own proved      *)
(* syntax (the RowView style of S13/S15).                              *)
(* ============================================================ *)
Section IdSlotTranslate.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Local Existing Instance RI_base.

(* ============ Bridge 1: the RI-carrier list folder plus the ============ *)
(* definitional instance resolving the sum_over_S interface argument.   *)
(* Carrier-side copies of sumd_list_sum (UpReqSumD L61) and sumd_sumf   *)
(* (UpReqSumD L68), translated literally; bare zero/plus = @zero RI /   *)
(* @plus RI (the same interface the host folds use).                    *)

Fixpoint idt_list_sum (f : S -> R) (l : list S) : R :=
  match l with
  | nil => @S01_BaseRing.zero RI
  | x :: t => @S01_BaseRing.plus RI (f x) (idt_list_sum f t)
  end.

(* Definitional resolver of the sum_over_S interface argument (same-position copy of sumd_sumf). *)
Definition idt_sumf (enum : list S) (f : S -> R) : R :=
  idt_list_sum f enum.

(* Bridge 1 body: the Id-form key bridge - a definitional collapse by   *)
(* id_refl (zero induction, zero rewrite; the same construction as the  *)
(* Id-carrier lemmas of S01_BaseRing).                                  *)
Lemma idt_sum_eq_list :
  forall (enum : list S) (g : S -> R),
    Id (idt_sumf enum g) (idt_list_sum g enum).
Proof.
  intros enum g.
  exact id_refl.
Qed.

(* ============ Bridge 2: host-fold agreement bridges (the fold side === *)
(* of the interface translation).  On the concrete cons shape the       *)
(* exported fold reduces by delta/zeta/iota in step with the local one; *)
(* id_cong2 carries the congruence step by step; the nil shape is       *)
(* id_refl (immune to the conversion wall: nothing rests on conversion  *)
(* of neutral arguments).  One bridge per host fold:                    *)
(*   AttnDoeblin.bs_list_sum (serving slots AttnDoeblin:485 / G01:476)  *)
(*   S13_NLiveAudit.bs_list_sum (serving slots S13:2676 / S15:147).     *)
(* Bare-name application = the exported implicit arguments {RI}{SS}     *)
(* (the same syntax as the slot row at G01:476 itself).                 *)

Lemma idt_bs_list_sum_attn_agree :
  forall (f : S -> R) (l : list S),
    Id (idt_list_sum f l) (AttnDoeblin.bs_list_sum f l).
Proof.
  intros f l. induction l as [| x t IH].
  - exact id_refl.
  - exact (id_cong2 (@S01_BaseRing.plus RI) id_refl IH).
Qed.

Lemma idt_bs_list_sum_s13_agree :
  forall (f : S -> R) (l : list S),
    Id (idt_list_sum f l) (S13_NLiveAudit.bs_list_sum f l).
Proof.
  intros f l. induction l as [| x t IH].
  - exact id_refl.
  - exact (id_cong2 (@S01_BaseRing.plus RI) id_refl IH).
Qed.

(* ============ Four host verification theorems (one per slot) =========== *)
(* Statement = the slot statement (with sum_over_S := idt_sumf resolved *)
(* definitionally) against the exported host fold; enum is promoted     *)
(* from the slot-section Variable position to an explicit universal     *)
(* (the stronger honest form).  Assembly = Bridge 2 specialized         *)
(* (idt_sumf collapses to idt_list_sum by delta/beta, as in Bridge 1).  *)
(* The four theorems are realizable witnesses for the four slots'       *)
(* sum_eq_list; the four dependency positions (G01:485/:500,            *)
(* AttnDoeblin:622/:629/:673, S13:2813/:2820/:2864, S15:156/:171)       *)
(* instantiate along them.                                              *)

(* slot AttnDoeblin:485 (BoundedSoftmax section) *)
Theorem idt_slot_attdoeblin :
  forall (enum : list S) (g : S -> R),
    Id (idt_sumf enum g) (AttnDoeblin.bs_list_sum g enum).
Proof.
  intros enum g.
  exact (idt_bs_list_sum_attn_agree g enum).
Qed.

(* slot G01_CoreMicro:476 (RowView section; the fold is the AttnDoeblin exported piece, :362) *)
Theorem idt_slot_g01 :
  forall (enum : list S) (g : S -> R),
    Id (idt_sumf enum g) (AttnDoeblin.bs_list_sum g enum).
Proof.
  intros enum g.
  exact (idt_bs_list_sum_attn_agree g enum).
Qed.

(* slot S13_NLiveAudit:2676 (its own fold, :2669) *)
Theorem idt_slot_s13 :
  forall (enum : list S) (g : S -> R),
    Id (idt_sumf enum g) (S13_NLiveAudit.bs_list_sum g enum).
Proof.
  intros enum g.
  exact (idt_bs_list_sum_s13_agree g enum).
Qed.

(* slot S15_TailFEPUp:147 (RowView section; the fold is the S13 exported piece, S15:26) *)
Theorem idt_slot_s15 :
  forall (enum : list S) (g : S -> R),
    Id (idt_sumf enum g) (S13_NLiveAudit.bs_list_sum g enum).
Proof.
  intros enum g.
  exact (idt_bs_list_sum_s13_agree g enum).
Qed.

(* ============ Acceptance census: all seven named pieces Closed ============ *)
Print Assumptions idt_sum_eq_list.
Print Assumptions idt_bs_list_sum_attn_agree.
Print Assumptions idt_bs_list_sum_s13_agree.
Print Assumptions idt_slot_attdoeblin.
Print Assumptions idt_slot_g01.
Print Assumptions idt_slot_s13.
Print Assumptions idt_slot_s15.

End IdSlotTranslate.

Print Assumptions idt_slot_s15.
Print Assumptions idt_slot_s13.
Print Assumptions idt_slot_g01.
Print Assumptions idt_slot_attdoeblin.
Print Assumptions idt_sum_eq_list.
