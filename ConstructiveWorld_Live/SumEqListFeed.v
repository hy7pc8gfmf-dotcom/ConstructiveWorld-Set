(* ConstructiveWorld-Set — restatement shims for the [sum_eq_list] slot use sites. *)
(** * SumEqListFeed: slot-to-Id connection restatements for [sum_eq_list] use sites.

    Mission.  Restatement shims for the four [sum_eq_list] use sites,
      consuming IdSlotTranslate.v (the bridge [idt_sum_eq_list] and the
      host connection theorems [idt_slot_attdoeblin]/[idt_slot_g01]/
      [idt_slot_s13]/[idt_slot_s15]).  Form A — the slot statement
      substituted as a proof term (six sites: AttnDoeblin :622/:629/:673
      and S13 :2813/:2820/:2864 feeding [le_id_r]/[le_id_l]/an
      [id_trans] chain head): the slot leg is replaced verbatim by
      [idt_slot_*] with the conclusion sum realized as [idt_sumf].  Form
      B — the slot statement as an explicit [forall g, Id (sum_over_S g)
      (bs_list_sum g enum)] argument filling [bs_kernel]/[bs_Zrow_pos] (G01, S15).

    Dependencies.  Stdlib [Lists.List]; requires [UpReqSumD],
      [AttnDoeblin], [S13_NLiveAudit], [IdSlotTranslate] (with the
      [S01_BaseRing] chain) of this development.

    References.  This development, SumEqListFeed.v, the baseline module
      in ConstructiveWorld-Main whose statement names are carried over
      here verbatim (the [idt_slot_*] theorems are the slot statement under the instantiation [sum_over_S := idt_sumf]).

    Constructivity.  Entirely Set-layer ([Id]/[le] are Set-valued
      interface fields); purely constructive with no admitted
      statements; the section mirrors the host BoundedSoftmax section
      ([Context {RI}{SS}{SO}] + [Existing Instance RI_base], [Let le := @le RI]).

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live ""
      SumEqListFeed.v] compiles cleanly (exit 0); the artifact starts
      with [436f7121 00015ff4]. *)

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
Require UpReqSumD.
Require Import AttnDoeblin.
Require Import IdSlotTranslate.
Import ListNotations.

(* =================== Section setup: the same opening as the host BoundedSoftmax section =================== *)
(* Context {RI}{SS}{SO} + Existing Instance RI_base, and *)
(* Let le := @le RI in the host syntax. *)
Section SumEqListFeed.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.
Local Existing Instance RI_base.

Let le := @le RI.

(* =================== Section 1. Form A restatement bridges, the three AttnDoeblin use sites =================== *)
(* Host sum = AttnDoeblin.bs_list_sum; the connector = idt_slot_attdoeblin. *)

(* Use site AttnDoeblin:622 (the bs_Zrow_ge shape). *)
(* Original inference: le_id_r a (bs_list_sum g enum) (sum_over_S g) *)
(* (id_sym (sum_eq_list g)) : le a (bs_list_sum g enum) -> le a (sum_over_S g). *)
(* Restated inference: the slot leg replaced verbatim by idt_slot_attdoeblin, *)
(* the conclusion sum realized as idt_sumf. *)
Lemma sef_attn_zrow_ge : forall (en : list S01_BaseRing.S) (g : S01_BaseRing.S -> R) (a : R),
  le a (AttnDoeblin.bs_list_sum g en) -> le a (idt_sumf en g).
Proof.
  intros en g a Hle.
  exact (le_id_r a (AttnDoeblin.bs_list_sum g en) (idt_sumf en g)                   (id_sym (idt_slot_attdoeblin en g)) Hle).
Qed.

(* Use site AttnDoeblin:629 (the bs_Zrow_le shape). *)
(* Original inference: le_id_l _ _ _ (sum_eq_list g) : le (bs_list_sum g enum) b -> le (sum_over_S g) b. *)
Lemma sef_attn_zrow_le : forall (en : list S01_BaseRing.S) (g : S01_BaseRing.S -> R) (b : R),
  le (AttnDoeblin.bs_list_sum g en) b -> le (idt_sumf en g) b.
Proof.
  intros en g b Hle.
  exact (le_id_l (idt_sumf en g) (AttnDoeblin.bs_list_sum g en) b                 (idt_slot_attdoeblin en g) Hle).
Qed.

(* Use site AttnDoeblin:673 (the bs_Unif_norm shape). *)
(* Original inference: id_trans (sum_eq_list Unif) heads the following chain — *)
(* the slot as the first argument of id_trans. *)
Lemma sef_attn_unif_norm : forall (en : list S01_BaseRing.S) (g : S01_BaseRing.S -> R) (b : R),
  Id (AttnDoeblin.bs_list_sum g en) b -> Id (idt_sumf en g) b.
Proof.
  intros en g b Hid.
  exact (id_trans (idt_slot_attdoeblin en g) Hid).
Qed.

(* =================== Section 2. Form A restatement bridges, the three S13 use sites =================== *)
(* Host sum = S13_NLiveAudit.bs_list_sum; connector = idt_slot_s13; *)
(* the shapes are literally isomorphic to the AttnDoeblin ones, only the *)
(* host sum and connector change. *)

(* Use site S13:2813 (the bs_Zrow_ge shape; the le_id_r + id_sym slot leg). *)
Lemma sef_s13_zrow_ge : forall (en : list S01_BaseRing.S) (g : S01_BaseRing.S -> R) (a : R),
  le a (S13_NLiveAudit.bs_list_sum g en) -> le a (idt_sumf en g).
Proof.
  intros en g a Hle.
  exact (le_id_r a (S13_NLiveAudit.bs_list_sum g en) (idt_sumf en g)                   (id_sym (idt_slot_s13 en g)) Hle).
Qed.

(* Use site S13:2820 (the bs_Zrow_le shape; the le_id_l slot substituted directly). *)
Lemma sef_s13_zrow_le : forall (en : list S01_BaseRing.S) (g : S01_BaseRing.S -> R) (b : R),
  le (S13_NLiveAudit.bs_list_sum g en) b -> le (idt_sumf en g) b.
Proof.
  intros en g b Hle.
  exact (le_id_l (idt_sumf en g) (S13_NLiveAudit.bs_list_sum g en) b                 (idt_slot_s13 en g) Hle).
Qed.

(* Use site S13:2864 (the bs_Unif_norm shape; the slot as the head argument of id_trans). *)
Lemma sef_s13_unif_norm : forall (en : list S01_BaseRing.S) (g : S01_BaseRing.S -> R) (b : R),
  Id (S13_NLiveAudit.bs_list_sum g en) b -> Id (idt_sumf en g) b.
Proof.
  intros en g b Hid.
  exact (id_trans (idt_slot_s13 en g) Hid).
Qed.

(* =================== Section 3. Form B argument fillers, G01:485/:500 and S15:156/:171 =================== *)
(* Original use shape: the slot statement passed as an explicit argument to *)
(* the upstream generalized lemma bs_kernel en enum_nonempty temp temp_pos *)
(* Delta z2 z_lb expf expf_pos expf_mono_le sum_eq_list s s'. *)
(* The retyped argument = the original argument type with the realization *)
(* sum_over_S replaced by idt_sumf en — exactly the statement type of *)
(* idt_slot_g01 / idt_slot_s15; the fillers are definitional. *)

(* The G01:476 slot-argument restatement filler (host sum = the AttnDoeblin *)
(* exit-section definition). *)
Definition sef_g01_slot_arg (en : list S01_BaseRing.S)
  : forall g : S01_BaseRing.S -> R, Id (idt_sumf en g) (AttnDoeblin.bs_list_sum g en) :=
  idt_slot_g01 en.

(* The S15:147 slot-argument restatement filler (host sum = the S13 *)
(* exit-section definition). *)
Definition sef_s15_slot_arg (en : list S01_BaseRing.S)
  : forall g : S01_BaseRing.S -> R, Id (idt_sumf en g) (S13_NLiveAudit.bs_list_sum g en) :=
  idt_slot_s15 en.

(* Self-check of the Form B filler shapes: the fillers agree pointwise with *)
(* the connection theorems (at the eta-expansion level). *)
Lemma sef_g01_slot_arg_pt : forall (en : list S01_BaseRing.S) (g : S01_BaseRing.S -> R),
  Id (idt_sumf en g) (AttnDoeblin.bs_list_sum g en).
Proof.
  intros en g.
  exact (sef_g01_slot_arg en g).
Qed.

Lemma sef_s15_slot_arg_pt : forall (en : list S01_BaseRing.S) (g : S01_BaseRing.S -> R),
  Id (idt_sumf en g) (S13_NLiveAudit.bs_list_sum g en).
Proof.
  intros en g.
  exact (sef_s15_slot_arg en g).
Qed.

(* =================== Assumption audits: all eight statements Closed =================== *)
Print Assumptions sef_attn_zrow_ge.
Print Assumptions sef_attn_zrow_le.
Print Assumptions sef_attn_unif_norm.
Print Assumptions sef_s13_zrow_ge.
Print Assumptions sef_s13_zrow_le.
Print Assumptions sef_s13_unif_norm.
Print Assumptions sef_g01_slot_arg.
Print Assumptions sef_s15_slot_arg.

End SumEqListFeed.
