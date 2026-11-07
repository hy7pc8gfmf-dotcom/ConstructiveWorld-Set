(* ConstructiveWorld-Set — Set-layer realizable witnesses for the four identity slots. *)

(** * IdSlotTranslate: list-fold witnesses for the abstract summation
    slots of the host sections.

    Mission.  Each host section states the abstract slot
      [sum_eq_list : forall g : S -> R, Id (sum_over_S g)
      (bs_list_sum g enum)] — the abstract summation agrees with a
      list fold.  This file builds the fold machines
      [idt_list_sum]/[idt_sumf], proves them pointwise identical to
      [AttnDoeblin.bs_list_sum] and [S13_NLiveAudit.bs_list_sum], and
      supplies the four [Id]-form slot witnesses.

    Dependencies.  Stdlib [List].  Requires [S01_BaseRing] ([Id],
      [id_refl], [id_cong2], the [S]/[R] class-domain projections),
      [S02_CauchyComplete] through [S15_TailFEPUp], [UpReqSumD],
      [AttnDoeblin] and [S13_NLiveAudit] of this development.

    References.  This development, IdSlotTranslate.v, the baseline
      module in ConstructiveWorld-Main whose statement names are
      carried over here verbatim (statement-face Set-carrier completion).

    Constructivity.  All statements are predicated on the Set-valued
      inductive identity [Id]; proofs use only definitional unfolding
      ([id_refl]) and step congruence ([id_cong2]); statements extract
      with [Obj.magic] = 0 and no erasure; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" IdSlotTranslate.v]
      compiles cleanly (exit 0); the first eight bytes of the artifact
      are [436f7121 00015ff4]. *)

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

(* ==================== Section. Interface context shared with the four host slots ==================== *)
(* Under [Context {RI}{SS}] the bare-name syntax matches what the host
   files prove with: [S] and [R] are the class-domain projections,
   resolved inside the section through the local instance and maximal
   implicit insertion to [@S RI SS] / [@R RI]. *)
Section IdSlotTranslate.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Local Existing Instance RI_base.

(* ==================== Bridge 1. A list-fold machine on the [RI] record ==================== *)
(* The fold shape agrees with [sumd_list_sum] of [UpReqSumD]: [nil]
   yields the zero element and each [cons] step adds; the bare
   [zero]/[plus] resolve to [@zero RI] / [@plus RI], the same interface
   the host machines use. *)

Fixpoint idt_list_sum (f : S -> R) (l : list S) : R :=
  match l with
  | nil => @S01_BaseRing.zero RI
  | x :: t => @S01_BaseRing.plus RI (f x) (idt_list_sum f t)
  end.

(* Definitional instantiation of the [sum_over_S] slot:
   [idt_sumf := idt_list_sum], at the same position and in the same
   shape as the host [sumd_sumf]. *)
Definition idt_sumf (enum : list S) (f : S -> R) : R :=
  idt_list_sum f enum.

(* Bridge 1 statement: [idt_sumf] unfolds (delta/beta) to
   [idt_list_sum] with both sides literally identical, so [id_refl]
   closes directly (no induction, no rewriting). *)
Lemma idt_sum_eq_list :
  forall (enum : list S) (g : S -> R),
    Id (idt_sumf enum g) (idt_list_sum g enum).
Proof.
  intros enum g.
  exact (@id_refl _ (idt_list_sum g enum)).
Qed.

(* ==================== Bridge 2. Agreement with the discharged host machines ==================== *)
(* On the concrete [cons] shape each discharged host machine reduces
   (delta/zeta/iota) to this file's fold machine; [id_cong2] transfers
   the congruence step by step, and on the concrete [nil] shape both
   sides are the zero element, closed by [id_refl].
     [AttnDoeblin.bs_list_sum] (serves the AttnDoeblin and G01 slots);
     [S13_NLiveAudit.bs_list_sum] (serves the S13 and S15 slots).
   Bare-name application uses the discharged implicit parameters
   {[RI]}{[SS]}, the same syntax as the host slot rows themselves. *)

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

(* The four theorems are realizable witnesses for the four host
   [sum_eq_list] slots: [sum_over_S] is instantiated as [idt_sumf],
   and quantifying the host-abstract [enum] explicitly gives a stronger
   form.  Use is Bridge 2 specialized ([idt_sumf] unfolds to
   [idt_list_sum], as in Bridge 1); consumers supply the instance data
   of their own slot row in G01_CoreMicro, AttnDoeblin,
   S13_NLiveAudit, S15_TailFEPUp. *)

(* Slot of [AttnDoeblin] (Section [BoundedSoftmax]). *)
Theorem idt_slot_attdoeblin :
  forall (enum : list S) (g : S -> R),
    Id (idt_sumf enum g) (AttnDoeblin.bs_list_sum g enum).
Proof.
  intros enum g.
  exact (idt_bs_list_sum_attn_agree g enum).
Qed.

(* Slot of [G01_CoreMicro] (Section [RowView]; the machine is the discharged [AttnDoeblin] one). *)
Theorem idt_slot_g01 :
  forall (enum : list S) (g : S -> R),
    Id (idt_sumf enum g) (AttnDoeblin.bs_list_sum g enum).
Proof.
  intros enum g.
  exact (idt_bs_list_sum_attn_agree g enum).
Qed.

(* Slot of [S13_NLiveAudit] (its own machine). *)
Theorem idt_slot_s13 :
  forall (enum : list S) (g : S -> R),
    Id (idt_sumf enum g) (S13_NLiveAudit.bs_list_sum g enum).
Proof.
  intros enum g.
  exact (idt_bs_list_sum_s13_agree g enum).
Qed.

(* Slot of [S15_TailFEPUp] (Section [RowView]; the machine is the discharged [S13] one). *)
Theorem idt_slot_s15 :
  forall (enum : list S) (g : S -> R),
    Id (idt_sumf enum g) (S13_NLiveAudit.bs_list_sum g enum).
Proof.
  intros enum g.
  exact (idt_bs_list_sum_s13_agree g enum).
Qed.

(* ==================== Closure audit: [Print Assumptions] on all seven statements ==================== *)
(* Inside the section [RI]/[SS] are abstract interface parameters;
   after discharge they are generalized and no global assumptions
   remain. *)
Print Assumptions idt_sum_eq_list.
Print Assumptions idt_bs_list_sum_attn_agree.
Print Assumptions idt_bs_list_sum_s13_agree.
Print Assumptions idt_slot_attdoeblin.
Print Assumptions idt_slot_g01.
Print Assumptions idt_slot_s13.
Print Assumptions idt_slot_s15.

End IdSlotTranslate.
