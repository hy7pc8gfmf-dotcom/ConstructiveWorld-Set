(* ==========================================================================
   SumEqListMark.v - the unified instantiation face of the sum_eq_list
   same-shape slots (the req-form slot 1, two witness theorems), plus the
   interface-translation forwarding face for slots 2-5 (four theorems
   carried over the IdSlotTranslate interface-translation piece).
   Mission. 使命: eight theorems - two instantiate the bridge
     sumd_sum_eq_list at sumf := sumd_sumf (req_refl collapse), two
     restate slot 1 against the host machine rsq_bs_list_sum, four
     forward the slot 2-5 verifications onto IdSlotTranslate's host
     theorems; zero new machinery.
   Dependencies. 依赖清单: S01_BaseRing..S15_TailFEPUp, UpReqSumD,
     UpReqSampling, AttnDoeblin, IdSlotTranslate, List of the -Set lineage
     world; argument-less Class RealInterfaceEnhancedSetoid; notation
     rebind Notation R := Real; predicate face converged to real_eq.
   References. 对标: list-sum folding isomorphism (the definitional
     instantiation layer of summation operators). Statement names carried
     over verbatim; adaptation = binder-pair removal + notation rebinding
     + argument reshaping to the world's discharged signatures.
   Constructivity. 构造性注记: all Set-layer statements; every station
     Qed-closed, zero admitted items; zero new machinery; the tail
     Print Assumptions probes report the closure face; no new axioms.
   Build. 编译配方: rocq c -native-compiler no -q -Q <world> ""
     SumEqListMark.v (cpu_guard thermal wrapper, ulimit -s 65532).
   ========================================================================== *)

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
Require Import UpReqSumD.
Require Import UpReqSampling.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.
Notation R := Real.

(* The bridge's discharged signature, printed at compile time:
   sumd_sum_eq_list : forall (S : Set) (enum : list S) (g : S -> R),
   real_eq (sumd_sumf S enum g) (sumd_list_sum S g enum). *)
About sumd_sum_eq_list.

(* ============ Instantiation 1: direct bridge substitution ============ *)
(* The slot statement req (sumf g) (rsq_bs_list_sum g enum) at the
   instance sumf := sumd_sumf is the key bridge substituted verbatim. *)
Theorem sem_sum_eq_list_req_slot :
  forall (S : Set) (enum : list S) (g : S -> R),
    real_eq (@sumd_sumf S enum g) (@sumd_list_sum S g enum).
Proof. intros S enum g. exact (@sumd_sum_eq_list S enum g). Qed.

(* ============ Instantiation 2: definitional collapse ============ *)
(* sumd_sumf g := sumd_list_sum g enum holds by definition, so the slot
   instance collapses to req_refl. *)
Theorem sem_sum_eq_list_collapse :
  forall (S : Set) (enum : list S) (g : S -> R),
    real_eq (@sumd_sumf S enum g) (@sumd_list_sum S g enum).
Proof. intros S enum g. exact (req_refl (@sumd_list_sum S g enum)). Qed.

(* ============ Instantiation 3: slot 1 against the host machine ============ *)
(* The statement is the verbatim shape of the UpReqSampling slot at the
   instance sumf := sumd_sumf. The bridge's list-sum machine and the host
   genuine machine rsq_bs_list_sum share the same fold shape, so the
   right-hand sides are convertible and the collapse closes the goal. *)
Theorem sem_slot1_witness_upreqsampling :
  forall (S : Set) (enum : list S) (g : S -> R),
    real_eq (@sumd_sumf S enum g) (@rsq_bs_list_sum S g enum).
Proof. intros S enum g. exact (req_refl (@sumd_list_sum S g enum)). Qed.

(* ============ Instantiation 4: slot 1 host-machine collapse ============ *)
Theorem sem_slot1_witness_collapse :
  forall (S : Set) (enum : list S) (g : S -> R),
    real_eq (@sumd_sumf S enum g) (@rsq_bs_list_sum S g enum).
Proof. intros S enum g. exact (req_refl _). Qed.

(* ============ Gate evidence: the four theorems are all Closed ============ *)
Print Assumptions sem_sum_eq_list_req_slot.
Print Assumptions sem_sum_eq_list_collapse.
Print Assumptions sem_slot1_witness_upreqsampling.
Print Assumptions sem_slot1_witness_collapse.

(* ============================================================
   Slots 2-5: the machine-conversion wall is discharged by forwarding.
   This section is a pure forwarding face (exact assembly of the
   IdSlotTranslate bridges already proved; zero new machinery, zero new
   mathematics); the four theorems above are unchanged.

   The original open item recorded that the host machines bs_list_sum run
   on the RealInterfaceEnhanced interface (a Context {RI}{SS} carrier),
   whose zero/plus projections differ in head from the sumd projections
   of RealInterfaceEnhancedSetoid, so direct substitution of the bridge
   onto the genuine host needed an interface-translation piece.

   That translation piece exists: IdSlotTranslate carries the RI-carrier
   list fold idt_list_sum / idt_sumf (same shape as the host machine,
   conversion-wall immune by design), the two agreement bridges
   idt_bs_list_sum_attn_agree / idt_bs_list_sum_s13_agree (stepwise id_cong2
   congruence, not betting on conversion), and four host verification
   theorems idt_slot_attdoeblin / idt_slot_g01 / idt_slot_s13 /
   idt_slot_s15. The usage-position coverage of the slots is carried by
   the SumEqListFeed restatement shims; the eight usage stations match the
   sum_eq_list usage shapes of slots 2-5 station by station.

   Verdict: the four forwarding theorems below are the extractable exits
   of the four slot verifications - each statement is the verbatim
   counterpart of the corresponding idt host verification theorem. The
   host files themselves are untouched.
   ============================================================ *)

Require Import AttnDoeblin.
Require Import IdSlotTranslate.

Section SumEqListMarkWriteoff.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Local Existing Instance RI_base.

(* Slot AttnDoeblin:485 verification forward (usage positions carried by
   SumEqListFeed section 1). *)
Theorem sem_czb12_slot_attdoeblin_writeoff :
  forall (en : list S) (g : S -> S01_BaseRing.R),
    Id (idt_sumf en g) (AttnDoeblin.bs_list_sum g en).
Proof. intros en g. exact (idt_slot_attdoeblin en g). Qed.

(* Slot G01_CoreMicro:476 verification forward (usage positions carried by
   SumEqListFeed section 3). *)
Theorem sem_czb12_slot_g01_writeoff :
  forall (en : list S) (g : S -> S01_BaseRing.R),
    Id (idt_sumf en g) (AttnDoeblin.bs_list_sum g en).
Proof. intros en g. exact (idt_slot_g01 en g). Qed.

(* Slot S13_NLiveAudit:2676 verification forward (usage positions carried by
   SumEqListFeed section 2). *)
Theorem sem_czb12_slot_s13_writeoff :
  forall (en : list S) (g : S -> S01_BaseRing.R),
    Id (idt_sumf en g) (S13_NLiveAudit.bs_list_sum g en).
Proof. intros en g. exact (idt_slot_s13 en g). Qed.

(* Slot S15_TailFEPUp:147 verification forward (usage positions carried by
   SumEqListFeed section 3). *)
Theorem sem_czb12_slot_s15_writeoff :
  forall (en : list S) (g : S -> S01_BaseRing.R),
    Id (idt_sumf en g) (S13_NLiveAudit.bs_list_sum g en).
Proof. intros en g. exact (idt_slot_s15 en g). Qed.

End SumEqListMarkWriteoff.

(* ============ Gate evidence: the forwarding four are all Closed ============ *)
Print Assumptions sem_czb12_slot_attdoeblin_writeoff.
Print Assumptions sem_czb12_slot_g01_writeoff.
Print Assumptions sem_czb12_slot_s13_writeoff.
Print Assumptions sem_czb12_slot_s15_writeoff.
